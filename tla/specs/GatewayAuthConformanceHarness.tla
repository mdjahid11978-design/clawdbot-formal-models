------------------------------ MODULE GatewayAuthConformanceHarness ------------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* GatewayAuthConformanceHarness.tla
*
* A more code-shaped model of gateway authorization decisions.
*
* This is NOT a full reimplementation of gateway/auth.ts, but it captures the
* security-relevant branches:
*   - local-direct (loopback + localhost host + no forwarded headers)
*   - auth modes: none|token|password (auto resolution via presence)
*   - remote attacker cannot be local-direct
*   - if mode=none and bind is non-loopback => attacker can connect
*
* Target claim:
*   Unsafe config (bind beyond loopback + auth resolves to none) => remote
*   attacker can connect and invoke sensitive tools.
******************************************************************************)

CONSTANTS
  BindResolved,      \* "loopback"|"non-loopback"
  HasToken,          \* BOOLEAN
  HasPassword,       \* BOOLEAN
  ModeConfig,        \* "auto"|"none"|"token"|"password"
  AttackerHasCreds,  \* BOOLEAN

  \* request properties (remote attacker)
  RemoteIpIsLoopback,    \* BOOLEAN (should be FALSE for remote attacker)
  HostIsLocal,           \* BOOLEAN
  HasForwardedHeaders,   \* BOOLEAN
  TrustedProxy,          \* BOOLEAN

  \* audit
  AuditEnabled           \* BOOLEAN (we record finding only if enabled)

ASSUME
  /\ BindResolved \in {"loopback","non-loopback"}
  /\ HasToken \in BOOLEAN
  /\ HasPassword \in BOOLEAN
  /\ ModeConfig \in {"auto","none","token","password"}
  /\ AttackerHasCreds \in BOOLEAN
  /\ RemoteIpIsLoopback \in BOOLEAN
  /\ HostIsLocal \in BOOLEAN
  /\ HasForwardedHeaders \in BOOLEAN
  /\ TrustedProxy \in BOOLEAN
  /\ AuditEnabled \in BOOLEAN

ResolvedMode ==
  IF ModeConfig = "none" THEN "none"
  ELSE IF ModeConfig = "token" THEN "token"
  ELSE IF ModeConfig = "password" THEN "password"
  ELSE IF HasPassword THEN "password" ELSE IF HasToken THEN "token" ELSE "none"

\* localDirect mirrors the intent of isLocalDirectRequest:
\* loopback client IP + local host + (no forwarded headers OR trusted proxy)
LocalDirect ==
  RemoteIpIsLoopback /\ HostIsLocal /\ (~HasForwardedHeaders \/ TrustedProxy)

\* Remote attacker can't be local-direct in the typical threat model.
\* We keep it as a constant so we can model misclassification bugs later.

Authorize ==
  IF BindResolved = "loopback" THEN FALSE
  ELSE IF ResolvedMode = "none" THEN TRUE
  ELSE AttackerHasCreds

AuditBindNoAuth == (BindResolved = "non-loopback") /\ (ResolvedMode = "none")

VARIABLES connected, invokedSensitive, auditFindings
vars == << connected, invokedSensitive, auditFindings >>

Init ==
  /\ connected = FALSE
  /\ invokedSensitive = FALSE
  /\ auditFindings = << >>

Connect ==
  /\ ~connected
  /\ connected' = Authorize
  /\ auditFindings' =
      IF AuditEnabled /\ AuditBindNoAuth THEN Append(auditFindings, "gateway.bind_no_auth") ELSE auditFindings
  /\ UNCHANGED invokedSensitive

InvokeSensitive ==
  /\ connected
  /\ ~invokedSensitive
  /\ invokedSensitive' = TRUE
  /\ UNCHANGED << connected, auditFindings >>

Next == Connect \/ InvokeSensitive
Spec == Init /\ [][Next]_vars

Inv_NotCompromised == ~invokedSensitive

Inv_AuditFlagsOpenGateway ==
  (AuditEnabled /\ AuditBindNoAuth /\ connected) =>
    (\E i \in 1..Len(auditFindings): auditFindings[i] = "gateway.bind_no_auth")

=============================================================================
