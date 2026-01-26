------------------------------ MODULE GatewayExposureHarness ------------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* GatewayExposureHarness.tla
*
* Models the class of incident:
*   "Gateway bound beyond loopback with auth.mode=none => remote attacker can connect"
*
* Code references:
*   - clawdbot/src/gateway/auth.ts (authorizeGatewayConnect)
*   - clawdbot/src/security/audit.ts (collectGatewayConfigFindings -> gateway.bind_no_auth)
*
* We keep this minimal but attacker-driven:
*   - attacker attempts to connect from remote IP
*   - authorization decision depends on bind/auth
*   - if connected, attacker can invoke a sensitive tool
******************************************************************************)

CONSTANTS
  BindMode,        \* "loopback" or "non-loopback" (coarse)
  AuthMode,        \* "none" | "token" | "password"
  HasCredential     \* BOOLEAN: attacker presents valid creds (if required)

ASSUME
  /\ BindMode \in {"loopback", "non-loopback"}
  /\ AuthMode \in {"none", "token", "password"}
  /\ HasCredential \in BOOLEAN

VARIABLES connected, invokedSensitive, auditFindings
vars == << connected, invokedSensitive, auditFindings >>

\* Authorization model (coarse):
\* - If bind is loopback, remote attacker cannot reach the gateway.
\* - If bind is non-loopback and auth.mode=none, connect succeeds.
\* - Otherwise connect requires valid credential.
Authorize ==
  IF BindMode = "loopback" THEN FALSE
  ELSE IF AuthMode = "none" THEN TRUE ELSE HasCredential

\* Deep security audit check modeled after audit.ts: bind beyond loopback without auth.
AuditBindNoAuth == (BindMode = "non-loopback") /\ (AuthMode = "none")

Init ==
  /\ connected = FALSE
  /\ invokedSensitive = FALSE
  /\ auditFindings = << >>

AttackerConnect ==
  /\ ~connected
  /\ connected' = Authorize
  /\ auditFindings' = IF AuditBindNoAuth THEN Append(auditFindings, "gateway.bind_no_auth") ELSE auditFindings
  /\ UNCHANGED invokedSensitive

AttackerInvokeSensitive ==
  /\ connected
  /\ ~invokedSensitive
  /\ invokedSensitive' = TRUE
  /\ UNCHANGED << connected, auditFindings >>

Next == AttackerConnect \/ AttackerInvokeSensitive

Spec == Init /\ [][Next]_vars

\* Security property: if bind is non-loopback and auth is none, remote compromise is reachable.
\* (This is a *reachability* check; we encode it as a negated safety property for TLC.)
Inv_NotCompromised == ~invokedSensitive

\* Audit property: in the dangerous config, audit should report gateway.bind_no_auth.
Inv_AuditFlagsOpenGateway ==
  AuditBindNoAuth => (connected => (\E i \in 1..Len(auditFindings): auditFindings[i] = "gateway.bind_no_auth"))

=============================================================================
