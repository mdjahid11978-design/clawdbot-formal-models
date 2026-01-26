------------------------------ MODULE GatewayAuthTrustedProxyHarness ------------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* GatewayAuthTrustedProxyHarness.tla
*
* Bounded micro-harness for the trusted-proxy / forwarded header rule.
*
* Intent (from src/gateway/auth.ts): localDirect only if:
*   - client IP is loopback
*   - host header is local
*   - and (no forwarded headers OR remote is a trusted proxy)
*
* We model an attacker attempting to appear localDirect by using forwarded headers.
******************************************************************************)

CONSTANTS
  BindResolved,        \* "loopback"|"non-loopback"
  AuthMode,            \* "none"|"token"|"password"
  HasCredential,       \* BOOLEAN

  ClientIsLoopback,    \* BOOLEAN
  HostIsLocal,         \* BOOLEAN
  HasForwardedHeaders, \* BOOLEAN
  RemoteIsTrustedProxy \* BOOLEAN

ASSUME
  /\ BindResolved \in {"loopback","non-loopback"}
  /\ AuthMode \in {"none","token","password"}
  /\ HasCredential \in BOOLEAN
  /\ ClientIsLoopback \in BOOLEAN
  /\ HostIsLocal \in BOOLEAN
  /\ HasForwardedHeaders \in BOOLEAN
  /\ RemoteIsTrustedProxy \in BOOLEAN

VARIABLES connected, invoked
vars == << connected, invoked >>

LocalDirect == ClientIsLoopback /\ HostIsLocal /\ (~HasForwardedHeaders \/ RemoteIsTrustedProxy)

Authorize ==
  IF BindResolved = "loopback" THEN FALSE
  ELSE IF AuthMode = "token" \/ AuthMode = "password" THEN HasCredential
  ELSE TRUE

Init == /\ connected = FALSE /\ invoked = FALSE

Connect ==
  /\ ~connected
  /\ connected' = Authorize
  /\ UNCHANGED invoked

InvokeSensitive ==
  /\ connected
  /\ ~invoked
  /\ invoked' = TRUE
  /\ UNCHANGED connected

Next == Connect \/ InvokeSensitive
Spec == Init /\ [][Next]_vars

\* Property: if forwarded headers exist and remote is NOT trusted proxy,
\* request must not be considered localDirect.
Inv_NoLocalDirectViaSpoof == (HasForwardedHeaders /\ ~RemoteIsTrustedProxy) => ~LocalDirect

=============================================================================
