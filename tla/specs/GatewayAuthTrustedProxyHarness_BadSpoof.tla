------------------------------ MODULE GatewayAuthTrustedProxyHarness_BadSpoof ------------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* BUG: ignores forwarded headers when determining localDirect.
******************************************************************************)

CONSTANTS
  BindResolved, AuthMode, HasCredential,
  ClientIsLoopback, HostIsLocal, HasForwardedHeaders, RemoteIsTrustedProxy

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

\* BUG: doesn't check forwarded headers
LocalDirect == ClientIsLoopback /\ HostIsLocal

Authorize ==
  IF BindResolved = "loopback" THEN FALSE
  ELSE IF AuthMode = "token" \/ AuthMode = "password" THEN HasCredential
  ELSE TRUE

Init == /\ connected = FALSE /\ invoked = FALSE
Connect == /\ ~connected /\ connected' = Authorize /\ UNCHANGED invoked
InvokeSensitive == /\ connected /\ ~invoked /\ invoked' = TRUE /\ UNCHANGED connected
Next == Connect \/ InvokeSensitive
Spec == Init /\ [][Next]_vars

Inv_NoLocalDirectViaSpoof == (HasForwardedHeaders /\ ~RemoteIsTrustedProxy) => ~LocalDirect

=============================================================================
