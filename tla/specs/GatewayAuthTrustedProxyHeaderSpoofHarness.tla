------------------ MODULE GatewayAuthTrustedProxyHeaderSpoofHarness ------------------
EXTENDS Naturals

(******************************************************************************
* GatewayAuthTrustedProxyHeaderSpoofHarness.tla
*
* Security conformance harness (tiny):
* - In "trusted proxy" mode, we only trust forwarded identity headers if the
*   request comes from a trusted proxy.
* - Attack: direct client spoofs X-Forwarded-User (or similar) header.
*
* Property: without TrustedProxy=true, header-based auth must NOT grant access.
******************************************************************************)

CONSTANTS
  TrustedProxy,         \* BOOLEAN: whether connection is from trusted proxy
  HeaderClaimsUser,     \* BOOLEAN: whether request contains forwarded user header
  BackendAcceptsUser    \* BOOLEAN: whether backend auth gate would accept that user

ASSUME
  /\ TrustedProxy \in BOOLEAN
  /\ HeaderClaimsUser \in BOOLEAN
  /\ BackendAcceptsUser \in BOOLEAN

\* Authorization rule:
\* Only consider header claims if connection is trusted.
Authorized ==
  IF TrustedProxy
    THEN (HeaderClaimsUser /\ BackendAcceptsUser)
    ELSE FALSE

Inv_NoSpoofWithoutTrustedProxy ==
  (~TrustedProxy /\ HeaderClaimsUser /\ BackendAcceptsUser) => ~Authorized

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
