----------- MODULE GatewayAuthTrustedProxyHeaderSpoofHarness_BadTrustHeadersAlways -----------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: forwarded identity headers are trusted even when the connection is not
* from a trusted proxy.
******************************************************************************)

CONSTANTS
  TrustedProxy,
  HeaderClaimsUser,
  BackendAcceptsUser

ASSUME
  /\ TrustedProxy \in BOOLEAN
  /\ HeaderClaimsUser \in BOOLEAN
  /\ BackendAcceptsUser \in BOOLEAN

\* BUG: ignore TrustedProxy bit
Authorized == HeaderClaimsUser /\ BackendAcceptsUser

Inv_NoSpoofWithoutTrustedProxy ==
  (~TrustedProxy /\ HeaderClaimsUser /\ BackendAcceptsUser) => ~Authorized

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
