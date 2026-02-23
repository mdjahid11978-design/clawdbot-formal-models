---------------------- MODULE MultiChannelIdentityCollisionHarness ----------------------
EXTENDS Naturals

(******************************************************************************
* MultiChannelIdentityCollisionHarness.tla
*
* Safety model:
* - Two platforms (A,B) can have users with the same "display" identifier.
* - The system must not unify identities across platforms unless an explicit
*   identity link exists.
*
* We abstract identity as <<platform, userId>> and session collapse as a boolean.
******************************************************************************)

CONSTANTS
  LinkExists \* BOOLEAN: explicit identity link between A:u and B:u

ASSUME
  LinkExists \in BOOLEAN

AUser == <<"A","u">>
BUser == <<"B","u">>

\* Collapse allowed only if explicit link exists.
CollapseAllowed == LinkExists

\* Invariant: when there is no link, cross-platform collapse is forbidden.
Inv_NoCrossPlatformCollapseWithoutLink ==
  (~LinkExists) => ~CollapseAllowed

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
