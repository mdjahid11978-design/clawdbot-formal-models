----------- MODULE MultiChannelIdentityCollisionHarness_BadDisplayNameUnifies -----------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: identities are unified based on a non-unique display identifier across
* platforms, effectively ignoring the LinkExists constraint.
******************************************************************************)

CONSTANTS
  LinkExists

ASSUME
  LinkExists \in BOOLEAN

\* BUG: collapse allowed regardless of explicit link
CollapseAllowed == TRUE

Inv_NoCrossPlatformCollapseWithoutLink ==
  (~LinkExists) => ~CollapseAllowed

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
