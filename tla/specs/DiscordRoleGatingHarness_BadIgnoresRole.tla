-------------------- MODULE DiscordRoleGatingHarness_BadIgnoresRole --------------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: role requirement is ignored, authorizing the action for everyone.
******************************************************************************)

CONSTANTS
  RequiresRole,
  HasRequiredRole

ASSUME
  /\ RequiresRole \in BOOLEAN
  /\ HasRequiredRole \in BOOLEAN

\* BUG: ignores role gating
Authorized == TRUE

Inv_NoRoleNoAuth == (RequiresRole /\ ~HasRequiredRole) => ~Authorized

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
