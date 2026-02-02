-------------- MODULE DiscordRoleGatingThreadParentHarness_BadThreadOverridesRole --------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: thread context overrides parent context (or disables role gating).
* This can authorize actions in threads even when parent requires a role.
******************************************************************************)

CONSTANTS
  ParentRequiresRole,
  ThreadRequiresRole,
  HasRequiredRole

ASSUME
  /\ ParentRequiresRole \in BOOLEAN
  /\ ThreadRequiresRole \in BOOLEAN
  /\ HasRequiredRole \in BOOLEAN

\* BUG: use thread context even when isThread
EffectiveRequiresRole(isThread) == ThreadRequiresRole

Authorized(isThread) == IF EffectiveRequiresRole(isThread) THEN HasRequiredRole ELSE TRUE

Inv_NoRoleNoAuthInThread == (ParentRequiresRole /\ ~HasRequiredRole) => ~Authorized(TRUE)

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
