-------------------- MODULE DiscordRoleGatingThreadParentHarness --------------------
EXTENDS Naturals

(******************************************************************************
* DiscordRoleGatingThreadParentHarness.tla
*
* Combined conformance/security model:
* - Interactions inside a thread must inherit the parent channel context.
* - Role gating must still apply (no bypass in threads).
******************************************************************************)

CONSTANTS
  ParentRequiresRole,
  ThreadRequiresRole,
  HasRequiredRole

ASSUME
  /\ ParentRequiresRole \in BOOLEAN
  /\ ThreadRequiresRole \in BOOLEAN
  /\ HasRequiredRole \in BOOLEAN

\* Thread-parent binding: permission context should come from parent.
EffectiveRequiresRole(isThread) == IF isThread THEN ParentRequiresRole ELSE ThreadRequiresRole

Authorized(isThread) == IF EffectiveRequiresRole(isThread) THEN HasRequiredRole ELSE TRUE

Inv_NoRoleNoAuthInThread == (EffectiveRequiresRole(TRUE) /\ ~HasRequiredRole) => ~Authorized(TRUE)

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
