--------------------------- MODULE DiscordRoleGatingHarness ---------------------------
EXTENDS Naturals

(******************************************************************************
* DiscordRoleGatingHarness.tla
*
* Security/conformance model (tiny):
* - Certain Discord interactions (slash commands / button clicks / modals)
*   should be gated by role/permission checks when configured.
*
* We model a single action requiring a role and check that it cannot be
* authorized without that role.
******************************************************************************)

CONSTANTS
  RequiresRole,      \* BOOLEAN: whether this action is configured to require a role
  HasRequiredRole    \* BOOLEAN: whether the user has that role

ASSUME
  /\ RequiresRole \in BOOLEAN
  /\ HasRequiredRole \in BOOLEAN

Authorized == IF RequiresRole THEN HasRequiredRole ELSE TRUE

Inv_NoRoleNoAuth == (RequiresRole /\ ~HasRequiredRole) => ~Authorized

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
