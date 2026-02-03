------------- MODULE DiscordInteractionRoleThreadHarness_BadBypassOnRetry -------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: on retry (when already seen), the system executes without re-checking
* authorization (or treats retry as authorized).
*
* This can allow a non-member to trigger execution by racing a retry path.
******************************************************************************)

CONSTANTS
  ParentRequiresRole,
  ThreadRequiresRole,
  HasRequiredRole

ASSUME
  /\ ParentRequiresRole \in BOOLEAN
  /\ ThreadRequiresRole \in BOOLEAN
  /\ HasRequiredRole \in BOOLEAN

Interaction == "i"

VARIABLES
  pending,
  seen,
  executed

Init ==
  /\ pending = {Interaction}
  /\ seen = {}
  /\ executed = {}

EffectiveRequiresRole(isThread) == IF isThread THEN ParentRequiresRole ELSE ThreadRequiresRole

Authorized(isThread) == IF EffectiveRequiresRole(isThread) THEN HasRequiredRole ELSE TRUE

\* BUG: retry path executes even if unauthorized
Handle(isThread) ==
  /\ Interaction \in pending
  /\ IF Interaction \in seen
        THEN /\ pending' = pending \ {Interaction}
             /\ seen' = seen
             /\ executed' = executed \cup {Interaction}
        ELSE /\ Authorized(isThread)
             /\ pending' = pending \ {Interaction}
             /\ seen' = seen \cup {Interaction}
             /\ executed' = executed \cup {Interaction}

\* BUG: also allow a retry to mark seen without auth
Retry ==
  /\ Interaction \in pending
  /\ pending' = pending
  /\ seen' = seen \cup {Interaction}
  /\ executed' = executed

Stutter == UNCHANGED <<pending, seen, executed>>

Next == Handle(TRUE) \/ Retry \/ Stutter

Inv_NoRoleBypassInThread == (EffectiveRequiresRole(TRUE) /\ ~HasRequiredRole) => ~(Interaction \in executed)

Spec == Init /\ [][Next]_<<pending, seen, executed>>

=============================================================================
