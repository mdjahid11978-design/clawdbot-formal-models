------------------- MODULE DiscordInteractionRoleThreadHarness -------------------
EXTENDS Naturals

(******************************************************************************
* DiscordInteractionRoleThreadHarness.tla
*
* Combined security/conformance model:
* - Interactions can be retried (same interaction id).
* - Interactions in threads must use parent context.
* - Role gating must be enforced (no bypass on retry).
*
* We model a single interaction id "i" executed at most once, and require role
* when the *parent* requires it.
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

\* Thread-parent binding for permission context
EffectiveRequiresRole(isThread) == IF isThread THEN ParentRequiresRole ELSE ThreadRequiresRole

Authorized(isThread) == IF EffectiveRequiresRole(isThread) THEN HasRequiredRole ELSE TRUE

Handle(isThread) ==
  /\ Interaction \in pending
  /\ IF Interaction \in seen
        THEN /\ pending' = pending \ {Interaction}
             /\ seen' = seen
             /\ executed' = executed
        ELSE /\ Authorized(isThread)
             /\ pending' = pending \ {Interaction}
             /\ seen' = seen \cup {Interaction}
             /\ executed' = executed \cup {Interaction}

Retry ==
  /\ Interaction \in pending
  /\ pending' = pending
  /\ UNCHANGED <<seen, executed>>

Stutter == UNCHANGED <<pending, seen, executed>>

Next == Handle(TRUE) \/ Retry \/ Stutter

Inv_NoRoleBypassInThread == (EffectiveRequiresRole(TRUE) /\ ~HasRequiredRole) => ~(Interaction \in executed)
Inv_AtMostOnce == executed \subseteq seen

Spec == Init /\ [][Next]_<<pending, seen, executed>>

=============================================================================
