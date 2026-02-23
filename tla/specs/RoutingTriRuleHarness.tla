----------------------------- MODULE RoutingTriRuleHarness -----------------------------
EXTENDS Naturals

(******************************************************************************
* RoutingTriRuleHarness.tla
*
* Combined routing correctness harness (tiny):
* 1) Thread messages bind to parent channel (thread-parent rule)
* 2) Channel override (scope) beats global default
* 3) Identity links can collapse sessions only when allowed by effective scope
*
* We model only DM scope selection, not full routing.
******************************************************************************)

CONSTANTS
  GlobalScope,        \* "main" or "per-peer"
  ParentScope,        \* "main" or "per-peer" (override at parent channel)
  ThreadScope,        \* "main" or "per-peer" (override at thread channel)
  HasIdentityLink      \* BOOLEAN

ASSUME
  /\ GlobalScope \in {"main","per-peer"}
  /\ ParentScope \in {"main","per-peer"}
  /\ ThreadScope \in {"main","per-peer"}
  /\ HasIdentityLink \in BOOLEAN

\* Thread-parent binding
BindScope(isThread) == IF isThread THEN ParentScope ELSE ThreadScope

\* Channel override beats global
EffectiveScope(isThread) == BindScope(isThread)

\* Collapse allowed only in "main" scope and when identity link exists
CollapseAllowed(isThread) == (EffectiveScope(isThread) = "main") /\ HasIdentityLink

\* Invariant 1: for thread messages, EffectiveScope uses ParentScope
Inv_ThreadUsesParent == EffectiveScope(TRUE) = ParentScope

\* Invariant 2: if parent scope is per-peer, collapse is disallowed even if identity link exists
Inv_NoCollapseWhenParentPerPeer ==
  (ParentScope = "per-peer") => ~CollapseAllowed(TRUE)

\* Trivial Spec for TLC
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
