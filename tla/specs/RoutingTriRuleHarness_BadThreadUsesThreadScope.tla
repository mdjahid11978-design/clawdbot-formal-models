------------------ MODULE RoutingTriRuleHarness_BadThreadUsesThreadScope ------------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: thread messages use the thread channel scope instead of parent scope.
* This can accidentally allow collapses when parent intended per-peer.
******************************************************************************)

CONSTANTS
  GlobalScope,
  ParentScope,
  ThreadScope,
  HasIdentityLink

ASSUME
  /\ GlobalScope \in {"main","per-peer"}
  /\ ParentScope \in {"main","per-peer"}
  /\ ThreadScope \in {"main","per-peer"}
  /\ HasIdentityLink \in BOOLEAN

\* BUG: thread-parent binding ignored
BindScope(isThread) == ThreadScope

EffectiveScope(isThread) == BindScope(isThread)

CollapseAllowed(isThread) == (EffectiveScope(isThread) = "main") /\ HasIdentityLink

Inv_ThreadUsesParent == EffectiveScope(TRUE) = ParentScope

Inv_NoCollapseWhenParentPerPeer ==
  (ParentScope = "per-peer") => ~CollapseAllowed(TRUE)

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
