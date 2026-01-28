------------------------------ MODULE RoutingIdentityLinksSymmetryHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* RoutingIdentityLinksSymmetryHarness.tla
*
* Routing nuance (R3++++): identityLinks must be symmetric (and reflexive).
*
* Motivation:
*   If routing collapses identities based on a linking relation, the relation
*   should behave like an equivalence relation. We already check a transitive
*   closure case elsewhere; this harness focuses on symmetry/reflexivity.
*
* Model:
*   - LinkGroups is a set of peer-sets; being in the same group means linked.
******************************************************************************)

CONSTANTS
  Peers,
  LinkGroups

ASSUME
  /\ Peers /= {}
  /\ LinkGroups \subseteq SUBSET Peers

Linked(a,b) == \E g \in LinkGroups: a \in g /\ b \in g

Inv_Reflexive == \A p \in Peers: Linked(p,p)
Inv_Symmetric == \A a \in Peers: \A b \in Peers: Linked(a,b) => Linked(b,a)

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
