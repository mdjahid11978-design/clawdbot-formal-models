------------------------------ MODULE RoutingIdentityLinksSymmetryHarness_BadAsymmetric ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* RoutingIdentityLinksSymmetryHarness_BadAsymmetric.tla
*
* "Red" variant: buggy Linked relation is asymmetric.
*
* We model a directional mapping (e.g., identityLinks stored one-way) and define
* Linked(a,b) based on membership in DirectedLinks, WITHOUT symmetric closure.
******************************************************************************)

CONSTANTS
  Peers

ASSUME
  /\ Peers /= {}

\* BUG: directional hard-coded link (asymmetric).
Linked(a,b) == (a = 1 /\ b = 2)

Inv_Reflexive == \A p \in Peers: Linked(p,p)
Inv_Symmetric == \A a \in Peers: \A b \in Peers: Linked(a,b) => Linked(b,a)

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
