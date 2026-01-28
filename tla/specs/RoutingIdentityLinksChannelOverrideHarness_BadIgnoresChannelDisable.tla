------------------------------ MODULE RoutingIdentityLinksChannelOverrideHarness_BadIgnoresChannelDisable ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* RoutingIdentityLinksChannelOverrideHarness_BadIgnoresChannelDisable.tla
*
* "Red" variant: ignores ChannelAllowIdentityLinks and uses the global flag.
*
* If GlobalAllowIdentityLinks=TRUE but ChannelAllowIdentityLinks=FALSE, routing
* should be strict, but this buggy model still collapses linked peers.
******************************************************************************)

CONSTANTS
  Peers,
  LinkGroups,
  GlobalAllowIdentityLinks,
  ChannelAllowIdentityLinks

ASSUME
  /\ Peers /= {}
  /\ LinkGroups \subseteq SUBSET Peers
  /\ GlobalAllowIdentityLinks \in BOOLEAN
  /\ ChannelAllowIdentityLinks \in BOOLEAN

DirectLinked(a,b) == \E g \in LinkGroups: a \in g /\ b \in g

MaxLen == Cardinality(Peers)

Reachable(a,b) ==
  \E n \in 1..MaxLen:
    \E path \in [1..n -> Peers]:
      /\ path[1] = a
      /\ path[n] = b
      /\ \A i \in 1..(n-1): DirectLinked(path[i], path[i+1])

LinkedGlobal(a,b) == (a=b) \/ Reachable(a,b)

\* BUG: precedence is wrong.
EffectiveAllowIdentityLinks == GlobalAllowIdentityLinks

LinkedEffective(a,b) ==
  IF EffectiveAllowIdentityLinks THEN LinkedGlobal(a,b) ELSE (a=b)

SessionKey(p) ==
  CHOOSE r \in Peers: \A q \in Peers: LinkedEffective(p,q) <=> LinkedEffective(r,q)

Inv_ChannelOverrideWins == EffectiveAllowIdentityLinks = ChannelAllowIdentityLinks

Inv_NoCollapseWhenDisabled ==
  ~EffectiveAllowIdentityLinks =>
    \A p1 \in Peers: \A p2 \in Peers:
      (p1 /= p2) => (SessionKey(p1) /= SessionKey(p2))

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
