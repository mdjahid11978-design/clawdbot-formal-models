------------------------------ MODULE RoutingIdentityLinksChannelOverrideHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* RoutingIdentityLinksChannelOverrideHarness.tla
*
* Routing nuance (R3+++++): per-channel override can DISABLE identityLinks.
*
* Motivation:
*   Even if identities are globally linkable (identityLinks exist), a specific
*   channel may want strict per-peer DM routing (no cross-identity collapse).
*
* Model:
*   - GlobalAllowIdentityLinks: BOOLEAN
*   - ChannelAllowIdentityLinks: BOOLEAN (override)
*   - LinkGroups: set of peer sets that define linking
*
* Precedence rule:
*   EffectiveAllowIdentityLinks == ChannelAllowIdentityLinks
*
* Safety:
*   If EffectiveAllowIdentityLinks = FALSE, then distinct peers must not
*   collapse to the same session key.
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

\* Direct link if a and b appear together in some group.
DirectLinked(a,b) == \E g \in LinkGroups: a \in g /\ b \in g

MaxLen == Cardinality(Peers)

Reachable(a,b) ==
  \E n \in 1..MaxLen:
    \E path \in [1..n -> Peers]:
      /\ path[1] = a
      /\ path[n] = b
      /\ \A i \in 1..(n-1): DirectLinked(path[i], path[i+1])

\* Global linking relation (if enabled).
LinkedGlobal(a,b) == (a=b) \/ Reachable(a,b)

EffectiveAllowIdentityLinks == ChannelAllowIdentityLinks

LinkedEffective(a,b) ==
  IF EffectiveAllowIdentityLinks THEN LinkedGlobal(a,b) ELSE (a=b)

SessionKey(p) ==
  CHOOSE r \in Peers: \A q \in Peers: LinkedEffective(p,q) <=> LinkedEffective(r,q)

Inv_ChannelOverrideWins == EffectiveAllowIdentityLinks = ChannelAllowIdentityLinks

Inv_NoCollapseWhenDisabled ==
  ~EffectiveAllowIdentityLinks =>
    \A p1 \in Peers: \A p2 \in Peers:
      (p1 /= p2) => (SessionKey(p1) /= SessionKey(p2))

\* Trivial behavior for TLC
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
