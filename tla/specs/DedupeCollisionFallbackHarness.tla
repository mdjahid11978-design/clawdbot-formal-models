------------------------ MODULE DedupeCollisionFallbackHarness ------------------------
EXTENDS Naturals

(******************************************************************************
* DedupeCollisionFallbackHarness.tla
*
* Safety model:
* - Two distinct logical events exist.
* - Primary dedupe key may collide.
* - A fallback key (event id) prevents loss/merging.
*
* We model a store of seen keys. If primary keys collide, the system must use
* a fallback key so both events can be emitted (at-most-once each) without
* collapsing into one.
******************************************************************************)

CONSTANTS
  Events,         \* {"e1","e2"}
  Keys,           \* finite set of primary keys
  KeyE1,          \* primary key for e1
  KeyE2,          \* primary key for e2
  UseFallback     \* BOOLEAN toggle: whether fallback is enabled

ASSUME
  /\ Events = {"e1","e2"}
  /\ Keys /= {}
  /\ KeyE1 \in Keys
  /\ KeyE2 \in Keys
  /\ UseFallback \in BOOLEAN

VARIABLES
  pending,        \* SUBSET Events
  emitted,        \* SUBSET Events
  seenPrimary,    \* SUBSET Keys
  seenFallback    \* SUBSET Events

Init ==
  /\ pending = Events
  /\ emitted = {}
  /\ seenPrimary = {}
  /\ seenFallback = {}

PKey(e) == IF e = "e1" THEN KeyE1 ELSE KeyE2

CanEmit(e) ==
  IF UseFallback
    THEN e \notin seenFallback
    ELSE PKey(e) \notin seenPrimary

Emit(e) ==
  /\ e \in pending
  /\ CanEmit(e)
  /\ pending' = pending \ {e}
  /\ emitted' = emitted \cup {e}
  /\ seenPrimary' = seenPrimary \cup {PKey(e)}
  /\ seenFallback' = IF UseFallback THEN seenFallback \cup {e} ELSE seenFallback

DropAsDuplicate(e) ==
  /\ e \in pending
  /\ ~CanEmit(e)
  /\ pending' = pending \ {e}
  /\ emitted' = emitted
  /\ seenPrimary' = seenPrimary
  /\ seenFallback' = seenFallback

Stutter ==
  /\ pending' = pending
  /\ emitted' = emitted
  /\ seenPrimary' = seenPrimary
  /\ seenFallback' = seenFallback

Next == (\E e \in Events: Emit(e) \/ DropAsDuplicate(e)) \/ Stutter

\* At-most-once: emitted is a set, but we assert monotonicity.
Inv_EmittedMonotone == emitted \subseteq emitted'

\* Key property: If fallback is enabled, both distinct events can be emitted even if primary keys collide.
\* Encoded as a safety condition: we never drop a distinct event due to primary collision when fallback is on.
Inv_NoLossUnderFallback ==
  UseFallback => (pending = {} => emitted = Events)

Spec == Init /\ [][Next]_<<pending, emitted, seenPrimary, seenFallback>>

=============================================================================
