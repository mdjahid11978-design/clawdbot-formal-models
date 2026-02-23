------------------- MODULE DedupeCollisionFallbackHarness_BadNoFallback -------------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: fallback is disabled, and primary keys collide, so one distinct event
* will be dropped as a duplicate.
******************************************************************************)

CONSTANTS
  Events,
  Keys,
  KeyE1,
  KeyE2

ASSUME
  /\ Events = {"e1","e2"}
  /\ Keys /= {}
  /\ KeyE1 \in Keys
  /\ KeyE2 \in Keys

VARIABLES
  pending,
  emitted,
  seenPrimary

Init ==
  /\ pending = Events
  /\ emitted = {}
  /\ seenPrimary = {}

PKey(e) == IF e = "e1" THEN KeyE1 ELSE KeyE2

CanEmit(e) == PKey(e) \notin seenPrimary

Emit(e) ==
  /\ e \in pending
  /\ CanEmit(e)
  /\ pending' = pending \ {e}
  /\ emitted' = emitted \cup {e}
  /\ seenPrimary' = seenPrimary \cup {PKey(e)}

DropAsDuplicate(e) ==
  /\ e \in pending
  /\ ~CanEmit(e)
  /\ pending' = pending \ {e}
  /\ emitted' = emitted
  /\ seenPrimary' = seenPrimary

Stutter ==
  /\ pending' = pending
  /\ emitted' = emitted
  /\ seenPrimary' = seenPrimary

Next == (\E e \in Events: Emit(e) \/ DropAsDuplicate(e)) \/ Stutter

\* Invariant that SHOULD hold if dedupe were collision-safe, but will fail here.
Inv_NoLoss == (pending = {} => emitted = Events)

Spec == Init /\ [][Next]_<<pending, emitted, seenPrimary>>

=============================================================================
