---------------------- MODULE NoCrossStreamLeakageHarness_BadSwap ----------------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: on alternating retries, we (incorrectly) use another event’s route when
* constructing the session key, causing cross-stream leakage.
******************************************************************************)

CONSTANTS
  Events,
  Routes,
  RouteE1,
  RouteE2

ASSUME
  /\ Events = {"e1","e2"}
  /\ Routes /= {}
  /\ RouteE1 \in Routes
  /\ RouteE2 \in Routes

VARIABLES
  pending,
  emitted,
  togg,
  seenSessions

Init ==
  /\ pending = Events
  /\ emitted = {}
  /\ togg = [e \in Events |-> 0]
  /\ seenSessions = [e \in Events |-> {}]

RouteOf(e) == IF e = "e1" THEN RouteE1 ELSE RouteE2
Other(e) == IF e = "e1" THEN "e2" ELSE "e1"

\* BUG: if togg[e]=1, use RouteOf(Other(e))
SessionKeyNow(e) ==
  IF togg[e] = 0
    THEN <<RouteOf(e), e>>
    ELSE <<RouteOf(Other(e)), e>>

Record(e) ==
  /\ seenSessions' = [seenSessions EXCEPT ![e] = @ \cup {SessionKeyNow(e)}]

Fail(e) ==
  /\ e \in pending
  /\ pending' = pending
  /\ emitted' = emitted
  /\ togg' = [togg EXCEPT ![e] = 1 - @]
  /\ Record(e)

Success(e) ==
  /\ e \in pending
  /\ pending' = pending \ {e}
  /\ emitted' = emitted \cup {e}
  /\ togg' = togg
  /\ Record(e)

Stutter ==
  /\ pending' = pending
  /\ emitted' = emitted
  /\ togg' = togg
  /\ seenSessions' = seenSessions

Next ==
  (\E e \in Events: Fail(e) \/ Success(e)) \/ Stutter

Inv_NoCrossStreamLeakage ==
  \A e \in Events: seenSessions[e] \subseteq {<<RouteOf(e), e>>}

Spec == Init /\ [][Next]_<<pending, emitted, togg, seenSessions>>

=============================================================================
