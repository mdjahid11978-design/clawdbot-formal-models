--------------------------- MODULE NoCrossStreamLeakageHarness ---------------------------
EXTENDS Naturals

(******************************************************************************
* NoCrossStreamLeakageHarness.tla
*
* Reliability/correctness model:
* - Multiple logical events may be in flight.
* - Retries must not cause an event to be emitted under another event’s
*   session binding (no cross-stream leakage).
*
* We track which session keys are ever used while processing each event.
* SessionKey(e) is intended to be <<RouteOf[e], e>>.
******************************************************************************)

CONSTANTS
  Events,        \* finite set of event ids
  Routes,        \* finite set of route ids
  RouteE1,       \* intended route for "e1"
  RouteE2        \* intended route for "e2"

ASSUME
  /\ Events = {"e1","e2"}
  /\ Routes /= {}
  /\ RouteE1 \in Routes
  /\ RouteE2 \in Routes

VARIABLES
  pending,        \* SUBSET Events
  emitted,        \* SUBSET Events
  togg,           \* [Events -> {0,1}] (tiny retry/progress bit)
  seenSessions    \* [Events -> SUBSET (Routes \X Events)] (sessionKey = <<route,event>>)

Init ==
  /\ pending = Events
  /\ emitted = {}
  /\ togg = [e \in Events |-> 0]
  /\ seenSessions = [e \in Events |-> {}]

RouteOf(e) == IF e = "e1" THEN RouteE1 ELSE RouteE2

SessionKeyNow(e) == <<RouteOf(e), e>>

Record(e) ==
  /\ seenSessions' = [seenSessions EXCEPT ![e] = @ \cup {SessionKeyNow(e)}]

\* transient retry/failure
Fail(e) ==
  /\ e \in pending
  /\ pending' = pending
  /\ emitted' = emitted
  /\ togg' = [togg EXCEPT ![e] = 1 - @]
  /\ Record(e)

\* success emit
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

\* No cross-stream leakage: each event only ever uses its own session key.
Inv_NoCrossStreamLeakage ==
  \A e \in Events: seenSessions[e] \subseteq {<<RouteOf(e), e>>}

Spec == Init /\ [][Next]_<<pending, emitted, togg, seenSessions>>

=============================================================================
