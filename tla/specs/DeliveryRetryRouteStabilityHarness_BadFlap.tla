---------------- MODULE DeliveryRetryRouteStabilityHarness_BadFlap ----------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: routing flaps based on attempt count parity, so retries can bind to a
* different route/session key for the same event.
******************************************************************************)

CONSTANTS
  Events,
  Routes,
  MaxAttempts,
  Route0Route

ASSUME
  /\ Events /= {}
  /\ Routes /= {}
  /\ MaxAttempts \in Nat
  /\ MaxAttempts >= 1
  /\ Route0Route \in Routes

VARIABLES
  pending,
  emitted,
  attempts,
  seenRoutes,
  seenSessions

Init ==
  /\ pending = Events
  /\ emitted = {}
  /\ attempts = [e \in Events |-> 0]
  /\ seenRoutes = [e \in Events |-> {}]
  /\ seenSessions = [e \in Events |-> {}]

CanTry(e) == attempts[e] < MaxAttempts

\* BUG: route depends on attempt count (flaps between Route0Route and some other route).
AltRoute(r) == CHOOSE r2 \in Routes: r2 /= r

RouteNow(e) == IF attempts[e] % 2 = 0 THEN Route0Route ELSE AltRoute(Route0Route)
SessionKey(e) == <<RouteNow(e), e>>

Record(e) ==
  /\ seenRoutes' = [seenRoutes EXCEPT ![e] = @ \cup {RouteNow(e)}]
  /\ seenSessions' = [seenSessions EXCEPT ![e] = @ \cup {SessionKey(e)}]

ProcessFail(e) ==
  /\ e \in pending
  /\ CanTry(e)
  /\ pending' = pending
  /\ emitted' = emitted
  /\ attempts' = [attempts EXCEPT ![e] = @ + 1]
  /\ Record(e)

ProcessSuccess(e) ==
  /\ e \in pending
  /\ CanTry(e)
  /\ pending' = pending \ {e}
  /\ emitted' = emitted \cup {e}
  /\ attempts' = [attempts EXCEPT ![e] = @ + 1]
  /\ Record(e)

Drop(e) ==
  /\ e \in pending
  /\ ~CanTry(e)
  /\ pending' = pending \ {e}
  /\ emitted' = emitted
  /\ attempts' = attempts
  /\ seenRoutes' = seenRoutes
  /\ seenSessions' = seenSessions

Stutter ==
  /\ pending' = pending
  /\ emitted' = emitted
  /\ attempts' = attempts
  /\ seenRoutes' = seenRoutes
  /\ seenSessions' = seenSessions

Next ==
  (\E e \in Events:
     ProcessFail(e) \/ ProcessSuccess(e) \/ Drop(e))
  \/ Stutter

Inv_RouteStable ==
  \A e \in Events: seenRoutes[e] \subseteq {Route0Route}

Inv_SessionStable ==
  \A e \in Events: seenSessions[e] \subseteq {<<Route0Route, e>>}

Spec == Init /\ [][Next]_<<pending, emitted, attempts, seenRoutes, seenSessions>>

=============================================================================
