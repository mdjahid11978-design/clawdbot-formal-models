---------------------- MODULE DeliveryRetryRouteStabilityHarness ----------------------
EXTENDS Naturals

(******************************************************************************
* DeliveryRetryRouteStabilityHarness.tla
*
* Non-security reliability/correctness model:
* - Ingress may retry delivering the same logical event.
* - Routing/session binding must be stable across retries for a given event.
*
* This abstracts “route resolution -> session key derivation -> emit”.
* We track all routes/sessionKeys observed during processing attempts.
******************************************************************************)

CONSTANTS
  Events,          \* finite set of event ids
  Routes,          \* finite set of route ids
  MaxAttempts,     \* small natural (e.g. 2 or 3)
  Route0Route      \* intended stable route id

ASSUME
  /\ Events /= {}
  /\ Routes /= {}
  /\ MaxAttempts \in Nat
  /\ MaxAttempts >= 1
  /\ Route0Route \in Routes

VARIABLES
  pending,         \* SUBSET Events
  emitted,         \* SUBSET Events
  attempts,        \* [Events -> Nat]
  seenRoutes,      \* [Events -> SUBSET Routes]
  seenSessions      \* [Events -> SUBSET (Routes \X Events)]  (sessionKey = <<route,event>>)

Init ==
  /\ pending = Events
  /\ emitted = {}
  /\ attempts = [e \in Events |-> 0]
  /\ seenRoutes = [e \in Events |-> {}]
  /\ seenSessions = [e \in Events |-> {}]

CanTry(e) == attempts[e] < MaxAttempts

RouteNow(e) == Route0Route
SessionKey(e) == <<RouteNow(e), e>>

Record(e) ==
  /\ seenRoutes' = [seenRoutes EXCEPT ![e] = @ \cup {RouteNow(e)}]
  /\ seenSessions' = [seenSessions EXCEPT ![e] = @ \cup {SessionKey(e)}]

\* Non-deterministic transient failure or success.
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

\* Invariants: for each event, all observed routes and session keys are stable.
Inv_RouteStable ==
  \A e \in Events: seenRoutes[e] \subseteq {Route0Route}

Inv_SessionStable ==
  \A e \in Events: seenSessions[e] \subseteq {<<Route0Route, e>>}

Spec == Init /\ [][Next]_<<pending, emitted, attempts, seenRoutes, seenSessions>>

=============================================================================
