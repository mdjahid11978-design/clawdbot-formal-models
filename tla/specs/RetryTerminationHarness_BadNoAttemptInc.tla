---------------------- MODULE RetryTerminationHarness_BadNoAttemptInc ----------------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: transient failures do not increment attempts, so the system can retry
* forever without ever reaching Drop.
******************************************************************************)

CONSTANTS
  MaxAttempts

ASSUME
  /\ MaxAttempts \in Nat
  /\ MaxAttempts >= 1
  /\ MaxAttempts <= 5

VARIABLES
  pending,
  attempts,
  emitted,
  tick

Init ==
  /\ pending = TRUE
  /\ attempts = 0
  /\ emitted = FALSE
  /\ tick = 0

TickSet == {0,1}

TypeOK ==
  /\ pending \in BOOLEAN
  /\ attempts \in Nat
  /\ emitted \in BOOLEAN
  /\ tick \in TickSet

CanTry == attempts < MaxAttempts

\* BUG: attempts' = attempts (no increment). We still update tick so TLC sees progress.
ProcessFail ==
  /\ pending
  /\ CanTry
  /\ pending' = TRUE
  /\ emitted' = emitted
  /\ attempts' = attempts
  /\ tick' = 1 - tick

ProcessSuccess ==
  /\ pending
  /\ CanTry
  /\ pending' = FALSE
  /\ emitted' = TRUE
  /\ attempts' = attempts + 1
  /\ tick' = tick

Drop ==
  /\ pending
  /\ ~CanTry
  /\ pending' = FALSE
  /\ emitted' = emitted
  /\ attempts' = attempts
  /\ tick' = tick

Step == ProcessFail \/ ProcessSuccess \/ Drop

Stutter ==
  /\ pending' = pending
  /\ attempts' = attempts
  /\ emitted' = emitted
  /\ tick' = tick

Next == Step \/ Stutter

Done == ~pending

Spec == Init /\ [][Next]_<<pending, attempts, emitted, tick>> /\ WF_<<pending, attempts, emitted, tick>>(Step)

Live_EventuallyDone == <>Done

=============================================================================
