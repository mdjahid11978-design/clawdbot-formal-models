------------------------------ MODULE RetryTerminationHarness ------------------------------
EXTENDS Naturals

(******************************************************************************
* RetryTerminationHarness.tla
*
* Liveness-lite reliability model (single-event to keep state space tiny):
* - An event may be retried on transient failure.
* - Attempts are bounded (MaxAttempts).
* - Therefore, under weak fairness of taking a step, the system eventually
*   terminates processing the event (either success or drop), i.e. pending
*   becomes empty.
******************************************************************************)

CONSTANTS
  MaxAttempts

ASSUME
  /\ MaxAttempts \in Nat
  /\ MaxAttempts >= 1
  /\ MaxAttempts <= 5

VARIABLES
  pending,   \* BOOLEAN (TRUE means event pending)
  attempts,  \* Nat
  emitted    \* BOOLEAN

Init ==
  /\ pending = TRUE
  /\ attempts = 0
  /\ emitted = FALSE

CanTry == attempts < MaxAttempts

ProcessFail ==
  /\ pending
  /\ CanTry
  /\ pending' = TRUE
  /\ emitted' = emitted
  /\ attempts' = attempts + 1

ProcessSuccess ==
  /\ pending
  /\ CanTry
  /\ pending' = FALSE
  /\ emitted' = TRUE
  /\ attempts' = attempts + 1

Drop ==
  /\ pending
  /\ ~CanTry
  /\ pending' = FALSE
  /\ emitted' = emitted
  /\ attempts' = attempts

Step == ProcessFail \/ ProcessSuccess \/ Drop

Stutter ==
  /\ pending' = pending
  /\ attempts' = attempts
  /\ emitted' = emitted

Next == Step \/ Stutter

Done == ~pending

Spec == Init /\ [][Next]_<<pending, attempts, emitted>> /\ WF_<<pending, attempts, emitted>>(Step)

Live_EventuallyDone == <>Done

=============================================================================
