---------------------- MODULE RetryEventualSuccessHarness_BadNoSuccess ----------------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: Success transition is missing/disabled.
* Under fairness, TLC will produce a liveness counterexample.
******************************************************************************)

VARIABLES
  pending,
  emitted,
  tick

Init ==
  /\ pending = TRUE
  /\ emitted = FALSE
  /\ tick = 0

Fail ==
  /\ pending
  /\ pending' = TRUE
  /\ emitted' = emitted
  /\ tick' = 1 - tick

\* BUG: no Success action
Success == FALSE

Stutter ==
  /\ pending' = pending
  /\ emitted' = emitted
  /\ tick' = tick

Next == Fail \/ Stutter

Spec == Init /\ [][Next]_<<pending, emitted, tick>> /\ WF_<<pending, emitted, tick>>(Success)

Live_EventuallyEmitted == <>emitted

=============================================================================
