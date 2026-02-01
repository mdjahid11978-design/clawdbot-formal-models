-------------------------- MODULE RetryEventualSuccessHarness --------------------------
EXTENDS Naturals

(******************************************************************************
* RetryEventualSuccessHarness.tla
*
* Liveness-lite model (tiny + enumerable):
* - A single pending event can experience transient failures forever.
* - If a Success step is weakly fair while the event is pending, then the event
*   is eventually emitted.
*
* We avoid unbounded counters; Fail just toggles a 1-bit tick.
******************************************************************************)

VARIABLES
  pending,   \* BOOLEAN
  emitted,   \* BOOLEAN
  tick       \* {0,1} (progress bit)

Init ==
  /\ pending = TRUE
  /\ emitted = FALSE
  /\ tick = 0

Fail ==
  /\ pending
  /\ pending' = TRUE
  /\ emitted' = emitted
  /\ tick' = 1 - tick

Success ==
  /\ pending
  /\ pending' = FALSE
  /\ emitted' = TRUE
  /\ tick' = tick

Stutter ==
  /\ pending' = pending
  /\ emitted' = emitted
  /\ tick' = tick

Next == Fail \/ Success \/ Stutter

Spec == Init /\ [][Next]_<<pending, emitted, tick>> /\ WF_<<pending, emitted, tick>>(Success)

Live_EventuallyEmitted == <>emitted

=============================================================================
