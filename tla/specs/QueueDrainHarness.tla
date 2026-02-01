------------------------------ MODULE QueueDrainHarness ------------------------------
EXTENDS Naturals

(******************************************************************************
* QueueDrainHarness.tla
*
* Liveness-lite correctness model:
* - If no new items arrive, the queue eventually drains.
*
* To keep TLC state space tiny and fully enumerable, we model only the queue
* length (not the item contents).
*
* Under weak fairness of Process, the queue should eventually become empty.
******************************************************************************)

CONSTANTS
  InitLen

ASSUME
  /\ InitLen \in Nat
  /\ InitLen <= 3

VARIABLES
  qLen

Init == qLen = InitLen

\* Process removes one item if queue non-empty
Process ==
  /\ qLen > 0
  /\ qLen' = qLen - 1

Stutter == qLen' = qLen

Next == Process \/ Stutter

Empty == qLen = 0

\* Liveness: if Process is weakly fair, eventually empty.
Spec == Init /\ [][Next]_<<qLen>> /\ WF_<<qLen>>(Process)

\* Property: eventually the queue becomes empty
Live_EventuallyEmpty == <>Empty

=============================================================================
