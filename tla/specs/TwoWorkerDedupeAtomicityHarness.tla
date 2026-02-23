----------------------- MODULE TwoWorkerDedupeAtomicityHarness -----------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* TwoWorkerDedupeAtomicityHarness.tla
*
* Concurrency/interleaving stress model:
* - Two workers may concurrently attempt to emit the same logical event.
* - Correct design uses an atomic check+set on a shared dedupe marker.
*
* Property: at-most-once emission.
******************************************************************************)

VARIABLES
  seen,        \* BOOLEAN (shared dedupe marker)
  emitLog      \* Seq({"e"})

Init ==
  /\ seen = FALSE
  /\ emitLog = << >>

\* Atomic check+set+emit
EmitAtomic ==
  /\ ~seen
  /\ seen' = TRUE
  /\ emitLog' = Append(emitLog, "e")

Stutter ==
  /\ seen' = seen
  /\ emitLog' = emitLog

Next == EmitAtomic \/ Stutter

NoDups(seq) ==
  \A i, j \in 1..Len(seq): (i /= j) => seq[i] /= seq[j]

Inv_AtMostOnce == NoDups(emitLog)

Spec == Init /\ [][Next]_<<seen, emitLog>>

=============================================================================
