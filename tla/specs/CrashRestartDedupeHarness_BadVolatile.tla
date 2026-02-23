--------------------- MODULE CrashRestartDedupeHarness_BadVolatile ---------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* Negative model:
* BUG: dedupe marker is only in memory (lost on crash).
* After crash+restart, event can be emitted again.
******************************************************************************)

VARIABLES
  memPending,
  memSeen,
  emitLog

Init ==
  /\ memPending = TRUE
  /\ memSeen = FALSE
  /\ emitLog = << >>

Emit ==
  /\ memPending
  /\ ~memSeen
  /\ memPending' = FALSE
  /\ memSeen' = TRUE
  /\ emitLog' = Append(emitLog, "e")

\* BUG: crash loses memSeen
CrashRestart ==
  /\ memPending' = TRUE
  /\ memSeen' = FALSE
  /\ emitLog' = emitLog

Stutter ==
  /\ memPending' = memPending
  /\ memSeen' = memSeen
  /\ emitLog' = emitLog

Next == Emit \/ CrashRestart \/ Stutter

NoDups(seq) ==
  \A i, j \in 1..Len(seq): (i /= j) => seq[i] /= seq[j]

Inv_AtMostOnce == NoDups(emitLog)

Spec == Init /\ [][Next]_<<memPending, memSeen, emitLog>>

=============================================================================
