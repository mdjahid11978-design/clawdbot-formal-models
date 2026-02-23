--------------------------- MODULE CrashRestartDedupeHarness ---------------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* CrashRestartDedupeHarness.tla
*
* Crash/restart recovery model:
* - A single logical event can be emitted once.
* - We persist a dedupe marker to stable storage.
* - After a crash+restart, in-memory state is reset, but stable store remains.
*
* Property: no duplicate emission across crash/restart.
******************************************************************************)

VARIABLES
  memPending,    \* BOOLEAN
  stableSeen,    \* BOOLEAN (persisted dedupe marker)
  emitLog        \* Seq({"e"})

Init ==
  /\ memPending = TRUE
  /\ stableSeen = FALSE
  /\ emitLog = << >>

Emit ==
  /\ memPending
  /\ ~stableSeen
  /\ memPending' = FALSE
  /\ stableSeen' = TRUE
  /\ emitLog' = Append(emitLog, "e")

CrashRestart ==
  /\ memPending' = TRUE          \* event may be retried after restart
  /\ stableSeen' = stableSeen    \* persisted
  /\ emitLog' = emitLog

Stutter ==
  /\ memPending' = memPending
  /\ stableSeen' = stableSeen
  /\ emitLog' = emitLog

Next == Emit \/ CrashRestart \/ Stutter

NoDups(seq) ==
  \A i, j \in 1..Len(seq): (i /= j) => seq[i] /= seq[j]

Inv_AtMostOnce == NoDups(emitLog)

Spec == Init /\ [][Next]_<<memPending, stableSeen, emitLog>>

=============================================================================
