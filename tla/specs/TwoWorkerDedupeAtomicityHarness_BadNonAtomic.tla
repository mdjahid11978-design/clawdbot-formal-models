------------------- MODULE TwoWorkerDedupeAtomicityHarness_BadNonAtomic -------------------
EXTENDS Naturals, Sequences

(******************************************************************************
* Negative model:
* BUG: check and set are non-atomic across two workers.
* Both can observe seen=FALSE and both can emit.
******************************************************************************)

VARIABLES
  seen,
  w1Checked,   \* BOOLEAN
  w2Checked,   \* BOOLEAN
  emitLog

Init ==
  /\ seen = FALSE
  /\ w1Checked = FALSE
  /\ w2Checked = FALSE
  /\ emitLog = << >>

W1Check ==
  /\ ~w1Checked
  /\ ~seen
  /\ w1Checked' = TRUE
  /\ UNCHANGED <<seen, w2Checked, emitLog>>

W2Check ==
  /\ ~w2Checked
  /\ ~seen
  /\ w2Checked' = TRUE
  /\ UNCHANGED <<seen, w1Checked, emitLog>>

\* Both workers can proceed to emit after checking.
W1Emit ==
  /\ w1Checked
  /\ seen' = TRUE
  /\ emitLog' = Append(emitLog, "e")
  /\ w1Checked' = w1Checked
  /\ w2Checked' = w2Checked

W2Emit ==
  /\ w2Checked
  /\ seen' = TRUE
  /\ emitLog' = Append(emitLog, "e")
  /\ w1Checked' = w1Checked
  /\ w2Checked' = w2Checked

Stutter == UNCHANGED <<seen, w1Checked, w2Checked, emitLog>>

Next == W1Check \/ W2Check \/ W1Emit \/ W2Emit \/ Stutter

NoDups(seq) ==
  \A i, j \in 1..Len(seq): (i /= j) => seq[i] /= seq[j]

Inv_AtMostOnce == NoDups(emitLog)

Spec == Init /\ [][Next]_<<seen, w1Checked, w2Checked, emitLog>>

=============================================================================
