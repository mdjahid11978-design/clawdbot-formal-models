------------------- MODULE TaintPropagationApprovalHarness_BadDropTaint -------------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: taint is dropped during prompt construction, so an unapproved tainted
* tool call can appear untainted and (depending on gates) execute.
******************************************************************************)

VARIABLES
  originTainted,
  promptTainted,
  toolCallTainted,
  approved,
  executed

Init ==
  /\ originTainted = TRUE
  /\ approved = FALSE
  /\ promptTainted = FALSE
  /\ toolCallTainted = FALSE
  /\ executed = FALSE

\* BUG: promptTainted' = FALSE always
BuildPrompt ==
  /\ promptTainted' = FALSE
  /\ UNCHANGED <<originTainted, toolCallTainted, approved, executed>>

ProposeToolCall ==
  /\ toolCallTainted' = promptTainted
  /\ UNCHANGED <<originTainted, promptTainted, approved, executed>>

\* BUG: gate mistakenly checks toolCallTainted instead of requiring approval
ExecuteSensitive ==
  /\ ~executed
  /\ ~toolCallTainted
  /\ executed' = TRUE
  /\ UNCHANGED <<originTainted, promptTainted, toolCallTainted, approved>>

NoOp == UNCHANGED <<originTainted, promptTainted, toolCallTainted, approved, executed>>

Next == BuildPrompt \/ ProposeToolCall \/ ExecuteSensitive \/ NoOp

Inv_NoExecWhenTaintedAndUnapproved == (originTainted /\ ~approved) => ~executed

Spec == Init /\ [][Next]_<<originTainted, promptTainted, toolCallTainted, approved, executed>>

=============================================================================
