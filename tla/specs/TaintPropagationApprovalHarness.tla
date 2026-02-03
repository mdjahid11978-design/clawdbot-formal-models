------------------------ MODULE TaintPropagationApprovalHarness ------------------------
EXTENDS Naturals

(******************************************************************************
* TaintPropagationApprovalHarness.tla
*
* End-to-end-ish taint propagation model (tiny):
* - External content (links/attachments) is tainted.
* - The system transforms/normalizes content into a prompt.
* - The model produces a tool-call request derived from that prompt.
*
* Property:
*   If the origin is tainted and approval is not granted, a sensitive tool must
*   not execute.
*
* We explicitly model a pipeline where a bug could drop taint during a
* transformation.
******************************************************************************)

VARIABLES
  originTainted,     \* BOOLEAN
  promptTainted,     \* BOOLEAN
  toolCallTainted,   \* BOOLEAN
  approved,          \* BOOLEAN
  executed           \* BOOLEAN

Init ==
  /\ originTainted \in BOOLEAN
  /\ approved \in BOOLEAN
  /\ promptTainted = FALSE
  /\ toolCallTainted = FALSE
  /\ executed = FALSE

\* Step 1: build prompt from origin content (should preserve taint)
BuildPrompt ==
  /\ promptTainted' = originTainted
  /\ UNCHANGED <<originTainted, toolCallTainted, approved, executed>>

\* Step 2: model proposes a tool call derived from the prompt (taint should carry)
ProposeToolCall ==
  /\ toolCallTainted' = promptTainted
  /\ UNCHANGED <<originTainted, promptTainted, approved, executed>>

\* Step 3: execution gate
ExecuteSensitive ==
  /\ ~executed
  /\ (approved) \* approval required regardless; taint can never relax this
  /\ executed' = TRUE
  /\ UNCHANGED <<originTainted, promptTainted, toolCallTainted, approved>>

NoOp == UNCHANGED <<originTainted, promptTainted, toolCallTainted, approved, executed>>

Next == BuildPrompt \/ ProposeToolCall \/ ExecuteSensitive \/ NoOp

\* Key invariant: if the tool call is tainted and not approved, execution must not happen.
Inv_NoExecWhenTaintedAndUnapproved == (toolCallTainted /\ ~approved) => ~executed

\* Also ensure that taint cannot disappear (desired property in the green model)
Inv_TaintMonotone ==
  /\ (originTainted => promptTainted \/ promptTainted') 

Spec == Init /\ [][Next]_<<originTainted, promptTainted, toolCallTainted, approved, executed>>

=============================================================================
