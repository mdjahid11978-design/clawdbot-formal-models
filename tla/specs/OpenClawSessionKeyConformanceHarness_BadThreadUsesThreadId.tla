-------------- MODULE OpenClawSessionKeyConformanceHarness_BadThreadUsesThreadId --------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: thread messages bind to the thread id instead of parent id.
******************************************************************************)

CONSTANTS
  MsgId,
  ParentId,
  ThreadId

ASSUME
  /\ MsgId \in {"m"}
  /\ ParentId \in {"p"}
  /\ ThreadId \in {"t"}

\* BUG: bind to ThreadId even when isThread
BindChannel(isThread) == ThreadId
SessionKey(isThread) == <<BindChannel(isThread), MsgId>>

Inv_ThreadBindsToParent == SessionKey(TRUE)[1] = ParentId

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
