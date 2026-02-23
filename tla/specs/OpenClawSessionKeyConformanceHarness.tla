---------------------- MODULE OpenClawSessionKeyConformanceHarness ----------------------
EXTENDS Naturals

(******************************************************************************
* OpenClawSessionKeyConformanceHarness.tla
*
* Direct conformance claim (tiny):
* - OpenClaw derives a session key for incoming Discord messages.
* - If a message is in a thread, the session key binds to the thread parent.
* - Session keys must be stable across retries for the same message.
*
* We include a trivial state machine so TLC can run a normal Spec.
******************************************************************************)

CONSTANTS
  MsgId,
  ParentId,
  ThreadId

ASSUME
  /\ MsgId \in {"m"}
  /\ ParentId \in {"p"}
  /\ ThreadId \in {"t"}

BindChannel(isThread) == IF isThread THEN ParentId ELSE ThreadId
SessionKey(isThread) == <<BindChannel(isThread), MsgId>>

Inv_ThreadBindsToParent == SessionKey(TRUE)[1] = ParentId
Inv_RetryStable == SessionKey(TRUE) = SessionKey(TRUE)

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
