------------------------------ MODULE AttackerHarness_ApprovalsToken_BadReplay ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* Negative test: buggy tokenized approvals where approval ignores rid binding.
******************************************************************************)

CONSTANTS
  Tools, NodesRunTool,
  NodeCommands, NodesRunCommand, PlatformDefaults, ExtraAllow, Deny, DeclaredByNode,
  ApprovalRequired, RequestIds, MaxQueueLen, MaxExecLen

ASSUME
  /\ Tools /= {} /\ NodesRunTool \in Tools /\ RequestIds /= {}
  /\ NodeCommands /= {} /\ NodesRunCommand \in NodeCommands
  /\ PlatformDefaults \subseteq NodeCommands /\ ExtraAllow \subseteq NodeCommands /\ Deny \subseteq NodeCommands
  /\ DeclaredByNode \subseteq NodeCommands
  /\ ApprovalRequired \in BOOLEAN /\ MaxQueueLen \in 0..5 /\ MaxExecLen \in 0..5

SessionTypes == {"main", "shared"}
ApprovalStates == {"none", "pending", "approved", "denied", "expired"}
Req(t, rid) == [tool |-> t, rid |-> rid]

VARIABLES sessionType, inbox, executed, approvalState, approvedRid
vars == << sessionType, inbox, executed, approvalState, approvedRid >>

EffectiveAllowlist == (PlatformDefaults \cup ExtraAllow) \ Deny
NodeCommandAllowlisted == NodesRunCommand \in EffectiveAllowlist
NodeCommandDeclared == NodesRunCommand \in DeclaredByNode
NodesGateOk == NodeCommandAllowlisted /\ NodeCommandDeclared

\* BUG: approval ignores rid (replay possible)
ApprovalOk(_req) == IF ~ApprovalRequired THEN TRUE ELSE approvalState = "approved"

MayExecute(req) ==
  LET isNodesRun == req.tool = NodesRunTool
      nodesOk == IF isNodesRun THEN NodesGateOk ELSE TRUE
      approvalOk == IF isNodesRun THEN ApprovalOk(req) ELSE TRUE
  IN  nodesOk /\ approvalOk

Init ==
  /\ sessionType = "shared"
  /\ inbox = << >>
  /\ executed = << >>
  /\ approvalState = "approved"
  /\ approvedRid = CHOOSE r \in RequestIds: TRUE

AttackerSend(t, rid) ==
  /\ t \in Tools
  /\ rid \in RequestIds
  /\ Len(inbox) < MaxQueueLen
  /\ inbox' = Append(inbox, Req(t, rid))
  /\ UNCHANGED << sessionType, executed, approvalState, approvedRid >>

AgentStep ==
  /\ Len(inbox) > 0
  /\ LET req == Head(inbox)
         approvedNow == (approvalState = "approved" /\ approvedRid = req.rid)
     IN  /\ inbox' = Tail(inbox)
         /\ executed' =
              IF MayExecute(req) /\ Len(executed) < MaxExecLen
                THEN Append(executed, [tool |-> req.tool, rid |-> req.rid, approved |-> approvedNow])
                ELSE executed
  /\ UNCHANGED << sessionType, approvalState, approvedRid >>

Next == (\E t \in Tools, rid \in RequestIds: AttackerSend(t, rid)) \/ AgentStep
Spec == Init /\ [][Next]_vars

Inv_NoNodesRunApprovalReplay ==
  ApprovalRequired =>
    \A i \in 1..Len(executed):
      executed[i].tool = NodesRunTool => executed[i].approved = TRUE

=============================================================================
