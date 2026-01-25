------------------------------ MODULE AttackerHarness_ApprovalsToken ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* AttackerHarness_ApprovalsToken.tla
*
* Tokenized / per-request approvals.
*
* We model requests as (tool, rid). Approval, when granted, is bound to a
* specific rid. Execution of nodes.run is allowed only if the current request
* rid matches the approved rid.
*
* This targets the bug class: "approval replay" / "approval leaked across
* requests/sessions".
******************************************************************************)

CONSTANTS
  Tools,
  NodesRunTool,

  \* Node command policy
  NodeCommands,
  NodesRunCommand,
  PlatformDefaults,
  ExtraAllow,
  Deny,
  DeclaredByNode,

  ApprovalRequired,

  RequestIds,
  MaxQueueLen,
  MaxExecLen

ASSUME
  /\ Tools /= {}
  /\ NodesRunTool \in Tools
  /\ RequestIds /= {}

  /\ NodeCommands /= {}
  /\ NodesRunCommand \in NodeCommands
  /\ PlatformDefaults \subseteq NodeCommands
  /\ ExtraAllow \subseteq NodeCommands
  /\ Deny \subseteq NodeCommands
  /\ DeclaredByNode \subseteq NodeCommands

  /\ ApprovalRequired \in BOOLEAN
  /\ MaxQueueLen \in 0..5
  /\ MaxExecLen \in 0..5

SessionTypes == {"main", "shared"}
ApprovalStates == {"none", "pending", "approved", "denied", "expired"}

\* Request record
Req(t, rid) == [tool |-> t, rid |-> rid]

VARIABLES sessionType, inbox, executed, approvalState, approvedRid
vars == << sessionType, inbox, executed, approvalState, approvedRid >>

EffectiveAllowlist == (PlatformDefaults \cup ExtraAllow) \ Deny
NodeCommandAllowlisted == NodesRunCommand \in EffectiveAllowlist
NodeCommandDeclared == NodesRunCommand \in DeclaredByNode
NodesGateOk == NodeCommandAllowlisted /\ NodeCommandDeclared

\* Approval check for a request
ApprovalOk(req) ==
  IF ~ApprovalRequired THEN TRUE
  ELSE approvalState = "approved" /\ approvedRid = req.rid

MayExecute(req) ==
  LET isNodesRun == req.tool = NodesRunTool
      nodesOk == IF isNodesRun THEN NodesGateOk ELSE TRUE
      approvalOk == IF isNodesRun THEN ApprovalOk(req) ELSE TRUE
  IN  nodesOk /\ approvalOk

Init ==
  /\ sessionType = "shared"
  /\ inbox = << >>
  /\ executed = << >>
  /\ approvalState = "none"
  /\ approvedRid = CHOOSE r \in RequestIds: TRUE

AttackerSend(t, rid) ==
  /\ t \in Tools
  /\ rid \in RequestIds
  /\ Len(inbox) < MaxQueueLen
  /\ inbox' = Append(inbox, Req(t, rid))
  /\ UNCHANGED << sessionType, executed, approvalState, approvedRid >>

\* Agent requests approval for a specific rid (typically for nodes.run)
RequestApproval(rid) ==
  /\ rid \in RequestIds
  /\ approvalState \in {"none", "denied", "expired"}
  /\ approvalState' = "pending"
  /\ approvedRid' = rid
  /\ UNCHANGED << sessionType, inbox, executed >>

HumanApprove ==
  /\ approvalState = "pending"
  /\ approvalState' = "approved"
  /\ UNCHANGED << sessionType, inbox, executed, approvedRid >>

ExpireApproval ==
  /\ approvalState = "approved"
  /\ approvalState' = "expired"
  /\ UNCHANGED << sessionType, inbox, executed, approvedRid >>

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

Next ==
  (\E t \in Tools, rid \in RequestIds: AttackerSend(t, rid))
  \/ (\E rid \in RequestIds: RequestApproval(rid))
  \/ HumanApprove
  \/ ExpireApproval
  \/ AgentStep

Spec == Init /\ [][Next]_vars

\* Security property: any executed nodes.run must be approved for *that rid*.
Inv_NoNodesRunApprovalReplay ==
  ApprovalRequired =>
    \A i \in 1..Len(executed):
      executed[i].tool = NodesRunTool => executed[i].approved = TRUE

=============================================================================
