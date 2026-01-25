------------------------------ MODULE ElevatedGating ------------------------------
EXTENDS Naturals

(******************************************************************************
* ElevatedGating.tla
*
* Claim (from docs): elevated execution requires BOTH:
*   - global elevated baseline gate (tools.elevated)
*   - agent-specific elevated gate (agents.list[].tools.elevated)
*
* This is modeled as a pure boolean conjunction.
******************************************************************************)

CONSTANTS
  GlobalElevatedEnabled,
  AgentElevatedEnabled

ASSUME
  /\ GlobalElevatedEnabled \in BOOLEAN
  /\ AgentElevatedEnabled \in BOOLEAN

ElevatedAllowed == GlobalElevatedEnabled /\ AgentElevatedEnabled

\* Stronger statement: if either gate is FALSE, elevated must be FALSE.
Inv_ElevatedRequiresBoth ==
  (~GlobalElevatedEnabled \/ ~AgentElevatedEnabled) => ~ElevatedAllowed

\* Trivial TLC behavior
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
