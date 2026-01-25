------------------------------ MODULE ElevatedGating_BadOr ------------------------------
EXTENDS Naturals

(******************************************************************************
* Negative test: WRONG elevated gating where either global OR agent gate suffices.
******************************************************************************)

CONSTANTS
  GlobalElevatedEnabled,
  AgentElevatedEnabled

ASSUME
  /\ GlobalElevatedEnabled \in BOOLEAN
  /\ AgentElevatedEnabled \in BOOLEAN

\* BUG: OR instead of AND
ElevatedAllowed == GlobalElevatedEnabled \/ AgentElevatedEnabled

Inv_ElevatedRequiresBoth ==
  (~GlobalElevatedEnabled \/ ~AgentElevatedEnabled) => ~ElevatedAllowed

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
