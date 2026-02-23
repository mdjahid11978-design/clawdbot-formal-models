-------------------------- MODULE PolicyHotReloadSafetyHarness --------------------------
EXTENDS Naturals

(******************************************************************************
* PolicyHotReloadSafetyHarness.tla
*
* Correctness/security model:
* - A request is pending under an initial (allowing) policy.
* - Policy is hot-reloaded to deny the action.
* - After reload, the pending request must not execute (no stale-cache window).
*
* Key modeling choice: reload happens while the request is still pending.
* This avoids false positives where execution completes before reload.
******************************************************************************)

VARIABLES
  pending,
  executed,
  reloaded,
  denyNow

Init ==
  /\ pending = TRUE
  /\ executed = FALSE
  /\ reloaded = FALSE
  /\ denyNow = FALSE

ReloadDeny ==
  /\ pending
  /\ ~reloaded
  /\ reloaded' = TRUE
  /\ denyNow' = TRUE
  /\ UNCHANGED <<pending, executed>>

\* Execution gate consults the live policy (denyNow).
Execute ==
  /\ pending
  /\ ~executed
  /\ ~denyNow
  /\ executed' = TRUE
  /\ pending' = FALSE
  /\ UNCHANGED <<reloaded, denyNow>>

Stutter == UNCHANGED <<pending, executed, reloaded, denyNow>>

Next == ReloadDeny \/ Execute \/ Stutter

\* Safety: after reload, execution cannot occur.
Inv_NoExecAfterReload == reloaded => ~executed

Spec == Init /\ [][Next]_<<pending, executed, reloaded, denyNow>>

=============================================================================
