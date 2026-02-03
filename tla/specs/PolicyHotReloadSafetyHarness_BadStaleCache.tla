-------------------- MODULE PolicyHotReloadSafetyHarness_BadStaleCache --------------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: execution consults a stale cached policy bit (cachedDeny) that does not
* update on hot reload.
* Result: after reload, a pending request can still execute.
******************************************************************************)

VARIABLES
  pending,
  executed,
  reloaded,
  denyNow,
  cachedDeny

Init ==
  /\ pending = TRUE
  /\ executed = FALSE
  /\ reloaded = FALSE
  /\ denyNow = FALSE
  /\ cachedDeny = FALSE

ReloadDeny ==
  /\ pending
  /\ ~reloaded
  /\ reloaded' = TRUE
  /\ denyNow' = TRUE
  /\ cachedDeny' = cachedDeny  \* BUG: stale cache not updated
  /\ UNCHANGED <<pending, executed>>

\* BUG: consult cachedDeny instead of denyNow
Execute ==
  /\ pending
  /\ ~executed
  /\ ~cachedDeny
  /\ executed' = TRUE
  /\ pending' = FALSE
  /\ UNCHANGED <<reloaded, denyNow, cachedDeny>>

Stutter == UNCHANGED <<pending, executed, reloaded, denyNow, cachedDeny>>

Next == ReloadDeny \/ Execute \/ Stutter

Inv_NoExecAfterReload == reloaded => ~executed

Spec == Init /\ [][Next]_<<pending, executed, reloaded, denyNow, cachedDeny>>

=============================================================================
