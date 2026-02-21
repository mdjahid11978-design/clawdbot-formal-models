# Codebase issue review: proposed fix tasks

This pass identifies one scoped task each for: typo, bug, docs/comment discrepancy, and test improvement.

## 1) Typo fix task

**Issue found:** In `docs/review-pack.md`, the negative-suite `make -k` command lists `attacker-nodes-allowlist-negative` twice, which reads like an accidental duplication/typo in the command line.

**Proposed task:** Remove the duplicate target from the command and keep each target listed once.

**Why it matters:** The duplicated token is confusing for reviewers copying the command and makes the canonical “how to run” docs look unpolished.

## 2) Bug fix task

**Issue found:** `scripts/check-tool-group-alias.mjs` contains an unreachable duplicated comparison block after `process.exit(2)`. Because every branch above exits, the trailing block can never execute.

**Proposed task:** Delete the dead duplicate block and keep a single control-flow path for alias comparison.

**Why it matters:** Dead code can mislead maintainers and create false confidence when making future edits.

## 3) Documentation discrepancy task

**Issue found:** `README.md` states extraction currently comes from `../clawdbot/src/agents/tool-policy.ts`, while `scripts/extract-tool-groups.mjs` supports `OPENCLAW_REPO_DIR` / `CLAWDBOT_REPO_DIR` and the docs elsewhere reference OpenClaw naming.

**Proposed task:** Update the README conformance section to document the env-var-based source selection and mention both supported repo names explicitly.

**Why it matters:** This avoids setup confusion for contributors using `openclaw` checkout paths and aligns docs with implemented behavior.

## 4) Test improvement task

**Issue found:** The alias-check and extraction scripts are effectively untested; no targeted tests assert behavior for (a) alias mismatch failure and (b) fallback to `group:moltbot` success.

**Proposed task:** Add a small Node test script (or npm test target) with fixture JSON inputs that validates exit codes and messages for `scripts/check-tool-group-alias.mjs` across key scenarios.

**Why it matters:** Script behavior is part of conformance tooling; lightweight tests prevent silent regressions in CI.
