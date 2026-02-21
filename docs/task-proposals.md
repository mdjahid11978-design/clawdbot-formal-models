# Task proposals from codebase review

This file captures four concrete follow-up tasks discovered during review.

## 1) Typo task: remove duplicated make target in review doc

**Issue:** The negative suite command in the review pack lists `attacker-nodes-allowlist-negative` twice in a row, which appears to be an accidental duplication/typo.

**Task:** Edit the command in `docs/review-pack.md` to include `attacker-nodes-allowlist-negative` only once.

**Why it matters:** It reduces noise for reviewers and avoids confusion about whether there are two distinct targets.

## 2) Bug task: delete unreachable duplicated code in alias check script

**Issue:** `scripts/check-tool-group-alias.mjs` contains a second copy of alias comparison logic after earlier branches that all terminate with `process.exit(...)`. The trailing block is unreachable dead code.

**Task:** Remove the unreachable duplicate block and keep only one execution path for comparison and success logging.

**Why it matters:** Dead code obscures intent and can drift from the active logic, creating maintenance risk.

## 3) Documentation discrepancy task: align generated header with current extraction source

**Issue:** `generated/tool-groups.cfg` says it is auto-generated from `../clawdbot/src/agents/tool-policy.ts`, but extraction now supports `OPENCLAW_REPO_DIR` / `CLAWDBOT_REPO_DIR` and may source from OpenClaw paths.

**Task:** Update the generator header text in `scripts/gen-tla-cfg-from-tool-groups.mjs` so output reflects the actual source selection behavior.

**Why it matters:** Accurate provenance in generated files is important for conformance audits.

## 4) Test improvement task: add a regression test for alias-key fallback behavior

**Issue:** Alias handling is implemented in `scripts/extract-tool-groups.mjs` and validated only partially by `scripts/check-tool-group-alias.mjs`, with no explicit regression test for fallback when only one of `group:clawdbot`, `group:openclaw`, or `group:moltbot` exists.

**Task:** Add a script-level test that feeds minimal fixture tool-group objects and verifies all alias keys are backfilled identically.

**Why it matters:** This behavior is security-conformance critical and currently easy to regress without immediate detection.
