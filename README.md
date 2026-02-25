# clawdbot-formal-models

Machine-checkable **security models** for Clawdbot, primarily in **TLA+** checked with **TLC**.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18452871.svg)](https://doi.org/10.5281/zenodo.18452871)

This repo is intentionally practical: it acts as a **security regression suite**.

- **Green models** should pass (no invariant violation).
- **Red models** are deliberately buggy variants that should fail with a **counterexample trace**.

## Quickstart (TLA+)

Prereqs:
- Java 11+ (Java 21 recommended)

Run a specific target:

```bash
make <target>
```

See `docs/formal-models.md` for the recommended “v1 publish” run set.

## Structure

- `tla/specs/` — TLA+ specs
- `tla/models/` — TLC model configs / notes
- `tools/tla/` — pinned TLA+ tool jar (`tla2tools.jar`)
- `bin/tlc` — convenience wrapper around TLC
- `docs/` — design notes and threat-models

## Conformance

Some checks are *conformance-style*: they validate that the formal model matches
Clawdbot’s actual implementation constants.

`scripts/extract-tool-groups.mjs` supports two source-selection modes:
- If `OPENCLAW_REPO_DIR` or `CLAWDBOT_REPO_DIR` is set, it reads
  `<that-dir>/src/agents/tool-policy.ts`.
- Otherwise it falls back to `../clawdbot/src/agents/tool-policy.ts`.

Generate the extracted constants (default fallback path):

```bash
node scripts/extract-tool-groups.mjs
```

Generate using an explicit checkout path:

```bash
OPENCLAW_REPO_DIR=../openclaw node scripts/extract-tool-groups.mjs
```

Output:
- `generated/tool-groups.json`

Run the alias-check regression test:

```bash
make group-alias-check-test
```

Run the full alias workflow (extract + validate + regression test):

```bash
make group-alias-full
```

## Key docs

- `docs/formal-models.md` — how to run, interpret green/red, and suggested CI approach
- `docs/security-claims.md` — claim inventory
- `docs/verification-roadmap.md` — roadmap for expanding fidelity/coverage

## Next steps

## CI

**Mode A (today):** CI runs TLC targets directly in this repo (no dependency on the main Clawdbot repo).

**Mode B (planned):** add a conformance job that checks out `clawdbot/clawdbot` alongside this repo and regenerates extracted constants (e.g. tool-group expansions). CI fails if the generated artifacts drift from what is committed here.

- Add CI to run TLC on PRs and upload counterexample traces as artifacts.
- Deepen fidelity: pairing-store concurrency/locking, provider-specific ingress nuances, routing identity-link semantics.
