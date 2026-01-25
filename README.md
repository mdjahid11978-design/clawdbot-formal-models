# clawdbot-formal-models

Formal models of **Clawdbot security protocols**, with a focus on:

- tool-gating (what actions are allowed from which channels/providers)
- memory isolation (what can be read/written in which session types)
- external side-effects (messaging, browser control, gateway config/update)
- approval / escalation paths ("ask-first" boundaries, elevated execution)

This repo currently contains a **TLA+** model-checking setup (CLI TLC via `tla2tools.jar`).

## Quickstart (TLA+)

Prereqs:
- Java 11+ (Java 21 works)

Run TLC (default model):

```bash
make tlc
```

Run a specific scenario model:

```bash
make tlc MODEL=tla/models/discord_shared.cfg
make tlc MODEL=tla/models/dm_main.cfg
```

## Structure

- `tla/specs/` — TLA+ specs
- `tla/models/` — TLC model configs / notes
- `tools/tla/` — pinned TLA+ tool jar (`tla2tools.jar`)
- `bin/tlc` — convenience wrapper around TLC
- `docs/` — design notes and threat-models

## Conformance

Some checks are *conformance-style*: they validate that the formal model matches
Clawdbot’s actual implementation constants.

Currently we extract tool-group expansions and tool-name aliases from:
- `../clawdbot/src/agents/tool-policy.ts`

Generate the extracted constants:

```bash
node scripts/extract-tool-groups.mjs
```

Output:
- `generated/tool-groups.json`

## Next steps

1. Extend conformance to cover policy precedence and channel-specific action gates.
2. Add an explicit attacker model (shared-channel adversary) and end-to-end invariants.
3. Iterate with counterexamples until the invariants match reality.
