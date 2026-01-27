# Formal security models (Clawdbot)

This repo contains **machine-checkable security models** for Clawdbot, primarily in **TLA+** checked with **TLC**.

The intent is practical: treat this as a **security regression suite**.

- **Green models**: the intended design; TLC should find no invariant violation.
- **Red models**: a deliberately buggy variant that should produce a **counterexample trace** (useful to demonstrate why a check matters, and to prevent regressions).

## Relationship to Clawdbot

Clawdbot’s user-facing documentation links here. The corresponding Clawdbot docs page is:
- `clawdbot/docs/security/formal-verification.md`

## Caveats (read this first)

- These are **models**, not the full TypeScript implementation.
- TLC results are bounded by the explored state space; a green result means “safe under these assumptions and bounds.”
- Some checks include explicit environment/config assumptions (e.g., proxy headers, deployment topology).

## Prerequisites

- Java 11+ (Java 21 recommended)

This repo vendors a pinned `tla2tools.jar` at `tools/tla/tla2tools.jar` and uses `bin/tlc`.

## Run locally

```bash
export PATH="/opt/homebrew/opt/openjdk@21/bin:$PATH"  # or any java 11+
make <target>
```

### Suggested “v1 publish” run set

Gateway exposure / misconfiguration:
- `make gateway-exposure-v2`
- `make gateway-exposure-v2-protected`
- `make gateway-exposure-v2-negative` (expected failure)

Nodes.run pipeline + approvals:
- `make nodes-pipeline`
- `make nodes-pipeline-negative` (expected failure)

Pairing store:
- `make pairing`
- `make pairing-negative` (expected failure)
- `make pairing-cap`
- `make pairing-cap-negative` (expected failure)

Ingress gating:
- `make ingress-gating`
- `make ingress-gating-negative` (expected failure)

Routing/session-key isolation:
- `make routing-isolation`
- `make routing-isolation-negative` (expected failure)

## CI / “run online” (recommended next)

The fastest credible “online run” is CI:

- GitHub Actions runs `make <targets>` on each PR
- Upload TLC output + counterexample traces as artifacts
- Add badges for green targets

A true hosted “click to run TLC in browser” flow is possible but heavier and not required for v1.
