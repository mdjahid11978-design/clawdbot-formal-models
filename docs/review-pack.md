# Formal models review pack (human-auditable)

This document is intended to make it easy to independently verify that the
TLA+ models in this repo are:
- non-vacuous (they actually constrain something)
- traceable to the OpenClaw implementation
- reproducible (green passes, negative fails for the right reasons)

## How to use this pack

### 1) Repro run (recommended)
Run from a clean checkout:

```bash
make precedence groups elevated nodes-policy attacker approvals approvals-token nodes-pipeline \
  gateway-exposure gateway-exposure-v2 gateway-exposure-v2-protected \
  gateway-auth-conformance gateway-auth-tailscale gateway-auth-proxy \
  pairing pairing-cap pairing-idempotency pairing-refresh pairing-refresh-race \
  ingress-gating ingress-idempotency ingress-dedupe-fallback ingress-trace ingress-trace2 \
  routing-isolation routing-precedence routing-identitylinks routing-identity-transitive routing-identity-symmetry routing-identity-channel-override \
  routing-thread-parent discord-pluralkit group-alias-check
```

Negative suite (expected failures):

```bash
make -k precedence-negative groups-negative elevated-negative nodes-policy-negative \
  attacker-negative attacker-nodes-negative attacker-nodes-allowlist-negative \
  approvals-negative approvals-token-negative nodes-pipeline-negative \
  gateway-exposure-negative gateway-exposure-v2-negative gateway-exposure-v2-protected-negative \
  gateway-exposure-v2-unsafe-custom gateway-exposure-v2-unsafe-tailnet gateway-exposure-v2-unsafe-auto \
  gateway-auth-conformance-negative gateway-auth-tailscale-negative gateway-auth-proxy-negative \
  pairing-negative pairing-cap-negative pairing-idempotency-negative pairing-refresh-negative pairing-refresh-race-negative \
  ingress-gating-negative ingress-idempotency-negative ingress-dedupe-fallback-negative ingress-trace-negative ingress-trace2-negative \
  routing-isolation-negative routing-precedence-negative routing-identitylinks-negative routing-identity-transitive-negative routing-identity-symmetry-negative routing-identity-channel-override-negative \
  routing-thread-parent-negative discord-pluralkit-negative
```

Expected outcomes:
- Green suite: exit 0
- Negative suite: non-zero exit (because each negative target should find an invariant violation)

### 2) “Not AI slop” sanity checks
For each harness you care about:
- Confirm it has a clear invariant (not a tautology)
- Confirm `ASSUME` does not trivialize the invariant
- Confirm the negative version changes *one thing* and causes TLC to fail

---

## Traceability map (models ↔ code)

The code references below are **implementation locations** you can inspect.
The models are abstractions (not full-code verification).

### Tool policy: precedence + group expansion
- Models:
  - `tla/specs/ToolPolicyPrecedence.tla` (+ `_BadAllowOverrides`)
  - `tla/specs/ToolGroupExpansion.tla`
- What it checks:
  - deny-wins monotonicity
  - group expansion exactness (e.g. group:memory contains expected tools)
- OpenClaw code:
  - `openclaw/src/agents/tool-policy.ts`
  - Conformance snapshot used for extraction: `openclaw/src/agents/tool-policy.conformance.ts`

### Elevated gating (exec approvals / sensitive operations)
- Models:
  - `tla/specs/ElevatedGating.tla` (+ `_BadOr`)
- What it checks:
  - elevated mode requires correct gating combination (no “OR” bug)
- Code:
  - OpenClaw tool invocation + approvals pipeline (see nodes + approvals harnesses)

### Nodes command policy + approvals pipeline
- Models:
  - `tla/specs/NodesCommandPolicy.tla` (+ `_BadNoDeclareCheck`)
  - `tla/specs/AttackerHarness_Approvals.tla` (+ `_BadIgnoresApproval`)
  - `tla/specs/AttackerHarness_ApprovalsToken.tla` (+ `_BadReplay`)
  - `tla/specs/NodesPipelineHarness.tla` (+ `_BadReplay`)
- What it checks:
  - shared-channel attacker can’t execute nodes.run without: declaredCommands + approval (+ tokenized)
- Code concepts:
  - nodes tool (`nodes.run`) policy + approvals lifecycle

### Gateway exposure + auth
- Models:
  - `tla/specs/GatewayExposureHarness.tla` (safe/unsafe configs)
  - `tla/specs/GatewayExposureHarnessV2.tla` (safe/protected/unsafe configs)
  - `tla/specs/GatewayAuthConformanceHarness.tla` (safe/unsafe)
  - `tla/specs/GatewayAuthTailscaleHarness.tla` (+ `_BadSpoof`)
  - `tla/specs/GatewayAuthTrustedProxyHarness.tla` (+ `_BadSpoof`)
- What it checks:
  - non-loopback bind requires auth
  - spoof protections for trusted proxy / tailnet
- Code:
  - `openclaw/src/gateway/auth.ts`

### Pairing store invariants
- Models:
  - `tla/specs/PairingStoreHarnessV2.tla` (+ `_BadExpiry`, `_BadNoCap`)
  - `tla/specs/PairingStoreIdempotencyHarness.tla` (+ `_BadDuplicates`)
  - `tla/specs/PairingStoreRefreshEnabledHarness.tla` (+ `_BadCapOnRefresh`)
  - `tla/specs/PairingStoreRefreshRaceHarness.tla` (+ `_BadNonAtomic`)
- What it checks:
  - expiry, max pending cap, idempotency, refresh races
- Code:
  - `openclaw/src/pairing/*`

### Ingress gating + idempotency + trace
- Models:
  - `tla/specs/IngressGatingHarness.tla` (+ `_BadBypass`)
  - `tla/specs/IngressEventIdempotencyHarness.tla` (+ `_BadNoDedupe`)
  - `tla/specs/IngressDedupeKeyFallbackHarness.tla` (+ `_BadNoFallback`)
  - `tla/specs/IngressMultiMessageTraceHarness.tla` (+ `_BadMissingTrace`)
  - `tla/specs/IngressMultiEventTraceHarness.tla` (+ `_BadCrossStream`)
- What it checks:
  - unauthorized can’t bypass
  - dedupe prevents duplicate emits
  - trace correlation rules
- Code concepts:
  - inbound processing, dedupe keys, trace propagation

### Routing invariants
- Models:
  - `tla/specs/RoutingIsolationHarness.tla` (+ `_BadAlwaysMain`)
  - `tla/specs/RoutingPrecedenceHarness.tla` (+ `_BadIgnoresChannelOverride`)
  - `tla/specs/RoutingIdentityLinksHarness.tla` (+ `_BadCanonical`)
  - `tla/specs/RoutingIdentityLinksTransitiveHarness.tla` (+ `_BadNonTransitive`)
  - `tla/specs/RoutingIdentityLinksSymmetryHarness.tla` (+ `_BadAsymmetric`)
  - `tla/specs/RoutingIdentityLinksChannelOverrideHarness.tla` (+ `_BadIgnoresChannelDisable`)
- Code:
  - `openclaw/src/routing/*`

### NEW: routing thread parent binding inheritance
- Models:
  - `tla/specs/RoutingThreadParentBindingHarness.tla` (+ `_BadThreadLoses`)
- What it checks:
  - explicit thread binding beats parent binding
  - otherwise parent binding is inherited
- Code:
  - `openclaw/src/routing/resolve-route.ts` (matchedBy="binding.peer.parent")
  - `openclaw/src/discord/monitor/message-handler.preflight.ts` (passes parentPeer)

### NEW: Discord PluralKit sender identity resolution
- Models:
  - `tla/specs/DiscordPluralKitIdentityHarness.tla` (+ `_BadWebhookPK`)
- What it checks:
  - PluralKit resolution does not apply to webhook messages
  - allowlist is applied to the resolved sender kind
- Code:
  - `openclaw/src/discord/pluralkit.ts`
  - `openclaw/src/discord/monitor/sender-identity.ts`
  - `openclaw/src/discord/monitor/message-handler.preflight.ts`

---

## Known limitations (explicitly acknowledged)
- Many harnesses are **static constraint checks** (trivial `Next`). This is fine for precedence/
  resolution invariants, but not a full temporal model.
- TLC model checking is bounded to finite state spaces defined by the constants.
- These models are not full-code proofs; they are abstractions tied to code by traceability + conformance tooling.
