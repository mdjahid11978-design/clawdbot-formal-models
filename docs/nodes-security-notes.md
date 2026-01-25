# Nodes Security Notes (code-informed)

This doc summarizes security-relevant behavior of the `nodes` feature as
implemented in Clawdbot, and enumerates verification targets.

## Surfaces

### Tool: `nodes`
Source: `../clawdbot/src/agents/tools/nodes-tool.ts`

Supported actions (tool schema):
- pairing / discovery: `status`, `describe`, `pending`, `approve`, `reject`
- notifications: `notify` → gateway `node.invoke` `system.notify`
- camera: `camera_list`, `camera_snap` → `camera.snap`, `camera_clip` → `camera.clip`
- screen: `screen_record` → `screen.record`
- location: `location_get` → `location.get`
- remote exec: `run` → `system.run` (argv + env + cwd)

### Gateway policy: node command allowlist
Source: `../clawdbot/src/gateway/node-command-policy.ts`

- The gateway maintains an allowlist of node commands derived from:
  1. platform defaults (iOS/Android/macOS/etc.)
  2. `gateway.nodes.allowCommands` (extra commands)
  3. `gateway.nodes.denyCommands` (removals)

- A node command is allowed only if:
  - it is in the allowlist, AND
  - the node session declares the command in `declaredCommands`.

Notable default:
- macOS platform defaults include `system.run` (remote command execution).

## Threat model (high level)

- Shared-channel prompt injection attempting to trigger nodes actions
- Confused deputy via subagents/tool groups/aliases to reach `nodes.run`
- Misclassification of session type (shared treated as main)
- Misconfiguration of gateway allow/deny command lists

## Verification targets

### NS1 — No nodes actions from shared contexts by default

### NS2 — `system.run` is reachable iff explicitly allowed + approved

### NS3 — denyCommands wins over allowCommands/defaults

### NS4 — node must declare commands; otherwise invocation is rejected

### NS5 — no bypass via tool groups/aliases/subagents

