import fs from 'node:fs';

const sourcePath = process.env.TOOL_GROUPS_JSON_PATH || new URL('../generated/tool-groups.json', import.meta.url);
const json = JSON.parse(fs.readFileSync(sourcePath, 'utf8'));

const g = json.groups || {};
// The project has been renamed a few times; treat these as aliases.
const a = g['group:clawdbot'];
const b = g['group:openclaw'];
const c = g['group:moltbot'];

// Prefer comparing openclaw <-> clawdbot when both exist.
if (a && b) {
  const as = JSON.stringify(a);
  const bs = JSON.stringify(b);
  if (as !== bs) {
    console.error('Tool group alias mismatch: group:clawdbot != group:openclaw');
    console.error('group:clawdbot:', a);
    console.error('group:openclaw:', b);
    process.exit(1);
  }
  console.log('OK: group:clawdbot and group:openclaw are identical.');
  process.exit(0);
}

// If only moltbot exists (common in this repo), just ensure it is non-empty.
if (c) {
  if (!Array.isArray(c) || c.length === 0) {
    console.error('Unexpected: group:moltbot is missing or empty');
    process.exit(1);
  }
  console.log('OK: group:moltbot exists (no openclaw/clawdbot alias keys present).');
  process.exit(0);
}

console.error('Expected group:moltbot or group:clawdbot/openclaw in tool groups input');
console.error('Present keys:', Object.keys(g).sort().join(', '));
process.exit(2);
