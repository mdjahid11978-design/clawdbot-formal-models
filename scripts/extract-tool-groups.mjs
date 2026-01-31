import fs from 'node:fs';
import path from 'node:path';

const OPENCLAW_REPO_DIR = process.env.OPENCLAW_REPO_DIR || process.env.CLAWDBOT_REPO_DIR;
const SRC = OPENCLAW_REPO_DIR
  ? path.resolve(OPENCLAW_REPO_DIR, 'src/agents/tool-policy.ts')
  : path.resolve('../clawdbot/src/agents/tool-policy.ts');
const out = path.resolve('generated/tool-groups.json');

const text = fs.readFileSync(SRC, 'utf8');

// Very small extractor: grab the TOOL_GROUPS object literal and TOOL_NAME_ALIASES.
function extractObject(name) {
  const re = new RegExp(`export const ${name}[^=]*=\\s*({[\\s\\S]*?^});`, 'm');
  const m = text.match(re);
  if (!m) throw new Error(`Could not find ${name} in ${SRC}`);
  return m[1];
}

const groupsSrc = extractObject('TOOL_GROUPS');
const aliasesSrc = (() => {
  const re = new RegExp(`const TOOL_NAME_ALIASES\\s*:\\s*Record<[^>]+>\\s*=\\s*({[\\s\\S]*?^});`, 'm');
  const m = text.match(re);
  if (!m) throw new Error(`Could not find TOOL_NAME_ALIASES in ${SRC}`);
  return m[1];
})();

// Evaluate safely-ish by converting to JSON-ish.
// Assumes keys/strings are quoted in the TS source (they are).
function evalObjectLiteral(src) {
  // Replace trailing comments and TS-style multiline comments (best-effort)
  const noComments = src
    .replace(/\/\*[\s\S]*?\*\//g, '')
    .replace(/(^|\s)\/\/.*$/gm, '');
  // Wrap in parentheses so Node treats it as an expression.
  // eslint-disable-next-line no-new-func
  return Function(`"use strict"; return (${noComments});`)();
}

const groups = evalObjectLiteral(groupsSrc);
const aliases = evalObjectLiteral(aliasesSrc);

fs.mkdirSync(path.dirname(out), { recursive: true });
fs.writeFileSync(out, JSON.stringify({ groups, aliases }, null, 2));
console.log(`Wrote ${out}`);
