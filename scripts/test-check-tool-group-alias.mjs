import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const repoRoot = path.resolve(__dirname, '..');
const checkerPath = path.join(repoRoot, 'scripts', 'check-tool-group-alias.mjs');

function runCase(name, payload, expectedCode, expectedText) {
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'alias-check-'));
  const fixturePath = path.join(tmpDir, 'tool-groups.json');
  fs.writeFileSync(fixturePath, JSON.stringify(payload, null, 2));

  const res = spawnSync(process.execPath, [checkerPath], {
    cwd: repoRoot,
    encoding: 'utf8',
    env: {
      ...process.env,
      TOOL_GROUPS_JSON_PATH: fixturePath,
    },
  });

  fs.rmSync(tmpDir, { recursive: true, force: true });

  if (res.status !== expectedCode) {
    throw new Error(
      `${name}: expected exit code ${expectedCode}, got ${res.status}\nstdout:\n${res.stdout}\nstderr:\n${res.stderr}`
    );
  }

  const combined = `${res.stdout}\n${res.stderr}`;
  if (!combined.includes(expectedText)) {
    throw new Error(
      `${name}: expected output to include ${JSON.stringify(expectedText)}\nstdout:\n${res.stdout}\nstderr:\n${res.stderr}`
    );
  }

  console.log(`PASS: ${name}`);
}

runCase(
  'mismatch clawdbot/openclaw exits 1',
  {
    groups: {
      'group:clawdbot': ['a'],
      'group:openclaw': ['b'],
    },
    aliases: {},
  },
  1,
  'Tool group alias mismatch'
);

runCase(
  'moltbot-only non-empty exits 0',
  {
    groups: {
      'group:moltbot': ['x'],
    },
    aliases: {},
  },
  0,
  'OK: group:moltbot exists'
);

runCase(
  'missing aliases exits 2',
  {
    groups: {
      'group:memory': ['memory_search'],
    },
    aliases: {},
  },
  2,
  'Expected group:moltbot or group:clawdbot/openclaw'
);

console.log('All alias-check script tests passed.');
