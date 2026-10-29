// Real Lean-server integration checks. Run with: lake env node tests/Widget/server.mjs
// No npm dependencies: the server inherits Lake's Lean search path.
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { resolve } from 'node:path';

const server = spawn('lean', ['--server'], { stdio: ['pipe', 'pipe', 'pipe'] });
let buffer = Buffer.alloc(0);
let nextId = 0;
let stderr = '';
const pending = new Map();
const diagnostics = new Map();
const exited = new Promise(resolve => server.once('close', resolve));
server.stderr.on('data', data => { stderr += data; });
function failPending(error) {
  for (const request of pending.values()) request.reject(error);
  pending.clear();
}
server.on('error', failPending);
server.stdin.on('error', failPending);
server.on('exit', code => failPending(new Error(`Lean server exited (${code}): ${stderr}`)));
server.stdout.on('data', data => {
  buffer = Buffer.concat([buffer, data]);
  while (true) {
    const headerEnd = buffer.indexOf('\r\n\r\n');
    if (headerEnd < 0) return;
    const length = Number(/Content-Length: (\d+)/i.exec(buffer.subarray(0, headerEnd).toString())[1]);
    if (buffer.length < headerEnd + 4 + length) return;
    const message = JSON.parse(buffer.subarray(headerEnd + 4, headerEnd + 4 + length).toString());
    buffer = buffer.subarray(headerEnd + 4 + length);
    if (message.method === 'textDocument/publishDiagnostics') {
      diagnostics.set(message.params.uri, message.params.diagnostics);
    } else if (pending.has(message.id)) {
      const request = pending.get(message.id);
      pending.delete(message.id);
      if (message.error) request.reject(Object.assign(new Error(message.error.message), message.error));
      else request.resolve(message.result);
    }
  }
});
function send(message) {
  const body = JSON.stringify({ jsonrpc: '2.0', ...message });
  server.stdin.write(`Content-Length: ${Buffer.byteLength(body)}\r\n\r\n${body}`);
}
function notify(method, params) { send({ method, params }); }
function request(method, params, timeoutMs = 30000) {
  const id = ++nextId;
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      pending.delete(id);
      reject(new Error(`Timed out: ${method}\n${stderr}`));
    }, timeoutMs);
    pending.set(id, {
      resolve: result => { clearTimeout(timer); resolve(result); },
      reject: error => { clearTimeout(timer); reject(error); }
    });
    send({ id, method, params });
  });
}

const source = `import DevWidgets.CE.API
import DevWidgets.DocString.API
import DevWidgets.InfoTreeExplorer.API
import DevWidgets.PTracker.API

/-- A documented integration-test declaration. -/
def serverWidgetExample (n : Nat) : Nat := n + 1
#check serverWidgetExample -- baseline

section
show_panel_widgets [local DevWidgets.CE.compilerExplorerWidget with DevWidgets.CE.Config.verbose]
show_panel_widgets [local DevWidgets.DocString.docStringWidget with DevWidgets.DocString.Config.expanded]
show_panel_widgets [local DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget with DevWidgets.InfoTreeExplorer.Config.focused]
show_panel_widgets [local DevWidgets.PTracker.progressWidget with DevWidgets.PTracker.Config.manual]
#check serverWidgetExample -- configured
show_panel_widgets [-DevWidgets.PTracker.progressWidget]
#check serverWidgetExample -- hidden
end

#eval show IO Unit from do
  let ref ← DevWidgets.PTracker.ProgressRef.create (some 3) "server integration"
  ref.update 3 (some "complete")
  ref.close (interrupted := false)
  discard <| DevWidgets.PTracker.ProgressRef.create none "still running"

#check serverWidgetExample -- finished
`;
const uri = pathToFileURL(resolve('tests/Widget/ServerFixture.lean')).href;
function position(marker, text = source) {
  const lines = text.split('\n');
  const line = lines.findIndex(line => line.endsWith(`-- ${marker}`));
  assert.ok(line >= 0, `missing marker ${marker}`);
  return { line, character: lines[line].indexOf('serverWidgetExample') + 3 };
}
function open(uri, text) {
  notify('textDocument/didOpen', { textDocument: { uri, languageId: 'lean4', version: 1, text } });
}
async function connect(uri) { return (await request('$/lean/rpc/connect', { uri })).sessionId; }
async function rpc(sessionId, uri, pos, method, params) {
  return request('$/lean/rpc/call', { sessionId, textDocument: { uri }, position: pos, method, params });
}

try {
  await request('initialize', {
    processId: process.pid, rootUri: pathToFileURL(process.cwd()).href,
    capabilities: {}, initializationOptions: { hasWidgets: true }
  });
  notify('initialized', {});
  open(uri, source);
  const session = await connect(uri);
  const pos = position('finished');
  // Hover waits for elaboration at this position; no sleeps or timing assumptions.
  assert.ok(await request('textDocument/hover', { textDocument: { uri }, position: pos }));
  const call = (method, params = {}, at = pos) => rpc(session, uri, at, method, params);
  let panels;
  for (const marker of ['baseline', 'configured', 'hidden', 'finished']) {
    const at = position(marker);
    const result = await call('Lean.Widget.getWidgets', at, at);
    assert.equal(result.widgets.length, { baseline: 0, configured: 4, hidden: 3, finished: 0 }[marker], marker);
    if (marker === 'configured') panels = Object.fromEntries(result.widgets.map(w => [w.id, w]));
    if (marker === 'hidden') assert.ok(result.widgets.every(w => w.id !== 'DevWidgets.PTracker.progressWidget'));
  }
  const ceProps = panels['DevWidgets.CE.compilerExplorerWidget'].props;
  assert.equal(ceProps.showAdvanced, true);
  assert.equal(ceProps.display.ppAll, true);
  assert.equal(panels['DevWidgets.DocString.docStringWidget'].props.maxHeight, 640);
  assert.deepEqual(panels['DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget'].props, { maxChildren: 10, maxDepth: 12 });
  assert.equal(panels['DevWidgets.PTracker.progressWidget'].props.autoRefresh, false);
  assert.equal(panels['DevWidgets.PTracker.progressWidget'].props.autoRemove, false);
  for (const panel of Object.values(panels)) {
    const widget = await call('Lean.Widget.getWidgetSource', { pos, hash: panel.javascriptHash });
    assert.match(widget.sourcetext, /export default function/);
    assert.match(widget.sourcetext, /usePanelSettings/);
  }

  const schema = await call('DevWidgets.CE.ceOptionSchema');
  assert.equal(schema.compiler.find(option => option.id === 'compilerSmall').defaultNat, 1);
  assert.equal(schema.display.find(option => option.id === 'ppAll').defaultBool, false);
  // Both reconstruction modes must work repeatedly without mutating the snapshot's environment.
  for (const pipeline of [true, false, true]) {
    const result = await call('DevWidgets.CE.irAtPos', {
      pos, display: ceProps.display, compiler: ceProps.compiler,
      forceRecompile: true, lcnfRecompileViaPipeline: pipeline
    });
    const analysis = result.declaration?.payload;
    assert.equal(analysis?.declName, 'serverWidgetExample');
    assert.equal(analysis.hasIR, true);
    for (const code of [analysis.ir, analysis.lcnf]) {
      assert.ok(code.available, JSON.stringify(code));
      assert.equal(code.available.origin, 'recompiledForced');
      assert.match(JSON.stringify(code.available.content), /serverWidgetExample/);
    }
  }
  const docs = await call('DevWidgets.DocString.docAtPos', { pos });
  assert.equal(docs.declName, 'serverWidgetExample');
  assert.equal(docs.doc, 'A documented integration-test declaration.');
  assert.equal(docs.docFormat, 'markdown');

  const tree = await call('DevWidgets.InfoTreeExplorer.infoTreeAtPos', { pos, uri, maxChildren: 1, maxDepth: 1 });
  assert.ok(tree.summary.includes(uri));
  assert.ok(tree.cursorPath.length > 0);
  assert.match(JSON.stringify(tree.tree), /depth limit reached/);
  assert.match(JSON.stringify(tree.stxTree), /depth limit reached/);
  // Old clients can omit the new optional limits.
  const defaultTree = await call('DevWidgets.InfoTreeExplorer.infoTreeAtPos', { pos, uri });
  assert.ok(JSON.stringify(defaultTree.tree).length > JSON.stringify(tree.tree).length);

  const progress = await call('DevWidgets.PTracker.readProgressViewRpc');
  const done = progress.entries.find(entry => entry.description === 'server integration');
  const running = progress.entries.find(entry => entry.description === 'still running');
  assert.equal(done?.status, 'done');
  assert.equal(done.stepsDone, 3);
  assert.equal(done.totalSteps, 3);
  assert.equal(done.label, 'complete');
  assert.equal(running?.status, 'running');
  await assert.rejects(call('DevWidgets.PTracker.deleteProgressRefRpc', { id: running.id }), /still running/);
  assert.equal(await call('DevWidgets.PTracker.deleteProgressRefRpc', { id: done.id }), true);
  // Separate sessions in the same file share the registry, including deletions.
  const secondSession = await connect(uri);
  const remaining = await rpc(secondSession, uri, pos, 'DevWidgets.PTracker.readProgressViewRpc', {});
  assert.deepEqual(remaining.entries.map(entry => entry.id), [running.id]);

  // A second file uses the short imports: exactly one of each panel, its own registry and docs.
  const otherUri = pathToFileURL(resolve('tests/Widget/OtherServerFixture.lean')).href;
  const otherSource = `import DevWidgets.CE
import DevWidgets.DocString
import DevWidgets.InfoTreeExplorer
import DevWidgets.PTracker
configure_panel_widget DevWidgets.PTracker.progressWidget with DevWidgets.PTracker.Config.quiet
configure_panel_widget DevWidgets.PTracker.progressWidget with DevWidgets.PTracker.Config.manual
/-- Documentation from another file. -/
def serverWidgetExample : Nat := 42
#check serverWidgetExample -- other
`;
  open(otherUri, otherSource);
  const otherPos = position('other', otherSource);
  const otherSession = await connect(otherUri);
  const otherCall = (method, params) => rpc(otherSession, otherUri, otherPos, method, params);
  const otherPanels = await otherCall('Lean.Widget.getWidgets', otherPos);
  assert.deepEqual(otherPanels.widgets.map(w => w.id).sort(), Object.keys(panels).sort());
  assert.equal(otherPanels.widgets.find(w => w.id === 'DevWidgets.PTracker.progressWidget').props.autoRemove, false);
  assert.deepEqual((await otherCall('DevWidgets.PTracker.readProgressViewRpc', {})).entries, []);
  assert.equal((await otherCall('DevWidgets.DocString.docAtPos', { pos: otherPos })).doc,
    'Documentation from another file.');

  // An edit must update both documentation and panel props within the existing session.
  const edited = source.replace('A documented integration-test declaration.', 'Updated documentation.')
    .replace('InfoTreeExplorer.Config.focused', 'InfoTreeExplorer.Config.detailed');
  notify('textDocument/didChange', {
    textDocument: { uri, version: 2 }, contentChanges: [{ text: edited }]
  });
  assert.ok(await request('textDocument/hover', { textDocument: { uri }, position: pos }));
  assert.equal((await call('DevWidgets.DocString.docAtPos', { pos })).doc, 'Updated documentation.');
  const configured = position('configured');
  const editedPanels = await call('Lean.Widget.getWidgets', configured, configured);
  assert.deepEqual(editedPanels.widgets.find(w => w.id === 'DevWidgets.InfoTreeExplorer.infoTreeExplorerWidget').props,
    { maxChildren: 60, maxDepth: 48 });
  for (const [file, messages] of diagnostics) {
    assert.deepEqual(messages.filter(message => message.severity === 1), [], `Lean errors in ${file}`);
  }
  notify('textDocument/didClose', { textDocument: { uri: otherUri } });
  notify('textDocument/didClose', { textDocument: { uri } });
} finally {
  if (server.exitCode === null) {
    try {
      await request('shutdown', null, 5000);
      notify('exit', null);
    } finally {
      const timer = setTimeout(() => server.kill('SIGKILL'), 2000);
      await exited;
      clearTimeout(timer);
    }
  }
}
assert.equal(server.exitCode, 0, stderr);
assert.doesNotMatch(stderr, /PANIC|ASSERTION VIOLATION/);
console.log('Lean-server widget integration checks passed.');
