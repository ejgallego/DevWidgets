import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import vm from 'node:vm';

const fixtures = JSON.parse(readFileSync(0, 'utf8'));
const pos = { uri: 'file:///workspace/Example.lean', line: 2, character: 4 };

// A small hook driver for RPC/effect behavior, not a DOM or layout renderer.
// Effects run after render, dependencies use Object.is, and cleanup runs before
// replacement effects and on unmount. Timers and RPC completion are controlled.
function mount(source, rpc, asyncValues = [], props = { pos }) {
  const slots = [];
  const timers = new Map();
  let cursor = 0, asyncCursor = 0, nextTimer = 0;
  let effects = [], dirty = false, mounted = true, tree;
  const sameDeps = (a, b) => a && b && a.length === b.length &&
    a.every((value, i) => Object.is(value, b[i]));
  const React = {
    Fragment: 'fragment',
    createElement: (type, props, ...children) => ({ type, props: props ?? {}, children: children.flat(Infinity) }),
    useState(initial) {
      const i = cursor++;
      slots[i] ??= { value: typeof initial === 'function' ? initial() : initial };
      return [slots[i].value, (update) => {
        assert.ok(mounted, 'state updated after unmount');
        const value = typeof update === 'function' ? update(slots[i].value) : update;
        if (!Object.is(value, slots[i].value)) {
          slots[i].value = value;
          dirty = true;
        }
      }];
    },
    useRef(value) {
      const i = cursor++;
      slots[i] ??= { current: value };
      return slots[i];
    },
    useMemo(fn, deps) {
      const i = cursor++;
      if (!sameDeps(slots[i]?.deps, deps)) slots[i] = { value: fn(), deps };
      return slots[i].value;
    },
    useCallback(fn, deps) { return React.useMemo(() => fn, deps); },
    useEffect(fn, deps) {
      const i = cursor++;
      if (!sameDeps(slots[i]?.deps, deps)) {
        const previous = slots[i];
        effects.push(() => {
          previous?.cleanup?.();
          slots[i] = { deps, cleanup: fn() };
        });
      }
    }
  };
  const asyncCalls = [];
  const asyncDeps = [];
  const context = vm.createContext({
    React,
    useRpcSession: () => rpc,
    useAsync: (fn, deps) => {
      asyncCalls.push(fn);
      asyncDeps.push(deps);
      const value = asyncValues[asyncCursor++];
      return value === undefined ? { state: 'loading' } : { state: 'resolved', value };
    },
    // Supply retained responses explicitly to test their position as the cursor changes.
    useAsyncPersistent: (fn, deps) => context.useAsync(fn, deps),
    mapRpcError: (error) => ({ message: String(error) }),
    setInterval: (fn) => { timers.set(++nextTimer, fn); return nextTimer; },
    clearInterval: (id) => timers.delete(id),
    Date
  });
  const script = source.replace(/^\s*import .+$/gm, '')
    .replace(/export default function(?:\s+\w+)?\s*\(/, 'globalThis.Widget = function(');
  vm.runInContext(script, context);
  function render() {
    let passes = 0;
    do {
      assert.ok(++passes < 20, 'render loop');
      dirty = false;
      cursor = 0;
      asyncCursor = 0;
      effects = [];
      asyncCalls.length = 0;
      asyncDeps.length = 0;
      tree = context.Widget(props);
      effects.forEach((effect) => effect());
    } while (dirty);
  }
  render();
  return {
    get tree() { return tree; },
    asyncCalls,
    asyncDeps,
    render,
    replaceProps(next) { props = next; render(); },
    replaceValue(index, value) { asyncValues[index] = value; render(); },
    replaceRpc(next) { rpc = next; render(); },
    tick() { [...timers.values()].forEach((fn) => fn()); render(); },
    unmount() {
      slots.forEach((slot) => slot?.cleanup?.());
      mounted = false;
      assert.equal(timers.size, 0, 'timers remain after unmount');
    }
  };
}

function nodes(tree) {
  if (!tree || typeof tree !== 'object') return [];
  return [tree, ...tree.children.flatMap(nodes)];
}
function button(widget, label) {
  const found = nodes(widget.tree).find((node) => node.type === 'button' && node.children.includes(label));
  assert.ok(found, `missing button: ${label}`);
  return found;
}
function deferred() {
  let resolve, reject;
  const promise = new Promise((yes, no) => { resolve = yes; reject = no; });
  return { promise, resolve, reject };
}
// A full event-loop turn also drains promises created inside the VM context.
const settle = async (widget) => { await new Promise(setImmediate); widget.render(); };
const view = (description) => ({
  nowNs: 100,
  entries: [{ id: 0, description, label: '', stepsDone: 1, totalSteps: 2,
    createdAtNs: 0, lastUpdatedAtNs: 100, status: 'running' }]
});
const text = (widget) => JSON.stringify(widget.tree);
const readMethod = 'DevWidgets.PTracker.readProgressViewRpc';

async function testCEDefaults(schema) {
  const calls = [];
  const widget = mount(fixtures.ce, { call: async (method, params) => calls.push({ method, params }) },
    [schema, fixtures.analysis]);
  button(widget, 'Verbose').props.onClick();
  widget.render();
  button(widget, 'Defaults').props.onClick();
  widget.render();
  await widget.asyncCalls[1]();
  const params = calls.at(-1).params;
  for (const group of ['display', 'compiler']) {
    for (const descriptor of fixtures.schema[group]) {
      assert.equal(params[group][descriptor.id], descriptor.defaultBool ?? descriptor.defaultNat,
        `CE reset default: ${descriptor.id}`);
    }
  }
  widget.unmount();
}

let infoRequest;
async function testInfoTreeUri() {
  const widget = mount(fixtures.infoTree, { call: async (_method, params) => { infoRequest = params; } });
  await widget.asyncCalls[0]();
  assert.equal(infoRequest.uri, pos.uri, 'InfoTreeExplorer request URI');
  widget.unmount();
}

async function testSessionChange() {
  const old = deferred(), current = deferred();
  let oldCalls = 0, currentCalls = 0;
  const widget = mount(fixtures.progress, { call: () => { oldCalls++; return old.promise; } });
  assert.equal(oldCalls, 1);
  widget.tick();
  assert.equal(oldCalls, 1, 'overlapping polls');
  widget.replaceRpc({ call: () => { currentCalls++; return current.promise; } });
  assert.equal(currentCalls, 1, 'new session must refresh while old request is pending');
  current.resolve(view('current session'));
  await settle(widget);
  old.resolve(view('obsolete session'));
  await settle(widget);
  assert.ok(text(widget).includes('current session'));
  assert.ok(!text(widget).includes('obsolete session'), 'late reply overwrote current data');
  widget.tick();
  await settle(widget);
  assert.equal(oldCalls, 1, 'poll used obsolete RPC session');
  assert.equal(currentCalls, 2, 'poll did not use current RPC session');
  widget.unmount();
}

async function testLateDelete() {
  const deletion = deferred();
  const completed = view('old completed task');
  completed.entries[0].status = 'done';
  completed.entries[0].closedAtNs = 100;
  const widget = mount(fixtures.progress, { call: (method) =>
    method === readMethod ? Promise.resolve(completed) : deletion.promise });
  await settle(widget);
  button(widget, '×').props.onClick();
  widget.replaceRpc({ call: async () => view('new task with same id') });
  assert.ok(!text(widget).includes('old completed task'), 'rows leaked across sessions');
  await settle(widget);
  deletion.resolve(true);
  await settle(widget);
  assert.ok(text(widget).includes('new task with same id'), 'old deletion removed a new session row');
  widget.unmount();
}

async function testLateError() {
  const pending = deferred();
  const widget = mount(fixtures.progress, { call: () => pending.promise });
  widget.replaceRpc({ call: async () => view('current task') });
  await settle(widget);
  pending.reject(new Error('obsolete failure'));
  await settle(widget);
  assert.ok(!text(widget).includes('obsolete failure'), 'old failure leaked into current session');
  assert.ok(text(widget).includes('current task'));
  widget.unmount();
}

async function testManualRefresh() {
  let calls = 0;
  const widget = mount(fixtures.progress, { call: async () => { calls++; return view('task'); } });
  await settle(widget);
  const auto = nodes(widget.tree).find((node) => node.type === 'input' && node.props.type === 'checkbox');
  auto.props.onChange({ target: { checked: false } });
  widget.render();
  widget.tick();
  assert.equal(calls, 1, 'automatic polling continued while disabled');
  button(widget, 'Refresh').props.onClick();
  await settle(widget);
  assert.equal(calls, 2, 'manual refresh did not run');
  assert.equal(button(widget, 'Refresh').props.disabled, false);
  widget.unmount();
}

async function testUnmount() {
  const pending = deferred();
  const widget = mount(fixtures.progress, { call: () => pending.promise });
  widget.unmount();
  pending.resolve(view('late reply'));
  await new Promise(setImmediate);
}

async function testCursorControls(kind, values, requestIndex) {
  const calls = [];
  const widget = mount(fixtures[kind], { call: async (_method, params) => calls.push(params) }, values);
  assert.equal(button(widget, 'Pin result').props.disabled, false);
  button(widget, 'Pin result').props.onClick();
  widget.render();
  assert.equal(button(widget, 'Refresh').props.disabled, true);
  const pinnedView = text(widget);
  widget.replaceProps({ pos: { uri: 'file:///another/File.lean', line: 90, character: 0 } });
  widget.replaceRpc({ call: async (_method, params) => calls.push(params) });
  // Even a new live response must not replace the captured response.
  widget.replaceValue(requestIndex, undefined);
  assert.equal(await widget.asyncCalls[requestIndex](), undefined);
  assert.equal(calls.length, 0, 'pinned panel issued a request through the new file session');
  assert.equal(text(widget), pinnedView, 'pinned result changed after cursor/session movement');
  button(widget, 'Follow cursor').props.onClick();
  widget.render();
  await widget.asyncCalls[requestIndex]();
  assert.equal(calls.at(-1).pos.uri, 'file:///another/File.lean');
  const beforeRefresh = JSON.stringify(widget.asyncDeps[requestIndex]);
  button(widget, 'Refresh').props.onClick();
  widget.render();
  assert.notEqual(JSON.stringify(widget.asyncDeps[requestIndex]), beforeRefresh, 'refresh did not invalidate the request');
  button(widget, 'Reset panel').props.onClick();
  widget.render();
  assert.equal(button(widget, 'Pin result').props.disabled, true, 'unresolved results should not be pinnable');
  await settle(widget);
  widget.unmount();
}

async function testCEConfiguration() {
  const calls = [];
  const config = { ...fixtures.ceConfig, compiler: { ...fixtures.ceConfig.compiler, compilerSmall: 7 } };
  const widget = mount(fixtures.ce, { call: async (_method, params) => calls.push(params) },
    [fixtures.schema, fixtures.analysis], { pos, ...config });
  await widget.asyncCalls[1]();
  assert.equal(calls.at(-1).display.ppFullNames, true);
  button(widget, 'Verbose').props.onClick();
  widget.render();
  await widget.asyncCalls[1]();
  assert.equal(calls.at(-1).compiler.compilerSmall, 7, 'verbosity must not change compiler settings');
  button(widget, 'Defaults').props.onClick();
  widget.render();
  await widget.asyncCalls[1]();
  assert.equal(calls.at(-1).display.ppFullNames, false);
  button(widget, 'Reset panel').props.onClick();
  widget.render();
  await widget.asyncCalls[1]();
  assert.equal(calls.at(-1).display.ppFullNames, true, 'reset must restore Lean props');
  button(widget, 'Defaults').props.onClick();
  widget.render();
  widget.replaceProps({ pos, ...config, display: { ...config.display, ppFullNames: false } });
  await widget.asyncCalls[1]();
  assert.equal(calls.at(-1).display.ppFullNames, false, 'new configuration must replace local overrides');
  widget.replaceProps({ pos, ...config });
  await widget.asyncCalls[1]();
  assert.equal(calls.at(-1).display.ppFullNames, true, 'old overrides must not reappear when a configuration returns');
  widget.unmount();
}

async function testTreeConfiguration() {
  const calls = [];
  const widget = mount(fixtures.infoTree, { call: async (_method, params) => calls.push(params) },
    [{}], { pos, ...fixtures.treeConfig });
  await widget.asyncCalls[0]();
  assert.equal(calls.at(-1).maxChildren, 10);
  button(widget, 'Detailed').props.onClick();
  widget.render();
  await widget.asyncCalls[0]();
  assert.equal(calls.at(-1).maxDepth, 48);
  button(widget, 'Reset panel').props.onClick();
  widget.render();
  await widget.asyncCalls[0]();
  assert.equal(calls.at(-1).maxDepth, 12);
  widget.replaceProps({ pos, maxDepth: 100000, maxChildren: -1 });
  await widget.asyncCalls[0]();
  assert.equal(calls.at(-1).maxDepth, 64);
  assert.equal(calls.at(-1).maxChildren, 1);
  widget.unmount();
}

async function testRetainedTreePosition() {
  const widget = mount(fixtures.infoTree, { call: async () => ({ summary: 'tree' }) },
    [{ sourcePos: pos, summary: 'retained tree' }]);
  const result = await widget.asyncCalls[0]();
  assert.equal(result.sourcePos.uri, pos.uri);
  widget.replaceProps({ pos: { ...pos, line: 90 } });
  assert.ok(text(widget).includes('L3:5'), 'retained tree must show its original cursor');
  button(widget, 'Pin result').props.onClick();
  widget.render();
  assert.ok(text(widget).includes('L3:5'), 'pin must preserve the retained result position');
  assert.ok(!text(widget).includes('L91:5'), 'pin mislabeled old tree with new cursor');
  widget.unmount();
}

async function testProgressConfiguration() {
  const calls = [];
  const old = view('completed task');
  old.nowNs = 100_000_000_000;
  old.entries[0].status = 'done';
  old.entries[0].closedAtNs = 1;
  const widget = mount(fixtures.progress, { call: async (method) => { calls.push(method); return old; } },
    [], { pos, ...fixtures.progressConfig });
  await settle(widget);
  widget.tick();
  await settle(widget);
  assert.deepEqual(calls, [readMethod], 'manual mode polled or deleted completed entries');
  assert.ok(text(widget).includes('completed task'));
  button(widget, 'Quiet').props.onClick();
  widget.render();
  const period = nodes(widget.tree).find((node) => node.type === 'input' && node.props.step === 100);
  assert.equal(period.props.value, 1000);
  button(widget, 'Reset panel').props.onClick();
  widget.render();
  const auto = nodes(widget.tree).find((node) => node.type === 'input' && node.props.type === 'checkbox');
  assert.equal(auto.props.checked, false);
  await settle(widget);
  widget.unmount();
}

async function testDocConfiguration() {
  const widget = mount(fixtures.docs, { call: async () => {} },
    [{ doc: 'example', docFormat: 'markdown' }], { pos, ...fixtures.docConfig });
  const rendered = nodes(widget.tree).find((node) => node.props.className === 'docstring-rendered');
  assert.equal(rendered.props.style.maxHeight, '640px');
  assert.equal(widget.tree.props.style.borderRadius, '8px', 'panel CSS must be applied as a style object');
  await settle(widget);
  widget.unmount();
}

async function testMissingCursor() {
  for (const [kind, values] of [['ce', [fixtures.schema]], ['infoTree', [{}]], ['docs', []]]) {
    const widget = mount(fixtures[kind], { call: async () => { throw new Error('unexpected request'); } }, values, {});
    assert.equal(button(widget, 'Pin result').props.disabled, true);
    assert.equal(button(widget, 'Refresh').props.disabled, true);
    assert.ok(text(widget).includes('Move the cursor'), `${kind} should explain how to get a result`);
    await settle(widget);
    widget.unmount();
  }
}

const failures = [];
for (const [name, run] of [
  ['CE backend defaults', () => testCEDefaults(fixtures.schema)],
  ['CE fallback defaults', () => testCEDefaults(undefined)],
  ['InfoTreeExplorer URI', testInfoTreeUri],
  ['PTracker session change', testSessionChange],
  ['PTracker late deletion', testLateDelete],
  ['PTracker late error', testLateError],
  ['PTracker manual refresh', testManualRefresh],
  ['PTracker unmount', testUnmount],
  ['CE cursor controls', () => testCursorControls('ce', [fixtures.schema, fixtures.analysis], 1)],
  ['InfoTreeExplorer cursor controls', () => testCursorControls('infoTree', [{}], 0)],
  ['DocString cursor controls', () => testCursorControls('docs', [{ doc: 'pinned documentation', docFormat: 'markdown' }], 0)],
  ['CE configuration', testCEConfiguration],
  ['InfoTreeExplorer configuration', testTreeConfiguration],
  ['InfoTreeExplorer retained position', testRetainedTreePosition],
  ['PTracker configuration', testProgressConfiguration],
  ['DocString configuration', testDocConfiguration],
  ['Missing cursor', testMissingCursor]
]) {
  try { await run(); }
  catch (error) { failures.push(new Error(name, { cause: error })); }
}
if (failures.length) throw new AggregateError(failures, 'Widget runtime regressions');
process.stdout.write(JSON.stringify(infoRequest));
