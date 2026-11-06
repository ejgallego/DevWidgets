// Optional actual InfoView checks. Use an isolated window with examples/SnapshotExplorer.lean.
// node tests/SnapshotExplorer/browser.mjs [debug-port] [window-width] [screenshot.png]
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';
import { connect } from '../Widget/cdp.mjs';
const port = Number(process.argv[2] || 9232);
const width = Number(process.argv[3] || 900);
const screenshot = process.argv[4];
const targets = await (await fetch(`http://127.0.0.1:${port}/json/list`, { signal: AbortSignal.timeout(10000) })).json();
const pages = targets.filter(target => target.type === 'page');
assert.equal(pages.length, 1, 'Use an isolated VSCode window.');
const frameTarget = targets.find(t => t.type === 'iframe' && t.parentId === pages[0].id && t.url.includes('leanprover.lean4'));
assert.ok(frameTarget, 'Open Lean InfoView first.');
const page = await connect(pages[0]);
let frame;
try {
  assert.equal(await page.evaluate(`Array.from(document.querySelectorAll('[role="dialog"]')).some(el =>
    el.getClientRects().length > 0 && getComputedStyle(el).visibility !== 'hidden' && getComputedStyle(el).display !== 'none')`),
    false, 'Dismiss VSCode dialogs before running the InfoView checks.');
  frame = await connect(frameTarget);
  const ui = code => frame.evaluate(`(async () => {
    const d = document.getElementById('active-frame').contentDocument;
    const root = d.querySelector('section[aria-label="Snapshot Explorer"]');
    ${code}
  })()`);
  const waitFor = async (condition, message) => {
    const deadline = Date.now() + 10000;
    while (!(await condition())) {
      assert.ok(Date.now() < deadline, message);
      await new Promise(resolve => setTimeout(resolve, 100));
    }
  };
  await waitFor(() => ui(`return root?.textContent.includes('Command discovery finished');`), 'Snapshot overview did not load.');
  assert.ok(await ui(`return d.body.innerText.startsWith('SnapshotExplorer.lean:');`), 'Use the snapshot example.');
  await page.send('Emulation.setDeviceMetricsOverride', { width, height: 1000, deviceScaleFactor: 1, mobile: false });
  // Electron resizes nested webviews asynchronously after the outer viewport.
  await new Promise(resolve => setTimeout(resolve, 250));
  // Start at the anchor so repeated runs still exercise a real position change.
  await ui(`const anchor = [...root.querySelectorAll('button')].find(b => b.textContent.startsWith('def snapshotAnchor'));
    if (!anchor) throw new Error('Example anchor missing'); anchor.click();`);
  await waitFor(() => ui(`return [...root.querySelectorAll('button')].some(b =>
    b.textContent.startsWith('def snapshotAnchor') && b.getAttribute('aria-pressed') === 'true');`), 'Anchor selection did not load.');
  await ui(`[...root.querySelectorAll('button')].find(b => b.textContent === 'Go to source').click();`);
  await waitFor(() => ui(`return d.body.innerText.startsWith('SnapshotExplorer.lean:9:');`), 'Unpin the host InfoView before running this check.');
  await ui(`const button = [...root.querySelectorAll('button')].find(b => b.textContent.startsWith('theorem snapshotExample'));
    if (!button) throw new Error('Example theorem missing'); button.click();`);
  await waitFor(() => ui(`return [...root.querySelectorAll('button')].some(b =>
    b.textContent.startsWith('theorem snapshotExample') && b.getAttribute('aria-pressed') === 'true');`), 'Command details did not load.');
  // Keep the host InfoView unpinned: source navigation must change its position,
  // while the file observer keeps the selected command and its details.
  const beforePosition = await ui(`return d.body.innerText.split('\\n')[0];`);
  const beforeSelection = await ui(`return root.querySelector('h4').textContent;`);
  await ui(`const source = [...root.querySelectorAll('button')].find(b => b.textContent === 'Go to source'); source.click();`);
  await waitFor(() => ui(`return d.body.innerText.split('\\n')[0] !== ${JSON.stringify(beforePosition)};`),
    'Source navigation did not move InfoView. Unpin the host InfoView before running this check.');
  await waitFor(() => ui(`return root?.querySelector('h4')?.textContent === ${JSON.stringify(beforeSelection)} &&
    ![...root.querySelectorAll('button')].find(b => b.textContent === 'Refresh').disabled;`),
    'Cursor navigation lost the selected snapshot.');
  await ui(`const nested = [...root.querySelectorAll('summary')].find(s => s.textContent.startsWith('Declaration 1'));
    if (!nested) throw new Error('Declaration snapshots missing'); nested.parentElement.open = true;`);
  assert.ok(await ui(`const summary = [...root.querySelectorAll('summary')].find(s => s.textContent.startsWith('Tactics'));
    return summary?.parentElement.parentElement.tagName === 'DETAILS';`), 'Snapshot rows are not nested disclosures.');
  // Refresh must retain the open disclosure for the same snapshot path.
  await ui(`const b = [...root.querySelectorAll('button')].find(b => b.textContent === 'Refresh'); b.click();`);
  await waitFor(() => ui(`return ![...root.querySelectorAll('button')].find(b => b.textContent === 'Refresh').disabled;`), 'Refresh did not settle.');
  assert.ok(await ui(`return [...root.querySelectorAll('summary')].find(s => s.textContent.startsWith('Declaration 1')).parentElement.open;`));
  await ui(`const b = [...root.querySelectorAll('button')].find(b => b.textContent === 'Freeze capture'); b.scrollIntoView(); b.focus();`);
  for (const expected of ['Resume live', 'Freeze capture']) {
    await page.send('Input.dispatchKeyEvent', { type: 'keyDown', key: ' ', code: 'Space', windowsVirtualKeyCode: 32 });
    await page.send('Input.dispatchKeyEvent', { type: 'keyUp', key: ' ', code: 'Space', windowsVirtualKeyCode: 32 });
    await waitFor(() => ui(`return d.activeElement?.textContent === '${expected}';`), 'Freeze/resume lost keyboard focus.');
  }
  const layout = await ui(`return {
    panelWidth: root.clientWidth,
    overflow: root.scrollWidth > root.clientWidth + 2,
    settingsClosed: [...root.querySelectorAll('summary')].find(s => s.textContent === 'Capture settings').parentElement.open === false,
    selection: root.querySelectorAll('button[aria-pressed="true"]').length
  };`);
  assert.equal(layout.overflow, false, 'Snapshot panel overflows horizontally.');
  assert.equal(layout.settingsClosed, true);
  assert.equal(layout.selection, 1);
  if (screenshot) {
    const image = await page.send('Page.captureScreenshot', { format: 'png' });
    writeFileSync(screenshot, Buffer.from(image.data, 'base64'));
  }
  assert.deepEqual(frame.exceptions, []);
  console.log(JSON.stringify({ result: 'Snapshot InfoView checks passed', ...layout }));
} finally { frame?.close(); page.close(); }
