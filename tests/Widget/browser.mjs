// Optional real InfoView regression. See tests/README.md; not part of lake test.
// Run only against an isolated VSCode window showing tests/Widget/Interactive.lean.
import assert from 'node:assert/strict';
import { writeFileSync } from 'node:fs';

const port = Number(process.argv[2] || 9231);
const width = Number(process.argv[3] || 900);
const screenshot = process.argv[4];
const targets = await (await fetch(`http://127.0.0.1:${port}/json/list`)).json();
const pages = targets.filter(t => t.type === 'page');
assert.equal(pages.length, 1, 'Use a dedicated VSCode instance with exactly one window.');
const pageTarget = pages[0];
const frameTarget = targets.find(t => t.type === 'iframe' && t.parentId === pageTarget.id && t.url.includes('leanprover.lean4'));
assert.ok(frameTarget, 'Open Lean InfoView first.');

async function connect(target) {
  const ws = new WebSocket(target.webSocketDebuggerUrl);
  await new Promise((resolve, reject) => {
    ws.addEventListener('open', resolve, { once: true });
    ws.addEventListener('error', reject, { once: true });
  });
  let id = 0;
  const pending = new Map();
  const exceptions = [];
  ws.onmessage = event => {
    const message = JSON.parse(event.data);
    if (message.id) {
      const request = pending.get(message.id);
      if (!request) return;
      pending.delete(message.id);
      clearTimeout(request.timer);
      if (message.error) request.reject(new Error(JSON.stringify(message.error)));
      else request.resolve(message.result);
    } else if (message.method === 'Runtime.exceptionThrown') exceptions.push(message.params);
  };
  const send = (method, params = {}) => new Promise((resolve, reject) => {
    const requestId = ++id;
    const timer = setTimeout(() => { pending.delete(requestId); reject(new Error(`Timeout: ${method}`)); }, 10000);
    pending.set(requestId, { resolve, reject, timer });
    ws.send(JSON.stringify({ id: requestId, method, params }));
  });
  const evaluate = async expression => {
    const result = await send('Runtime.evaluate', { expression, returnByValue: true, awaitPromise: true });
    assert.ok(!result.exceptionDetails, JSON.stringify(result.exceptionDetails));
    return result.result.value;
  };
  await send('Runtime.enable');
  return { send, evaluate, exceptions, close: () => ws.close() };
}

const page = await connect(pageTarget);
let frame;
try {
  frame = await connect(frameTarget);
  const ui = code => frame.evaluate(`(async () => {
    const d = document.getElementById('active-frame').contentDocument;
    ${code}
  })()`);
  const settle = () => new Promise(resolve => setTimeout(resolve, 150));
  assert.ok(await ui(`return d.body.innerText.startsWith('Interactive.lean:');`),
    'Place the cursor in Interactive.lean before running the UI checks.');
  await page.send('Emulation.setDeviceMetricsOverride', { width, height: 1000, deviceScaleFactor: 1, mobile: false });
  await settle();
  assert.ok(await ui(`return d.body.innerText.includes('IR available');`), 'Wait for the fixture to elaborate.');
  // Manual mode may have made its initial read before the fixture's #eval finished.
  await ui(`const title = [...d.querySelectorAll('strong')].find(e => e.textContent === 'Progress Tracker');
    [...title.parentElement.querySelectorAll('button')].find(b => b.textContent === 'Refresh').click();`);
  for (let attempt = 0; attempt < 40 && await ui(`return d.querySelectorAll('article').length !== 3;`); attempt++) await settle();
  assert.equal(await ui(`return d.querySelectorAll('article').length;`), 3,
    'Restart the fixture to recreate the sample tasks.');

  // Use actual keyboard events: React must preserve the focused DOM node as the label changes.
  for (let index = 0; index < 3; index++) {
    await ui(`const b = [...d.querySelectorAll('button')].filter(b => b.textContent === 'Pin result')[${index}];
      if (!b || b.disabled) throw new Error('Missing resolved cursor widget');
      b.scrollIntoView(); b.focus();`);
    for (const expected of ['Follow cursor', 'Pin result']) {
      await page.send('Input.dispatchKeyEvent', { type: 'keyDown', key: ' ', code: 'Space', windowsVirtualKeyCode: 32 });
      await page.send('Input.dispatchKeyEvent', { type: 'keyUp', key: ' ', code: 'Space', windowsVirtualKeyCode: 32 });
      await settle();
      assert.equal(await ui(`return d.activeElement?.tagName === 'BUTTON' ? d.activeElement.textContent : d.activeElement?.tagName;`), expected, `Pin/Follow lost keyboard focus in widget ${index} (${expected})`);
    }
  }

  const layout = await ui(`
    const cards = [...d.querySelectorAll('article')];
    cards[0].scrollIntoView();
    const button = cards[0].querySelector('button');
    const rect = button.getBoundingClientRect();
    return {
      width: d.documentElement.clientWidth,
      cardOverflow: cards.some(c => c.scrollWidth > c.clientWidth + 2),
      deleteVisible: rect.left >= 0 && rect.right <= d.documentElement.clientWidth,
      deleteLabel: button.textContent,
      retention: d.body.innerText.includes('Completed tasks are kept until you delete them.'),
      optionsClosed: [...d.querySelectorAll('summary')].find(s => s.textContent === 'Inspector options')?.parentElement.open === false
    };
  `);
  assert.equal(layout.cardOverflow, false, 'Task content overflows its card');
  assert.equal(layout.deleteVisible, true, 'Delete action is outside the pane');
  assert.equal(layout.deleteLabel, 'Delete');
  assert.equal(layout.retention, true);
  assert.equal(layout.optionsClosed, true);
  const contrast = await ui(`
    const luminance = color => {
      const rgb = color.match(/[0-9.]+/g).slice(0, 3).map(Number).map(v => v / 255)
        .map(v => v <= 0.04045 ? v / 12.92 : ((v + 0.055) / 1.055) ** 2.4);
      return rgb[0] * 0.2126 + rgb[1] * 0.7152 + rgb[2] * 0.0722;
    };
    return [...d.querySelectorAll('.dw-compiler span[style*="--dw-code-"]')].map(span => {
      let parent = span;
      let background;
      do {
        background = d.defaultView.getComputedStyle(parent).backgroundColor;
        parent = parent.parentElement;
      } while (parent && background === 'rgba(0, 0, 0, 0)');
      const [a, b] = [luminance(d.defaultView.getComputedStyle(span).color), luminance(background)].sort((a, b) => a - b);
      return (b + 0.05) / (a + 0.05);
    });
  `);
  assert.ok(contrast.length > 0, 'No syntax-colored output found');
  assert.ok(Math.min(...contrast) >= 4.5, `Code text contrast is too low: ${Math.min(...contrast).toFixed(2)}:1`);
  if (screenshot) {
    await settle();
    const shot = await page.send('Page.captureScreenshot', { format: 'png' });
    writeFileSync(screenshot, Buffer.from(shot.data, 'base64'));
  }
  await ui(`d.querySelector('article button').click();`);
  for (let attempt = 0; attempt < 40 && await ui(`return d.querySelectorAll('article').length !== 2;`); attempt++) await settle();
  assert.equal(await ui(`return d.querySelectorAll('article').length;`), 2, 'Delete did not remove the completed sample');
  assert.deepEqual(frame.exceptions, [], 'InfoView raised a runtime exception');
  console.log(`InfoView keyboard, layout, contrast, retention, and deletion checks passed (${layout.width}px pane; minimum syntax contrast ${Math.min(...contrast).toFixed(2)}:1).`);
} finally {
  await page.send('Emulation.clearDeviceMetricsOverride');
  frame?.close();
  page.close();
}
