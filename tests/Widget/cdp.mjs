// Shared CDP transport for the optional isolated-VSCode browser checks.
import assert from 'node:assert/strict';

export async function connect(target) {
  const ws = new WebSocket(target.webSocketDebuggerUrl);
  try {
    await new Promise((resolve, reject) => {
      const timer = setTimeout(() => reject(new Error('CDP connection timed out')), 10000);
      const finish = (fn, value) => { clearTimeout(timer); fn(value); };
      ws.addEventListener('open', () => finish(resolve), { once: true });
      ws.addEventListener('error', error => finish(reject, error), { once: true });
      ws.addEventListener('close', () => finish(reject, new Error('CDP closed during connection')), { once: true });
    });
  } catch (error) { ws.close(); throw error; }
  let id = 0;
  const pending = new Map();
  const exceptions = [];
  const failPending = error => {
    for (const request of pending.values()) { clearTimeout(request.timer); request.reject(error); }
    pending.clear();
  };
  ws.addEventListener('close', () => failPending(new Error('CDP connection closed')));
  ws.addEventListener('error', failPending);
  ws.onmessage = event => {
    let message;
    try { message = JSON.parse(event.data); }
    catch (error) { failPending(error); ws.close(); return; }
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
    try { ws.send(JSON.stringify({ id: requestId, method, params })); }
    catch (error) { clearTimeout(timer); pending.delete(requestId); reject(error); }
  });
  const evaluate = async expression => {
    const result = await send('Runtime.evaluate', { expression, returnByValue: true, awaitPromise: true });
    assert.ok(!result.exceptionDetails, JSON.stringify(result.exceptionDetails));
    return result.result.value;
  };
  try { await send('Runtime.enable'); }
  catch (error) { ws.close(); throw error; }
  return { send, evaluate, exceptions, close: () => ws.close() };
}
