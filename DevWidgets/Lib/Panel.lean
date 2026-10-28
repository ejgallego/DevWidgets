/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/

module
public section

namespace DevWidgets.Lib.Panel

/-- Shared frontend helpers, embedded in each independent widget module. -/
def javascript : String := r#"
function boundedNat(value, fallback, min, max) {
  return typeof value === 'number' && Number.isFinite(value)
    ? Math.max(min, Math.min(max, Math.floor(value))) : fallback;
}

// Overrides belong to this panel and this configuration. New Lean props replace them.
function usePanelSettings(defaults) {
  const key = JSON.stringify(defaults);
  const [override, setOverride] = React.useState(null);
  React.useEffect(() => { setOverride(null); }, [key]);
  const value = override?.key === key ? override.value : defaults;
  const update = (next) => setOverride((previous) => {
    const current = previous?.key === key ? previous.value : defaults;
    const value = typeof next === 'function' ? next(current) : next;
    return Object.is(value, current) ? previous : { key, value };
  });
  return [value, update, () => setOverride(null)];
}

function panelButton(label, onClick, disabled = false, title = '') {
  return React.createElement('button', {
    key: label, type: 'button', onClick, disabled, title,
    style: { padding: '0.1rem 0.45rem', cursor: disabled ? 'default' : 'pointer' }
  }, label);
}

// Pin a completed response, not an RPC position: the current session may change files.
function useCursorControls(pos) {
  const [pinned, setPinned] = React.useState(null);
  const [revision, setRevision] = React.useState(0);
  return {
    pinned: pinned !== null,
    revision,
    pos: pinned ? pinned.pos : pos,
    view: (state) => pinned ? pinned.state : state,
    pin: (state, sourcePos = pos) => setPinned({ pos: sourcePos ? { ...sourcePos } : null, state }),
    follow: () => setPinned(null),
    refresh: () => setRevision((n) => n + 1),
    reset: () => { setPinned(null); setRevision((n) => n + 1); }
  };
}

function cursorToolbar(control, state, onReset = () => {}, sourcePos = control.pos) {
  return React.createElement('div', {
    role: 'group', 'aria-label': 'Panel controls',
    style: { display: 'flex', flexWrap: 'wrap', alignItems: 'center', gap: '0.4rem', padding: '0.4rem 0' }
  },
    panelButton(control.pinned ? 'Follow cursor' : 'Pin result',
      () => control.pinned ? control.follow() : control.pin(state, sourcePos),
      !control.pinned && (!control.pos || !(state.state === 'resolved' && state.value)),
      control.pinned ? 'Resume updates at the current cursor.' : 'Keep this result while moving the cursor.'),
    panelButton('Refresh', control.refresh, control.pinned || !control.pos,
      control.pinned ? 'Follow the cursor to refresh.' : 'Request a fresh result at the current cursor.'),
    panelButton('Reset panel', () => { onReset(); control.reset(); }, false,
      'Restore the configuration supplied by the Lean file and follow the cursor.'),
    control.pinned ? React.createElement('span', { role: 'status' }, 'Pinned snapshot') : null
  );
}
"#

end DevWidgets.Lib.Panel
