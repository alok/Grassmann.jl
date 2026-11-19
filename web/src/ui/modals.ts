// Connection Settings Modal (Native ga-server / Lean WASM / Static .gsir Wire Inspector)
// + Attribution & About Modal crediting Michael Reed (Grassmann.jl) & Steven De Keninck (ganja.js)

export interface ConnectionModalCallbacks {
  onConnectServer: (url: string) => void;
  onConnectWasm: (url: string) => void;
  onInspectStaticFixture: () => void;
}

export function createConnectionModal(
  initialServerUrl: string,
  initialWasmUrl: string,
  callbacks: ConnectionModalCallbacks
): {
  element: HTMLDivElement;
  open: (errorDetail?: string) => void;
  close: () => void;
} {
  const backdrop = document.createElement('div');
  backdrop.className = 'gs-modal-backdrop hidden';

  const dialog = document.createElement('div');
  dialog.className = 'gs-modal';

  const head = document.createElement('div');
  head.className = 'gs-modal-head';
  head.innerHTML = '<h3>Lean 4 Backend Transport</h3>';
  const closeBtn = document.createElement('button');
  closeBtn.type = 'button';
  closeBtn.className = 'gs-icon-btn';
  closeBtn.textContent = '×';
  head.appendChild(closeBtn);

  const errorBox = document.createElement('div');
  errorBox.className = 'gs-modal-error hidden';

  const note = document.createElement('p');
  note.className = 'gs-modal-note';
  note.innerHTML =
    '<strong>“It’s All in Lean” Purity:</strong> Zero Geometric Algebra math, mesh slicing, contour extraction, or Wedge rules run in JS/TS. Connect to either the native Lean <code>ga-server</code> or compiled <code>grassmann.wasm</code>.';

  // Server section
  const serverRow = document.createElement('div');
  serverRow.className = 'gs-field';
  serverRow.innerHTML = '<label>Native Lean <code>ga-server</code> (HTTP / WebSocket Binary GSIR)</label>';
  const sLine = document.createElement('div');
  sLine.className = 'gs-row-gap';
  const serverInput = document.createElement('input');
  serverInput.className = 'gs-input mono';
  serverInput.value = initialServerUrl;
  const serverBtn = document.createElement('button');
  serverBtn.type = 'button';
  serverBtn.className = 'gs-btn gs-btn-primary';
  serverBtn.textContent = 'Connect';
  serverBtn.addEventListener('click', () => {
    close();
    callbacks.onConnectServer(serverInput.value.trim());
  });
  sLine.append(serverInput, serverBtn);
  serverRow.appendChild(sLine);

  // WASM section
  const wasmRow = document.createElement('div');
  wasmRow.className = 'gs-field';
  wasmRow.innerHTML = '<label>Compiled Lean WASM (<code>grassmann.wasm</code> C ABI)</label>';
  const wLine = document.createElement('div');
  wLine.className = 'gs-row-gap';
  const wasmInput = document.createElement('input');
  wasmInput.className = 'gs-input mono';
  wasmInput.value = initialWasmUrl;
  const wasmBtn = document.createElement('button');
  wasmBtn.type = 'button';
  wasmBtn.className = 'gs-btn gs-btn-accent';
  wasmBtn.textContent = 'Load WASM';
  wasmBtn.addEventListener('click', () => {
    close();
    callbacks.onConnectWasm(wasmInput.value.trim());
  });
  wLine.append(wasmInput, wasmBtn);
  wasmRow.appendChild(wLine);

  // Static binary GSIR wire fixture inspector (zero GA math!)
  const fixtureBox = document.createElement('div');
  fixtureBox.className = 'gs-modal-divider';
  const fixBtn = document.createElement('button');
  fixBtn.type = 'button';
  fixBtn.className = 'gs-btn gs-btn-ghost';
  fixBtn.textContent = 'Inspect Static Binary GSIR v1 Wire Fixture (Offline Test Snapshot)';
  fixBtn.addEventListener('click', () => {
    close();
    callbacks.onInspectStaticFixture();
  });
  fixtureBox.appendChild(fixBtn);

  dialog.append(head, errorBox, note, serverRow, wasmRow, fixtureBox);
  backdrop.appendChild(dialog);

  const open = (errorDetail?: string) => {
    if (errorDetail) {
      errorBox.textContent = errorDetail;
      errorBox.classList.remove('hidden');
    } else {
      errorBox.classList.add('hidden');
    }
    backdrop.classList.remove('hidden');
  };

  const close = () => backdrop.classList.add('hidden');

  closeBtn.addEventListener('click', close);
  backdrop.addEventListener('click', (e) => {
    if (e.target === backdrop) close();
  });

  return { element: backdrop, open, close };
}

export function createAboutModal(): {
  element: HTMLDivElement;
  open: () => void;
  close: () => void;
} {
  const backdrop = document.createElement('div');
  backdrop.className = 'gs-modal-backdrop hidden';

  const dialog = document.createElement('div');
  dialog.className = 'gs-modal';

  const head = document.createElement('div');
  head.className = 'gs-modal-head';
  head.innerHTML = '<h3>About Grassmann 3D Studio</h3>';
  const closeBtn = document.createElement('button');
  closeBtn.type = 'button';
  closeBtn.className = 'gs-icon-btn';
  closeBtn.textContent = '×';
  head.appendChild(closeBtn);

  const body = document.createElement('div');
  body.className = 'gs-about-body';
  body.innerHTML = `
    <p>
      <strong>Grassmann 3D Studio</strong> is a pure <code>GSIR</code> v1 binary renderer, spatial studio IDE,
      and WebXR frontend for <strong>Grassmann.lean</strong> (Lean 4) &amp; <strong>LeanCalculator</strong>.
      Every Clifford/Geometric Algebra product, PGA3 mesh slice, CGA round classification, contour extraction,
      OPNS shader emission, and Wedge puzzle rule executes exclusively in <strong>Lean 4</strong>.
    </p>
    <div class="gs-credit-card">
      <div class="gs-credit-name">Michael Reed (<code>chakravala</code>)</div>
      <div class="gs-credit-role">Creator of <strong>Grassmann.jl</strong> &amp; the Leibniz / DirectSum / Cartan Geometric Algebra ecosystem realized here in Lean 4.</div>
    </div>
    <div class="gs-credit-card">
      <div class="gs-credit-name">Steven De Keninck (<code>enkimute</code>)</div>
      <div class="gs-credit-role">Creator of <strong>ganja.js</strong>, the CoffeeShop IDE, GAlculator, and the coordinate-free <em>Wedge</em> game inspiring these interactive modes.</div>
    </div>
  `;

  dialog.append(head, body);
  backdrop.appendChild(dialog);

  const open = () => backdrop.classList.remove('hidden');
  const close = () => backdrop.classList.add('hidden');
  closeBtn.addEventListener('click', close);
  backdrop.addEventListener('click', (e) => {
    if (e.target === backdrop) close();
  });

  return { element: backdrop, open, close };
}
