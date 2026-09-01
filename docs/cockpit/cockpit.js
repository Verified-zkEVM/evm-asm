const GROUPS = [
  "Arithmetic",
  "Compare / bitwise",
  "Environmental",
  "Block",
  "Stack / memory / flow",
  "Push / Dup / Swap",
  "System",
];

const OPCODE_GROUP = {
  STOP: "Arithmetic",
  ADD: "Arithmetic",
  MUL: "Arithmetic",
  SUB: "Arithmetic",
  DIV: "Arithmetic",
  SDIV: "Arithmetic",
  MOD: "Arithmetic",
  SMOD: "Arithmetic",
  ADDMOD: "Arithmetic",
  MULMOD: "Arithmetic",
  EXP: "Arithmetic",
  SIGNEXTEND: "Arithmetic",
  LT: "Compare / bitwise",
  GT: "Compare / bitwise",
  SLT: "Compare / bitwise",
  SGT: "Compare / bitwise",
  EQ: "Compare / bitwise",
  ISZERO: "Compare / bitwise",
  AND: "Compare / bitwise",
  OR: "Compare / bitwise",
  XOR: "Compare / bitwise",
  NOT: "Compare / bitwise",
  BYTE: "Compare / bitwise",
  SHL: "Compare / bitwise",
  SHR: "Compare / bitwise",
  SAR: "Compare / bitwise",
  KECCAK256: "Environmental",
  ADDRESS: "Environmental",
  BALANCE: "Environmental",
  ORIGIN: "Environmental",
  CALLER: "Environmental",
  CALLVALUE: "Environmental",
  CALLDATALOAD: "Environmental",
  CALLDATASIZE: "Environmental",
  CALLDATACOPY: "Environmental",
  CODESIZE: "Environmental",
  CODECOPY: "Environmental",
  GASPRICE: "Environmental",
  EXTCODESIZE: "Environmental",
  EXTCODECOPY: "Environmental",
  RETURNDATASIZE: "Environmental",
  RETURNDATACOPY: "Environmental",
  EXTCODEHASH: "Environmental",
  BLOCKHASH: "Block",
  COINBASE: "Block",
  TIMESTAMP: "Block",
  NUMBER: "Block",
  PREVRANDAO: "Block",
  GASLIMIT: "Block",
  CHAINID: "Block",
  SELFBALANCE: "Block",
  BASEFEE: "Block",
  BLOBHASH: "Block",
  BLOBBASEFEE: "Block",
  POP: "Stack / memory / flow",
  MLOAD: "Stack / memory / flow",
  MSTORE: "Stack / memory / flow",
  MSTORE8: "Stack / memory / flow",
  SLOAD: "Stack / memory / flow",
  SSTORE: "Stack / memory / flow",
  JUMP: "Stack / memory / flow",
  JUMPI: "Stack / memory / flow",
  PC: "Stack / memory / flow",
  MSIZE: "Stack / memory / flow",
  GAS: "Stack / memory / flow",
  JUMPDEST: "Stack / memory / flow",
  TLOAD: "Stack / memory / flow",
  TSTORE: "Stack / memory / flow",
  MCOPY: "Stack / memory / flow",
  PUSH0: "Stack / memory / flow",
  PUSH1: "Push / Dup / Swap",
  "PUSH2..32": "Push / Dup / Swap",
  "DUP1..16": "Push / Dup / Swap",
  "SWAP1..16": "Push / Dup / Swap",
  "LOG0..4": "System",
  CREATE: "System",
  CALL: "System",
  CALLCODE: "System",
  RETURN: "System",
  DELEGATECALL: "System",
  CREATE2: "System",
  STATICCALL: "System",
  REVERT: "System",
  INVALID: "System",
  SELFDESTRUCT: "System",
};

const OBLIGATION_SHORT = {
  1: "RV64 ELF",
  2: "Host I/O",
  3: "RLP decode",
  4: "Interpreter",
  5: "Opcode cov.",
  6: "Accelerators",
  7: "MPT verify",
  8: "Post-state",
  9: "Halt",
  10: "Witness reads",
};

const OBLIGATION_EDGES = [
  ["3", "4"],
  ["5", "4"],
  ["7", "10"],
  ["4", "8"],
  ["5", "8"],
  ["6", "8"],
  ["7", "8"],
  ["10", "8"],
  ["1", "8"],
];

const TIER_COLOR = {
  proven: "var(--green)",
  conditional: "var(--yellow)",
  partly: "var(--cyan)",
  execSpec: "var(--orange)",
  notStarted: "var(--gray)",
};

const STATUS_COLOR = {
  done: "var(--green)",
  blocked: "var(--yellow)",
  notStarted: "var(--gray)",
};

const state = {
  data: null,
  filter: "gaps",
  selectedOpcode: null,
  selectedObligation: null,
};

function esc(s) {
  return String(s ?? "")
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

function formatBp(bp) {
  const whole = Math.floor(bp / 100);
  const frac = bp % 100;
  return `${whole}.${frac < 10 ? "0" : ""}${frac}`;
}

function githubBlob(path) {
  const sha = state.data.githubSha;
  return `https://github.com/Verified-zkEVM/evm-asm/blob/${sha}/${path}`;
}

function tierLabel(tier) {
  return tier === "partly" ? "partial" : tier;
}

function render() {
  const root = document.getElementById("app");
  const d = state.data;
  if (!d) {
    root.innerHTML = `<p class="status">Loading cockpit snapshot…</p>`;
    return;
  }

  const oc = d.opcodeCounts;
  const rc = d.routineCounts;
  const ob = d.obligationCounts;
  const img = d.imageCoverage;
  const corr = d.correspondence;
  const provenPct = Math.round((1000 * oc.proven) / oc.total) / 10;
  const imgPct = formatBp(img.coverageBasisPoints);

  root.innerHTML = `
    <div class="stack stack-28">
      ${renderHeader(d, provenPct, oc, rc, ob, img, imgPct, corr)}
      <div class="callout info">
        <div class="callout-title">Two lenses</div>
        <p class="small">The heat map is verification <span class="semibold">breadth</span>
        (opcode tiers). The DAG is <span class="semibold">direction</span>
        (guest obligations). High proven% can coexist with a blocked post-state
        root — that is intentional. Host I/O can be done while RLP is blocked:
        transport vs parse.</p>
      </div>
      ${renderHeat(d)}
      <hr />
      ${renderDag(d)}
      <hr />
      ${renderDetails(d)}
    </div>
  `;
  bind(root);
}

function renderHeader(d, provenPct, oc, rc, ob, img, imgPct, corr) {
  return `
    <div class="stack stack-12">
      <div class="stack stack-4">
        <div class="row">
          <h1>evm-asm progress cockpit</h1>
          <span class="pill active">as of ${esc(d.displayDate)}</span>
          <span class="pill">${esc(d.branch)} @ ${esc(d.sha)}</span>
        </div>
        <p class="muted">Refreshed ${esc(d.date)} from checked-out ${esc(d.branch)} HEAD ·
          ${esc(d.toolchain)} · matches live Lean registries</p>
        <p class="faint">Embedded view of ${esc(d.source)}. CI truth remains
          <code>DRIFT.md</code> / <code>lake exe progress-report</code>.</p>
      </div>
      <div class="callout success">
        <div class="callout-title">Current as of ${esc(d.displayDate)}</div>
        <p class="small">Snapshot taken at <code>${esc(d.sha)}</code> and stamped
        from the Lean registries. Merge to <code>main</code> republishes this page.
        Do not hand-edit the counts.</p>
      </div>
      <div class="stats">
        <div class="stat success"><div class="stat-value">${provenPct}%</div><div class="stat-label">Opcodes proven</div></div>
        <div class="stat success"><div class="stat-value">${oc.proven}</div><div class="stat-label">Proven</div></div>
        <div class="stat warning"><div class="stat-value">${oc.conditional}</div><div class="stat-label">Conditional</div></div>
        <div class="stat danger"><div class="stat-value">${oc.execSpec}</div><div class="stat-label">execSpec gaps</div></div>
        <div class="stat"><div class="stat-value">${ob.done}/${ob.total}</div><div class="stat-label">Obligations done</div></div>
        <div class="stat warning"><div class="stat-value">${ob.blocked}</div><div class="stat-label">Obligations blocked</div></div>
      </div>
      ${usageBar(oc.total, [
        ["proven", oc.proven, "var(--green)"],
        ["conditional", oc.conditional, "var(--yellow)"],
        ["execSpec", oc.execSpec, "var(--orange)"],
      ], `Opcode registry (${oc.total} entries)`,
        `${oc.proven} proven · ${oc.conditional} conditional · ${oc.execSpec} execSpec`)}
      ${usageBar(rc.total, [
        ["rproven", rc.proven, "var(--green)"],
        ["rcond", rc.conditional, "var(--yellow)"],
        ["rpartly", rc.partly, "var(--cyan)"],
      ], `Guest-routine registry (${rc.total} entries · ${d.routineSymbols} symbols)`,
        `${rc.proven} proven · ${rc.conditional} conditional · ${rc.partly} partial`)}
      ${usageBar(img.textBytes, [
        ["pinned", img.coveredBytes, "var(--blue)"],
        ["unpinned", img.textBytes - img.coveredBytes, "var(--gray)"],
      ], `Guest image CodeReq (${img.entries} linked entries)`,
        `${imgPct}% of .text · ${img.coveredBytes.toLocaleString()} / ${img.textBytes.toLocaleString()} bytes`)}
      ${usageBar(corr.total, [
        ["agrees", corr.agrees, "var(--green)"],
        ["restricted", corr.domainRestricted, "var(--yellow)"],
        ["none", corr.noCounterpart, "var(--gray)"],
        ["unproven", corr.unproven, "var(--orange)"],
      ], `Spec correspondence (${corr.total} audited rows)`,
        `${corr.agrees} agrees · ${corr.domainRestricted} domain-restricted · ${corr.unproven} unproven`)}
    </div>
  `;
}

function usageBar(total, segs, left, right) {
  const parts = segs
    .filter(([, v]) => v > 0)
    .map(([, v, color]) =>
      `<span style="width:${(100 * v) / total}%;background:${color}"></span>`)
    .join("");
  return `
    <div>
      <div class="bar-meta"><span>${esc(left)}</span><span>${esc(right)}</span></div>
      <div class="bar">${parts}</div>
    </div>
  `;
}

function renderHeat(d) {
  const selected = state.selectedOpcode;
  const groups = GROUPS.map((group) => {
    const cells = d.opcodes
      .filter((o) => (OPCODE_GROUP[o.name] || "System") === group)
      .map((op) => {
        const isSelected = selected === op.name;
        const isGap = op.tier !== "proven";
        const cls = [
          "heat-cell",
          isGap ? "gap" : "",
          isSelected ? "selected" : "",
          selected && !isSelected ? "dim" : "",
        ].filter(Boolean).join(" ");
        return `<button type="button" class="${cls}" data-opcode="${esc(op.name)}"
          style="border-left-color:${TIER_COLOR[op.tier]}"
          title="${esc(op.name)} · ${tierLabel(op.tier)}${op.notes ? ` — ${op.notes}` : ""}">${esc(op.name)}</button>`;
      })
      .join("");
    return `<div class="heat-group">
      <p class="small semibold muted">${esc(group)}</p>
      <div class="heat-cells">${cells}</div>
    </div>`;
  }).join("");

  return `
    <div class="stack stack-12">
      <div class="row">
        <h2>Opcode coverage heat map</h2>
        <div class="legend">
          ${legendItem("var(--green)", "proven")}
          ${legendItem("var(--yellow)", "conditional")}
          ${legendItem("var(--orange)", "execSpec")}
          ${legendItem("var(--cyan)", "partial")}
          ${legendItem("var(--gray)", "notStarted")}
        </div>
      </div>
      <p class="muted">Registry entries by ISA family. Click a cell to filter the gap table. Click again to clear.</p>
      ${groups}
    </div>
  `;
}

function legendItem(color, label) {
  return `<span class="row" style="gap:6px"><span class="swatch" style="background:${color}"></span><span class="small muted">${label}</span></span>`;
}

function dagLayout(obligations) {
  const ids = obligations.map((o) => String(o.id));
  const incoming = new Map(ids.map((id) => [id, []]));
  const outgoing = new Map(ids.map((id) => [id, []]));
  for (const [from, to] of OBLIGATION_EDGES) {
    if (outgoing.has(from) && incoming.has(to)) {
      outgoing.get(from).push(to);
      incoming.get(to).push(from);
    }
  }
  const rank = new Map();
  const visit = (id, seen) => {
    if (rank.has(id)) return rank.get(id);
    if (seen.has(id)) return 0;
    seen.add(id);
    const preds = incoming.get(id) || [];
    const r = preds.length === 0 ? 0 : 1 + Math.max(...preds.map((p) => visit(p, seen)));
    rank.set(id, r);
    return r;
  };
  for (const id of ids) visit(id, new Set());

  const byRank = new Map();
  for (const id of ids) {
    const r = rank.get(id);
    if (!byRank.has(r)) byRank.set(r, []);
    byRank.get(r).push(id);
  }
  const ranks = [...byRank.keys()].sort((a, b) => a - b);
  const nodeW = 112;
  const nodeH = 44;
  const rankGap = 72;
  const nodeGap = 16;
  const pad = 16;
  const maxCols = Math.max(...ranks.map((r) => byRank.get(r).length));
  const width = pad * 2 + maxCols * nodeW + (maxCols - 1) * nodeGap;
  const height = pad * 2 + ranks.length * nodeH + (ranks.length - 1) * rankGap;
  const nodes = [];
  for (const r of ranks) {
    const row = byRank.get(r);
    const rowWidth = row.length * nodeW + (row.length - 1) * nodeGap;
    const x0 = (width - rowWidth) / 2;
    row.forEach((id, i) => {
      nodes.push({
        id,
        x: x0 + i * (nodeW + nodeGap),
        y: pad + r * (nodeH + rankGap),
        cx: x0 + i * (nodeW + nodeGap) + nodeW / 2,
        cy: pad + r * (nodeH + rankGap) + nodeH / 2,
      });
    });
  }
  const pos = new Map(nodes.map((n) => [n.id, n]));
  const edges = OBLIGATION_EDGES.filter(([a, b]) => pos.has(a) && pos.has(b)).map(([a, b]) => {
    const s = pos.get(a);
    const t = pos.get(b);
    return { x1: s.cx, y1: s.y + nodeH, x2: t.cx, y2: t.y };
  });
  return { width, height, nodeW, nodeH, nodes, edges };
}

function renderDag(d) {
  const layout = dagLayout(d.obligations);
  const byId = new Map(d.obligations.map((o) => [String(o.id), o]));
  const selected = state.selectedObligation;
  const selectedObl = selected == null ? null : byId.get(String(selected));

  const lines = layout.edges.map((e, i) =>
    `<line key="${i}" x1="${e.x1}" y1="${e.y1}" x2="${e.x2}" y2="${e.y2}"
      stroke="currentColor" stroke-width="1.5" marker-end="url(#arrow)" />`).join("");

  const nodes = layout.nodes.map((n) => {
    const obl = byId.get(n.id);
    const isSelected = selected === obl.id;
    return `<button type="button" class="dag-node${isSelected ? " selected" : ""}"
      data-obligation="${obl.id}"
      style="left:${n.x}px;top:${n.y}px;width:${layout.nodeW}px;height:${layout.nodeH}px;border-top-color:${STATUS_COLOR[obl.status]}"
      title="#${obl.id} ${obl.name}">
      <span class="dag-id">#${obl.id} · ${obl.status}</span>
      <span class="dag-short">${esc(OBLIGATION_SHORT[obl.id] || obl.name)}</span>
    </button>`;
  }).join("");

  const blurb = selectedObl
    ? `<p class="small semibold">#${selectedObl.id} ${esc(selectedObl.name)} — ${selectedObl.status}</p>
       <p class="muted">${esc(selectedObl.note || "")}</p>`
    : `<p class="muted">Direction axis: what still blocks a complete L1 stateless guest. Edges
       are pipeline dependencies toward post-state root (#8). Green = done;
       amber = blocked. Click a node for what it means.</p>`;

  return `
    <div class="stack stack-12">
      <h2>Guest-program obligations</h2>
      ${blurb}
      <div class="dag-wrap" style="width:${layout.width}px;max-width:100%;height:${layout.height}px">
        <svg width="${layout.width}" height="${layout.height}" style="position:absolute;inset:0;color:var(--stroke)">
          <defs>
            <marker id="arrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">
              <path d="M 0 0 L 10 5 L 0 10 z" fill="currentColor" />
            </marker>
          </defs>
          ${lines}
        </svg>
        ${nodes}
      </div>
      <div class="legend">
        ${legendItem("var(--green)", `done (${d.obligationCounts.done})`)}
        ${legendItem("var(--yellow)", `blocked (${d.obligationCounts.blocked})`)}
      </div>
    </div>
  `;
}

function renderDetails(d) {
  const gapCount = d.opcodes.filter((o) => o.tier !== "proven").length;
  const f = state.filter;
  const selOp = state.selectedOpcode;
  const selObl = state.selectedObligation;

  let body;
  if (selObl != null) {
    const obl = d.obligations.find((o) => o.id === selObl);
    body = obl ? obligationDetail(obl) : "<p class='muted'>No matching obligation</p>";
  } else if (f === "obligations") {
    const rows = d.obligations.filter((o) => o.status !== "done");
    body = obligationTable(rows);
  } else {
    let ops = d.opcodes;
    if (selOp) ops = ops.filter((o) => o.name === selOp);
    else if (f === "gaps") ops = ops.filter((o) => o.tier !== "proven");
    body = opcodeTable(ops);
  }

  return `
    <div class="stack stack-12">
      <div class="row filters">
        <h2>Gaps &amp; details</h2>
        <button type="button" data-filter="gaps" class="${f === "gaps" && !selOp && selObl == null ? "active" : ""}">Gaps (${gapCount})</button>
        <button type="button" data-filter="opcodes" class="${f === "opcodes" && !selOp ? "active" : ""}">All opcodes (${d.opcodes.length})</button>
        <button type="button" data-filter="obligations" class="${f === "obligations" || selObl != null ? "active" : ""}">Obligations</button>
        ${(selOp || selObl != null) ? `<button type="button" data-clear="1">Clear selection</button>` : ""}
      </div>
      ${selOp ? `<p class="muted">Filtered to opcode <code>${esc(selOp)}</code></p>` : ""}
      ${body}
    </div>
  `;
}

function opcodeTable(ops) {
  const rows = ops.map((o) => {
    const tone = o.tier === "proven" ? "success"
      : o.tier === "conditional" ? "warning"
      : o.tier === "execSpec" ? "danger"
      : o.tier === "partly" ? "info"
      : "";
    return `<tr class="${tone}"><td>${esc(o.name)}</td><td>${esc(OPCODE_GROUP[o.name] || "—")}</td>
      <td>${tierLabel(o.tier)}</td><td>${esc(o.notes || "—")}</td></tr>`;
  }).join("");
  return `<table>
    <thead><tr><th>Opcode</th><th>Group</th><th>Tier</th><th>Note</th></tr></thead>
    <tbody>${rows || `<tr><td colspan="4">No matching opcodes</td></tr>`}</tbody>
  </table>`;
}

function obligationTable(rows) {
  const body = rows.map((o) => {
    const tone = o.status === "done" ? "success" : o.status === "blocked" ? "warning" : "";
    const blockers = (o.blockedBy || []).map((b) => b.label).join(" · ") || "Complete — no open blockers";
    return `<tr class="${tone}"><td>${o.id}</td><td>${esc(o.name)}</td><td>${o.status}</td><td>${esc(blockers)}</td></tr>`;
  }).join("");
  return `<table>
    <thead><tr><th>#</th><th>Obligation</th><th>Status</th><th>Blocker summary</th></tr></thead>
    <tbody>${body || `<tr><td colspan="4">No matching obligations</td></tr>`}</tbody>
  </table>`;
}

function obligationDetail(o) {
  const blockers = o.blockedBy || [];
  const cards = blockers.length === 0
    ? `<p class="small muted">Closure condition met — no remaining blockers.</p>`
    : `<div class="stack stack-8">
        <h3>What’s blocking this? (${blockers.length})</h3>
        <div class="blocker-grid">${blockers.map((b) => `
          <div class="blocker" style="border-left-color:${b.kind === "opcode" ? "var(--orange)" : "var(--yellow)"}">
            <p class="small semibold">${esc(b.label)}</p>
            <p class="faint">${b.kind}</p>
          </div>`).join("")}
        </div>
      </div>`;
  return `<div class="card"><div class="card-body stack stack-12">
    <div>
      <p class="semibold">#${o.id} ${esc(o.name)}</p>
      <p class="small muted">${esc(o.note || "")}</p>
      ${o.auditedAt ? `<p class="faint">Audited ${esc(o.auditedAt)}</p>` : ""}
      ${o.witness ? `<p class="faint">Witness: <code>${esc(o.witness)}</code></p>` : ""}
      <p class="faint"><a href="${githubBlob("EvmAsm/Progress/Obligations.lean")}">Obligations.lean on GitHub</a></p>
    </div>
    ${cards}
  </div></div>`;
}

function bind(root) {
  root.querySelectorAll("[data-opcode]").forEach((el) => {
    el.addEventListener("click", () => {
      const name = el.getAttribute("data-opcode");
      state.selectedOpcode = state.selectedOpcode === name ? null : name;
      state.selectedObligation = null;
      if (state.selectedOpcode) state.filter = "gaps";
      render();
    });
  });
  root.querySelectorAll("[data-obligation]").forEach((el) => {
    el.addEventListener("click", () => {
      const id = Number(el.getAttribute("data-obligation"));
      state.selectedObligation = state.selectedObligation === id ? null : id;
      state.selectedOpcode = null;
      if (state.selectedObligation != null) state.filter = "obligations";
      render();
    });
  });
  root.querySelectorAll("[data-filter]").forEach((el) => {
    el.addEventListener("click", () => {
      state.filter = el.getAttribute("data-filter");
      state.selectedOpcode = null;
      state.selectedObligation = null;
      render();
    });
  });
  root.querySelectorAll("[data-clear]").forEach((el) => {
    el.addEventListener("click", () => {
      state.selectedOpcode = null;
      state.selectedObligation = null;
      render();
    });
  });
}

function showError(msg) {
  document.getElementById("app").innerHTML = `
    <div class="stack stack-12">
      <h1>evm-asm progress cockpit</h1>
      <div class="callout warning">
        <div class="callout-title">Snapshot not available</div>
        <p class="small">${esc(msg)}</p>
        <p class="small">Generate it locally with <code>scripts/progress-cockpit.sh --write</code>,
        then serve from <code>docs/</code> (<code>python3 -m http.server</code>).
        On GitHub Pages the snapshot is published by CI on every push to <code>main</code>.</p>
      </div>
    </div>
  `;
}

fetch("cockpit/snapshot.json")
  .then((res) => {
    if (!res.ok) throw new Error(`snapshot.json HTTP ${res.status}`);
    return res.json();
  })
  .then((data) => {
    state.data = data;
    render();
  })
  .catch((err) => showError(err.message || String(err)));
