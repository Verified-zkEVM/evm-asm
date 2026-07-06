#!/usr/bin/env python3
"""Exhaustive control-flow census of the emitted guest asm corpus
(EvmAsm/Codegen/Programs/*.lean `*Function : String` defs).

Classifies every local (.L) loop back-edge as while (top-test) / doWhile
(bottom-test) / whileBreak (mid-break) / while_rotated (no byte-match) and
reports straight-line vs looping vs nested vs indirect. Run from repo root:
    python3 scripts/shape-census.py
Backs docs/agents/4ch8f-shape-survey.md (bead evm-asm-4ch8f.70). The bead
.70.1 lint reuses parse()/classify() to reject non-canonical loop lowering.
"""
import os, re, glob, sys, json
from collections import defaultdict, Counter

PROG = "EvmAsm/Codegen/Programs"

# conditional branch mnemonics
BR = {"beq","bne","bltu","bgeu","bgtu","bleu","bltz","bgez","bge","bgt","blt","ble",
      "bnez","beqz","bgez","blez","bgtz","bltz"}
UNCOND = {"j"}
CALLISH = {"jal","call","tail"}
INDIRECT = {"jr","jalr"}

def extract_functions(path):
    """Return list of (name, [asm_lines]) for each `def XxxFunction : String :=` block."""
    src = open(path).read()
    out = []
    # find def NAMEFunction : String :=
    for m in re.finditer(r'def\s+([A-Za-z0-9_]*Function)\s*:\s*String\s*:=', src):
        name = m.group(1)
        start = m.end()
        # grab until next top-level `def ` / `theorem`/`end namespace` etc; use next `\ndef ` or `\n#` or `\ntheorem`
        rest = src[start:]
        nxt = re.search(r'\n(def |theorem |lemma |#guard|#eval|namespace |end )', rest)
        block = rest[:nxt.start()] if nxt else rest
        # collect all string-literal contents
        lits = re.findall(r'"((?:[^"\\]|\\.)*)"', block)
        content = "".join(lits)
        # unescape \n
        content = content.replace("\\n", "\n").replace('\\"', '"').replace("\\t","\t")
        lines = [l.strip() for l in content.split("\n")]
        lines = [l for l in lines if l]
        out.append((name, lines))
    return out

def parse(lines):
    """Return (labels: name->index, insns, idx_labels: idx->[labels])."""
    labels = {}
    idx_labels = defaultdict(list)
    seq = []
    cleaned = []
    for l in lines:
        # strip line comments first (-- or #), but NOT ; (that's an insn separator)
        c = re.split(r'--|#', l, 1)[0].strip()
        if not c: continue
        # split packed instructions on ';'
        for sub in c.split(";"):
            sub = sub.strip()
            if sub:
                cleaned.append(sub)
    idx = 0
    for c in cleaned:
        if c.endswith(":") and " " not in c.rstrip(":").strip():
            lbl = c[:-1].strip()
            labels[lbl] = idx
            idx_labels[idx].append(lbl)
            continue
        parts = c.split(None,1)
        mnem = parts[0]
        args = parts[1] if len(parts)>1 else ""
        seq.append((idx, mnem, args))
        idx += 1
    return labels, seq, idx_labels

def target_label(args):
    # last comma-separated token that looks like a label
    toks = [t.strip() for t in args.split(",")]
    if not toks: return None
    last = toks[-1]
    if re.match(r'^\.?[A-Za-z_]\w*$', last):
        return last
    return None

def classify(name, lines):
    labels, seq, idx_labels = parse(lines)
    ninsn = len(seq)
    backedges = []   # (from_idx, to_idx, mnem, cond)
    forward_br = 0
    has_indirect = False
    calls = 0
    for (idx,mnem,args) in seq:
        base = mnem.lower()
        if base in INDIRECT:
            has_indirect = True
            continue
        if base in CALLISH:
            # jal to a .L label is actually a local jump/call; treat jal x0 style?
            tl = target_label(args)
            # jal with a local .L target and no return usage -> could be jump; count as call otherwise
            if tl and tl in labels and tl.startswith(".") and labels[tl] <= idx and base=="jal":
                backedges.append((idx, labels[tl], mnem, False))
            else:
                calls += 1
            continue
        if base in UNCOND or base in BR:
            tl = target_label(args)
            if tl is None:
                continue
            # only local (.L) labels are loop/branch targets; non-dotted = named
            # routine entry (tail-call / cross-routine jump), not a loop back-edge
            if tl in labels and not tl.startswith("."):
                if base in UNCOND:
                    calls += 1
                continue
            if tl in labels:
                tgt = labels[tl]
                if tgt <= idx:
                    backedges.append((idx, tgt, mnem, base in BR))
                else:
                    forward_br += 1
            else:
                # external label (call-like j to routine)
                if base in UNCOND:
                    calls += 1
    nloops = len(backedges)
    # loop shape heuristics per backedge
    shapes = []
    for (frm,to,mnem,cond) in backedges:
        # header at `to`. Is there an exit conditional branch near the top (to..to+2)?
        top_test = False
        for j in range(to, min(to+3, frm)):
            _,m2,a2 = seq[j]
            if m2.lower() in BR:
                tl = target_label(a2)
                if tl and tl in labels and labels[tl] > frm:  # exits past the back-edge
                    top_test = True
                    break
        if cond:
            # conditional back-edge to `to`. Could be a true bottom-test do-while,
            # OR a GCC "rotated while": entry jumps forward to the test that sits
            # just above this back-edge, so the body may run 0 times.
            # The test label = label(s) at the back-edge instruction `frm`.
            test_labels = idx_labels.get(frm, [])
            rotated = False
            for j in range(0, to):
                _, m2, a2 = seq[j]
                if m2.lower() in UNCOND:
                    tl = target_label(a2)
                    if tl in test_labels:
                        rotated = True
                        break
            shapes.append("while_rotated" if rotated else "doWhile")
        elif top_test:
            shapes.append("while_top")
        else:
            # unconditional back-edge, no obvious top test -> maybe mid-break or infinite w/ inner ret
            # look for a branch anywhere in body that exits
            mid_exit=False
            for j in range(to, frm):
                _,m2,a2 = seq[j]
                if m2.lower() in BR:
                    tl=target_label(a2)
                    if tl and tl in labels and labels[tl] > frm:
                        mid_exit=True; break
                if m2.lower()=="ret":
                    mid_exit=True; break
            shapes.append("whileBreak" if mid_exit else "infinite")
    return {
        "name": name, "ninsn": ninsn, "nloops": nloops,
        "shapes": shapes, "indirect": has_indirect,
        "calls": calls, "forward_br": forward_br,
        "nested": nloops>=2,
    }

results = []
for path in sorted(glob.glob(f"{PROG}/*.lean")):
    for (name, lines) in extract_functions(path):
        r = classify(name, lines)
        r["file"] = os.path.basename(path)
        results.append(r)

# Aggregate
total = len(results)
straight = [r for r in results if r["nloops"]==0 and not r["indirect"]]
straight_flat = [r for r in straight if r["forward_br"]==0]
straight_br = [r for r in straight if r["forward_br"]>0]
looped = [r for r in results if r["nloops"]>=1]
indirect = [r for r in results if r["indirect"]]
nested = [r for r in results if r["nested"]]

shape_counter = Counter()
for r in looped:
    # dominant shape
    for s in r["shapes"]:
        shape_counter[s]+=1

print(f"TOTAL Function defs analyzed: {total}")
print(f"  straight-line (no loop, no indirect): {len(straight)}")
print(f"      - pure straight/branch-cascade, forward branches>0: {len(straight_br)}")
print(f"      - no branches at all (flat block): {len(straight_flat)}")
print(f"  with >=1 loop back-edge: {len(looped)}")
print(f"  nested (>=2 back-edges): {len(nested)}")
print(f"  indirect jump (jr/jalr): {len(indirect)}")
print()
print("Loop back-edge shape tally (per back-edge, loops only):")
for s,c in shape_counter.most_common():
    print(f"    {s}: {c}")
print()
# routines by number of loops
loopdist = Counter(r["nloops"] for r in results)
print("Distribution by #back-edges:", dict(sorted(loopdist.items())))
print()
print("Indirect routines:", [(r["name"],r["file"]) for r in indirect])
print()
print("Nested (>=2 loops) routines (sample up to 40):")
for r in nested[:40]:
    print(f"    {r['file']}::{r['name']} loops={r['nloops']} shapes={r['shapes']}")

# dump full json
import os as _os
if _os.environ.get("SHAPE_JSON"):
    json.dump(results, open(_os.environ["SHAPE_JSON"],"w"))

