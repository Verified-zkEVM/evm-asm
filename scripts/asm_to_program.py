#!/usr/bin/env python3
"""asm_to_program.py -- mechanical GNU-as text -> EvmAsm.Rv64 `Program` converter.

Bead evm-asm-4ch8f.9.  Converts a hand-written `*Function : String` asm def
under `EvmAsm/Codegen/Programs/` into a `Program` value (list of `Instr`)
rendered back to the same string via `emitProgram`, plus the `rfl` drift-guard
theorem and `#guard` length pins -- the RlpWalk template
(`EvmAsm/Codegen/Programs/RlpWalk.lean:79-92`).

TRUST MODEL.  Parsing lives here, entirely OUTSIDE the Lean kernel.  The only
kernel-checked fact is the generated `rfl` theorem
`fooFunction = "label:\n" ++ emitProgram foo_prog`, which holds by construction
(the def *is* that render).  The guarantee that the *guest binary is unchanged*
is established OFFLINE by assembling the original hand-written text and the
`emitProgram foo_prog` render with `riscv64-unknown-elf-as` and byte-comparing
the `.text` sections (`--check` / the `assemble_cmp` gate).  A conversion is only
sound to land if that byte-compare passes.

The 4-byte-per-`Instr` model.  `Program` execution advances pc by 4 per `Instr`
and stores branch/jump targets as signed BYTE offsets.  For the model layout to
coincide with the assembled binary EVERY instruction must occupy exactly 4
bytes -- in particular every `li rd, C` must fit a single RV64 instruction
(C in [-2048, 2047]).  Functions with a wider `li` are reported
NEEDS-LI-EXPANSION and deferred (a later wave emits the explicit lui/addiw
expansion as separate `Instr`s).
"""
import argparse, os, re, subprocess, sys, tempfile, shutil

# --------------------------------------------------------------------------- #
# Register table (ABI + xNN names) -> Reg constructor suffix                  #
# --------------------------------------------------------------------------- #
_ABI = {
    'zero':0,'ra':1,'sp':2,'gp':3,'tp':4,'t0':5,'t1':6,'t2':7,'s0':8,'fp':8,
    's1':9,'a0':10,'a1':11,'a2':12,'a3':13,'a4':14,'a5':15,'a6':16,'a7':17,
    's2':18,'s3':19,'s4':20,'s5':21,'s6':22,'s7':23,'s8':24,'s9':25,'s10':26,
    's11':27,'t3':28,'t4':29,'t5':30,'t6':31,
}
def reg_num(tok):
    tok = tok.strip()
    if tok in _ABI: return _ABI[tok]
    m = re.fullmatch(r'x(\d+)', tok)
    if m and 0 <= int(m.group(1)) <= 31: return int(m.group(1))
    raise ValueError(f"unknown register {tok!r}")
def reg(tok): return f".x{reg_num(tok)}"

def parse_imm(tok):
    tok = tok.strip()
    neg = tok.startswith('-')
    body = tok[1:] if neg else tok
    if body.lower().startswith('0x'):
        v = int(body, 16)
    else:
        v = int(body, 10)
    return -v if neg else v

class ConvError(Exception): pass

# --------------------------------------------------------------------------- #
# Linker-facts symbol->address table (bead evm-asm-4ch8f.6 / wave .9.3)       #
#   Maps every guest symbol to its linked address so `la <symbol>` and         #
#   cross-function `jal <callee>` acquire concrete PC-relative immediates.      #
#   Mirrors EvmAsm/Codegen/AsmReloc.lean {laHi,laLo,jalOff} + GuestAddrs.lean.  #
# --------------------------------------------------------------------------- #
_SYMTSV = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       'asm-fixtures', 'symbol-addresses.tsv')
def _load_symmap():
    m = {}
    if not os.path.exists(_SYMTSV): return m
    for ln in open(_SYMTSV):
        if ln.startswith('#') or not ln.strip(): continue
        f = ln.rstrip('\n').split('\t')
        if len(f) < 3: continue
        unit, sym, addr = f[0], f[1], f[2]
        if unit != 'stateless_guest': continue   # the single fully-linked guest
        if sym.startswith('.'): continue          # section pseudo-symbols
        m[sym] = int(addr, 16)
    return m
SYMMAP = _load_symmap()
GA = 'GuestAddrs'   # Lean namespace for the generated address constants

# Python mirrors of AsmReloc.lean (kept identical; the byte-identity gate is the
# arbiter that both reproduce GNU-as's %pcrel_hi/%pcrel_lo/jal expansion).
def _la_delta(sym, pc):     return (sym - pc) & 0xffffffff      # two's-comp 32
def _la_hi(sym, pc):        return ((_la_delta(sym, pc) + 0x800) >> 12) & 0xfffff
def _la_lo(sym, pc):
    v = _la_delta(sym, pc) & 0xfff
    return v - 0x1000 if v >= 0x800 else v                      # sign-interpret
def _jal_off(target, pc):   return target - pc                  # signed byte off
def _br_off_asm(n):         return f".+{n}" if n >= 0 else f".{n}"
def xr(tok):                return f"x{reg_num(tok)}"

# --------------------------------------------------------------------------- #
# Lean-string extraction                                                      #
# --------------------------------------------------------------------------- #
def _decode(s):
    out=[];i=0
    while i<len(s):
        c=s[i]
        if c=='\\':
            n=s[i+1]; out.append({'n':'\n','t':'\t','\\':'\\','"':'"','r':'\r'}.get(n,n)); i+=2
        else: out.append(c);i+=1
    return ''.join(out)

def _strip_lean_line_comments(src):
    """Drop Lean `--` comments while leaving `--` in assembly strings intact."""
    out=[]; i=0; in_string=False
    while i<len(src):
        c=src[i]
        if in_string:
            out.append(c)
            if c=='\\' and i+1<len(src):
                out.append(src[i+1]); i+=2; continue
            if c=='"': in_string=False
            i+=1; continue
        if c=='"':
            in_string=True; out.append(c); i+=1; continue
        if src.startswith('--', i):
            i=src.find('\n', i)
            if i<0: break
            out.append('\n'); i+=1; continue
        out.append(c); i+=1
    return ''.join(out)

def extract_function(text, fname):
    """Return the decoded asm string of `def <fname> : String := "..." ++ ...`.
    Raises if the RHS is not a pure string-literal concatenation.  Callers
    converting generated String combinators should use `lean_string_render`
    as the fallback; keeping this parser literal-only preserves its fast,
    source-local behavior for the ordinary conversion path."""
    m = re.search(r'def\s+'+re.escape(fname)+r'\s*:\s*String\s*:=', text)
    if not m: raise ConvError(f"def {fname} not found")
    rest = text[m.end():]
    body_lines=[]
    for ln in rest.split('\n'):
        st=ln.strip()
        if st.startswith(('def ','theorem ','lemma ','#guard','#eval','end ',
                          'namespace ','/-!','/--','@[','private','example','set_option')):
            break
        body_lines.append(ln)
    body=_strip_lean_line_comments('\n'.join(body_lines))
    strs=re.findall(r'"((?:[^"\\]|\\.)*)"',body)
    stripped=re.sub(r'"(?:[^"\\]|\\.)*"','',body)
    if re.sub(r'[+\s]','',stripped):
        raise ConvError(f"{fname}: RHS is not a pure string literal (references idents)")
    return ''.join(_decode(s) for s in strs)

# --------------------------------------------------------------------------- #
# asm text -> instruction items                                               #
# --------------------------------------------------------------------------- #
# GNU-as numeric local labels (GH #12204 step 2). `137:` defines; `137f` and
# `137b` refer to the nearest definition forward / backward. Used by
# `stackUnderflowGuardAsm` / `stackOverflowGuardAsm` (`Dispatch.lean:180,197`),
# which is why no dispatcher handler was convertible.
#
# ⚠️ They are deliberately kept a SEPARATE item kind from ordinary labels, not
# folded into the same dict, because a numeric label may legally be defined
# many times in one function — `1:` repeated is the normal GNU-as idiom — and
# `name -> addr` would silently retain only the last definition and then
# resolve every `1f`/`1b` against it.
_NUMLABEL_DEF_RE = re.compile(r'^(\d+):\s*(.*)$')
_NUMLABEL_REF_RE = re.compile(r'^(\d+)([fb])$')


def tokenize(asm):
    """Yield ('label', name), ('numlabel', digits) and ('insn', mnemonic, [ops])."""
    items=[]
    for line in asm.split('\n'):
        line=line.split('#',1)[0]
        if not line.strip(): continue
        for piece in line.split(';'):
            piece=piece.strip()
            if not piece: continue
            m=re.match(r'^([.A-Za-z_][.A-Za-z0-9_$]*):\s*(.*)$',piece)
            if not m:
                mnum=_NUMLABEL_DEF_RE.match(piece)
                if mnum:
                    items.append(('numlabel', mnum.group(1)))
                    if not mnum.group(2).strip(): continue
                    piece=mnum.group(2).strip()
            if m:
                items.append(('label', m.group(1)))
                if not m.group(2).strip(): continue
                piece=m.group(2).strip()
            mn=piece.split(None,1)[0]
            rest=piece[len(mn):].strip()
            ops=[o.strip() for o in rest.split(',')] if rest else []
            items.append(('insn', mn, ops))
    return items

def layout_items(items):
    """Assign a byte address to every tokenized item.

    Returns ``(label_addr, num_addr, seq, end_addr)`` where ``seq`` is
    ``[(addr, mnemonic, ops)]`` and ``num_addr`` maps each numeric local label
    to the list of EVERY address it is defined at (see `_NUMLABEL_DEF_RE`).

    Shared by the three sites that lay out an asm body — the converter proper
    and the two ratchet geometry scanners — so a numeric label cannot be
    understood by one and invisible to another.
    """
    label_addr = {}
    num_addr = {}
    seq = []
    addr = 0
    for it in items:
        if it[0] == 'label':
            label_addr[it[1]] = addr
        elif it[0] == 'numlabel':
            num_addr.setdefault(it[1], []).append(addr)
        else:
            _, mn, ops = it
            seq.append((addr, mn, ops))
            addr += insn_size(mn, ops)
    return label_addr, num_addr, seq, addr


def numlabel_off(num_addr, tok, cur):
    """Resolve a GNU-as ``Nf``/``Nb`` reference to a byte offset from ``cur``.

    Returns ``None`` when ``tok`` is not a numeric-local reference, so callers
    can fall through to their ordinary label lookup.

    ``Nf`` binds to the nearest definition STRICTLY after ``cur``; ``Nb`` to
    the nearest at or before it. The `at or before` is deliberate: a label
    sitting immediately ahead of the referring instruction shares its address
    and is a legal backward target (offset 0).
    """
    m = _NUMLABEL_REF_RE.fullmatch(tok)
    if not m:
        return None
    n, direction = m.group(1), m.group(2)
    defs = num_addr.get(n)
    if not defs:
        raise ConvError(f"numeric local label {tok!r}: no {n}: definition in this function")
    if direction == 'f':
        after = [a for a in defs if a > cur]
        if not after:
            raise ConvError(f"numeric local label {tok!r}: no {n}: definition after pc={cur}")
        return min(after) - cur
    before = [a for a in defs if a <= cur]
    if not before:
        raise ConvError(f"numeric local label {tok!r}: no {n}: definition at or before pc={cur}")
    return max(before) - cur


# memory operand `off(base)` -> (off, base)
def mem(op):
    m=re.fullmatch(r'\s*(-?\w+|-?0x[0-9a-fA-F]+)?\s*\(\s*(\w+)\s*\)\s*', op)
    if not m: raise ConvError(f"bad mem operand {op!r}")
    off = parse_imm(m.group(1)) if m.group(1) else 0
    return off, m.group(2)

def fits(v, bits):  # signed fit
    lo, hi = -(1<<(bits-1)), (1<<(bits-1))-1
    return lo <= v <= hi

# --------------------------------------------------------------------------- #
# li-expansion: mirror the EXACT `li rd, C` machine sequence GNU-as emits      #
#   (bead evm-asm-4ch8f.9.2). A `li` with C outside signed-12 range assembles  #
#   to 1-6 real instructions (lui/addiw/slli/addi); a faithful 4-byte-per-     #
#   Instr Program must carry that exact sequence. Rather than reimplement the  #
#   assembler's constant-materialization algorithm, we assemble the real `li`  #
#   pseudo and DECODE the emitted words back to (mn, ops) source tuples — the  #
#   ONLY opcodes `li` ever expands to are LUI/ADDIW/ADDI/SLLI. The whole-guest #
#   byte-identity gate is the arbiter that this sequence reassembles to the    #
#   same bytes as the original `li` (it must, since it was decoded from it).   #
# --------------------------------------------------------------------------- #
_LI_EXPAND_CACHE = {}
def _li_expand(rd_tok, imm_tok):
    """Return the exact GAS `li rd, C` expansion as a list of (mn, ops) source
    tuples, obtained by assembling the real `li` pseudo and decoding the raw
    machine words (offline, outside the TCB; validated by assemble+cmp)."""
    key = (reg_num(rd_tok), parse_imm(imm_tok))
    if key in _LI_EXPAND_CACHE: return _LI_EXPAND_CACHE[key]
    with tempfile.TemporaryDirectory() as d:
        s=os.path.join(d,'li.s'); o=os.path.join(d,'li.o'); b=os.path.join(d,'li.bin')
        with open(s,'w') as f:
            f.write(f".text\n.globl _f\n_f:\n  li {xr(rd_tok)}, {imm_tok}\n")
        subprocess.run([AS,'-march=rv64im','-mno-relax','-o',o,s],check=True,
                       stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        subprocess.run([OBJCOPY,'-O','binary','-j','.text',o,b],check=True,
                       stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        words=open(b,'rb').read()
    out=[]
    for i in range(0,len(words),4):
        w=int.from_bytes(words[i:i+4],'little')
        opc=w&0x7f; rd=(w>>7)&0x1f; f3=(w>>12)&7; rs1=(w>>15)&0x1f
        def simm12(x): return x-0x1000 if x>=0x800 else x
        if opc==0x37:                       # LUI rd, imm20
            out.append(('lui',  [f"x{rd}", f"0x{(w>>12)&0xfffff:x}"]))
        elif opc==0x1b and f3==0:           # ADDIW rd, rs1, simm12
            out.append(('addiw',[f"x{rd}", f"x{rs1}", str(simm12((w>>20)&0xfff))]))
        elif opc==0x13 and f3==0:           # ADDI rd, rs1, simm12
            out.append(('addi', [f"x{rd}", f"x{rs1}", str(simm12((w>>20)&0xfff))]))
        elif opc==0x13 and f3==1:           # SLLI rd, rs1, shamt6
            out.append(('slli', [f"x{rd}", f"x{rs1}", str((w>>20)&0x3f)]))
        else:
            raise ConvError(f"li {imm_tok}: unexpected expansion word 0x{w:08x} "
                            f"(NEEDS-LI-EXPANSION)")
    _LI_EXPAND_CACHE[key]=out
    return out

# --------------------------------------------------------------------------- #
# instruction byte size in the 4-byte model (all must be 4; li may not be)    #
# --------------------------------------------------------------------------- #
def insn_size(mn, ops):
    if mn == 'li':
        v = parse_imm(ops[1])
        if not fits(v, 12):
            # Explicit multi-instruction expansion (bead evm-asm-4ch8f.9.2): the
            # real GAS `li` sequence, each word a separate 4-byte `Instr`.
            return 4 * len(_li_expand(ops[0], ops[1]))
    if mn in ('call','tail'):
        # `call`/`tail` expand to auipc+jalr (8 bytes) with a linker-relaxable
        # relocation; not handled by the la/jal-offset story of this wave.
        raise ConvError(f"{mn}: cross-function call macro (NEEDS-CALL-EXPANSION)")
    if mn == '.4byte':
        # Raw pre-encoded word (the ZisK accelerator `.CSRS`/`csrrs` pattern that
        # `emitInstr` renders as `.4byte N`). Decoded back to `.CSRS` in
        # `render_insn`; one 4-byte instruction. A `.4byte` that is NOT a `csrrs`
        # accelerator word is refused there (NEEDS-DOTWORD; bead .9.3.3).
        return 4
    if mn == 'la':
        # `la reg, symbol` -> auipc reg,%pcrel_hi + addi reg,reg,%pcrel_lo = 8 B.
        return 8
    return 4

# --------------------------------------------------------------------------- #
# instruction -> Instr constructor render (mirrors nothing; produces Lean)    #
#   `off_of` resolves a branch/jal label/PC-rel operand to a signed byte off  #
# --------------------------------------------------------------------------- #
def bv(v, bits): return f"({v} : BitVec {bits})"

# Same-function B-type immediates with |off| ≥ this many bytes are emitted as
# `brOff (entry + tgt) (entry + pc)` rather than a bare `(N : BitVec 13)`.
# Threshold matches the #11510 mid-epilogue class (fail arms that skip `ld ra`):
# short forward skips stay numeric; long fail/epilogue arms name their target
# so a body edit that shifts the restore sequence cannot silently retarget
# (#11512).  `brOff` reduces to the same BitVec under the kernel, so emission
# stays byte-identical when the geometry was already correct.
BR_NAMED_THRESHOLD = 64

# Same-function J-type immediates use the same policy threshold as B-type
# immediates.  JAL has a wider encoding range, but long local loop/epilogue
# transfers still need a symbolic target so body edits cannot silently move
# their destination (#11512).  Short jumps remain numeric for readable output.
# Keep this as a reference, not a second literal: the two relocation policies
# must not drift unless a future change has a separately justified threshold.
JAL_NAMED_THRESHOLD = BR_NAMED_THRESHOLD

# Site-level ratchet for the local-J migration.  This is the sole blocking
# counter: every intentional conversion or counting change must update the
# committed value in the same commit, so decreases cannot pass silently.
EXPECTED_BARE_J_SITES = 162

# Site-level ratchet for the local-B geometry guard.  The predicate is every
# manifest fixture local conditional branch with abs(target_pc - branch_pc) >=
# BR_NAMED_THRESHOLD, paired in layout order with its checked-in Program
# constructor.  This is the number of those sites still represented by a bare
# BitVec-13 literal.  It is a debt figure, not a target: a source change may
# only decrease it, and the corresponding constant update belongs in that same
# change.
EXPECTED_BARE_B_SITES = 761

def br_imm(off, entry, cur):
    """Render a B-type byte offset; long arms use named `brOff` (#11512)."""
    if abs(off) >= BR_NAMED_THRESHOLD:
        tgt = cur + off
        return f"(brOff {pc_expr(entry, tgt)} {pc_expr(entry, cur)})"
    return bv(off, 13)

def jal_imm(off, entry, cur):
    """Render a same-function J-type byte offset; long arms use `jalOff`."""
    if abs(off) >= JAL_NAMED_THRESHOLD:
        tgt = cur + off
        return f"(jalOff {pc_expr(entry, tgt)} {pc_expr(entry, cur)})"
    return bv(off, 21)

def pc_expr(entry, offset):
    """Render a program-counter expression for a function entry.

    Linked guest entries use the generated GuestAddrs symbol. Probe-only
    entries deliberately use the stable ``0x80000000`` placeholder because
    they are not present in the monolithic guest link.
    """
    if entry in SYMMAP:
        return f"({GA}.{entry} + {offset})"
    return str(0x80000000 + offset)

def render_insn(mn, ops, off_of):
    R = reg
    def imm12(o):
        v=parse_imm(o)
        if not fits(v,12): raise ConvError(f"{mn}: imm {o} out of BitVec 12")
        return bv(v,12)
    def r3(c): return f".{c} {R(ops[0])} {R(ops[1])} {R(ops[2])}"
    def ri(c): return f".{c} {R(ops[0])} {R(ops[1])} {imm12(ops[2])}"
    # RV64I R-type
    RTYPE={'add':'ADD','sub':'SUB','sll':'SLL','srl':'SRL','sra':'SRA','and':'AND',
           'or':'OR','xor':'XOR','slt':'SLT','sltu':'SLTU','mul':'MUL','mulh':'MULH',
           'mulhsu':'MULHSU','mulhu':'MULHU','div':'DIV','divu':'DIVU','rem':'REM','remu':'REMU'}
    ITYPE={'addi':'ADDI','andi':'ANDI','ori':'ORI','xori':'XORI','slti':'SLTI',
           'sltiu':'SLTIU','addiw':'ADDIW'}
    SHAMT={'slli':'SLLI','srli':'SRLI','srai':'SRAI'}
    LOAD={'ld':'LD','lw':'LW','lwu':'LWU','lb':'LB','lh':'LH','lbu':'LBU','lhu':'LHU'}
    STORE={'sd':'SD','sw':'SW','sb':'SB','sh':'SH'}
    BRANCH={'beq':'BEQ','bne':'BNE','blt':'BLT','bge':'BGE','bltu':'BLTU','bgeu':'BGEU'}
    if mn in RTYPE: return r3(RTYPE[mn])
    if mn in ITYPE: return ri(ITYPE[mn])
    if mn in SHAMT:
        v=parse_imm(ops[2])
        if not (0<=v<64): raise ConvError(f"{mn}: shamt {v} out of range")
        return f".{SHAMT[mn]} {R(ops[0])} {R(ops[1])} {bv(v,6)}"
    if mn=='lui' or mn=='auipc':
        v=parse_imm(ops[1])
        return f".{'LUI' if mn=='lui' else 'AUIPC'} {R(ops[0])} {bv(v,20)}"
    if mn in LOAD:
        off,base=mem(ops[1]); return f".{LOAD[mn]} {R(ops[0])} {R(base)} {bv(off,12)}"
    if mn in STORE:
        off,base=mem(ops[1]); return f".{STORE[mn]} {R(base)} {R(ops[0])} {bv(off,12)}"
    if mn in BRANCH:
        return f".{BRANCH[mn]} {R(ops[0])} {R(ops[1])} {bv(off_of(ops[2]),13)}"
    if mn=='jal':
        if len(ops)==1: rd,tgt='ra',ops[0]
        else: rd,tgt=ops[0],ops[1]
        return f".JAL {R(rd)} {bv(off_of(tgt),21)}"
    if mn=='jalr':
        if len(ops)==2: off,base=mem(ops[1]); return f".JALR {R(ops[0])} {R(base)} {bv(off,12)}"
        # jalr rd, rs, imm
        return f".JALR {R(ops[0])} {R(ops[1])} {bv(parse_imm(ops[2]),12)}"
    if mn=='.4byte':
        # Raw pre-encoded word -> `.CSRS csr rs1` (the ZisK accelerator `csrrs
        # x0, csr, rs1` pattern `emitInstr` renders back as `.4byte`). Encoding:
        # (csr << 20) | (rs1 << 15) | 0x2073 (funct3=csrrs, rd=x0, opcode=SYSTEM).
        # Any word NOT matching that fixed pattern is not an accelerator call and
        # is refused (bead evm-asm-4ch8f.9.3.3).
        n=parse_imm(ops[0])
        if n < 0 or n >= (1<<32) or (n & 0x7fff) != 0x2073:
            raise ConvError(f".4byte 0x{n & 0xffffffff:08x}: not a csrrs/CSRS "
                            f"accelerator word (NEEDS-DOTWORD)")
        csr=(n>>20)&0xfff; rs1=(n>>15)&0x1f
        return f".CSRS ({csr} : BitVec 12) .x{rs1}"
    if mn=='mv': return f".MV {R(ops[0])} {R(ops[1])}"
    if mn=='li': return f".LI {R(ops[0])} ({parse_imm(ops[1])} : Word)"
    if mn=='nop': return ".NOP"
    if mn=='ecall': return ".ECALL"
    if mn=='fence': return ".FENCE"
    if mn=='ebreak': return ".EBREAK"
    if mn=='ret': return f".JALR .x0 .x1 {bv(0,12)}"
    if mn=='jr':  return f".JALR .x0 {R(ops[0])} {bv(0,12)}"
    if mn=='j':   return f".JAL .x0 {bv(off_of(ops[0]),21)}"
    # branch pseudos
    if mn=='beqz': return f".BEQ {R(ops[0])} .x0 {bv(off_of(ops[1]),13)}"
    if mn=='bnez': return f".BNE {R(ops[0])} .x0 {bv(off_of(ops[1]),13)}"
    if mn=='bltz': return f".BLT {R(ops[0])} .x0 {bv(off_of(ops[1]),13)}"
    if mn=='bgez': return f".BGE {R(ops[0])} .x0 {bv(off_of(ops[1]),13)}"
    if mn=='bgtz': return f".BLT .x0 {R(ops[0])} {bv(off_of(ops[1]),13)}"
    if mn=='blez': return f".BGE .x0 {R(ops[0])} {bv(off_of(ops[1]),13)}"
    if mn=='bgt':  return f".BLT {R(ops[1])} {R(ops[0])} {bv(off_of(ops[2]),13)}"
    if mn=='ble':  return f".BGE {R(ops[1])} {R(ops[0])} {bv(off_of(ops[2]),13)}"
    if mn=='bgtu': return f".BLTU {R(ops[1])} {R(ops[0])} {bv(off_of(ops[2]),13)}"
    if mn=='bleu': return f".BGEU {R(ops[1])} {R(ops[0])} {bv(off_of(ops[2]),13)}"
    if mn=='seqz': return f".SLTIU {R(ops[0])} {R(ops[1])} {bv(1,12)}"
    if mn=='snez': return f".SLTU {R(ops[0])} .x0 {R(ops[1])}"
    if mn=='sltz': return f".SLT {R(ops[0])} {R(ops[1])} .x0"
    if mn=='sgtz': return f".SLT {R(ops[0])} .x0 {R(ops[1])}"
    if mn=='not': return f".XORI {R(ops[0])} {R(ops[1])} {bv(-1,12)}"
    if mn=='neg': return f".SUB {R(ops[0])} .x0 {R(ops[1])}"
    if mn=='sext.w': return f".ADDIW {R(ops[0])} {R(ops[1])} {bv(0,12)}"
    raise ConvError(f"unsupported mnemonic {mn!r}")

# --------------------------------------------------------------------------- #
# top-level: asm string -> (label, [Instr-render], count)                     #
# --------------------------------------------------------------------------- #
def _emit_one(mn, ops, off_of, entry, entry_addr, cur, label_addr, externals):
    """Resolve ONE source instruction into (lean_renders, asm_lines, reloc).

    Straight-line/local-control instructions delegate to `render_insn`
    (one `Instr` each, `reloc=None`).  The two link-layout-dependent forms:

      * `la reg, sym`            -> AUIPC+ADDI pair (2 `Instr`s, 8 bytes), with
        the concrete guest-linked immediates via `laHi`/`laLo GuestAddrs.sym
        (GuestAddrs.entry + cur)` (the VERIFICATION view), plus a reloc marker
        `('la', reg, sym)` so the emitted string keeps the SYMBOLIC `la reg,sym`
        (the image-agnostic EMISSION view — each image relocates it itself).
      * cross-function `jal`/`j`  -> single JAL with `jalOff GuestAddrs.callee …`
        + reloc marker `('jal', rd, callee)`.

    `asm_lines` are the CONCRETE guest-linked mnemonics used only by the
    per-function consistency gate (numeric render ≟ symbolic form linked at the
    guest addresses).  They are NOT what lands in any image."""
    if mn == 'la':
        rg = ops[0]; sym = ops[1].strip()
        if entry_addr is None:
            raise ConvError(f"la: entry {entry!r} address unknown (BLOCKED_ON_.6)")
        if sym not in SYMMAP:
            raise ConvError(f"la {sym}: symbol not in address table (BLOCKED_ON_.6)")
        externals[sym] = SYMMAP[sym]
        pc = entry_addr + cur
        pcx = pc_expr(entry, cur)
        lean = [f".AUIPC {reg(rg)} (laHi {GA}.{sym} {pcx})",
                f".ADDI {reg(rg)} {reg(rg)} (laLo {GA}.{sym} {pcx})"]
        hi, lo = _la_hi(SYMMAP[sym], pc), _la_lo(SYMMAP[sym], pc)
        asm = [f"auipc {xr(rg)}, 0x{hi:x}", f"addi {xr(rg)}, {xr(rg)}, {lo}"]
        return lean, asm, ('la', reg(rg), sym)
    if mn in ('jal', 'j'):
        if mn == 'j':                 rd, tgt = 'x0', ops[0]
        elif len(ops) == 1:           rd, tgt = 'ra', ops[0]
        else:                         rd, tgt = ops[0], ops[1]
        tgt = tgt.strip()
        # local (label or PC-relative) targets keep the ordinary single-JAL path;
        # long transfers use the same named-target policy as B-type branches.
        if tgt in label_addr or tgt.startswith('.'):
            off = off_of(tgt)
            lean = [f".JAL {reg(rd)} {jal_imm(off, entry, cur)}"]
            return lean, [py_emit_line(mn, ops, off_of)], None
        # cross-function symbol target -> resolved PC-relative offset
        if entry_addr is None:
            raise ConvError(f"{mn}: entry {entry!r} address unknown (BLOCKED_ON_.6)")
        if tgt not in SYMMAP:
            raise ConvError(f"unresolved branch/jump target {tgt!r}")
        externals[tgt] = SYMMAP[tgt]
        off = _jal_off(SYMMAP[tgt], entry_addr + cur)
        lean = [f".JAL {reg(rd)} (jalOff {GA}.{tgt} {pc_expr(entry, cur)})"]
        asm = [f"jal {xr(rd)}, {_br_off_asm(off)}"]
        return lean, asm, ('jal', reg(rd), tgt)
    if mn == 'li' and not fits(parse_imm(ops[1]), 12):
        # Explicit `li` expansion (bead evm-asm-4ch8f.9.2): emit the real
        # lui/addiw/slli/addi machine instructions as separate `Instr`s. The
        # constant is image-independent (no relocation), so no reloc marker.
        tuples = _li_expand(ops[0], ops[1])
        lean = [render_insn(m2, o2, off_of) for (m2, o2) in tuples]
        asm  = [py_emit_line(m2, o2, off_of) for (m2, o2) in tuples]
        return lean, asm, None
    # Same-function B-type: long arms use named `brOff` against the entry
    # symbol so epilogue drift fails the source/geometry gate rather than
    # silently landing mid-restore (#11510 / #11512).  Short arms stay bare
    # BitVec literals.  Emission is unchanged either way (`brOff` reduces).
    BRANCH_R = {'beq':'BEQ','bne':'BNE','blt':'BLT','bge':'BGE',
                'bltu':'BLTU','bgeu':'BGEU'}
    if mn in BRANCH_R:
        off = off_of(ops[2])
        lean = [f".{BRANCH_R[mn]} {reg(ops[0])} {reg(ops[1])} {br_imm(off, entry, cur)}"]
        return lean, [py_emit_line(mn, ops, off_of)], None
    BRANCH_Z = {
        'beqz': ('BEQ', lambda o: (reg(o[0]), '.x0', o[1])),
        'bnez': ('BNE', lambda o: (reg(o[0]), '.x0', o[1])),
        'bltz': ('BLT', lambda o: (reg(o[0]), '.x0', o[1])),
        'bgez': ('BGE', lambda o: (reg(o[0]), '.x0', o[1])),
        'bgtz': ('BLT', lambda o: ('.x0', reg(o[0]), o[1])),
        'blez': ('BGE', lambda o: ('.x0', reg(o[0]), o[1])),
    }
    if mn in BRANCH_Z:
        ctor, parts = BRANCH_Z[mn]
        rs1, rs2, tgt = parts(ops)
        off = off_of(tgt)
        lean = [f".{ctor} {rs1} {rs2} {br_imm(off, entry, cur)}"]
        return lean, [py_emit_line(mn, ops, off_of)], None
    BRANCH_SWAP = {
        'bgt':  ('BLT', 0, 1, 2),
        'ble':  ('BGE', 0, 1, 2),
        'bgtu': ('BLTU', 0, 1, 2),
        'bleu': ('BGEU', 0, 1, 2),
    }
    if mn in BRANCH_SWAP:
        ctor, a, b, t = BRANCH_SWAP[mn]
        # asm is `bgt rs1, rs2, tgt` → BLT rs2, rs1
        off = off_of(ops[t])
        lean = [f".{ctor} {reg(ops[b])} {reg(ops[a])} {br_imm(off, entry, cur)}"]
        return lean, [py_emit_line(mn, ops, off_of)], None
    return [render_insn(mn, ops, off_of)], [py_emit_line(mn, ops, off_of)], None

def _resolve(asm):
    """Tokenize + lay out `asm`, returning (entry, entry_addr, items, externals)
    where `items` is a list of (lean_renders, asm_lines) per source instruction.
    Shared by `convert` (Program) and `emit_program_text` (byte-identity)."""
    items = tokenize(asm)
    if not items or items[0][0] != 'label':
        raise ConvError("first line is not a label")
    entry = items[0][1]
    # A converted function keeps ONLY its entry label ("entry:\n" ++ emitProgram);
    # emitProgram strips every internal label, turning branches into PC-relative
    # offsets. That is safe for `.L`-local labels (never cross-function targets by
    # convention) but a secondary NON-`.L` label is a potential cross-function
    # entry point: external `jal`s in OTHER files resolve to it, and stripping it
    # silently breaks the guest link. Per-function byte-identity still passes (the
    # bundle is self-consistent in isolation), so ONLY the whole-guest byte-identity
    # gate catches it. Refuse such multi-entry bundles here so they are classified,
    # not mis-converted. (bead evm-asm-4ch8f.9.1 finding: receiptRecordsFunction /
    # storageEffectRecordsFunction expose *_clear/_append/_record_nth entries.)
    # GNU-as numeric locals (`137:`) are exempt by construction: they are a
    # separate item kind, and unlike a bare `foo:` they can never be a
    # cross-function entry point — the assembler does not emit them to the
    # symbol table at all, so nothing outside the function can resolve to one.
    # Stripping them is therefore as safe as stripping a `.L` label.
    for it in items[1:]:
        if it[0] == 'label' and not it[1].startswith('.L'):
            raise ConvError(f"secondary non-.L label {it[1]!r}: multi-entry bundle, "
                            f"cross-function entry point stripped by emitProgram "
                            f"(MULTI-ENTRY-BUNDLE)")
    # Linked guest entry uses the real TSV address.  Probe-only conversions
    # (entry absent from the guest image / TSV) still need a stable PC base so
    # cross-function `jal`/`la` can resolve; match the Lean-side placeholder
    # convention (balCanonicalSortSelftestPc := 0x80000000).  GuestAddrs
    # generation already skips these entries (_collect_guest_addr_syms).
    entry_addr = SYMMAP.get(entry, 0x80000000)
    # assign byte address to each insn; record label -> address
    label_addr, num_addr, seq, _end_addr = layout_items(items)
    externals = {}
    out = []          # list of (lean_renders, asm_lines) per source instruction
    relocs = []       # [(flat_prog_index, kind, reg_lean, symbol)]
    flat = 0          # running index into the flattened Program
    for cur, mn, ops in seq:
        def off_of(tok, cur=cur):
            tok=tok.strip()
            # PC-relative .+N / .-N (relative to current insn address `cur`)
            if tok.startswith('.+'): return int(tok[2:])
            if tok.startswith('.-'): return -int(tok[2:])
            if tok=='.': return 0
            if tok in label_addr:
                return label_addr[tok] - cur
            noff = numlabel_off(num_addr, tok, cur)
            if noff is not None:
                return noff
            raise ConvError(f"unresolved branch/jump target {tok!r}")
        lean, asm, reloc = _emit_one(mn, ops, off_of, entry, entry_addr, cur, label_addr, externals)
        if reloc is not None:
            relocs.append((flat, reloc[0], reloc[1], reloc[2]))
        out.append((lean, asm))
        flat += len(lean)
    return entry, entry_addr, out, externals, relocs

def convert(asm):
    entry, _entry_addr, out, _ext, _rel = _resolve(asm)
    renders = [r for (lean, _asm) in out for r in lean]
    return entry, renders

# --------------------------------------------------------------------------- #
# py_emit: mirror of EvmAsm.Codegen.emitInstr (offline .text cross-check)     #
# --------------------------------------------------------------------------- #
def _xr(n): return f"x{n}"
def py_emit_line(mn, ops, off_of):
    """Render the canonical GNU-as line the way Lean's emitInstr would, given
    the SAME parsed instruction. Used only to build the .s for assemble_cmp."""
    r = render_insn(mn, ops, off_of)  # reuse the Instr render, then translate
    return _render_to_asm(r)

# Instr-render string -> emitInstr GNU-as line
def _render_to_asm(r):
    toks = r.split()
    c = toks[0][1:]  # strip leading '.'
    def reg_s(t): return t[1:] if t.startswith('.x') else t  # .x5 -> x5
    def intval(rest):
        # rest like "(N : BitVec k)" or "(N : Word)"
        m=re.match(r'\((-?\d+)\s*:', rest); return int(m.group(1))
    # rejoin remainder
    rest = r[len(toks[0]):].strip()
    def args_regs(n):
        return [reg_s(t) for t in toks[1:1+n]]
    simpleR={'ADD':'add','SUB':'sub','SLL':'sll','SRL':'srl','SRA':'sra','AND':'and',
             'OR':'or','XOR':'xor','SLT':'slt','SLTU':'sltu','MUL':'mul','MULH':'mulh',
             'MULHSU':'mulhsu','MULHU':'mulhu','DIV':'div','DIVU':'divu','REM':'rem','REMU':'remu'}
    if c in simpleR:
        a=args_regs(3); return f"{simpleR[c]} {a[0]}, {a[1]}, {a[2]}"
    immI={'ADDI':'addi','ANDI':'andi','ORI':'ori','XORI':'xori','SLTI':'slti',
          'SLTIU':'sltiu','ADDIW':'addiw'}
    if c in immI:
        a=args_regs(2); v=intval(rest[rest.index('('):]); return f"{immI[c]} {a[0]}, {a[1]}, {v}"
    shI={'SLLI':'slli','SRLI':'srli','SRAI':'srai'}
    if c in shI:
        a=args_regs(2); v=intval(rest[rest.index('('):]); return f"{shI[c]} {a[0]}, {a[1]}, {v}"
    if c in ('LUI','AUIPC'):
        a=args_regs(1); v=intval(rest[rest.index('('):]); return f"{c.lower()} {a[0]}, 0x{v:x}"
    loadC={'LD':'ld','LW':'lw','LWU':'lwu','LB':'lb','LH':'lh','LBU':'lbu','LHU':'lhu'}
    if c in loadC:
        a=args_regs(2); v=intval(rest[rest.rindex('('):]); return f"{loadC[c]} {a[0]}, {v}({a[1]})"
    storeC={'SD':'sd','SW':'sw','SB':'sb','SH':'sh'}
    if c in storeC:
        # constructor: .SD base src off  -> "sd src, off(base)"
        a=args_regs(2); v=intval(rest[rest.rindex('('):]); return f"{storeC[c]} {a[1]}, {v}({a[0]})"
    branchC={'BEQ':'beq','BNE':'bne','BLT':'blt','BGE':'bge','BLTU':'bltu','BGEU':'bgeu'}
    if c in branchC:
        a=args_regs(2); v=intval(rest[rest.rindex('('):])
        off = f".+{v}" if v>=0 else f".{v}"
        return f"{branchC[c]} {a[0]}, {a[1]}, {off}"
    if c=='JAL':
        a=args_regs(1); v=intval(rest[rest.rindex('('):])
        off = f".+{v}" if v>=0 else f".{v}"
        return f"jal {a[0]}, {off}"
    if c=='JALR':
        a=args_regs(2); v=intval(rest[rest.rindex('('):]); return f"jalr {a[0]}, {v}({a[1]})"
    if c=='MV': a=args_regs(2); return f"mv {a[0]}, {a[1]}"
    if c=='LI': a=args_regs(1); v=intval(rest[rest.rindex('('):]); return f"li {a[0]}, {v}"
    if c=='NOP': return "nop"
    if c=='ECALL': return "ecall"
    if c=='FENCE': return "fence"
    if c=='EBREAK': return "ebreak"
    if c=='CSRS':
        # .CSRS (csr : BitVec 12) .xN  ->  ".4byte <word>" (mirror emitInstr:
        # (csr << 20) | (rs1 << 15) | 0x2073), decimal like Lean renders it.
        csr=intval(rest[rest.index('('):]); rs1=reg_num(toks[-1][1:])
        return f".4byte {(csr<<20)|(rs1<<15)|0x2073}"
    raise ConvError(f"_render_to_asm: unhandled {c}")

def emit_program_text(entry, asm):
    """Reproduce `"entry:\n" ++ emitProgram prog` purely in Python (the py_emit
    offline pre-flight render)."""
    e, _ea, out, _ext, _rel = _resolve(asm)
    lines = ["  " + l for (_lean, asml) in out for l in asml]
    return e + ":\n" + "\n".join(lines)

# --------------------------------------------------------------------------- #
# assemble + compare .text                                                    #
# --------------------------------------------------------------------------- #
def _riscv_tool(env_var, tool):
    """Resolve a RISC-V binutils tool across both triple spellings.

    Same convention as `resolve_riscv_tool` in
    `scripts/codegen-eest-stateless-check.sh` and the two-triple probes in
    `check-region-map.sh` / `check-opcode-tables.sh`: CI installs
    `binutils-riscv64-unknown-elf`, but Homebrew ships the identical GNU
    binutils as `riscv64-elf-*`.  Without the fallback every byte-identity
    check silently skips on macOS, which reads as "verified" when nothing ran.
    """
    return (os.environ.get(env_var) or
            shutil.which(f'riscv64-unknown-elf-{tool}') or
            shutil.which(f'riscv64-elf-{tool}') or
            f'riscv64-unknown-elf-{tool}')

AS = _riscv_tool('RISCV_AS', 'as')
OBJCOPY = _riscv_tool('RISCV_OBJCOPY', 'objcopy')
LD = _riscv_tool('RISCV_LD', 'ld')

def _text_bytes(asm_text, d, tag='a'):
    """Assemble a snippet and return its raw `.text` (assemble-only; used for
    functions with no `la`/cross-`jal` externals)."""
    s=os.path.join(d,tag+'.s'); o=os.path.join(d,tag+'.o'); b=os.path.join(d,tag+'.bin')
    with open(s,'w') as f:
        f.write(".text\n.globl _f\n_f:\n"+asm_text+"\n")
    subprocess.run([AS,'-march=rv64im','-mno-relax','-o',o,s],check=True,
                   stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    subprocess.run([OBJCOPY,'-O','binary','-j','.text',o,b],check=True,
                   stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    return open(b,'rb').read()

def _linked_text_bytes(asm_text, d, tag, entry_addr, externals):
    """Assemble THEN link the snippet at its real entry address with each
    external symbol `--defsym`'d to its real linked address, returning `.text`.

    This reproduces exactly what the guest link does for `la`/cross-`jal`:
    leaving the target symbols UNDEFINED at assemble time makes GNU-as emit the
    PC-relative form (`auipc`+`addi` for `la`, a relocatable `jal`), and the
    (non-relaxing, matching the guest's `-mno-relax`/`--no-relax`) link fills in
    the real PC-relative immediates. The emitted render's concrete
    `auipc`/`addi`/`jal` are position-invariant, so this compare pins the
    generated immediates to what the hand-written `la`/`jal` linked to. The
    whole-guest byte-identity gate is the final arbiter over the same facts."""
    s=os.path.join(d,tag+'.s'); o=os.path.join(d,tag+'.o')
    e=os.path.join(d,tag+'.elf'); b=os.path.join(d,tag+'.bin')
    with open(s,'w') as f:
        f.write(".text\n.globl _f\n_f:\n"+asm_text+"\n")
    subprocess.run([AS,'-march=rv64im','-mno-relax','-o',o,s],check=True,
                   stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    defs=[f'--defsym={sym}={addr}' for sym,addr in sorted(externals.items())]
    subprocess.run([LD,f'-Ttext=0x{entry_addr:x}','-e','_f','--no-relax','-nostdlib',
                    *defs,'-o',e,o],check=True,
                   stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    subprocess.run([OBJCOPY,'-O','binary','-j','.text',e,b],check=True,
                   stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    return open(b,'rb').read()

READELF = (os.environ.get('RISCV_READELF') or
           shutil.which('riscv64-unknown-elf-readelf') or
           shutil.which('riscv64-elf-readelf') or
           shutil.which('readelf') or 'readelf')
def symbol_binding(asm_text, sym):
    """Assemble `asm_text` and return `sym`'s ELF binding ('GLOBAL' / 'LOCAL'),
    or None if the symbol is absent from the object.

    Exists because `.text` byte-comparison is STRUCTURALLY BLIND to symbol
    binding: a symbol demoted GLOBAL -> LOCAL, or dropped entirely, leaves the
    `.text` bytes identical. Any conversion whose Lean string carries a `.globl`
    therefore has a property no other leg of `check_file` can see -- `.globl` is
    a directive with no `Instr` constructor, so it lives in the string prefix
    rather than in the `Program`, and nothing else re-checks it. (GH #11046.)
    """
    with tempfile.TemporaryDirectory() as d:
        s=os.path.join(d,'b.s'); o=os.path.join(d,'b.o')
        open(s,'w').write(".text\n"+asm_text+"\n")
        r=subprocess.run([AS,'-march=rv64im','-mno-relax','-o',o,s],
                         stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        if r.returncode!=0: return None
        out=subprocess.run([READELF,'-sW',o],check=True,
                           capture_output=True,text=True).stdout
        for ln in out.splitlines():
            c=ln.split()
            if len(c)>=8 and c[7]==sym: return c[4]
    return None

def emitted_reloc_count(asm_text):
    """Assemble `asm_text` and count RISC-V PC-relative / call / jump
    relocations in the object. A reloc-bearing function's EMITTED (symbolic)
    render MUST have >0 — i.e. `la`/`jal` stayed symbolic and each linked image
    (guest, dispatcher, every `zisk_*` probe) relocates them for itself. Zero
    would mean the immediates were baked from one image's layout (the defect
    Fable caught) and would resolve to garbage in every other image."""
    with tempfile.TemporaryDirectory() as d:
        s=os.path.join(d,'r.s'); o=os.path.join(d,'r.o')
        with open(s,'w') as f: f.write(".text\n.globl _f\n_f:\n"+asm_text+"\n")
        subprocess.run([AS,'-march=rv64im','-mno-relax','-o',o,s],check=True,
                       stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        out=subprocess.run([READELF,'-r',o],capture_output=True,text=True).stdout
    return sum(1 for ln in out.splitlines()
               if any(t in ln for t in ('R_RISCV_PCREL','R_RISCV_CALL','R_RISCV_JAL','R_RISCV_HI20')))

def assemble_cmp(orig_asm, emitted_asm, entry_addr=None, externals=None):
    """Compare the `.text` of the original hand-written asm and the emitted
    render.  With `la`/cross-`jal` externals, both are assembled+linked at the
    real entry address (`--defsym` the externals); otherwise a plain assemble."""
    with tempfile.TemporaryDirectory() as d:
        if externals:
            a=_linked_text_bytes(orig_asm,d,'a',entry_addr,externals)
            b=_linked_text_bytes(emitted_asm,d,'b',entry_addr,externals)
        else:
            a=_text_bytes(orig_asm,d,'a')
            b=_text_bytes(emitted_asm,d,'b')
    return a==b, a, b

# --------------------------------------------------------------------------- #
# Lean file generation                                                        #
# --------------------------------------------------------------------------- #
def lean_camel(entry):
    # entry label like rlp_walk_init -> rlpWalkInit
    parts=entry.split('_')
    return parts[0]+''.join(p.capitalize() for p in parts[1:])

def layout_leaf_path(path, root="", fname=None):
    # GH #10753 layout split: a converted module `<Name>.lean` (the bridge)
    # has its generated program blocks in the leaf `<Name>Prog.lean` next to
    # it.  Return the leaf path (same relative/absolute flavour as `path`)
    # when it exists, else None.  `root` is prepended for the existence
    # test only, so both repo-relative and absolute callers work.  Shared
    # by check_file's layout detection and guest_image_coverage.py.
    leaf=path[:-len(".lean")]+"Prog.lean"
    if not os.path.exists(os.path.join(root,leaf)):
        return None
    # A sibling *Prog file is not sufficient evidence that this bridge file
    # uses the layout split: large modules can have a leaf for a different
    # function.  In that case treating the sibling as the target silently
    # sends rewrite/check drift into the wrong file (notably TxIntrinsicStateGas
    # and U256GasPricing).  When a function is known, require its declaration
    # in the leaf before selecting layout mode.
    if fname is not None:
        leaf_text=open(os.path.join(root,leaf)).read()
        if not re.search(r'(?m)^def\s+'+re.escape(fname)+r'\b', leaf_text):
            return None
    return leaf

def gen_lean(entry, renders, func_name, prog_name, relocs=None):
    body=",\n    ".join(renders)
    n=len(renders)
    if not relocs:
        # straight-line / local-only: emitted string == the Program render.
        return f'''def {prog_name} : Program :=
  [ {body} ]

def {func_name} : String :=
  "{entry}:\\n" ++ emitProgram {prog_name}

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `{prog_name}` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem {func_name}_eq_prog :
    {func_name} = "{entry}:\\n" ++ emitProgram {prog_name} := rfl

#guard {func_name}.startsWith "{entry}:\\n"
#guard {prog_name}.length = {n}
'''
    # Reloc-bearing (`la`/cross-`jal`): TWO views (bead evm-asm-4ch8f.9.3).
    #  * {prog_name}   — the VERIFICATION view: concrete guest-linked immediates
    #    (`laHi`/`laLo`/`jalOff GuestAddrs.…`), the Program the guest triples run.
    #  * {func_name}   — the EMISSION view: `emitProgramR` keeps `la`/`jal`
    #    SYMBOLIC, so EVERY linked image (guest, dispatcher, every `zisk_*`
    #    probe) relocates it against its own layout — image-agnostic and
    #    byte-identical to the hand-written source in each image.
    reloc_kind={'la':'la','jal':'jal'}
    rel_body=",\n    ".join(
        f"({idx}, .{reloc_kind[kind]} {rg} \"{sym}\")" for (idx,kind,rg,sym) in relocs)
    reloc_name=prog_name[:-5]+'_relocs' if prog_name.endswith('_prog') else prog_name+'_relocs'
    return f'''def {prog_name} : Program :=
  [ {body} ]

/-- Reloc side-table for `{prog_name}`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def {reloc_name} : RelocTable :=
  [ {rel_body} ]

def {func_name} : String :=
  "{entry}:\\n" ++ emitProgramR {prog_name} {reloc_name}

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `{prog_name}` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem {func_name}_eq_prog :
    {func_name} = "{entry}:\\n" ++ emitProgramR {prog_name} {reloc_name} := rfl

#guard {func_name}.startsWith "{entry}:\\n"
#guard {prog_name}.length = {n}
'''

def gen_lean_layout(entry, renders, func_name, prog_name, relocs=None):
    """GH #10753 layout-parameterised conversion. Returns (leaf_block, bridge_block).

    Leaf block (`Programs/<Name>Prog.lean`, imports GuestLayout, NOT
    GuestAddrs): `def {prog}_of (L : GuestLayout) : Program` with every
    `GuestAddrs.X` in the renders rewritten to `L.X` (or `_L` when the
    generated body has no layout references); the emission view
    (`{func_name}`, `_eq_prog`, `#guard`s) is applied at `.zero`, which is
    sound because `emitProgramR` keeps `la`/`jal` symbolic via the reloc
    side-table, so the emitted string and the length facts are independent
    of the layout.

    Bridge block (`Programs/<Name>.lean`, the manifest path, unchanged):
    `def {prog} : Program := {prog}_of guestLayout` — the ORIGINAL name and
    type, so all consumers compile untouched.  The concrete immediates are
    tied to the real link by the `{fn}#c` concrete-render gate against the
    bridge's applied program.
    """
    lrenders=[r.replace('GuestAddrs.','L.') for r in renders]
    # Lean's conventional unused binder spelling keeps layout-independent
    # leaves warning-free.  Keep the source-drift generator canonical for
    # both shapes: only a body with linked-address references needs `L`.
    layout_binder='L' if any('L.' in r for r in lrenders) else '_L'
    body=",\n    ".join(lrenders)
    n=len(renders)
    bridge=f"def {prog_name} : Program := {prog_name}_of guestLayout\n"
    if not relocs:
        leaf=f'''def {prog_name}_of ({layout_binder} : GuestLayout) : Program :=
  [ {body} ]

def {func_name} : String :=
  "{entry}:\\n" ++ emitProgram ({prog_name}_of .zero)

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `{prog_name}_of .zero` rendered under its label (layout-parameterised
    per GH #10753; emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). -/
theorem {func_name}_eq_prog :
    {func_name} = "{entry}:\\n" ++ emitProgram ({prog_name}_of .zero) := rfl

#guard {func_name}.startsWith "{entry}:\\n"
#guard ({prog_name}_of .zero).length = {n}
'''
        return leaf, bridge
    reloc_kind={'la':'la','jal':'jal'}
    rel_body=",\n    ".join(
        f"({idx}, .{reloc_kind[kind]} {rg} \"{sym}\")" for (idx,kind,rg,sym) in relocs)
    reloc_name=prog_name[:-5]+'_relocs' if prog_name.endswith('_prog') else prog_name+'_relocs'
    leaf=f'''def {prog_name}_of ({layout_binder} : GuestLayout) : Program :=
  [ {body} ]

/-- Reloc side-table for `{prog_name}_of`: the `la`/cross-`jal` instruction
    indices kept SYMBOLIC in the emitted image text (`emitProgramR`), while
    the Program above carries the layout-parameterised immediates
    (`laHi`/`laLo`/`jalOff L.…`) for verification. -/
def {reloc_name} : RelocTable :=
  [ {rel_body} ]

def {func_name} : String :=
  "{entry}:\\n" ++ emitProgramR ({prog_name}_of .zero) {reloc_name}

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `{prog_name}_of .zero` rendered under its label with the
    `la`/`jal` relocs kept symbolic (layout-parameterised per GH #10753;
    emission is layout-independent, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp
    over the bridge's `{prog_name}` (`_of guestLayout`). -/
theorem {func_name}_eq_prog :
    {func_name} = "{entry}:\\n" ++ emitProgramR ({prog_name}_of .zero) {reloc_name} := rfl

#guard {func_name}.startsWith "{entry}:\\n"
#guard ({prog_name}_of .zero).length = {n}
'''
    return leaf, bridge

# --------------------------------------------------------------------------- #
# CLI                                                                         #
# --------------------------------------------------------------------------- #
FIXDIR=os.path.join(os.path.dirname(os.path.abspath(__file__)),'asm-fixtures')

def do_asm(asm):
    entry, entry_addr, out, externals, relocs = _resolve(asm)
    renders = [r for (lean, _a) in out for r in lean]
    # CONCRETE guest-linked render (numeric auipc/addi/jal); the consistency gate
    # links the symbolic original at the guest addresses and compares .text.
    emitted = entry + ":\n" + "\n".join("  " + l for (_l, asml) in out for l in asml)
    ok, a, b = assemble_cmp(asm, emitted, entry_addr, externals)
    return entry, renders, emitted, ok, len(a), len(b), relocs

def do_one(path, func_name):
    return do_asm(extract_or_render(path, func_name))

def fixture_path(func_name): return os.path.join(FIXDIR, func_name+'.s')
MANIFEST=os.path.join(FIXDIR,'MANIFEST.tsv')

def _module_of(rel_path):
    """EvmAsm/Codegen/Programs/U256.lean -> EvmAsm.Codegen.Programs.U256"""
    return rel_path[:-5].replace('/','.') if rel_path.endswith('.lean') else rel_path

_BEG="-=-=-=BEGIN "; _MID="=-=-=-\n"; _END="\n-=-=-=END=-=-=-"
def lean_render(manifest):
    """Return {func: actual `emitProgram`-rendered string} by running the real
    Lean elaborator over the manifest modules. This is the AUTHORITATIVE render
    used by the byte-identity gate (py_emit is only a fast offline pre-flight);
    it closes the gap that the `rfl` theorem is definitionally trivial and so
    never cross-checks py_emit against Lean's `emitInstr`."""
    if not manifest: return {}
    repo=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    mods=sorted({_module_of(p) for p in manifest.values()})
    # A pure-fetch Lake build can leave these modules only in the artifact
    # cache.  `lake env lean` resolves imports from `.lake/build`, so make the
    # manifest's exact render surface local before invoking Lean.  Keep this
    # explicit rather than relying on the caller's cache environment: the
    # byte-tie must behave the same in a fresh worktree and in CI.
    materialize_env=os.environ.copy()
    materialize_env["LAKE_ARTIFACT_CACHE"]="false"
    subprocess.run(['lake', 'build', *mods], cwd=repo, env=materialize_env,
                   check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    funcs=sorted(manifest)
    # For reloc-bearing functions the emitted string ({fn}) is the SYMBOLIC
    # image-agnostic view; we ALSO render `emitProgram <prog>` (key "{fn}#c") —
    # the CONCRETE guest-linked verification Program — so the per-function gate
    # can pin BOTH views to the fixture (symbolic == emitted, concrete ==
    # symbolic linked at the guest addresses).
    items=[(fn, fn) for fn in funcs]
    for fn in funcs:
        fp=fixture_path(fn)
        if not os.path.exists(fp): continue
        try:
            entry,_ea,_out,_ext,relocs=_resolve(open(fp).read())
        except ConvError:
            continue
        if relocs:
            items.append((fn+"#c", f"emitProgram {lean_camel(entry)}_prog"))
    # Emit the render harness as a `forM` over a `List (String × String)` of
    # (key, lean-expr) pairs rather than one giant `do` block: a `do`
    # block desugars to nested binds and blows the default `maxRecDepth` once
    # the manifest passes ~32 funcs (~96 statements).  The `forM` body has
    # fixed nesting depth, so this scales to the full manifest without touching
    # `maxRecDepth`.  This harness is a pure print tool run OUTSIDE the kernel;
    # the trust-bearing artifact remains the per-func `rfl` theorem in-source.
    src =''.join(f"import {m}\n" for m in mods)
    src+="open EvmAsm.Codegen\n"
    src+="def _renderItems : List (String × String) :=\n"
    src+="  [ "+",\n    ".join(f'("{k}", {v})' for k,v in items)+" ]\n"
    src+="def main : IO Unit :=\n"
    src+="  _renderItems.forM fun (nm, s) => do\n"
    src+=f'    IO.print ("{_BEG}" ++ nm ++ "{_MID}")\n'
    src+="    IO.print s\n"
    src+=f'    IO.print "{_END}"\n'
    with tempfile.NamedTemporaryFile('w',suffix='.lean',dir=repo,delete=False) as f:
        f.write(src); tmp=f.name
    try:
        out=subprocess.run(['lake','env','lean','--run',tmp],cwd=repo,
                           env=materialize_env,
                           check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout.decode()
    except subprocess.CalledProcessError as exc:
        raise ConvError("Lean render failed:\n" + exc.stdout.decode() + exc.stderr.decode()) from exc
    finally:
        os.unlink(tmp)
    res={}
    for k,_v in items:
        beg=out.index(_BEG+k+_MID)+len(_BEG+k+_MID)
        end=out.index(_END,beg)
        res[k]=out[beg:end]
    return res

def lean_string_render(functions):
    """Evaluate String-valued Function defs through the real Lean elaborator.

    The original converter only accepted a literal-string RHS, which made a
    reusable String combinator invisible to the conversion gate even though
    its fully evaluated output is ordinary GNU-as text.  This path is the
    general fallback for that shape: the source definition remains the
    authority, Lean evaluates the named String, and the existing assembler /
    Program conversion machinery then handles the resulting text.

    `functions` maps a Function name to its repo-relative Lean source path.
    The batch harness deliberately evaluates all names in one temporary
    module so a family generated by one combinator is checked together.
    """
    if not functions:
        return {}
    repo=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    mods=sorted({_module_of(p) for p in functions.values()})
    materialize_env=os.environ.copy()
    materialize_env["LAKE_ARTIFACT_CACHE"]="false"
    subprocess.run(['lake', 'build', *mods], cwd=repo, env=materialize_env,
                   check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    items=sorted(functions)
    src=''.join(f"import {m}\n" for m in mods)
    src+="open EvmAsm.Codegen\n"
    src+="def _renderItems : List (String × String) :=\n"
    src+="  [ "+",\n    ".join(f'("{fn}", {fn})' for fn in items)+" ]\n"
    src+="def main : IO Unit :=\n"
    src+="  _renderItems.forM fun (nm, s) => do\n"
    src+=f'    IO.print ("{_BEG}" ++ nm ++ "{_MID}")\n'
    src+="    IO.print s\n"
    src+=f'    IO.print "{_END}"\n'
    with tempfile.NamedTemporaryFile('w',suffix='.lean',dir=repo,delete=False) as f:
        f.write(src); tmp=f.name
    try:
        try:
            out=subprocess.run(['lake','env','lean','--run',tmp],cwd=repo,
                               env=materialize_env,check=True,
                               stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout.decode()
        except subprocess.CalledProcessError as exc:
            raise ConvError("Lean String render failed:\n" +
                            exc.stdout.decode() + exc.stderr.decode()) from exc
    finally:
        os.unlink(tmp)
    res={}
    for fn in items:
        beg=out.index(_BEG+fn+_MID)+len(_BEG+fn+_MID)
        end=out.index(_END,beg)
        res[fn]=out[beg:end]
    return res

def extract_or_render(path, func_name):
    """Extract a literal Function or evaluate a String combinator via Lean."""
    text=open(path).read()
    try:
        return extract_function(text, func_name)
    except ConvError as exc:
        if "RHS is not a pure string literal" not in str(exc):
            raise
        rel=os.path.relpath(os.path.abspath(path),
                            os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        return lean_string_render({func_name: rel})[func_name]

def _load_manifest():
    m={}
    if os.path.exists(MANIFEST):
        for ln in open(MANIFEST):
            ln=ln.strip()
            if not ln or ln.startswith('#'): continue
            fn,path=ln.split('\t'); m[fn]=path
    return m

def manifest_binding_issues(manifest):
    """Return manifest rows whose Function is not declared by its path.

    A file-size split must update MANIFEST.tsv when a Function moves to a
    sibling source module.  The one legitimate exception is the GH #10753
    bridge/leaf shape: the manifest keeps the bridge path while the matching
    `<Name>Prog.lean` leaf declares the Function.  Keep that exception tied to
    ``layout_leaf_path(..., fname=...)`` so an arbitrary source sibling cannot
    masquerade as a layout leaf.
    """
    root=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    issues=[]
    for fn,path in sorted(manifest.items()):
        source=os.path.join(root,path)
        try:
            text=open(source).read()
        except OSError as exc:
            issues.append(f"{fn}: manifest source {path} cannot be read: {exc}")
            continue
        if re.search(r'(?m)^def\s+'+re.escape(fn)+r'\s*:\s*String\s*:=', text):
            continue
        leaf=layout_leaf_path(path, root=root, fname=fn)
        if leaf is not None:
            continue
        issues.append(
            f"{fn}: MANIFEST.tsv points at {path}, but that module declares "
            "no matching Function (update the row to the declaring module or "
            "use the GH #10753 bridge/leaf shape)")
    return issues

def _save_manifest(m):
    with open(MANIFEST,'w') as f:
        f.write("# asm_to_program.py conversion manifest: <func>\\t<lean file> (bead evm-asm-4ch8f.9)\n")
        for fn in sorted(m): f.write(f"{fn}\t{m[fn]}\n")

def _def_span(text, fname):
    """Return (start, end) char span of `def <fname> : String := <body>`."""
    m=re.search(r'def\s+'+re.escape(fname)+r'\s*:\s*String\s*:=', text)
    if not m: raise ConvError(f"def {fname} not found")
    start=m.start()
    rest=text[m.end():]; consumed=m.end()
    for ln in rest.split('\n'):
        st=ln.strip()
        if st.startswith(('def ','theorem ','lemma ','#guard','#eval','end ',
                          'namespace ','/-!','/--','@[','private','example','set_option')):
            break
        consumed += len(ln)+1
    return start, consumed

def _generated_block_span(text, fname, prog, layout=False):
    """Span of an ALREADY-GENERATED block for `fname`, or None.

    `_def_span` finds only the `def <fname> : String :=` line, which is correct
    for the FIRST conversion of a raw-string routine.  On a re-generation --
    the prescribed workflow when a converted routine's fixture changes -- that
    span excludes the `_prog`/`_relocs`/theorem/`#guard` declarations the block
    also emits, so the replacement APPENDS a second copy of each instead of
    replacing them.  Lean then fails on the duplicate declarations.

    A generated block runs from `def <prog> : Program :=` to the trailing
    `#guard <prog>.length = N`, with the `def <fname> : String :=` line inside
    it; require that containment so a hand-written file is never matched.
    """
    if layout:
        mp_pat = (r'(?m)^def\s+'+re.escape(prog)+
                  r'_of\s*\([^\n]*\)\s*:\s*Program\s*:=' )
        guard_pat = (r'(?m)^#guard\s+\('+re.escape(prog)+
                     r'_of\s+\.zero\)\.length\s*=\s*\d+\s*$')
    else:
        mp_pat = r'(?m)^def\s+'+re.escape(prog)+r'\s*:\s*Program\s*:='
        guard_pat = r'(?m)^#guard\s+'+re.escape(prog)+r'\.length\s*=\s*\d+\s*$'
    mp=re.search(mp_pat, text)
    if not mp: return None
    mg=None
    for m in re.finditer(guard_pat, text):
        if m.start()>mp.start(): mg=m
    if mg is None: return None
    mf=re.search(r'(?m)^def\s+'+re.escape(fname)+r'\s*:\s*String\s*:=', text)
    if not mf or not (mp.start()<mf.start()<mg.start()): return None
    return mp.start(), mg.end()+1

def rewrite_file(path, funcs):
    """Replace each named Function def in `path` with its generated
    prog+def+theorem+guards block, saving the original asm as a fixture."""
    # Layout-parameterised modules keep the concrete bridge in `path` and the
    # generated Function/program block in the adjacent `*Prog.lean` leaf.
    # Rewrite the leaf in place while retaining the manifest's bridge path;
    # trying to splice the bridge used to fail after fixture fallback found
    # the right asm.
    target_path=layout_leaf_path(path, fname=funcs[0]) or path
    text=open(target_path).read()
    os.makedirs(FIXDIR, exist_ok=True)
    evaluated={}
    generated=[]
    for fn in funcs:
        try:
            extract_function(text, fn)
        except ConvError as exc:
            if "RHS is not a pure string literal" not in str(exc):
                raise
            generated.append(fn)
    if generated:
        rel=os.path.relpath(os.path.abspath(path),
                            os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        evaluated=lean_string_render({fn: rel for fn in generated})
    spans=[]
    uses_reloc=False
    for fn in funcs:
        try:
            asm=extract_function(text, fn)
        except ConvError:
            if fn in evaluated:
                asm=evaluated[fn]
            else:
                # A previously converted definition can be reformatted or moved
                # to another module. Its checked-in fixture remains the authority
                # for regenerating the canonical generated block.
                fp=fixture_path(fn)
                if not os.path.exists(fp): raise
                asm=open(fp).read()
        entry,renders,emitted,ok,la,lb,relocs=do_asm(asm)
        if not ok:
            raise ConvError(f"{fn}: guest-linked .text differs -- refusing to rewrite")
        # A local long B/J also names the entry through `brOff`/`jalOff`, so it
        # needs the same AsmReloc + GuestAddrs imports as a cross-function
        # relocation even though it has no side-table entry.
        if relocs or any(('brOff ' in r or 'jalOff ' in r) for r in renders):
            uses_reloc=True
        open(fixture_path(fn),'w').write(asm if asm.endswith('\n') else asm+'\n')
        prog=lean_camel(entry)+'_prog'
        layout = target_path != path
        if layout:
            block=gen_lean_layout(entry, renders, fn, prog, relocs)[0]
        else:
            block=gen_lean(entry, renders, fn, prog, relocs)
        span=_generated_block_span(text, fn, prog, layout=layout) or _def_span(text, fn)
        spans.append((span[0],span[1],block))
    spans.sort(reverse=True)
    new=text
    for s,e,block in spans:
        new=new[:s]+block.rstrip()+'\n'+new[e:]
    new=_ensure_emit_import(new)
    # Layout leaves substitute `L.` for linked addresses and therefore do not
    # need GuestAddrs; only a concrete Program file gets those imports.
    if uses_reloc and target_path == path: new=_ensure_reloc_imports(new)
    new=_ensure_rv64_open(new)   # `.ADDI`/`.CSRS` dot-notation needs Instr in scope
    if new!=text: open(target_path,'w').write(new)
    man=_load_manifest()
    rel=os.path.relpath(os.path.abspath(path),
                        os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    for fn in funcs: man[fn]=rel
    _save_manifest(man)
    return len(funcs)

def _import_insert_pos(text):
    """Char index at which to insert a top-level `import`. After the last
    real `^import …` line if any; otherwise after a leading `/- … -/` block
    comment and any `--` line comments (never inside prose — the old regex
    matched a stray "import" WORD in the module doc comment)."""
    last=None
    for m in re.finditer(r'(?m)^import\s+\S+.*\n', text):
        last=m.end()
    if last is not None: return last
    i=0; n=len(text)
    # skip a leading block comment /- ... -/ (Lean block comments don't nest here)
    while i<n:
        # skip blank lines
        while i<n and text[i] in ' \t\r\n': i+=1
        if text.startswith('/-', i):
            end=text.find('-/', i+2)
            i = (end+2) if end!=-1 else n
        elif text.startswith('--', i):
            nl=text.find('\n', i); i=(nl+1) if nl!=-1 else n
        else:
            break
    return i

def _ensure_import(text, mod):
    if re.search(r'(?m)^import\s+'+re.escape(mod)+r'\s*$', text): return text
    p=_import_insert_pos(text)
    had_import = re.search(r'(?m)^import\s', text) is not None
    lead='' if (p==0 or text[p-1]=='\n') else '\n'
    # If this is the FIRST import (inserted before code, no prior imports), add a
    # blank line after it to separate the import block from the following code.
    trail='' if had_import else '\n'
    return text[:p]+lead+'import '+mod+'\n'+trail+text[p:]

def _ensure_emit_import(text):
    return _ensure_import(text, 'EvmAsm.Codegen.Emit')

def _ensure_rv64_open(text):
    """`Program` is `def … := List Instr` (not an abbrev), so a `[ .ADDI …,
    .CSRS … ]` literal only resolves its dot-notation constructors when
    `EvmAsm.Rv64` is opened. Files with pre-existing `_prog` conversions already
    open it; a string-only file (e.g. HashBridge) does not — add it after the
    first `namespace` (or at the import-insert point if there is no namespace)."""
    if re.search(r'(?m)^open\s+EvmAsm\.Rv64\b', text): return text
    m=re.search(r'(?m)^namespace\s+\S+.*\n', text)
    if m:
        return text[:m.end()]+'\nopen EvmAsm.Rv64\n'+text[m.end():]
    p=_import_insert_pos(text)
    return text[:p]+'open EvmAsm.Rv64\n'+text[p:]

def _ensure_reloc_imports(text):
    """Ensure `AsmReloc` (laHi/laLo/jalOff) + `GuestAddrs` (address constants)
    are imported for functions that resolve a `la`/cross-`jal`."""
    for mod in ('EvmAsm.Codegen.AsmReloc', 'EvmAsm.Codegen.GuestAddrs'):
        text=_ensure_import(text, mod)
    return text

# --------------------------------------------------------------------------- #
# GuestAddrs.lean generation (churn-containment: the ONLY file that moves on   #
# guest layout drift; regenerated mechanically from the linker-facts TSV).     #
# --------------------------------------------------------------------------- #
GUESTADDRS_PATH=os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    'EvmAsm','Codegen','GuestAddrs.lean')

def _collect_guest_addr_syms():
    """Union over every converted (manifest) function of the symbols its
    `_prog` references through `GuestAddrs`: its own entry (the `pc` base for
    `la`/`jal`) plus every `la`/cross-`jal` target. Returns sorted [(sym,addr)]."""
    man=_load_manifest(); need=set()
    # Hand-maintained converted programs in Dispatch.lean are not in the asm-fixture
    # manifest, but their Program views still use GuestAddrs constants.
    need.update({
        'evm_state_gas_spilled',
        # GH #10619: the tracked code accessor.  Called from the hand-maintained
        # extcodecopy/extcodesize/code-at-state-root Program views, which are not
        # in the asm-fixture manifest, so it is not discovered by the scan above.
        'code_read_fetch',
        # GH #11798: halt_kind cell moved off OUTPUT+32; dispatcherTxGasSettle_prog
        # (hand-maintained in Dispatch.lean) loads GuestAddrs.rdg_halt_kind.
        'rdg_halt_kind',
        # GH #12011: assemble_execution_requests Program (hand-maintained) loads
        # aer_bd_*/aer_be_* BSS globals for builder deposit/exit ABI compatibility.
        'aer_bd_ptr',
        'aer_bd_len',
        'aer_be_ptr',
        'aer_be_len',
        # GH #11808: settle stores folded regular/state left + used for independent regular arm.
        'runtime_tx_settle_regular_gas_left',
        'runtime_tx_settle_state_gas_left',
        'runtime_tx_settle_state_gas_used',
        # Canonical-strict RLP siblings are hand-maintained SAsm programs,
        # not entries in the legacy asm-fixture manifest.  Their wrappers and
        # leaves are nevertheless linked into the guest closure and therefore
        # must be retained when GuestAddrs is regenerated from the ELF.
        'rlp_content_to_u64_strict',
        'rlp_content_to_u256_be_strict',
        'rlp_field_to_u64_strict',
        # GH #12021: rlp_walk_next recursive wrapper Programs (multi-label unit).
        'rlp_walk_next_nested',
        'rlp_walk_next_shared',
        'rlp_validate_payload',
        'rlp_walk_next_core',
    })
    root=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    for fn in man:
        fp=fixture_path(fn)
        if not os.path.exists(fp): continue
        try:
            entry,entry_addr,out,externals,relocs=_resolve(open(fp).read())
        except ConvError:
            continue
        if entry not in SYMMAP:
            # Probe-only conversions have no GuestAddrs entry for their own
            # placeholder PC, but their `la`/cross-`jal` targets may still be
            # real guest globals. Keep those target constants when present in
            # the linker facts; only the probe's own entry is omitted.
            for sym in externals:
                if sym in SYMMAP:
                    need.add(sym)
            continue
        # every linked converted function's entry: the guest-image CodeReq
        # (bead 4ch8f.63) anchors `CodeReq.ofProg` at it BY NAME, so it
        # must exist even for straight-line (reloc-free) functions.
        need.add(entry)
        if externals:                      # reloc-using functions also need addrs
            need.update(externals)
    missing=sorted(s for s in need if s not in SYMMAP)
    if missing:
        raise ConvError(f"GuestAddrs: symbols absent from address table: {missing}")
    return sorted((s, SYMMAP[s]) for s in need)

def gen_guest_addrs():
    syms=_collect_guest_addr_syms()
    L=[]
    L.append("/-")
    L.append("  EvmAsm.Codegen.GuestAddrs")
    L.append("")
    L.append("  GENERATED — do not edit by hand.")
    L.append("  `python3 scripts/asm_to_program.py guest-addrs` regenerates this from")
    L.append("  `scripts/asm-fixtures/symbol-addresses.tsv` (the linker-facts table of")
    L.append("  bead evm-asm-4ch8f.6). One `Nat` constant per guest symbol that a")
    L.append("  converted `_prog` references — function entries (the `pc` base for a")
    L.append("  `la`/`jal` immediate) and `la`/cross-`jal` targets (data arenas, tables,")
    L.append("  callee entries).")
    L.append("")
    L.append("  This is the SINGLE file that churns on guest layout drift: the per-")
    L.append("  function `_prog` defs reference these constants by name via")
    L.append("  `AsmReloc.{laHi,laLo,jalOff}`, so a `.text`/`.data` size change only")
    L.append("  requires regenerating the TSV + this file, never the 100s of `_prog`s.")
    L.append("  Guarded by `scripts/check-asm-to-program.sh` (regenerate + diff).")
    L.append("")
    L.append("  Addresses are LINK_DEPENDENT (move on any layout change); the trusted")
    L.append("  arbiter that they are correct is the whole-guest byte-identity gate.")
    L.append("-/")
    L.append("")
    L.append("namespace EvmAsm.Codegen.GuestAddrs")
    L.append("")
    for sym,addr in syms:
        L.append(f"def {sym} : Nat := 0x{addr:08x}")
    L.append("")
    L.append("end EvmAsm.Codegen.GuestAddrs")
    return '\n'.join(L)+'\n'

# These functions are verified drop-ins whose `_prog` definitions are intentionally
# expressed through SAsm `Stmt.flatten` rather than pasted mechanical literals. The
# fixture/Lean-render assemble checks still guard their emitted bytes; only the
# verbatim generated-block source check is skipped.
SOURCE_DRIFT_ALLOW = {
    'bls12G1Eq48Function',
    'bls12G2EqNFunction',
    'p256Eq32Function',
    'p256IsZeroNFunction',
    'secp256k1FieldEq32Function',
    'secp256k1FieldIsZeroFunction',
    'bn254FieldEq32Function',
    'bn254FieldIsZeroFunction',
    'rlpListNthItemFunction',
    'rlpListCountItemsFunction',
    'rlpFieldToU64Function',
    # #12134: pre-existing proved Program registered into MANIFEST/
    # GuestImageEntries. Its source is a hand-written core-side copy with a
    # dedicated rfl tie, not a paste of gen_lean's decimal form; byte-identity
    # assembly checks still cover the fixture.
    'rlpItemSizeFunction',
    # The four BAL sort routines (GH #10817). Two deviations from the generated
    # block shape, both deliberate and both maintainer-approved:
    #   1. They are the first converted defs that are also EXPORTED, so each
    #      keeps `"  .globl <sym>\n"` ahead of the label. `.globl` is a directive
    #      with no `Instr` constructor, so it cannot live in a `Program` and
    #      `emitProgramR` does not emit it.
    #   2. `balCanonicalSort_prog` is `head ++ balCanonicalDigit_prog ++ tail`
    #      rather than one flat literal, because the module's four anti-drift
    #      `#guard`s on the digit extractor have to be restatable over just that
    #      fragment. The split is a SLICE of one conversion (indices 67..94), so
    #      the branch offsets are still the ones resolved against the whole.
    # Legs (a) and (c) -- the byte-identity checks -- still run on all four.
    'balCanonicalSortFunction',
    'balCanonicalSortSelftestFunction',
}


def _gen_with_br_threshold(asm, fn, prog, relocs, layout, thr, jal_thr=None):
    """Re-render with temporary B/J named-target thresholds (module globals).

    The source-drift transition accepts the pre-symbolic bare form for both
    relocation kinds while existing hand-written blocks are migrated.  The
    optional ``jal_thr`` lets the transition accept a mixed tree where the
    B-type migration has landed but the J-type migration has not (or vice
    versa).
    """
    import sys
    mod = sys.modules[__name__]
    saved = mod.BR_NAMED_THRESHOLD
    saved_jal = mod.JAL_NAMED_THRESHOLD
    mod.BR_NAMED_THRESHOLD = thr
    mod.JAL_NAMED_THRESHOLD = thr if jal_thr is None else jal_thr
    try:
        entry, renders, _em, _ok, _la, _lb, relocs2 = do_asm(asm)
        if layout:
            return gen_lean_layout(entry, renders, fn, prog, relocs2)
        return gen_lean(entry, renders, fn, prog, relocs2).rstrip()
    finally:
        mod.BR_NAMED_THRESHOLD = saved
        mod.JAL_NAMED_THRESHOLD = saved_jal


_BROFF_TO_BARE_RE = re.compile(
    r'\(brOff\s*\(\s*[A-Za-z_][A-Za-z0-9_.]*\s*\+\s*(-?\d+)\s*\)\s*'
    r'\(\s*[A-Za-z_][A-Za-z0-9_.]*\s*\+\s*(-?\d+)\s*\)\s*\)'
)


def _strip_broff_to_bare(text):
    """Replace ``brOff (base+tgt) (base+cur)`` with the equivalent bare BitVec-13.

    Used by the source-drift gate to accept surgical partial B-naming
    migrations (#11512 head retarget): a module may name a subset of long-B
    sites while leaving the rest bare.  After stripping, the block must match
    the all-bare converter output.  Geometry of each named site is already
    enforced by ``_check_b_geometry``.
    """
    def repl(m):
        tgt = int(m.group(1))
        cur = int(m.group(2))
        off = tgt - cur
        return f'({off} : BitVec 13)'
    return _BROFF_TO_BARE_RE.sub(repl, text)


def _source_matches_bare_up_to_broff(text, bare_block):
    """True if ``text`` is ``bare_block`` with a subset of long-B imms upgraded to brOff."""
    return bare_block in _strip_broff_to_bare(text)

def _local_long_jal_sites(asm):
    """Return local `j`/`jal` sites at the named-target threshold or above."""
    items=tokenize(asm)
    labels, num_addr, seq, _end = layout_items(items)
    hits=[]
    for cur,mn,ops in seq:
        if mn=='j':
            target=ops[0]
        elif mn=='jal':
            target=ops[0] if len(ops)==1 else ops[1]
        else:
            continue
        target=target.strip()
        if target.startswith('.+'):
            off=int(target[2:])
        elif target.startswith('.-'):
            off=-int(target[2:])
        elif target in labels:
            off=labels[target]-cur
        elif numlabel_off(num_addr, target, cur) is not None:
            off=numlabel_off(num_addr, target, cur)
        else:
            # A symbol outside this function is a cross-function relocation,
            # not a local target covered by this ratchet.
            continue
        if abs(off) >= JAL_NAMED_THRESHOLD:
            hits.append((cur,mn,off,target))
    return hits


_LOCAL_B_MNEMONICS = frozenset({
    'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu',
    'beqz', 'bnez', 'bltz', 'bgez', 'bgtz', 'blez',
    'bgt', 'ble', 'bgtu', 'bleu',
})
_B_SOURCE_FORM_RE = re.compile(
    r'\.(?:BEQ|BNE|BLT|BGE|BLTU|BGEU)\b[^\n]*')
_B_BARE_IMM_RE = re.compile(r'\((-?\d+)\s*:\s*BitVec\s+13\)')
_B_NAMED_IMM_RE = re.compile(
    r'\bbrOff\s*\(\s*([^()]*)\s*\)\s*\(\s*([^()]*)\s*\)')
_B_NAMED_NUMERIC_RE = re.compile(
    r'\bbrOff\s+(-?\d+)\s+(-?\d+)')
_B_NAMED_EXPR_RE = re.compile(
    r'^\s*([A-Za-z_][A-Za-z0-9_.]*)\s*\+\s*(-?\d+)\s*$')
_PROGRAM_DEF_RE = re.compile(
    r'(?m)^\s*(?:private\s+)?def\s+([A-Za-z_][A-Za-z0-9_]*)[^\n]*:\s*'
    r'(?:Program|List\s+Instr)\s*:=')
_TOP_DECL_RE = re.compile(
    r'(?m)^\s*(?:private\s+)?(?:def|theorem|lemma|opaque|abbrev|instance|namespace|section|end)\b'
    r'|^\s*#(?:guard|eval|check)\b')
_PROGRAM_REF_RE = re.compile(
    r'\b(?:[A-Za-z_][A-Za-z0-9_]*\.)*([A-Za-z_][A-Za-z0-9_]*_prog(?:_of)?)\b')


def _local_long_b_sites(asm, threshold=None):
    """Return every local B-type site at ``BR_NAMED_THRESHOLD`` or above.

    The fixture is the geometry authority: labels and instruction addresses
    are assigned by the same tokenizer and 4-byte layout used by the
    converter.  Keeping this parser independent of the rendered Lean source
    lets the check catch a stale named offset as well as a stale bare one.
    """
    items = tokenize(asm)
    labels, num_addr, seq, addr = layout_items(items)

    hits = []
    for cur, mn, ops in seq:
        if mn not in _LOCAL_B_MNEMONICS:
            continue
        if not ops:
            raise ConvError(f'{mn}: missing branch target')
        target_token = ops[-1].strip()
        if target_token.startswith('.+'):
            off = int(target_token[2:])
            target = cur + off
        elif target_token.startswith('.-'):
            off = -int(target_token[2:])
            target = cur + off
        elif target_token in labels:
            target = labels[target_token]
            off = target - cur
        elif numlabel_off(num_addr, target_token, cur) is not None:
            off = numlabel_off(num_addr, target_token, cur)
            target = cur + off
        else:
            raise ConvError(f'{mn}: unresolved local target {target_token!r}')
        if off % 4 != 0 or target < 0 or target >= addr:
            raise ConvError(
                f'{mn}: target geometry is not an instruction address '
                f'(pc={cur}, target={target}, off={off})')
        cutoff = BR_NAMED_THRESHOLD if threshold is None else threshold
        if abs(off) >= cutoff:
            hits.append((cur, target, off, mn, target_token))
    return hits


_PROGRAM_DEFS_CACHE = None


def _program_definitions():
    """Index every source ``Program`` definition used by a manifest program.

    Converted Codegen programs may concatenate verified RLP or helper programs
    from ``EvmAsm/Rv64``.  Looking only in the manifest module would therefore
    silently omit branches from the source-form check.  The index is built
    once, and an ambiguous program name is rejected by the caller rather than
    guessed.
    """
    global _PROGRAM_DEFS_CACHE
    if _PROGRAM_DEFS_CACHE is not None:
        return _PROGRAM_DEFS_CACHE
    defs = {}
    root = os.path.join(REPO, 'EvmAsm')
    for dirpath, _dirs, filenames in os.walk(root):
        for filename in filenames:
            if not filename.endswith('.lean'):
                continue
            path = os.path.join(dirpath, filename)
            text = open(path).read()
            matches = list(_PROGRAM_DEF_RE.finditer(text))
            for match in matches:
                next_decl = _TOP_DECL_RE.search(text, match.end())
                end = next_decl.start() if next_decl is not None else len(text)
                name = match.group(1)
                defs.setdefault(name, []).append((path, text[match.end():end]))
    _PROGRAM_DEFS_CACHE = defs
    return defs


def _program_branch_forms(prog_name):
    """Expand a Program expression to its source B-constructor lines.

    Some manifest rows are intentionally composed from a wrapper plus a
    verified RLP leaf, and the source-drift allow-list contains a few such
    rows.  Recursively expanding ``*_prog`` references preserves the actual
    append order, so those rows receive the same geometry check as a flat
    generated block.  An absent or cyclic reference is a hard failure.
    """
    defs = _program_definitions()
    stack = []

    def expand(name):
        if name in stack:
            raise ConvError(f'cyclic Program reference: {" -> ".join(stack + [name])}')
        choices = defs.get(name, [])
        if len(choices) != 1:
            if not choices:
                raise ConvError(f'Program definition {name!r} not found')
            raise ConvError(f'Program definition {name!r} is ambiguous')
        _path, body = choices[0]
        stack.append(name)
        result = []
        for line in body.splitlines():
            if _B_SOURCE_FORM_RE.search(line):
                result.append(line.strip())
                continue
            for ref in _PROGRAM_REF_RE.findall(line):
                if ref != name:
                    result.extend(expand(ref))
        stack.pop()
        return result

    return expand(prog_name)


def _parse_b_source_form(line):
    """Parse a source B constructor as ``('bare', off)`` or named offsets.

    Named forms must be simple ``base + Nat`` expressions on both sides.  A
    composite expression is deliberately rejected: accepting it would turn
    the geometry check back into a text-presence heuristic.
    """
    named = _B_NAMED_IMM_RE.search(line)
    if named:
        target_expr, pc_expr = named.groups()
        target = _B_NAMED_EXPR_RE.fullmatch(target_expr)
        pc = _B_NAMED_EXPR_RE.fullmatch(pc_expr)
        if target is None or pc is None:
            raise ConvError(f'unsupported brOff expression: {line}')
        if target.group(1) != pc.group(1):
            raise ConvError(f'brOff uses different PC bases: {line}')
        return ('named', int(target.group(2)), int(pc.group(2)))
    numeric = _B_NAMED_NUMERIC_RE.search(line)
    if numeric:
        return ('named', int(numeric.group(1)) - 0x80000000,
                int(numeric.group(2)) - 0x80000000)
    bare = _B_BARE_IMM_RE.search(line)
    if bare:
        return ('bare', int(bare.group(1)))
    raise ConvError(f'unsupported B source form: {line}')


_B_GEOMETRY_CACHE = {}


def _check_b_geometry(path, fn, asm):
    """Check source B forms against parsed fixture geometry.

    Returns ``(long_count, named_count, bare_count)``.  Every local long B is
    checked, including currently bare forms; the bare count is the ratchet
    debt.  A missing fixture, unparseable Program composition, or source/fixture
    instruction-count mismatch raises ``ConvError`` so the caller fails closed.
    """
    cache_key = (path, fn)
    cached = _B_GEOMETRY_CACHE.get(cache_key)
    if cached is not None:
        return cached
    hits = _local_long_b_sites(asm)
    if not hits:
        _B_GEOMETRY_CACHE[cache_key] = (0, 0, 0)
        return (0, 0, 0)

    entry = tokenize(asm)[0][1]
    prog = lean_camel(entry) + '_prog'
    choices = _program_definitions().get(prog + '_of', [])
    if len(choices) == 1:
        source_forms = _program_branch_forms(prog + '_of')
    else:
        source_forms = _program_branch_forms(prog)

    # The converter parser sees all local conditional B instructions, not just
    # the long ones.  Pairing the complete sequence makes duplicate offsets
    # harmless and detects a missing or extra source branch deterministically.
    source_branch_count = len(source_forms)
    all_hits = _all_local_b_sites(asm)
    expected_branch_count = len(all_hits)
    if source_branch_count != expected_branch_count:
        raise ConvError(
            f'{fn}: source has {source_branch_count} conditional B constructors, '
            f'fixture has {expected_branch_count}')

    long_by_pc = {cur: (target, off) for cur, target, off, _mn, _tok in hits}
    named_count = 0
    bare_count = 0
    for hit, source_line in zip(all_hits, source_forms):
        cur, _target, off, _mn, _tok = hit
        parsed = _parse_b_source_form(source_line)
        if cur not in long_by_pc:
            continue
        target, expected_off = long_by_pc[cur]
        if parsed[0] == 'named':
            _kind, target_off, pc_off = parsed
            if target_off != target or pc_off != cur:
                raise ConvError(
                    f'{fn}: brOff geometry mismatch at pc {cur}: '
                    f'expected target {target}, pc {cur}; '
                    f'source has target {target_off}, pc {pc_off}')
            named_count += 1
        else:
            _kind, bare_off = parsed
            if bare_off != expected_off:
                raise ConvError(
                    f'{fn}: bare B geometry mismatch at pc {cur}: '
                    f'fixture offset {expected_off}, source offset {bare_off}')
            bare_count += 1
    result = (len(hits), named_count, bare_count)
    _B_GEOMETRY_CACHE[cache_key] = result
    return result


def _all_local_b_sites(asm):
    """Return all local conditional B sites, including short branches."""
    return _local_long_b_sites(asm, threshold=0)


def count_bare_b_sites(man=None):
    """Count source files, definitions, and sites carrying bare long local B."""
    if man is None:
        man = _load_manifest()
    files = set()
    defs = 0
    sites = 0
    errors = []
    for fn, rel in man.items():
        fixture = fixture_path(fn)
        path = os.path.join(REPO, rel)
        if not os.path.exists(fixture):
            errors.append(f'{fn}: missing fixture {fixture}')
            continue
        try:
            asm = open(fixture).read()
            _long, _named, bare = _check_b_geometry(path, fn, asm)
        except (ConvError, ValueError, IndexError) as exc:
            errors.append(f'{fn}: B geometry check failed: {exc}')
            continue
        if bare:
            files.add(rel)
            defs += 1
            sites += bare
    return len(files), defs, sites, errors

def count_bare_j_program_files(man=None):
    """Count manifest source files that still carry a bare long local J.

    This intentionally includes the two blocked manifest rows: a converter
    failure must not make a surviving hardcoded target disappear from the
    ratchet.  For convertible rows, compare the checked-in source against the
    named-J and mixed/bare transitional renders used by ``check_file``.
    Returns ``(file_count, definition_count, site_count)``.
    """
    if man is None:
        man=_load_manifest()
    files=set(); defs=0; sites=0
    for fn,rel in man.items():
        path=os.path.join(REPO,rel)
        asm_path=fixture_path(fn)
        if not os.path.exists(asm_path):
            continue
        asm=open(asm_path).read()
        hits=_local_long_jal_sites(asm)
        if not hits:
            continue
        try:
            entry,renders,emitted,ok,la,lb,relocs=do_asm(asm)
        except ConvError:
            # Unlinked/blocked functions cannot be regenerated into a named
            # block yet; count them until their blocker is retired.
            files.add(rel); defs += 1; sites += len(hits)
            continue
        prog=lean_camel(entry)+'_prog'
        leaf=layout_leaf_path(path, fname=fn)
        if leaf:
            source=open(leaf).read()
            j_bare=_gen_with_br_threshold(asm,fn,prog,relocs,True,
                                          BR_NAMED_THRESHOLD,
                                          jal_thr=10**9)[0]
            both_bare=_gen_with_br_threshold(asm,fn,prog,relocs,True,
                                             10**9)[0]
        else:
            source=open(path).read()
            j_bare=_gen_with_br_threshold(asm,fn,prog,relocs,False,
                                          BR_NAMED_THRESHOLD,
                                          jal_thr=10**9)
            both_bare=_gen_with_br_threshold(asm,fn,prog,relocs,False,
                                             10**9)
        if j_bare.rstrip() in source or both_bare.rstrip() in source:
            files.add(os.path.relpath(leaf,REPO) if leaf else rel)
            defs += 1
            # Count only the sites that are still bare in this source block,
            # not every long local J in the fixture (some may already have
            # been converted to a named `jalOff`).
            span = _generated_block_span(source, fn, prog, layout=leaf is not None)
            if span is None:
                span = _def_span(source, fn)
            lo, hi = span
            segment = source[lo:hi]
            offsets={off for _cur,_mn,off,_target in hits}
            for line in segment.splitlines():
                if '.JAL' not in line or 'BitVec 21' not in line:
                    continue
                m=re.search(r'\((-?\d+)\s*:\s*BitVec 21\)', line)
                if m and int(m.group(1)) in offsets:
                    sites += 1
    return len(files), defs, sites

def check_file(path, funcs, rendered=None):
    """CI drift guard for one file. For each func, confirm:
      (a) the ACTUAL Lean-rendered string (`emitProgram <prog>`, obtained from
          the real elaborator via `lean_render`) assembles `.text`-identically
          to the saved original-asm fixture -- this is the authoritative
          binary-identity check and it exercises Lean's `emitInstr`, not
          py_emit;
      (b) the exact generated block is present verbatim in the Lean file (source
          drift guard), except for explicit verified drop-ins whose `_prog` is
          intentionally defined by Lean code rather than a pasted literal;
      (c) py_emit's offline render still agrees (fast cross-check of the mirror).
    `rendered` may be a precomputed {func: lean-string} map (so a batch caller
    runs the Lean elaborator once). Returns a list of problem strings."""
    text=open(path).read(); problems=[]
    # GH #10753 layout-parameterised conversion: a manifest file <Name>.lean
    # that has been split into a leaf <Name>Prog.lean (abstract `_prog_of`
    # (L : GuestLayout)) + a bridge <Name>.lean (`_prog := _prog_of
    # guestLayout`) is detected by the leaf's existence.  The drift gate then
    # pins the LEAF block verbatim in the leaf and the BRIDGE def verbatim in
    # the manifest file; the render gates above are unchanged (the bridge
    # re-exposes every name, so `lean_render` over the manifest modules sees
    # both the symbolic `{fn}` and the concrete `{fn}#c` views).
    leaf_path=layout_leaf_path(path, fname=funcs[0])
    layout_mode=leaf_path is not None
    leaf_text=open(leaf_path).read() if layout_mode else None
    if rendered is None:
        rendered=lean_render({fn:os.path.relpath(os.path.abspath(path),
                     os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) for fn in funcs})
    for fn in funcs:
        fp=fixture_path(fn)
        if not os.path.exists(fp): problems.append(f"{fn}: missing fixture {fp}"); continue
        asm=open(fp).read()
        # Cheap entry label for probe-only classification before SYMMAP resolve.
        try:
            _toks=tokenize(asm)
            if not _toks or _toks[0][0]!='label':
                problems.append(f"{fn}: first line is not a label"); continue
            entry=_toks[0][1]
        except Exception as e:
            problems.append(f"{fn}: tokenize failed: {e}"); continue
        try:
            _check_b_geometry(path, fn, asm)
        except (ConvError, ValueError, IndexError) as e:
            # This check is deliberately independent of the byte-identity
            # gate: a stale bare literal can still assemble to today's bytes.
            # Never let an unparseable/composite/blocked definition escape the
            # geometry ratchet by treating it as zero sites.
            problems.append(f"{fn}: B geometry check failed: {e}")
        try:
            entry,renders,emitted,ok,la,lb,relocs=do_asm(asm)   # py_emit consistency pre-flight
        except ConvError as e:
            # Probe-only entry absent from the linked guest image/TSV (SYMMAP).
            # SYMMAP-based conversion (concrete laHi/laLo/jalOff against the guest
            # address table) is outside this gate's domain: an unlinked→unlinked
            # jal/la cannot be expressed against a table that does not define the
            # target.  Do NOT invent a placeholder jalOff/la offset here — a
            # wrong baked immediate would silently pass every gate.  Drift is
            # covered by the kernel-checked `<Name>Function_eq_prog` theorem
            # (e.g. balAllAccountsCodeConsistentFunction_eq_prog,
            # balStorageReadsInExecLogFunction_eq_prog).  Still run the
            # symbolic safety assemble against the Lean-rendered emitProgramR
            # string when available.
            if entry not in SYMMAP:
                if fn not in rendered:
                    problems.append(f"{fn}: no Lean render captured"); continue
                safe_ok,_,_=assemble_cmp(asm, rendered[fn])
                if not safe_ok:
                    problems.append(f"{fn}: emitted SYMBOLIC render is not byte-identical to the "
                                    f"hand-written source (probe-only, SYMMAP-excluded)"); continue
                continue
            problems.append(f"{fn}: {e}"); continue
        if not ok: problems.append(f"{fn}: py_emit render no longer assembles identically"); continue
        if fn not in rendered:
            problems.append(f"{fn}: no Lean render captured"); continue
        _e,_ea,_out,_ext,_rel=_resolve(asm)
        if _rel:
            # Reloc-bearing: TWO independent gates over the real Lean renders.
            # (a) SAFETY — the emitted (symbolic, image-agnostic) string assembles
            #     `.text`-identically to the fixture WITHOUT linking (both keep
            #     `la`/`jal` symbolic, so this holds in every image, not just the
            #     guest). Exercises Lean's `emitProgramR`.
            safe_ok,_,_=assemble_cmp(asm, rendered[fn])
            if not safe_ok:
                problems.append(f"{fn}: emitted SYMBOLIC render is not byte-identical to the "
                                f"hand-written source (would change the guest/probe images)"); continue
            # image-agnostic guarantee: the emitted render must still carry
            # PC-relative relocations (la/jal symbolic), never baked immediates.
            if emitted_reloc_count(rendered[fn]) == 0:
                problems.append(f"{fn}: emitted render has NO relocations — `la`/`jal` immediates "
                                f"appear baked from one image's layout (breaks other images)"); continue
            # (b) CONSISTENCY — the concrete verification Program (`emitProgram
            #     <prog>`, key "{fn}#c") assembles to the SAME bytes the guest
            #     link produces for the symbolic form (fixture linked at the
            #     guest entry with the externals `--defsym`'d). Ties `_prog`'s
            #     baked immediates to the actual guest layout.
            # Probe-only (entry not in the guest TSV): skip concrete consistency —
            # there is no guest link site; Lean uses a local PC placeholder, not
            # GuestAddrs.entry.  Safety gate (a) already covers symbolic emit.
            ckey=fn+"#c"
            if _e not in SYMMAP:
                pass
            elif ckey not in rendered:
                problems.append(f"{fn}: no concrete Lean render captured"); continue
            else:
                cons_ok,_,_=assemble_cmp(asm, rendered[ckey], _ea, _ext)
                if not cons_ok:
                    problems.append(f"{fn}: concrete verification Program does NOT match the guest-linked "
                                    f"`la`/`jal` (laHi/laLo/jalOff immediate wrong for this layout)"); continue
        else:
            # Straight-line / local-only: emitted == Program render; plain assemble.
            real_ok,_,_=assemble_cmp(asm, rendered[fn])
            if not real_ok:
                problems.append(f"{fn}: LEAN-RENDERED string does NOT assemble identically to fixture "
                                f"(emitInstr/py_emit divergence or guest-binary change)"); continue
        # (d) SYMBOL BINDING — only for conversions whose Lean string declares
        #     `.globl`. `.text` identity cannot see a lost or demoted export, and
        #     `.globl` is the one part of the emitted text the conversion does not
        #     establish (no `Instr` constructor, so it is not in the `Program`).
        if f".globl {entry}" in rendered[fn]:
            b=symbol_binding(rendered[fn], entry)
            if b is None:
                problems.append(f"{fn}: declares `.globl {entry}` but {entry} is absent from the "
                                f"assembled object (or the render no longer assembles)")
            elif b!='GLOBAL':
                problems.append(f"{fn}: {entry} is {b}, not GLOBAL — the `.globl` was lost or "
                                f"demoted; `.text` bytes are unchanged, so no other leg sees this")
        # source drift — skip for probe-only entries (entry ∉ SYMMAP).  gen_lean
        # always emits GuestAddrs.<entry> for the PC base, but probe-only Lean
        # sources use a local `<Name>Pc := 0x80000000` placeholder (see
        # balAccountCodeConsistentPc / balAllAccountsCodeConsistentPc /
        # balStorageReadsInExecLogPc).  Verbatim-block match is therefore the
        # wrong shape; the kernel-checked `<Name>Function_eq_prog` theorem is
        # the drift guard for these.
        if entry not in SYMMAP:
            continue
        prog=lean_camel(entry)+'_prog'
        if layout_mode:
            leaf_block,bridge_block=gen_lean_layout(entry,renders,fn,prog,relocs)
            if leaf_block.rstrip() not in leaf_text:
                # Transitional (#11512): accept bare-imm form until module is
                # rewritten; assemble gates above already proved byte-identity.
                # B and J migrations can land independently, so accept all
                # three mixed states rather than requiring one migration to
                # roll back when the other is still pending.
                leaf_forms = [
                    _gen_with_br_threshold(asm, fn, prog, relocs, layout=True,
                                          thr=10**9)[0],
                    _gen_with_br_threshold(asm, fn, prog, relocs, layout=True,
                                          thr=10**9, jal_thr=JAL_NAMED_THRESHOLD)[0],
                    _gen_with_br_threshold(asm, fn, prog, relocs, layout=True,
                                          thr=BR_NAMED_THRESHOLD, jal_thr=10**9)[0],
                ]
                if not any(form.rstrip() in leaf_text for form in leaf_forms):
                    if not any(_source_matches_bare_up_to_broff(leaf_text, form.rstrip())
                               for form in leaf_forms):
                        problems.append(f"{fn}: generated LEAF block not found verbatim in "
                                        f"{os.path.basename(leaf_path)} (source drift)")
            if bridge_block.rstrip() not in text:
                problems.append(f"{fn}: generated BRIDGE def not found verbatim (source drift)")
        elif fn not in SOURCE_DRIFT_ALLOW:
            block=gen_lean(entry, renders, fn, prog, relocs).rstrip()
            if block not in text:
                forms = [
                    _gen_with_br_threshold(asm, fn, prog, relocs, layout=False,
                                          thr=10**9),
                    _gen_with_br_threshold(asm, fn, prog, relocs, layout=False,
                                          thr=10**9, jal_thr=JAL_NAMED_THRESHOLD),
                    _gen_with_br_threshold(asm, fn, prog, relocs, layout=False,
                                          thr=BR_NAMED_THRESHOLD, jal_thr=10**9),
                ]
                if not any(form in text for form in forms):
                    # Partial B-naming (#11512 surgical head retarget): source may
                    # brOff a subset of long-B sites.  Strip brOff→bare BitVec-13
                    # and match any of the threshold forms (B/J migration axes
                    # are independent).  Per-site geometry already checked above.
                    if not any(_source_matches_bare_up_to_broff(text, form)
                               for form in forms):
                        problems.append(f"{fn}: generated block not found verbatim (source drift)")
    return problems

REPO=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCAN_DIRS=['EvmAsm/Codegen/Programs','EvmAsm/Codegen']

_CLS_DESC={
 'CONVERTED-CLEAN':'Parses to a `Program`; the `emitProgram` render assembles `.text`-identically to the original hand-written text. Directly landable (straight-line / local control only).',
 'READY-WAVE3':'Parses to a `Program` using the wave-.9.3 `la`/cross-`jal` resolution. TWO views: the `Program` carries the CONCRETE guest-linked immediates (`laHi`/`laLo`/`jalOff GuestAddrs.…`) for verification, while the emitted string keeps `la`/`jal` SYMBOLIC via `emitProgramR` + a reloc side-table so EVERY linked image (guest, dispatcher, every `zisk_*` probe) relocates it for itself — byte-identical to the hand-written source in each image. Directly landable.',
 'NEEDS-CALL-EXPANSION':'Contains a `call`/`tail` macro (auipc+jalr, linker-relaxable) — a separate expansion from the `la`/`jal`-offset story of wave .9.3; deferred to a follow-up wave.',
 'NEEDS-DOTWORD':'Contains a raw pre-encoded `.4byte N` word — the ZisK accelerator `.CSRS`/`csrrs` pattern `emitInstr` renders as `.4byte`. Needs a word-literal `Instr` (or a `.4byte`→`.CSRS` decoder) to convert; deferred to a follow-up wave.',
 'BLOCKED_ON_.6':'References a `la <symbol>` or cross-function `jal <callee>` whose target symbol is NOT in the linker-facts address table (`scripts/asm-fixtures/symbol-addresses.tsv`) — typically a routine registered as a probe unit but not yet linked into the monolithic `stateless_guest`. Resolves once it is emitted into the guest and the table regenerated.',
 'NEEDS-LI-EXPANSION':'Contains an `li rd, C` with C outside 12-bit signed range; a faithful 4-byte-per-`Instr` Program must emit the explicit `lui`/`addiw`/… expansion as separate `Instr`s (follow-up wave).',
 'CALLER-LOCAL-FRAGMENT':'Branches/jumps to a `.L` label owned by the caller, or has no own entry label — no independent ABI; needs extraction into a status-returning callable first.',
 'MULTI-ENTRY-BUNDLE':'Defines secondary non-`.L` labels (e.g. `*_clear`/`*_append`/`*_record_nth`) that other files `jal` into as cross-function entry points; `emitProgram` keeps only the entry label, so converting would silently break the guest link (caught only by the whole-guest byte-identity gate). Needs a multi-entry ABI / the .6 layout.',
 'ALREADY-STRUCTURED':'RHS is already `"label:\\n" ++ emitProgram <prog>` — a landed conversion or a prior template splice (RlpWalk, *SAsm).',
 'COMPOSITE':'RHS is not a pure string literal (concatenates other defs / probe prologues / data sections) — not a standalone routine body. **No wave bead needed:** these resolve automatically as their component functions convert.',
 'CMP-DIFFER':'Parses, but the `emitProgram` render does NOT assemble byte-identically — investigate before landing.',
 'UNPARSEABLE':'Other parse failure (see per-function reason).',
}

def render_coverage(rows, landed):
    import collections as _c
    cnt=_c.Counter(r[2] for r in rows); L=[]
    L.append("# 4ch8f.9 — asm-string → Program conversion coverage\n")
    L.append("_Regenerate with `python3 scripts/asm_to_program.py coverage` (requires "
             "`riscv64-unknown-elf-as`/`-objcopy`)._\n")
    L.append("**Multi-image constraint (wave .9.3).** A converted `*Function` string is "
             "emitted into N linked images — the monolithic `stateless_guest`, the "
             "`runtime_dispatcher`, and hundreds of `zisk_*` probe programs — each with a "
             "different `.text`/`.data` layout. `la`/cross-`jal` are therefore emitted "
             "**symbolically** (`emitProgramR` + a reloc side-table) so every image's linker "
             "relocates them itself; the per-function `Program` separately carries the "
             "**concrete** `stateless_guest`-linked immediates (`laHi`/`laLo`/`jalOff "
             "GuestAddrs.…`) as the verification view. Only the guest link pins that view; "
             "the emitted text stays byte-identical to the hand-written source in every "
             "image (checked per-function by assemble/link+`cmp` and by a probe-image "
             "execution check in CI).\n")
    L.append("Every `*Function : String` def under `EvmAsm/Codegen/Programs/` and "
             "`EvmAsm/Codegen/Dispatch.lean` is parsed to a `Program`, rendered back with "
             "`emitProgram`, and the render is assembled with `riscv64-unknown-elf-as` and "
             "byte-compared against the original hand-written text (`.text` of both). See "
             "`docs/4ch8f-asm-to-program.md` for the design and trust model.\n")
    L.append("## Summary\n")
    L.append("| Class | Count | Meaning |\n|---|---:|---|")
    for k,_ in cnt.most_common(): L.append(f"| {k} | {cnt[k]} | {_CLS_DESC.get(k,'')} |")
    L.append(f"| **TOTAL** | **{len(rows)}** | |\n")
    L.append(f"## Landed in this PR ({len(landed)})\n")
    L.append("| Function | File | Instrs |\n|---|---|---:|")
    for r in sorted(rows,key=lambda r:r[1]):
        if r[1] in landed: L.append(f"| `{r[1]}` | `{r[0]}` | {r[3]} |")
    L.append("")
    for cls in ['READY-WAVE3','CONVERTED-CLEAN','NEEDS-LI-EXPANSION','NEEDS-CALL-EXPANSION','NEEDS-DOTWORD','CALLER-LOCAL-FRAGMENT','MULTI-ENTRY-BUNDLE']:
        items=sorted([r for r in rows if r[2]==cls],key=lambda r:(r[0],r[1]))
        L.append(f"## {cls} ({len(items)})\n")
        L.append("| Function | File | Instrs | Note |\n|---|---|---:|---|")
        for r in items:
            flag=' ✅ landed' if r[1] in landed else ''
            L.append(f"| `{r[1]}` | `{r[0]}` | {r[3] or ''} | {r[4]}{flag} |")
        L.append("")
    for cls in ['BLOCKED_ON_.6','ALREADY-STRUCTURED','COMPOSITE','UNPARSEABLE','CMP-DIFFER']:
        items=[r for r in rows if r[2]==cls]
        if not items: continue
        byfile=_c.Counter(r[0] for r in items)
        L.append(f"## {cls} ({len(items)}) — by file\n")
        L.append("| File | Count |\n|---|---:|")
        for f,c in sorted(byfile.items()): L.append(f"| `{f}` | {c} |")
        L.append("")
    return '\n'.join(L)+'\n'

def classify_all():
    """Scan every *Function def and classify. Returns list of (rel,name,cls,n,note)."""
    rows=[]; seen=set()
    for rd in SCAN_DIRS:
        d=os.path.join(REPO,rd)
        for fn in sorted(os.listdir(d)):
            if not fn.endswith('.lean'): continue
            path=os.path.join(d,fn)
            if path in seen: continue
            seen.add(path)
            rel=os.path.relpath(path,REPO); text=open(path).read()
            for m in re.finditer(r'def\s+([A-Za-z0-9_]+Function)\s*:\s*String\s*:=',text):
                name=m.group(1)
                try: asm=extract_function(text,name)
                except ConvError as e:
                    # distinguish already-emitProgram-structured defs from other composites
                    seg=text[m.end():m.end()+400]
                    cls='ALREADY-STRUCTURED' if 'emitProgram' in seg else 'COMPOSITE'
                    rows.append((rel,name,cls,0,'')); continue
                try:
                    entry,entry_addr,out,externals,relocs=_resolve(asm)
                    renders=[r for (lean,_a) in out for r in lean]
                except ConvError as e:
                    msg=str(e)
                    if 'NEEDS-DOTWORD' in msg: cls='NEEDS-DOTWORD'
                    elif 'NEEDS-CALL-EXPANSION' in msg: cls='NEEDS-CALL-EXPANSION'
                    elif 'BLOCKED_ON_.6' in msg: cls='BLOCKED_ON_.6'
                    elif 'MULTI-ENTRY-BUNDLE' in msg: cls='MULTI-ENTRY-BUNDLE'
                    elif 'NEEDS-LI-EXPANSION' in msg: cls='NEEDS-LI-EXPANSION'
                    elif 'unresolved branch/jump target' in msg:
                        tgt=msg.split("'")[1]
                        cls='CALLER-LOCAL-FRAGMENT' if tgt.startswith('.') else 'BLOCKED_ON_.6'
                    elif 'first line is not a label' in msg: cls='CALLER-LOCAL-FRAGMENT'
                    else: cls='UNPARSEABLE'
                    rows.append((rel,name,cls,0,msg[:70])); continue
                try:
                    ok=do_asm(asm)[3]
                except Exception as e:
                    rows.append((rel,name,'UNPARSEABLE',len(renders),str(e)[:60])); continue
                if not ok:
                    rows.append((rel,name,'CMP-DIFFER',len(renders),'asm .text differs')); continue
                # A clean parse that resolves a `la`/cross-`jal` via the .6 address
                # table is a NEW capability of this wave: report it as READY-WAVE3
                # (vs already-landable straight-line/local-only CONVERTED-CLEAN).
                cls='READY-WAVE3' if externals else 'CONVERTED-CLEAN'
                rows.append((rel,name,cls,len(renders),
                             f"{len(externals)} reloc sym(s)" if externals else ''))
    return rows

_NUMLABEL_UNDERFLOW_ASM = """probe_underflow:
  la x14, evm_cur_stack_top
  ld x14, 0(x14)
  addi x14, x14, -32
  bgeu x14, x12, 137f
  li x13, 7
  la x14, evm_halt_flag
  sd x14, 0(x13)
  ret
137:
  ret
"""

# Two definitions of the same number: the case a `name -> addr` dict gets wrong.
_NUMLABEL_REPEAT_ASM = """probe_rep:
  beq x1, x2, 1f
  nop
1:
  beq x1, x2, 1f
  nop
1:
  ret
"""


def numlabel_self_test():
    """GH #12204 step 2: GNU-as numeric local labels resolve by nearest-definition.

    Needs no assembler, so it is run BEFORE the cross-toolchain probe in
    `check-asm-to-program.sh` — a check that can only skip is not a check.
    """
    fails = []

    def check(what, got, want):
        if got != want:
            fails.append(f"{what}: got {got!r} want {want!r}")

    lab, num, seq, _end = layout_items(tokenize(_NUMLABEL_UNDERFLOW_ASM))
    # `la` is a two-instruction pseudo, so 137: lands at 40 and the bgeu at 16.
    check("137: address", num.get('137'), [40])
    check("bgeu pc", [a for a, mn, _ in seq if mn == 'bgeu'], [16])
    check("forward ref 137f", numlabel_off(num, '137f', 16), 24)
    check("backward ref at same addr", numlabel_off(num, '137b', 40), 0)
    check("backward ref", numlabel_off(num, '137b', 44), -4)
    check("named label falls through", numlabel_off(num, '.Lfoo', 0), None)
    check("plain symbol falls through", numlabel_off(num, 'evm_halt_flag', 0), None)

    # Unresolvable references must raise, never bind to the wrong definition.
    for tok, cur in (('137b', 0), ('137f', 40), ('9f', 0)):
        try:
            numlabel_off(num, tok, cur)
            fails.append(f"{tok}@{cur}: expected ConvError, got a silent resolution")
        except ConvError:
            pass

    lab2, num2, _seq2, _e2 = layout_items(tokenize(_NUMLABEL_REPEAT_ASM))
    check("repeated 1: both recorded", num2.get('1'), [8, 16])
    check("1f binds nearest forward (pc=0)", numlabel_off(num2, '1f', 0), 8)
    check("1f binds nearest forward (pc=8)", numlabel_off(num2, '1f', 8), 8)
    check("1b binds nearest backward (pc=12)", numlabel_off(num2, '1b', 12), -4)
    check("1b binds nearest backward (pc=16)", numlabel_off(num2, '1b', 16), 0)

    # End to end: the guard converts, and its branch carries the resolved offset.
    entry, renders = convert(_NUMLABEL_UNDERFLOW_ASM)
    check("entry", entry, 'probe_underflow')
    check("branch offset rendered",
          any('.BGEU' in r and '(24 : BitVec 13)' in r for r in renders), True)

    if fails:
        for f in fails:
            print(f"numlabel-self-test: FAIL {f}", file=sys.stderr)
        sys.exit(1)
    print("numlabel-self-test: OK — numeric local labels bind to the nearest "
          "definition forward/backward, repeats included")


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('command', choices=['convert','check','emit-lean','rewrite','check-file','check-all','coverage','guest-addrs','check-guest-addrs','numlabel-self-test'])
    ap.add_argument('--file', help='Lean source file')
    ap.add_argument('--func', help='<name>Function def')
    ap.add_argument('--funcs', help='comma-separated Function defs (rewrite/check-file)')
    ap.add_argument('--prog-name', help='program def name (default <camel>_prog)')
    args=ap.parse_args()
    if args.command=='numlabel-self-test':
        numlabel_self_test()
        return
    if args.command=='guest-addrs':
        out=gen_guest_addrs()
        open(GUESTADDRS_PATH,'w').write(out)
        print(f"wrote {GUESTADDRS_PATH} ({out.count(' : Nat :=')} symbols)")
        return
    if args.command=='check-guest-addrs':
        want=gen_guest_addrs()
        have=open(GUESTADDRS_PATH).read() if os.path.exists(GUESTADDRS_PATH) else ''
        if want!=have:
            print("GuestAddrs.lean DRIFT: regenerate with "
                  "`python3 scripts/asm_to_program.py guest-addrs` "
                  "(guest layout / converted-set changed)")
            sys.exit(1)
        print(f"check-guest-addrs: CLEAN ({want.count(' : Nat :=')} symbols)")
        return
    if args.command=='coverage':
        rows=classify_all()
        landed=set(_load_manifest().keys())
        out=render_coverage(rows, landed)
        dst=os.path.join(REPO,'docs','4ch8f-asm-to-program-coverage.md')
        open(dst,'w').write(out)
        import collections as _c
        print(f"wrote {dst}: {len(rows)} funcs "
              f"{dict(_c.Counter(r[2] for r in rows))}")
        return
    if args.command=='check-all':
        man=_load_manifest()
        binding_prob=manifest_binding_issues(man)
        if binding_prob:
            print("MANIFEST BINDING DRIFT:")
            for p in binding_prob:
                print("  "+p)
            sys.exit(1)
        # Bijection gate: every fixture file must have a MANIFEST row.
        #
        # Every other leg of this check walks the MANIFEST, so an ORPHANED
        # fixture -- a `.s` whose routine was retired while the file survived --
        # is invisible to all of them. The deletion looks complete from every
        # angle except this one: the Lean def goes, the manifest row goes, the
        # symbol leaves the image, and the fixture stays behind ungated, so
        # nothing would notice it drifting or contradicting the tree.
        #
        # Three had accumulated before anyone counted them (GH #11054): the two
        # bal_sort routines and eip7702NonceReuseGuardFunction, against 386
        # gated rows. 386 of 389 is a rule with exceptions, and an exception to
        # a rule nobody states becomes the new rule -- hence a gate rather than
        # a one-off cleanup.
        #
        # Direction matters, and only one direction needs a new check: a
        # MANIFEST row with no fixture already fails loudly in check_file, while
        # an orphaned file fails silently.
        orphans=[f for f in sorted(os.listdir(FIXDIR))
                 if f.endswith('.s') and f[:-len('.s')] not in man]
        if orphans:
            print("DRIFT DETECTED:")
            for o in orphans:
                print(f"  scripts/asm-fixtures/{o}: fixture has no MANIFEST.tsv row "
                      "(routine retired? delete the fixture; still live? re-add its row)")
            sys.exit(1)
        # Most files have one conversion mode, but a bridge can also import a
        # sibling layout leaf for a different routine.  Group by the selected
        # leaf as well as the manifest path so check_file never applies one
        # routine's layout mode to its sibling (e.g. U256GasPricing).
        byfile={}
        for fn,path in man.items():
            leaf=layout_leaf_path(path, fname=fn)
            byfile.setdefault((path, leaf),[]).append(fn)
        root=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        rendered=lean_render(man)   # ONE elaborator run for the whole manifest
        allprob=[]
        for (path,_leaf),fns in sorted(byfile.items(), key=lambda item: (item[0][0], item[0][1] or "")):
            allprob += [f"[{path}] "+p for p in check_file(os.path.join(root,path), fns, rendered)]
        # GuestAddrs.lean must match a fresh regeneration from the TSV+manifest.
        gaprob=[]
        try:
            if gen_guest_addrs()!=(open(GUESTADDRS_PATH).read() if os.path.exists(GUESTADDRS_PATH) else ''):
                gaprob=["GuestAddrs.lean out of date: regenerate with "
                        "`python3 scripts/asm_to_program.py guest-addrs`"]
        except ConvError as e:
            gaprob=[f"GuestAddrs: {e}"]
        allprob+=gaprob
        bare_j_files,bare_j_defs,bare_j_sites=count_bare_j_program_files(man)
        if bare_j_sites != EXPECTED_BARE_J_SITES:
            allprob.append(
                f"bare local J site ratchet: expected exactly {EXPECTED_BARE_J_SITES} "
                f"sites, found {bare_j_sites} ({bare_j_files} files / "
                f"{bare_j_defs} defs); update the committed value with a stated reason")
        bare_b_files, bare_b_defs, bare_b_sites, b_errors = count_bare_b_sites(man)
        for error in b_errors:
            allprob.append(error)
        if not b_errors and bare_b_sites != EXPECTED_BARE_B_SITES:
            allprob.append(
                f"bare local B site ratchet: expected exactly {EXPECTED_BARE_B_SITES} "
                f"sites, found {bare_b_sites} ({bare_b_files} files / "
                f"{bare_b_defs} defs); update the committed value only with "
                "the corresponding source migration")
        if allprob:
            print("DRIFT DETECTED:")
            for p in allprob: print("  "+p)
            sys.exit(1)
        print(f"check-all: CLEAN ({len(man)} converted defs across {len(byfile)} files; "
              f"bare local J report {bare_j_files} files / {bare_j_defs} defs; "
              f"blocking J ratchet {bare_j_sites} sites; "
              f"bare local B report {bare_b_files} files / {bare_b_defs} defs; "
              f"blocking B ratchet {bare_b_sites} sites)")
        return
    if args.command in ('rewrite','check-file'):
        funcs=[f.strip() for f in args.funcs.split(',') if f.strip()]
        if args.command=='check-file':
            problems=check_file(args.file, funcs)
            if problems:
                print(f"{args.file}: DRIFT DETECTED")
                for p in problems: print("  "+p)
                sys.exit(1)
            print(f"{args.file}: CLEAN (no drift, {len(funcs)} defs)")
            return
        n=rewrite_file(args.file, funcs)
        print(f"rewrote {n} defs in {args.file}")
        return
    entry, renders, emitted, ok, la, lb, relocs = do_one(args.file, args.func)
    if args.command=='check':
        print(f"{args.func}: entry={entry} n={len(renders)} reloc={len(relocs)} "
              f"asm_cmp={'IDENTICAL' if ok else 'DIFFER'} ({la} vs {lb} bytes)")
        sys.exit(0 if ok else 1)
    if args.command=='emit-lean':
        prog=args.prog_name or (lean_camel(entry)+'_prog')
        print(gen_lean(entry, renders, args.func, prog, relocs))
    else:
        print(f"-- entry {entry}, {len(renders)} instrs, "
              f"asm_cmp={'OK' if ok else 'FAIL'}")
        print("\n".join(renders))

if __name__=='__main__': main()
