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
    Raises if the RHS is not a pure string-literal concatenation."""
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
def tokenize(asm):
    """Yield ('label', name) and ('insn', mnemonic, [operands...])."""
    items=[]
    for line in asm.split('\n'):
        line=line.split('#',1)[0]
        if not line.strip(): continue
        for piece in line.split(';'):
            piece=piece.strip()
            if not piece: continue
            m=re.match(r'^([.A-Za-z_][.A-Za-z0-9_$]*):\s*(.*)$',piece)
            if m:
                items.append(('label', m.group(1)))
                if not m.group(2).strip(): continue
                piece=m.group(2).strip()
            mn=piece.split(None,1)[0]
            rest=piece[len(mn):].strip()
            ops=[o.strip() for o in rest.split(',')] if rest else []
            items.append(('insn', mn, ops))
    return items

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
        pcx = f"({GA}.{entry} + {cur})"
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
        # local (label or PC-relative) targets keep the ordinary single-JAL path
        if tgt in label_addr or tgt.startswith('.'):
            return [render_insn(mn, ops, off_of)], [py_emit_line(mn, ops, off_of)], None
        # cross-function symbol target -> resolved PC-relative offset
        if entry_addr is None:
            raise ConvError(f"{mn}: entry {entry!r} address unknown (BLOCKED_ON_.6)")
        if tgt not in SYMMAP:
            raise ConvError(f"unresolved branch/jump target {tgt!r}")
        externals[tgt] = SYMMAP[tgt]
        off = _jal_off(SYMMAP[tgt], entry_addr + cur)
        lean = [f".JAL {reg(rd)} (jalOff {GA}.{tgt} ({GA}.{entry} + {cur}))"]
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
    for it in items[1:]:
        if it[0] == 'label' and not it[1].startswith('.L'):
            raise ConvError(f"secondary non-.L label {it[1]!r}: multi-entry bundle, "
                            f"cross-function entry point stripped by emitProgram "
                            f"(MULTI-ENTRY-BUNDLE)")
    entry_addr = SYMMAP.get(entry)   # None if this def is not linked into the guest
    # assign byte address to each insn; record label -> address
    label_addr = {}
    addr = 0
    seq = []  # (addr, mn, ops)
    for it in items:
        if it[0]=='label':
            label_addr[it[1]] = addr
        else:
            _, mn, ops = it
            sz = insn_size(mn, ops)
            seq.append((addr, mn, ops))
            addr += sz
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
AS = shutil.which('riscv64-unknown-elf-as') or 'riscv64-unknown-elf-as'
OBJCOPY = (shutil.which('riscv64-unknown-elf-objcopy') or
           'riscv64-unknown-elf-objcopy')
LD = shutil.which('riscv64-unknown-elf-ld') or 'riscv64-unknown-elf-ld'

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

READELF = (shutil.which('riscv64-unknown-elf-readelf') or
           shutil.which('readelf') or 'readelf')
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
    text=open(path).read()
    return do_asm(extract_function(text, func_name))

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

def _load_manifest():
    m={}
    if os.path.exists(MANIFEST):
        for ln in open(MANIFEST):
            ln=ln.strip()
            if not ln or ln.startswith('#'): continue
            fn,path=ln.split('\t'); m[fn]=path
    return m

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

def rewrite_file(path, funcs):
    """Replace each named Function def in `path` with its generated
    prog+def+theorem+guards block, saving the original asm as a fixture."""
    text=open(path).read()
    os.makedirs(FIXDIR, exist_ok=True)
    spans=[]
    uses_reloc=False
    for fn in funcs:
        try:
            asm=extract_function(text, fn)
        except ConvError:
            # A previously converted definition can be reformatted or moved to
            # another module.  Its checked-in fixture remains the authority for
            # regenerating the canonical generated block.
            fp=fixture_path(fn)
            if not os.path.exists(fp): raise
            asm=open(fp).read()
        entry,renders,emitted,ok,la,lb,relocs=do_asm(asm)
        if not ok:
            raise ConvError(f"{fn}: guest-linked .text differs -- refusing to rewrite")
        if relocs: uses_reloc=True   # references la/cross-jal externals
        open(fixture_path(fn),'w').write(asm if asm.endswith('\n') else asm+'\n')
        prog=lean_camel(entry)+'_prog'
        block=gen_lean(entry, renders, fn, prog, relocs)
        s,e=_def_span(text, fn)
        spans.append((s,e,block))
    spans.sort(reverse=True)
    new=text
    for s,e,block in spans:
        new=new[:s]+block.rstrip()+'\n'+new[e:]
    new=_ensure_emit_import(new)
    if uses_reloc: new=_ensure_reloc_imports(new)
    new=_ensure_rv64_open(new)   # `.ADDI`/`.CSRS` dot-notation needs Instr in scope
    if new!=text: open(path,'w').write(new)
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
    })
    root=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    for fn in man:
        fp=fixture_path(fn)
        if not os.path.exists(fp): continue
        try:
            entry,entry_addr,out,externals,relocs=_resolve(open(fp).read())
        except ConvError:
            continue
        if entry in SYMMAP:
            # every linked converted function's entry: the guest-image CodeReq
            # (bead 4ch8f.63) anchors `CodeReq.ofProg` at it BY NAME, so it
            # must exist even for straight-line (reloc-free) functions.
            # Unlinked conversions (entry absent from the TSV) are skipped.
            need.add(entry)
        if externals:                      # reloc-using functions also need addrs
            need.add(entry); need.update(externals)
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
    # This helper is an intentional hand-composed wrapper around a mechanically
    # converted core, so its source is not one generated literal block.
    'committedStorageChunkedSnapshotUpsertFunction',
}

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
    if rendered is None:
        rendered=lean_render({fn:os.path.relpath(os.path.abspath(path),
                     os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) for fn in funcs})
    for fn in funcs:
        fp=fixture_path(fn)
        if not os.path.exists(fp): problems.append(f"{fn}: missing fixture {fp}"); continue
        asm=open(fp).read()
        entry,renders,emitted,ok,la,lb,relocs=do_asm(asm)   # py_emit consistency pre-flight
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
            ckey=fn+"#c"
            if ckey not in rendered:
                problems.append(f"{fn}: no concrete Lean render captured"); continue
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
        # source drift
        prog=lean_camel(entry)+'_prog'
        block=gen_lean(entry, renders, fn, prog, relocs).rstrip()
        if fn not in SOURCE_DRIFT_ALLOW and block not in text:
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
 'ALREADY-STRUCTURED':'RHS is already `"label:\\n" ++ emitProgram <prog>` — a landed conversion (this PR: 16) or a prior template splice (RlpWalk, *SAsm).',
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

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('command', choices=['convert','check','emit-lean','rewrite','check-file','check-all','coverage','guest-addrs','check-guest-addrs'])
    ap.add_argument('--file', help='Lean source file')
    ap.add_argument('--func', help='<name>Function def')
    ap.add_argument('--funcs', help='comma-separated Function defs (rewrite/check-file)')
    ap.add_argument('--prog-name', help='program def name (default <camel>_prog)')
    args=ap.parse_args()
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
        byfile={}
        for fn,path in man.items(): byfile.setdefault(path,[]).append(fn)
        root=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        rendered=lean_render(man)   # ONE elaborator run for the whole manifest
        allprob=[]
        for path,fns in sorted(byfile.items()):
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
        if allprob:
            print("DRIFT DETECTED:")
            for p in allprob: print("  "+p)
            sys.exit(1)
        print(f"check-all: CLEAN ({len(man)} converted defs across {len(byfile)} files)")
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
