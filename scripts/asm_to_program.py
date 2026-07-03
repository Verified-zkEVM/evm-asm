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
    body='\n'.join(body_lines)
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
# instruction byte size in the 4-byte model (all must be 4; li may not be)    #
# --------------------------------------------------------------------------- #
def insn_size(mn, ops):
    if mn == 'li':
        v = parse_imm(ops[1])
        if not fits(v, 12):
            raise ConvError(f"li {ops[1]}: constant needs multi-instruction expansion "
                            f"(NEEDS-LI-EXPANSION)")
    if mn in ('la','call','tail'):
        raise ConvError(f"{mn}: symbol/cross-function operand (BLOCKED_ON_.6)")
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
def convert(asm):
    items = tokenize(asm)
    # first item must be the function label
    if not items or items[0][0] != 'label':
        raise ConvError("first line is not a label")
    entry = items[0][1]
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
    def off_of(tok):
        tok=tok.strip()
        # PC-relative .+N / .-N (relative to current insn address `cur`)
        if tok.startswith('.+'): return int(tok[2:])
        if tok.startswith('.-'): return -int(tok[2:])
        if tok=='.': return 0
        if tok in label_addr:
            return label_addr[tok] - cur
        # bare integer -> absolute target address (GNU-as); treat as offset only
        # if it is a label; otherwise unsupported for a relocatable Program.
        raise ConvError(f"unresolved branch/jump target {tok!r}")
    renders=[]
    for cur, mn, ops in seq:
        renders.append(render_insn(mn, ops, off_of))
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
    raise ConvError(f"_render_to_asm: unhandled {c}")

def emit_program_text(entry, asm):
    """Reproduce `"entry:\n" ++ emitProgram prog` purely in Python."""
    items = tokenize(asm)
    label_addr={}; addr=0; seq=[]
    for it in items:
        if it[0]=='label': label_addr[it[1]]=addr
        else:
            _,mn,ops=it; sz=insn_size(mn,ops); seq.append((addr,mn,ops)); addr+=sz
    def mk_off_of(cur):
        def off_of(tok):
            tok=tok.strip()
            if tok.startswith('.+'): return int(tok[2:])
            if tok.startswith('.-'): return -int(tok[2:])
            if tok in label_addr: return label_addr[tok]-cur
            raise ConvError(f"unresolved {tok}")
        return off_of
    lines=[]
    for cur,mn,ops in seq:
        lines.append("  "+py_emit_line(mn,ops,mk_off_of(cur)))
    return entry+":\n"+"\n".join(lines)

# --------------------------------------------------------------------------- #
# assemble + compare .text                                                    #
# --------------------------------------------------------------------------- #
AS = shutil.which('riscv64-unknown-elf-as') or 'riscv64-unknown-elf-as'
OBJCOPY = (shutil.which('riscv64-unknown-elf-objcopy') or
           'riscv64-unknown-elf-objcopy')
def _text_bytes(asm_text, d):
    s=os.path.join(d,'a.s'); o=os.path.join(d,'a.o'); b=os.path.join(d,'a.bin')
    with open(s,'w') as f:
        f.write(".text\n.globl _f\n_f:\n"+asm_text+"\n")
    subprocess.run([AS,'-march=rv64im','-o',o,s],check=True,
                   stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    subprocess.run([OBJCOPY,'-O','binary','-j','.text',o,b],check=True,
                   stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    return open(b,'rb').read()

def assemble_cmp(orig_asm, emitted_asm):
    with tempfile.TemporaryDirectory() as d:
        a=_text_bytes(orig_asm,d)
        b=_text_bytes(emitted_asm,d)
    return a==b, a, b

# --------------------------------------------------------------------------- #
# Lean file generation                                                        #
# --------------------------------------------------------------------------- #
def lean_camel(entry):
    # entry label like rlp_walk_init -> rlpWalkInit
    parts=entry.split('_')
    return parts[0]+''.join(p.capitalize() for p in parts[1:])

def gen_lean(entry, renders, func_name, prog_name):
    body=",\n    ".join(renders)
    n=len(renders)
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

# --------------------------------------------------------------------------- #
# CLI                                                                         #
# --------------------------------------------------------------------------- #
FIXDIR=os.path.join(os.path.dirname(os.path.abspath(__file__)),'asm-fixtures')

def do_asm(asm):
    entry, renders = convert(asm)
    emitted=emit_program_text(entry, asm)
    ok, a, b = assemble_cmp(asm, emitted)
    return entry, renders, emitted, ok, len(a), len(b)

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
    src =''.join(f"import {m}\n" for m in mods)
    src+="open EvmAsm.Codegen\n"
    src+="def main : IO Unit := do\n"
    for fn in funcs:
        src+=f'  IO.print "{_BEG}{fn}{_MID}"; IO.print {fn}; IO.print "{_END}"\n'
    with tempfile.NamedTemporaryFile('w',suffix='.lean',dir=repo,delete=False) as f:
        f.write(src); tmp=f.name
    try:
        out=subprocess.run(['lake','env','lean','--run',tmp],cwd=repo,
                           check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout.decode()
    finally:
        os.unlink(tmp)
    res={}
    for fn in funcs:
        beg=out.index(_BEG+fn+_MID)+len(_BEG+fn+_MID)
        end=out.index(_END,beg)
        res[fn]=out[beg:end]
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
    for fn in funcs:
        asm=extract_function(text, fn)
        entry,renders,emitted,ok,la,lb=do_asm(asm)
        if not ok:
            raise ConvError(f"{fn}: assemble .text differs -- refusing to rewrite")
        open(fixture_path(fn),'w').write(asm if asm.endswith('\n') else asm+'\n')
        prog=lean_camel(entry)+'_prog'
        block=gen_lean(entry, renders, fn, prog)
        s,e=_def_span(text, fn)
        spans.append((s,e,block))
    spans.sort(reverse=True)
    new=text
    for s,e,block in spans:
        new=new[:s]+block.rstrip()+'\n'+new[e:]
    new=_ensure_emit_import(new)
    if new!=text: open(path,'w').write(new)
    man=_load_manifest()
    rel=os.path.relpath(os.path.abspath(path),
                        os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    for fn in funcs: man[fn]=rel
    _save_manifest(man)
    return len(funcs)

def _ensure_emit_import(text):
    if 'EvmAsm.Codegen.Emit' in text: return text
    t=re.sub(r'(import EvmAsm\.Codegen\.Layout\n)',
             r'\1import EvmAsm.Codegen.Emit\n', text, count=1)
    if 'EvmAsm.Codegen.Emit' not in t:
        t=re.sub(r'(import [^\n]+\n)', r'\1import EvmAsm.Codegen.Emit\n', t, count=1)
    return t

def check_file(path, funcs, rendered=None):
    """CI drift guard for one file. For each func, confirm:
      (a) the ACTUAL Lean-rendered string (`emitProgram <prog>`, obtained from
          the real elaborator via `lean_render`) assembles `.text`-identically
          to the saved original-asm fixture -- this is the authoritative
          binary-identity check and it exercises Lean's `emitInstr`, not
          py_emit;
      (b) the exact generated block is present verbatim in the Lean file (source
          drift guard);
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
        entry,renders,emitted,ok,la,lb=do_asm(asm)          # (c) py_emit pre-flight
        if not ok: problems.append(f"{fn}: py_emit render no longer assembles identically"); continue
        # (a) authoritative: real Lean render vs fixture
        if fn not in rendered:
            problems.append(f"{fn}: no Lean render captured"); continue
        real_ok,_,_=assemble_cmp(asm, rendered[fn])
        if not real_ok:
            problems.append(f"{fn}: LEAN-RENDERED string does NOT assemble identically to fixture "
                            f"(emitInstr/py_emit divergence or guest-binary change)"); continue
        # (b) source drift
        prog=lean_camel(entry)+'_prog'
        block=gen_lean(entry, renders, fn, prog).rstrip()
        if block not in text:
            problems.append(f"{fn}: generated block not found verbatim (source drift)")
    return problems

REPO=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCAN_DIRS=['EvmAsm/Codegen/Programs','EvmAsm/Codegen']

_CLS_DESC={
 'CONVERTED-CLEAN':'Parses to a `Program`; the `emitProgram` render assembles `.text`-identically to the original hand-written text. Directly landable.',
 'BLOCKED_ON_.6':'Contains `la <symbol>` scratch/global addressing or a cross-function `jal <callee>` — needs the authoritative linker-pinned address table (bead evm-asm-4ch8f.6).',
 'NEEDS-LI-EXPANSION':'Contains an `li rd, C` with C outside 12-bit signed range; a faithful 4-byte-per-`Instr` Program must emit the explicit `lui`/`addiw`/… expansion as separate `Instr`s (follow-up wave).',
 'CALLER-LOCAL-FRAGMENT':'Branches/jumps to a `.L` label owned by the caller, or has no own entry label — no independent ABI; needs extraction into a status-returning callable first.',
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
    for cls in ['CONVERTED-CLEAN','NEEDS-LI-EXPANSION','CALLER-LOCAL-FRAGMENT']:
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
                    entry,renders=convert(asm)
                except ConvError as e:
                    msg=str(e)
                    if 'BLOCKED_ON_.6' in msg: cls='BLOCKED_ON_.6'
                    elif 'NEEDS-LI-EXPANSION' in msg: cls='NEEDS-LI-EXPANSION'
                    elif 'unresolved branch/jump target' in msg:
                        tgt=msg.split("'")[1]
                        cls='CALLER-LOCAL-FRAGMENT' if tgt.startswith('.') else 'BLOCKED_ON_.6'
                    elif 'first line is not a label' in msg: cls='CALLER-LOCAL-FRAGMENT'
                    else: cls='UNPARSEABLE'
                    rows.append((rel,name,cls,0,msg[:70])); continue
                try:
                    ok=assemble_cmp(asm, emit_program_text(entry,asm))[0]
                except Exception as e:
                    rows.append((rel,name,'UNPARSEABLE',len(renders),str(e)[:60])); continue
                rows.append((rel,name,'CONVERTED-CLEAN' if ok else 'CMP-DIFFER',
                             len(renders),'' if ok else 'asm .text differs'))
    return rows

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('command', choices=['convert','check','emit-lean','rewrite','check-file','check-all','coverage'])
    ap.add_argument('--file', help='Lean source file')
    ap.add_argument('--func', help='<name>Function def')
    ap.add_argument('--funcs', help='comma-separated Function defs (rewrite/check-file)')
    ap.add_argument('--prog-name', help='program def name (default <camel>_prog)')
    args=ap.parse_args()
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
    entry, renders, emitted, ok, la, lb = do_one(args.file, args.func)
    if args.command=='check':
        print(f"{args.func}: entry={entry} n={len(renders)} "
              f"asm_cmp={'IDENTICAL' if ok else 'DIFFER'} ({la} vs {lb} bytes)")
        sys.exit(0 if ok else 1)
    if args.command=='emit-lean':
        prog=args.prog_name or (lean_camel(entry)+'_prog')
        print(gen_lean(entry, renders, args.func, prog))
    else:
        print(f"-- entry {entry}, {len(renders)} instrs, "
              f"asm_cmp={'OK' if ok else 'FAIL'}")
        print("\n".join(renders))

if __name__=='__main__': main()
