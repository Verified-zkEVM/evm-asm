/-
  EvmAsm.Rv64.SAsm.TriCmpStoreJoin

  The **three-outcome compare/store join** (bead evm-asm-4ch8f.38.2.2.3).

  `TwoBreakWritable` gives the two-outcome comparison shape (`u256_lt_be`):
  a scan loop whose iterations route through TWO break guards to TWO
  writable-output return tails.  Compare-against-modulus routines like
  `secf_cmp_p` need the THREE-outcome shape — a dual byte scan with two
  ORDERED mid-loop exits plus the exhausted-equality exit, all three
  reconverging at the shared `ret` through result-store tails writing
  three DISTINCT values:

  ```
  hdr:  beq  ctr, x0, .tailEq         -- exhaustion (all equal) → value v1
        <load a[i], b[i]>
        bltu tA, tB, .tailLt          -- a[i] < b[i]            → value v0
        bltu tB, tA, .tailGt          -- b[i] < a[i]            → value v2
        <advance> ; jal x0, hdr
  .tailLt:            sd x0, 0(out) ; li a0, 0 ; ret
  .tailEq: li rs, v1 ; sd rs, 0(out) ; li a0, 0 ; ret
  .tailGt: li rs, v2 ; sd rs, 0(out) ; li a0, 0 ; ret
  ```

  Everything is at `cpsTripleWithin` level (additive; no `Ast`/`Vc`
  changes), register/offset/value-agnostic.  Two pieces:

  * `liStoreRetTail_spec` — the value-loading writable-output return tail
    `LI rs, c ; SD rb, rs, ofs ; LI rd, c' ; ret`, proven ONCE,
    address-generically: it loads the tail's constant into the scratch
    register, stores it into the OWNED output dword cell `[rb + ofs]` and
    returns.  The address-generic form of what `u256_lt_be` proved inline
    per tail; the eq/gt tails instantiate it at their two distinct stored
    values (the lt tail stores the hardwired `x0` zero and is a plain
    `storeRetTail_spec`).

  * `triCmpStoreJoin_spec` — the three-outcome join station: TWO
    consecutive break guards (the ordered `bltu` pair) whose taken arms
    run RETURN TAILS reaching the shared `ret` with the loop's final post
    `Q` under the decided facts `condLt` / `condGt`, and whose common
    fall-through CONTINUES the iteration knowing `¬condLt ∧ ¬condGt`
    (byte equality, for the scan invariant).  Exactly two nested
    `breakStation_spec`s, packaged so a consumer supplies only the two
    branch specs and the three arms.

  The loop wrapper is unchanged: `twoBreakRetLoop_spec` is
  station-count-agnostic (each iteration is a single two-exit branch
  `hdr → {ret, hdr}` no matter how many break stations it nests), so the
  three-outcome loop reuses it as-is.

  Consumer: `secf_cmp_p` (`Codegen/Programs/Secp256k1FieldCmpPSAsm.lean`)
  — input bytes vs the read-only `globalConst secp256k1_p_be`, tails
  writing 0 / 1 / 2 for `< p` / `= p` / `> p`.
-/

import EvmAsm.Rv64.SAsm.TwoBreakWritable

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

-- ============================================================================
-- §1  The value-loading writable-output return tail
-- ============================================================================

/-- **The value-loading writable-output return tail**
    `LI rs, c ; SD rb, rs, ofs ; LI rd, cRes ; ret`: loads the tail's
    constant `c` into the scratch register `rs`, stores it into the OWNED
    output dword cell `[rb + ofs]`, loads the result register, and
    returns.  Address-, register- and value-agnostic — proven once; the
    distinct-value tails of a multi-outcome join instantiate it at their
    respective constants.  The `LI`-prefixed `storeRetTail_spec` (the
    post pins the output cell to the stored constant — no arbitrary
    write). -/
theorem liStoreRetTail_spec (cr : CodeReq) (addr ret : Word) (rb rs rd : Reg)
    (ofs : BitVec 12) (p a0Old c cRes : Word)
    (hrs : rs ≠ .x0) (hrd : rd ≠ .x0)
    (halign : (ret &&& ~~~(1 : Word)) = ret)
    (hli : ∀ a i, CodeReq.singleton addr (.LI rs c) a = some i →
      cr a = some i)
    (hsd : ∀ a i, CodeReq.singleton (addr + 4) (.SD rb rs ofs) a = some i →
      cr a = some i)
    (hliR : ∀ a i, CodeReq.singleton (addr + 8) (.LI rd cRes) a = some i →
      cr a = some i)
    (hret : ∀ a i, CodeReq.singleton (addr + 12) (.JALR .x0 .x1 0) a = some i →
      cr a = some i) :
    cpsTripleWithin 4 addr ret cr
      (regOwn rs ** (rb ↦ᵣ p) ** memOwn (p + signExtend12 ofs) **
        (rd ↦ᵣ a0Old) ** ((.x1 : Reg) ↦ᵣ ret))
      ((rs ↦ᵣ c) ** (rb ↦ᵣ p) ** ((p + signExtend12 ofs) ↦ₘ c) **
        (rd ↦ᵣ cRes) ** ((.x1 : Reg) ↦ᵣ ret)) := by
  have hLi := cpsTripleWithin_extend_code (hmono := hli)
    (h := li_spec_gen_own_within rs c addr hrs)
  have hTail := storeRetTail_spec cr (addr + 4) ret rb rs rd ofs p c a0Old cRes
    hrd halign hsd
    (by rw [BitVec.add_assoc, show ((4 : Word) + 4) = (8 : Word) from by decide]
        exact hliR)
    (by rw [BitVec.add_assoc, show ((4 : Word) + 8) = (12 : Word) from by decide]
        exact hret)
  have hLiF := cpsTripleWithin_frameR
    ((rb ↦ᵣ p) ** memOwn (p + signExtend12 ofs) **
      (rd ↦ᵣ a0Old) ** ((.x1 : Reg) ↦ᵣ ret))
    (by pcf) hLi
  have hc := cpsTripleWithin_seq_perm_same_cr
    (fun _ hp => by xperm_hyp hp) hLiF hTail
  exact cpsTripleWithin_weaken (fun _ hp => by xperm_hyp hp)
    (fun _ hq => by xperm_hyp hq) hc

-- ============================================================================
-- §2  The three-outcome join station
-- ============================================================================

/-- **The three-outcome compare/store join station.**  Two consecutive
    break guards inside a loop iteration — the ordered compare pair
    (`bltu a b ; bltu b a`): the FIRST guard's taken arm runs a return
    tail under the decided `condLt` (e.g. a `storeRetTail_spec`
    instance), the SECOND guard's taken arm runs a return tail under
    `condGt` (e.g. a `liStoreRetTail_spec` instance), and the common
    fall-through CONTINUES the iteration knowing `¬condLt` and `¬condGt`
    (for the ordered byte compare: equality, feeding the scan
    invariant).  Both tails reach the shared `ret` continuation with the
    loop's final post `Q`; the continuation may still break later or
    loop back to `hdr` with `I` — exactly the iteration shape
    `twoBreakRetLoop_spec` consumes.  Two nested `breakStation_spec`s,
    packaged. -/
theorem triCmpStoreJoin_spec {nA nB m : Nat}
    {addrA tgtLt addrB tgtGt fallB ret hdr : Word} {cr : CodeReq}
    {P QAT QAF PLt PMid QBT QBF PGt PEq Q I : Assertion}
    {condLt condGt : Prop}
    (hbrA : cpsBranchWithin nA addrA cr P tgtLt QAT addrB QAF)
    (hentAT : ∀ h, QAT h → (⌜condLt⌝ ** PLt) h)
    (hentAF : ∀ h, QAF h → (⌜¬ condLt⌝ ** PMid) h)
    (htailLt : condLt → cpsTripleWithin (nB + m) tgtLt ret cr PLt Q)
    (hbrB : ¬ condLt → cpsBranchWithin nB addrB cr PMid tgtGt QBT fallB QBF)
    (hentBT : ∀ h, QBT h → (⌜condGt⌝ ** PGt) h)
    (hentBF : ∀ h, QBF h → (⌜¬ condGt⌝ ** PEq) h)
    (htailGt : ¬ condLt → condGt → cpsTripleWithin m tgtGt ret cr PGt Q)
    (hcont : ¬ condLt → ¬ condGt →
      cpsBranchWithin m fallB cr PEq ret Q hdr I) :
    cpsBranchWithin (nA + (nB + m)) addrA cr P ret Q hdr I :=
  breakStation_spec hbrA hentAT hentAF htailLt
    (fun hnLt => breakStation_spec (hbrB hnLt) hentBT hentBF
      (htailGt hnLt) (hcont hnLt))

#print axioms liStoreRetTail_spec
#print axioms triCmpStoreJoin_spec

end EvmAsm.Rv64.SAsm
