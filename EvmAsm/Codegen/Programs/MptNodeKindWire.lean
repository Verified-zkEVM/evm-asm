/-
  Result → kindTag wiring for `mpt_node_kind` (#12027).

  The machine triple posts operational `MptNodeKindResult`. The pure bridge
  `mptNodeKindGuest_eq_kindTag` already exists and was unused. This file
  supplies the missing Result-to-WF link so a caller holding a WF `MptNode`
  and a **successful** operational result (`kind < 3`) can recover `kindTag`.

  Item-two verdict (#12027 milestone): does NOT need #11341 fuel-insensitivity.
  Under `MptNode.WF`, `rlpItem` is a top-level list of `.bytes` only (no nested
  RLP lists). Forward stack `listPayload_chain_of_decodeFully` +
  `rlpItemDecode_of_decodeAux_bytes` already covers that domain.

  Note on `kind = 3` arms (`countFail` / `badArity` / `nthFail` / `emptyPath` /
  bad-nibble `path`): pure `Failure` is slightly over-broad (a complete
  `Success` prefix to `listLen` also inhabits `Failure.walk` via the bound
  disjunct of `WalkFailure` at the exclusive end). The machine never posts
  those arms on WF input; the pure theorem therefore restricts to success
  tags `kind < 3`. Constructive existence of the correct tag is also
  provided so the tie is inhabited, not only unique.
-/

import EvmAsm.Codegen.Programs.MptNodeKindSpec
import EvmAsm.Codegen.Programs.RlpDecodeFullyForward
import EvmAsm.Codegen.Programs.RlpWalkDeterminism
import EvmAsm.Codegen.Programs.RlpListCountItemsSAsmBase
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinalsWalk
import EvmAsm.Evm64.MptAssertions

namespace EvmAsm.Codegen.MptNodeKindWire

open EvmAsm.Codegen.MptNodeKindSpec
open EvmAsm.Codegen.RlpListNthItemSAsm
open EvmAsm.Codegen.RlpListCountItemsSAsm (Success Result)
open EvmAsm.Codegen.BalAccountNonstorageFinalsSpec (rlpItemDecode_advance)
open EvmAsm.Rv64 EvmAsm.Rv64.RLP EvmAsm.EL.RLP
open EvmAsm.Evm64

/-! ## Item 1 — identify Result bytes with `n.rlp` under WF -/

/-- Structural item list of a node (matches `decodeFully` under WF). -/
def mptNodeItems : MptNode → List RLPItem
  | .leaf p v => [.bytes (hpEncode true p), .bytes v]
  | .extension p c => [.bytes (hpEncode false p), .bytes c]
  | .branch cs v => cs.map .bytes ++ [.bytes v]

/-- Every top-level item of a well-formed MPT node is a byte string. -/
theorem mptNodeItems_are_bytes (n : MptNode) :
    ∀ it ∈ mptNodeItems n, ∃ q, it = RLPItem.bytes q := by
  cases n with
  | leaf p v =>
    intro it hit
    simp [mptNodeItems] at hit
    rcases hit with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  | extension p c =>
    intro it hit
    simp [mptNodeItems] at hit
    rcases hit with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  | branch cs v =>
    intro it hit
    simp only [mptNodeItems, List.mem_append, List.mem_map, List.mem_singleton] at hit
    rcases hit with ⟨q, _, hq⟩ | h
    · exact ⟨q, hq.symm⟩
    · exact ⟨v, h⟩

/-- Decode of a WF node RLP is its structural item list. -/
theorem decodeFully_mptNode_rlp (n : MptNode) (hwf : n.WF) :
    decodeFully n.rlp = some (.list (mptNodeItems n)) := by
  cases n with
  | leaf p v => exact decodeFully_leaf_rlp p v hwf
  | extension p c => exact decodeFully_extension_rlp p c hwf
  | branch cs v => exact decodeFully_branch_rlp cs v hwf

/-- Item arity under WF. -/
def mptNodeArity : MptNode → Nat
  | .branch .. => 17
  | .leaf .. | .extension .. => 2

theorem mptNodeItems_length (n : MptNode) (hwf : n.WF) :
    (mptNodeItems n).length = mptNodeArity n := by
  cases n with
  | leaf p v => simp [mptNodeItems, mptNodeArity]
  | extension p c => simp [mptNodeItems, mptNodeArity]
  | branch cs v =>
    obtain ⟨hcs, -, -⟩ := hwf
    simp [mptNodeItems, mptNodeArity, hcs]

theorem mptNodeArity_lt_2_64 (n : MptNode) : mptNodeArity n < 2 ^ 64 := by
  cases n <;> simp only [mptNodeArity] <;> omega

theorem mptNodeArity_eq_kindTag_branch (n : MptNode) (hwf : n.WF)
    (h : mptNodeArity n = 17) : n.kindTag = 0 := by
  cases n with
  | branch cs v => rfl
  | leaf p v => simp [mptNodeArity] at h
  | extension p c => simp [mptNodeArity] at h

theorem mptNodeArity_eq_2_not_branch (n : MptNode) (h : mptNodeArity n = 2) :
    n.kindTag = 1 ∨ n.kindTag = 2 := by
  cases n with
  | branch cs v => simp [mptNodeArity] at h
  | leaf p v => exact Or.inr rfl
  | extension p c => exact Or.inl rfl

/-! ## Item 2 — Count `Success` from encode-domain decode (all-bytes children) -/

/-- Forward: a byte-string `DecodeChain` covering `[startOff, endOff)` yields a
    guest `StrictPrefix` of length `items.length` ending at `endOff`. -/
theorem strictPrefix_of_decodeChain_bytes
    (bytes : List Byte) (base : Word) (endOff : Nat)
    (hendOff : endOff ≤ bytes.length)
    (hover : base.toNat + bytes.length < 2 ^ 64) :
    ∀ (items : List RLPItem) (startOff : Nat),
      DecodeChain bytes startOff items endOff →
      (∀ it ∈ items, ∃ q, it = RLPItem.bytes q) →
      StrictPrefix bytes base (base + BitVec.ofNat 64 endOff)
        startOff items.length endOff := by
  intro items startOff
  have hfold :
      ∀ (rest : List RLPItem) (mid c : Nat),
        DecodeChain bytes mid rest endOff →
        (∀ it ∈ rest, ∃ q, it = RLPItem.bytes q) →
        StrictPrefix bytes base (base + BitVec.ofNat 64 endOff) startOff c mid →
        StrictPrefix bytes base (base + BitVec.ofNat 64 endOff)
          startOff (c + rest.length) endOff := by
    intro rest
    induction rest with
    | nil =>
      intro mid c hchain _ hpref
      have heq : mid = endOff := hchain
      subst heq
      simpa using hpref
    | cons it rs ih =>
      intro mid c hchain hbytes hpref
      obtain ⟨mid', hdec, hrest⟩ := hchain
      obtain ⟨q, hq⟩ := hbytes it (List.mem_cons_self ..)
      subst hq
      have hmid'le : mid' ≤ endOff :=
        DecodeChain.le_of_bytes rs mid' endOff hrest hendOff
          (fun x hx => hbytes x (List.mem_cons_of_mem _ hx))
      have hitem :=
        rlpItemDecode_of_decodeAux_bytes bytes base mid mid' endOff 0 q
          (hdec 0) hmid'le hendOff hover
      have hback :
          ((base + BitVec.ofNat 64 mid') - base).toNat = mid' :=
        sub_base_of_base_add (bound := bytes.length) (by omega) hover
      have hpref' :
          StrictPrefix bytes base (base + BitVec.ofNat 64 endOff)
            startOff (c + 1) mid' := by
        have h :=
          StrictPrefix.succ c mid (base + BitVec.ofNat 64 mid')
            (BitVec.ofNat 64 q.length) hpref hitem
        simpa [hback] using h
      have hfin := ih mid' (c + 1) hrest
        (fun x hx => hbytes x (List.mem_cons_of_mem _ hx)) hpref'
      have hlen : c + (RLPItem.bytes q :: rs).length = c + 1 + rs.length := by
        simp [List.length_cons]; omega
      rw [hlen]
      exact hfin
  intro hchain hbytes
  have h0 : StrictPrefix bytes base (base + BitVec.ofNat 64 endOff)
      startOff 0 startOff := StrictPrefix.zero
  have hfin := hfold items startOff 0 hchain hbytes h0
  simpa using hfin

/-- Count `Success` from a whole-buffer list decode of byte-string children. -/
theorem countSuccess_of_decodeFully_list
    (bytes : List Byte) (base : Word) (items : List RLPItem)
    (hdec : decodeFully bytes = some (.list items))
    (hbytes : ∀ it ∈ items, ∃ q, it = RLPItem.bytes q)
    (hover : base.toNat + bytes.length + 9 < 2 ^ 64) :
    Success bytes base bytes.length items.length := by
  obtain ⟨cursorOff, hpay, hchain⟩ :=
    listPayload_chain_of_decodeFully bytes base items hdec hbytes
  have hpref :=
    strictPrefix_of_decodeChain_bytes bytes base bytes.length (le_refl _)
      (by omega) items cursorOff hchain hbytes
  exact ⟨cursorOff, base + BitVec.ofNat 64 bytes.length, hpay, hpref⟩

/-- Count `Success` for a well-formed MPT node at the structural arity. -/
theorem countSuccess_of_mptNode
    (n : MptNode) (hwf : n.WF) (base : Word)
    (hover : base.toNat + n.rlp.length + 9 < 2 ^ 64) :
    Success n.rlp base n.rlp.length (mptNodeArity n) := by
  have hdec := decodeFully_mptNode_rlp n hwf
  have hlen := mptNodeItems_length n hwf
  have hs :=
    countSuccess_of_decodeFully_list n.rlp base (mptNodeItems n) hdec
      (mptNodeItems_are_bytes n) hover
  simpa [hlen] using hs

/-- Count `Result.ok` for a well-formed MPT node. -/
theorem countResult_ok_of_mptNode
    (n : MptNode) (hwf : n.WF) (base : Word)
    (hover : base.toNat + n.rlp.length + 9 < 2 ^ 64) :
    Result n.rlp base n.rlp.length (0 : Word)
      (BitVec.ofNat 64 (mptNodeArity n)) :=
  Result.ok (mptNodeArity n) (mptNodeArity_lt_2_64 n)
    (countSuccess_of_mptNode n hwf base hover)

/-! ## Uniqueness of complete count Success -/

/-- Peel the first item off a positive-length prefix (snoc-structure uncons). -/
theorem strictPrefix_cons {bytes : List (BitVec 8)} {base endPtr : Word}
    {startOff finalOff : Nat} :
    ∀ (n : Nat),
      StrictPrefix bytes base endPtr startOff (n + 1) finalOff →
      ∃ mid next len,
        rlpItemDecode bytes startOff (base + BitVec.ofNat 64 startOff)
          endPtr next len ∧
        mid = (next - base).toNat ∧
        StrictPrefix bytes base endPtr mid n finalOff := by
  intro n h
  generalize hc : n + 1 = c at h
  induction h generalizing n with
  | zero => exact False.elim (by omega)
  | succ count off next len hp hi ih =>
    have hcnt : count = n := by omega
    subst hcnt
    cases count with
    | zero =>
      cases hp
      refine ⟨(next - base).toNat, next, len, hi, rfl, ?_⟩
      exact StrictPrefix.zero
    | succ count' =>
      have ⟨mid, next0, len0, hitem0, hmid, hrest⟩ := ih count' rfl
      refine ⟨mid, next0, len0, hitem0, hmid, ?_⟩
      exact StrictPrefix.succ count' off next len hrest hi

/-- Two complete prefixes ending at the same exclusive end have equal counts. -/
theorem strictPrefix_count_unique {bytes : List (BitVec 8)} {base : Word}
    {endOff startOff : Nat}
    (hover : base.toNat + endOff + 9 < 2 ^ 64)
    (hstart : startOff ≤ endOff) :
    ∀ (c1 c2 : Nat),
      StrictPrefix bytes base (base + BitVec.ofNat 64 endOff) startOff c1 endOff →
      StrictPrefix bytes base (base + BitVec.ofNat 64 endOff) startOff c2 endOff →
      c1 = c2 := by
  intro c1
  induction c1 generalizing startOff with
  | zero =>
    intro c2 h1 h2
    cases h1
    cases c2 with
    | zero => cases h2; rfl
    | succ c2' =>
      obtain ⟨mid, next, len, hitem, hmid, -⟩ := strictPrefix_cons c2' h2
      have ha := rlpItemDecode_advance hitem hstart hover
      omega
  | succ c1 ih =>
    intro c2 h1 h2
    cases c2 with
    | zero =>
      cases h2
      obtain ⟨mid, next, len, hitem, hmid, -⟩ := strictPrefix_cons c1 h1
      have ha := rlpItemDecode_advance hitem hstart hover
      omega
    | succ c2' =>
      obtain ⟨mid1, n1, l1, hi1, hm1, hr1⟩ := strictPrefix_cons c1 h1
      obtain ⟨mid2, n2, l2, hi2, hm2, hr2⟩ := strictPrefix_cons c2' h2
      obtain ⟨rfl, -⟩ := rlpItemDecode_deterministic hi1 hi2
      have hmidEq : mid1 = mid2 := by rw [hm1, hm2]
      subst hmidEq
      have ha := rlpItemDecode_advance hi1 hstart hover
      have hcnt := ih (startOff := mid1) (by omega) c2' hr1 hr2
      exact congrArg Nat.succ hcnt

/-- Count Success determines the count. -/
theorem countSuccess_unique {bytes : List (BitVec 8)} {base : Word}
    {listLen c1 c2 : Nat}
    (hover : base.toNat + listLen + 9 < 2 ^ 64)
    (h1 : Success bytes base listLen c1)
    (h2 : Success bytes base listLen c2) :
    c1 = c2 := by
  obtain ⟨cur1, ep1, hlist1, hpref1⟩ := h1
  obtain ⟨cur2, ep2, hlist2, hpref2⟩ := h2
  obtain ⟨rfl, rfl⟩ := strictListPayload_deterministic hlist1 hlist2
  have hend : ep1 = base + BitVec.ofNat 64 listLen := hlist1.end_eq
  have hstart : cur1 ≤ listLen := hlist1.cursor_le
  rw [hend] at hpref1 hpref2
  exact strictPrefix_count_unique hover hstart c1 c2 hpref1 hpref2

/-- `BitVec.ofNat 64` is injective below `2^64`. -/
theorem ofNat64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

/-- Extract Success from a status-0 count `Result`. -/
theorem countResult_ok_success {bytes : List (BitVec 8)} {base : Word}
    {listLen : Nat} {result : Word}
    (h : Result bytes base listLen (0 : Word) result) :
    ∃ count : Nat, count < 2 ^ 64 ∧ result = BitVec.ofNat 64 count ∧
      Success bytes base listLen count := by
  cases h with
  | ok c hc hs => exact ⟨c, hc, rfl, hs⟩

/-- Specialize when the result word is a known `ofNat`. -/
theorem countResult_ok_count {bytes : List (BitVec 8)} {base : Word}
    {listLen count : Nat}
    (h : Result bytes base listLen (0 : Word) (BitVec.ofNat 64 count))
    (hc : count < 2 ^ 64) :
    Success bytes base listLen count := by
  obtain ⟨c, hc', hr, hs⟩ := countResult_ok_success h
  have heq : c = count := ofNat64_inj hc' hc hr.symm
  subst heq
  exact hs

/-! ## Item 3 — path first-byte content under WF (arity 2) -/

/-- Path bytes of a leaf/extension under WF. -/
def mptNodePath : MptNode → Option (List (BitVec 8))
  | .leaf p _ => some (hpEncode true p)
  | .extension p _ => some (hpEncode false p)
  | .branch .. => none

/-- Nth-item Success + content for the compact path (index 0) of a 2-ary node. -/
theorem path_nth_success_of_mptNode
    (n : MptNode) (hwf : n.WF) (base : Word)
    (hary : mptNodeArity n = 2)
    (hover : base.toNat + n.rlp.length + 9 < 2 ^ 64) :
    ∃ (path : List (BitVec 8)) (offset : Word),
      path ≠ [] ∧
      mptNodePath n = some path ∧
      RlpListNthItemSAsm.Success n.rlp base n.rlp.length 0 offset
        (BitVec.ofNat 64 path.length) ∧
      (n.rlp.drop offset.toNat).take path.length = path ∧
      offset.toNat + path.length ≤ n.rlp.length := by
  have hdec := decodeFully_mptNode_rlp n hwf
  have hbytes := mptNodeItems_are_bytes n
  match n, hwf, hary, hdec, hbytes, hover with
  | .branch cs v, _, hary, _, _, _ =>
    simp [mptNodeArity] at hary
  | .leaf p v, hwf, hary, hdec, hbytes, hover =>
    set path := hpEncode true p
    have hne : path ≠ [] := by
      obtain ⟨hp, -, -⟩ := hwf
      obtain ⟨b0, tl, heq, -⟩ := hpEncodeAux_head_div 2 (by omega) p hp
      intro hnil
      simp only [path, show hpEncode true p = hpEncodeAux 2 p from rfl, heq] at hnil
      cases hnil
    have hidx : (mptNodeItems (.leaf p v))[0]? = some (.bytes path) := by
      simp [mptNodeItems, path]
    obtain ⟨offset, hsucc, hcont, hle⟩ :=
      success_content_of_decodeFully_list (MptNode.leaf p v).rlp base
        (mptNodeItems (.leaf p v)) 0 path hdec hbytes hidx (by omega)
    exact ⟨path, offset, hne, rfl, hsucc, hcont, hle⟩
  | .extension p c, hwf, hary, hdec, hbytes, hover =>
    set path := hpEncode false p
    have hne : path ≠ [] := by
      obtain ⟨hp, -, -⟩ := hwf
      obtain ⟨b0, tl, heq, -⟩ := hpEncodeAux_head_div 0 (by omega) p hp
      intro hnil
      simp only [path, show hpEncode false p = hpEncodeAux 0 p from rfl, heq] at hnil
      cases hnil
    have hidx : (mptNodeItems (.extension p c))[0]? = some (.bytes path) := by
      simp [mptNodeItems, path]
    obtain ⟨offset, hsucc, hcont, hle⟩ :=
      success_content_of_decodeFully_list (MptNode.extension p c).rlp base
        (mptNodeItems (.extension p c)) 0 path hdec hbytes hidx (by omega)
    exact ⟨path, offset, hne, rfl, hsucc, hcont, hle⟩

/-- High-nibble of the path head under WF equals the structural kind tag. -/
theorem path_head_hpKind_eq_kindTag
    (n : MptNode) (hwf : n.WF) (hary : mptNodeArity n = 2)
    (path : List (BitVec 8)) (b0 : BitVec 8)
    (hp : mptNodePath n = some path) (hhead : path.head? = some b0) :
    hpKind b0 = n.kindTag := by
  match n, hwf, hary, hp with
  | .branch cs v, _, hary, _ => simp [mptNodeArity] at hary
  | .leaf p v, hwf, _, hp =>
    obtain ⟨hp', -, -⟩ := hwf
    obtain ⟨b0', tl, heq, hdiv⟩ := hpEncodeAux_head_div 2 (by omega) p hp'
    simp only [mptNodePath, Option.some.injEq] at hp
    have hpath : path = hpEncode true p := hp.symm
    have hb0 : b0' = b0 := by
      rw [hpath, show hpEncode true p = hpEncodeAux 2 p from rfl, heq] at hhead
      simpa [List.head?] using hhead
    subst hb0
    unfold hpKind
    have hmod : p.length % 2 < 2 := Nat.mod_lt _ (by decide)
    have hge : ¬ b0'.toNat / 16 < 2 := by omega
    have hlt : b0'.toNat / 16 < 4 := by omega
    simp [hge, hlt, MptNode.kindTag]
  | .extension p c, hwf, _, hp =>
    obtain ⟨hp', -, -⟩ := hwf
    obtain ⟨b0', tl, heq, hdiv⟩ := hpEncodeAux_head_div 0 (by omega) p hp'
    simp only [mptNodePath, Option.some.injEq] at hp
    have hpath : path = hpEncode false p := hp.symm
    have hb0 : b0' = b0 := by
      rw [hpath, show hpEncode false p = hpEncodeAux 0 p from rfl, heq] at hhead
      simpa [List.head?] using hhead
    subst hb0
    unfold hpKind
    have hmod : p.length % 2 < 2 := Nat.mod_lt _ (by decide)
    have hlt : b0'.toNat / 16 < 2 := by omega
    simp [hlt, MptNode.kindTag]

/-- Read the first path byte from nth Success content. -/
theorem path_byte_of_content {bytes : List (BitVec 8)} {offset : Word}
    {path : List (BitVec 8)} {b0 : BitVec 8}
    (hcont : (bytes.drop offset.toNat).take path.length = path)
    (hhead : path.head? = some b0)
    (hne : path ≠ []) :
    bytes[offset.toNat]? = some b0 := by
  obtain ⟨x, xs, rfl⟩ : ∃ x xs, path = x :: xs := by
    cases path with
    | nil => exact False.elim (hne rfl)
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hx : x = b0 := by simpa [List.head?] using hhead
  -- take (1+xs.length) of drop = x::xs ⇒ drop is x::_
  have ht : (bytes.drop offset.toNat).take (xs.length + 1) = x :: xs := by
    simpa [List.length_cons] using hcont
  cases hdrop : bytes.drop offset.toNat with
  | nil =>
    have := congrArg List.length ht
    simp [hdrop] at this
  | cons y ys =>
    simp [hdrop] at ht
    have hyx : y = x := ht.1
    have hbytes0 : bytes[offset.toNat]? = some y := by
      have : bytes[offset.toNat]? = (bytes.drop offset.toNat)[0]? := by
        rw [List.getElem?_drop, Nat.add_zero]
      rw [this, hdrop]; rfl
    rw [hbytes0, hyx, hx]

/-! ## Item 4 — WF case split: Result → kindTag (success arms) -/

/-- ⭐ Main wiring: a successful operational kind (`kind < 3`) equals `kindTag`.

    Fail arms (`kind = 3`) are excluded: pure `Failure` is over-broad at the
    exclusive list end (see file header). Machine consumers only need the
    success tags the guest returns on WF input. -/
theorem mptNodeKindResult_eq_kindTag
    (n : MptNode) (hwf : n.WF) (base oldCount oldOff oldLen : Word) (kind : Nat)
    (hres : MptNodeKindResult n.rlp base n.rlp.length oldCount oldOff oldLen kind)
    (hover : base.toNat + n.rlp.length + 9 < 2 ^ 64)
    (hok : kind < 3) :
    kind = n.kindTag := by
  cases hres with
  | countFail h => exact False.elim (Nat.lt_irrefl _ hok)
  | badArity c hc h hne17 hne2 => exact False.elim (Nat.lt_irrefl _ hok)
  | nthFail hc hn => exact False.elim (Nat.lt_irrefl _ hok)
  | emptyPath off hc hn => exact False.elim (Nat.lt_irrefl _ hok)
  | branch h =>
    -- kind = 0
    have hs17 : Success n.rlp base n.rlp.length 17 :=
      countResult_ok_count h (by omega)
    have hsN := countSuccess_of_mptNode n hwf base hover
    have hary : 17 = mptNodeArity n := countSuccess_unique hover hs17 hsN
    exact (mptNodeArity_eq_kindTag_branch n hwf hary.symm).symm
  | path off len b kind' hc hn hlen hb hk =>
    -- kind = kind' = hpKind b; need = kindTag
    have hs2 : Success n.rlp base n.rlp.length 2 :=
      countResult_ok_count hc (by omega)
    have hsN := countSuccess_of_mptNode n hwf base hover
    have hary : 2 = mptNodeArity n := countSuccess_unique hover hs2 hsN
    cases hn with
    | ok offset len' hsucc =>
      obtain ⟨path, offset', hne, hpath, hsucc', hcont, hle⟩ :=
        path_nth_success_of_mptNode n hwf base hary.symm hover
      have hdet := success_deterministic hsucc hsucc'
      -- path head is b via content at `off`
      have hc' : (n.rlp.drop off.toNat).take path.length = path := by
        rw [hdet.1]; exact hcont
      have hb0 : path.head? = some b := by
        obtain ⟨x, xs, rfl⟩ : ∃ x xs, path = x :: xs := by
          cases path with
          | nil => exact False.elim (hne rfl)
          | cons x xs => exact ⟨x, xs, rfl⟩
        have ht : (n.rlp.drop off.toNat).take (xs.length + 1) = x :: xs := by
          simpa [List.length_cons] using hc'
        cases hdrop : n.rlp.drop off.toNat with
        | nil =>
          have := congrArg List.length ht
          simp [hdrop] at this
        | cons y ys =>
          simp [hdrop] at ht
          have hyx : y = x := ht.1
          have hyb : y = b := by
            have hbytes0 : n.rlp[off.toNat]? = some y := by
              have : n.rlp[off.toNat]? = (n.rlp.drop off.toNat)[0]? := by
                rw [List.getElem?_drop, Nat.add_zero]
              rw [this, hdrop]; rfl
            exact Option.some.inj (hbytes0.symm.trans hb)
          have : x = b := hyx.symm.trans hyb
          simp [List.head?, this]
      have hkind := path_head_hpKind_eq_kindTag n hwf hary.symm path b hpath hb0
      rw [hk]
      exact hkind

private theorem path_head_exists {path : List (BitVec 8)} (hne : path ≠ []) :
    ∃ b0, path.head? = some b0 := by
  cases path with
  | nil => exact False.elim (hne rfl)
  | cons b t => exact ⟨b, rfl⟩

private theorem path_len_pos_word {path : List (BitVec 8)} (hne : path ≠ [])
    (hbound : path.length < 2 ^ 64) :
    0 < (BitVec.ofNat 64 path.length).toNat := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
  exact List.length_pos_of_ne_nil hne

/-- Constructive: the correct operational result is inhabited under WF. -/
theorem mptNodeKindResult_exists_kindTag
    (n : MptNode) (hwf : n.WF) (base oldCount oldOff oldLen : Word)
    (hover : base.toNat + n.rlp.length + 9 < 2 ^ 64) :
    MptNodeKindResult n.rlp base n.rlp.length oldCount oldOff oldLen n.kindTag := by
  have hok := countResult_ok_of_mptNode n hwf base hover
  match n, hwf, hover, hok with
  | .branch cs v, hwf, hover, hok =>
    have hary : mptNodeArity (.branch cs v) = 17 := by simp [mptNodeArity]
    have hres : Result (MptNode.branch cs v).rlp base
        (MptNode.branch cs v).rlp.length (0 : Word) (BitVec.ofNat 64 17) := by
      simpa [hary] using hok
    exact MptNodeKindResult.branch hres
  | .leaf p v, hwf, hover, hok =>
    have hary : mptNodeArity (.leaf p v) = 2 := by simp [mptNodeArity]
    have hc : Result (MptNode.leaf p v).rlp base (MptNode.leaf p v).rlp.length
        (0 : Word) (BitVec.ofNat 64 2) := by
      simpa [hary] using hok
    obtain ⟨path, offset, hne, hpath, hsucc, hcont, hle⟩ :=
      path_nth_success_of_mptNode (.leaf p v) hwf base hary hover
    have hn : RlpListNthItemSAsm.Result (MptNode.leaf p v).rlp base
        (MptNode.leaf p v).rlp.length 0 oldOff oldLen
        (0 : Word) offset (BitVec.ofNat 64 path.length) :=
      RlpListNthItemSAsm.Result.ok offset (BitVec.ofNat 64 path.length) hsucc
    obtain ⟨b0, hb0⟩ := path_head_exists hne
    have hrlp := (MptNode.leaf p v).rlp_length_lt hwf
    have hlen := path_len_pos_word hne (by omega)
    have hb : (MptNode.leaf p v).rlp[offset.toNat]? = some b0 :=
      path_byte_of_content hcont hb0 hne
    refine MptNodeKindResult.path offset (BitVec.ofNat 64 path.length) b0
      (MptNode.leaf p v).kindTag hc hn hlen hb ?_
    exact (path_head_hpKind_eq_kindTag (.leaf p v) hwf hary path b0 hpath hb0).symm
  | .extension p c, hwf, hover, hok =>
    have hary : mptNodeArity (.extension p c) = 2 := by simp [mptNodeArity]
    have hc : Result (MptNode.extension p c).rlp base
        (MptNode.extension p c).rlp.length (0 : Word) (BitVec.ofNat 64 2) := by
      simpa [hary] using hok
    obtain ⟨path, offset, hne, hpath, hsucc, hcont, hle⟩ :=
      path_nth_success_of_mptNode (.extension p c) hwf base hary hover
    have hn : RlpListNthItemSAsm.Result (MptNode.extension p c).rlp base
        (MptNode.extension p c).rlp.length 0 oldOff oldLen
        (0 : Word) offset (BitVec.ofNat 64 path.length) :=
      RlpListNthItemSAsm.Result.ok offset (BitVec.ofNat 64 path.length) hsucc
    obtain ⟨b0, hb0⟩ := path_head_exists hne
    have hrlp := (MptNode.extension p c).rlp_length_lt hwf
    have hlen := path_len_pos_word hne (by omega)
    have hb : (MptNode.extension p c).rlp[offset.toNat]? = some b0 :=
      path_byte_of_content hcont hb0 hne
    refine MptNodeKindResult.path offset (BitVec.ofNat 64 path.length) b0
      (MptNode.extension p c).kindTag hc hn hlen hb ?_
    exact (path_head_hpKind_eq_kindTag (.extension p c) hwf hary path b0 hpath hb0).symm

end EvmAsm.Codegen.MptNodeKindWire
