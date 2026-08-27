/-
# Equal-route shape adapter for the K73 Route-B contract (#12346 residual 2b)

`k73_equal_route_spec_within` (`EvmAsm.Codegen.HeaderBaseFeeSpec`) is a
premise-free whole-routine triple covering the linked equal route of the
emitted `eip1559_calc_base_fee_per_gas` (used == target, which copies the
parent-fee bytes into the output window).  This file instantiates it at
the wrapper's vocabulary and converts the result pointwise into exactly
the SUCCESS ARM of the revised wrapper premise
`k73RouteBCallPost` — certifying that the repaired #12346-residual-2b
contract is discharge-able, not merely well-typed.

Atom mapping (wrapper name := source name):
* wrapper `spH` := their `sp0`; wrapper `spK` := their `spH`
  (the frame-offset hypotheses coincide: `spK = spH + signExtend12 (-56)`);
* `raIn := H + 40`, `v8 := headerPtr`, `v18-slot := old18`,
  `basePtr := parentPtr`, `outPtr := Expected`;
* equal-route guard `gasUsed = gasLimit >>> 1`.

Post conversion weakens the three source pins (`x10 ↦ 0`, `x11 ↦ gasUsed`,
`x5 ↦ packBytes …`) to `regOwn`s and casts the copied window through two
lemmas: the copy overwrites all four dwords so `k73CopyOut src out = src`
for length-32 lists, and at the guard the written image reduces to the
parent bytes (`k73_fixed_bytes_repr` roundtrip).
-/

import EvmAsm.Codegen.Programs.HeaderBaseFeeSpec
import EvmAsm.Codegen.Programs.K73Arithmetic
import EvmAsm.Codegen.Programs.HeaderValidateBaseFeeSpecCore
import EvmAsm.Rv64.MemRegionWriteWide
import EvmAsm.Rv64.Tactics.XPermCert

namespace EvmAsm.Codegen.HeaderValidateBaseFeeCompositionEqualRoute

open EvmAsm.Rv64 EvmAsm.Rv64.SAsm
open EvmAsm.Codegen.HeaderBaseFeeSpec hiding K73
open EvmAsm.Codegen.HeaderValidateBaseFeeSpec
open EvmAsm.Stateless.SpecRef

/-- A full dword paste is byte-transparent: the little-endian expansion of a
    packed word reproduces an 8-byte chunk exactly. -/
theorem dwordBytes_packBytes_eq_self {c : List (BitVec 8)} (hlen : c.length = 8) :
    dwordBytes (packBytes c) = c := by
  apply List.ext_get
  · simp [dwordBytes, hlen]
  · intro n hn1 hn2
    have hn8 : n < 8 := by simpa [dwordBytes] using hn1
    interval_cases n <;> simp [dwordBytes, hlen, extractByte_packBytes]

private theorem take_succ_set {α : Type} (bs : List α) (b : α) (i : Nat)
    (h : i < bs.length) :
    (bs.take (i + 1)).set i b = bs.take i ++ [b] := by
  have hle : (List.take i bs).length ≤ i := by simp
  rw [List.take_add_one, List.getElem?_eq_getElem h,
    List.set_append_right (s := List.take i bs) i b hle]
  have hlt : (List.take i bs).length = min i bs.length := List.length_take
  have heq : (List.take i bs).length = i := by omega
  rw [heq]
  simp

/-- Pasting `ns` into `bs` at offset `i` splices prefix/chunk/suffix:
    prefix unchanged, pasted chunk whole, suffix after the chunk. -/
theorem win8_splice {bs : List (BitVec 8)} (ns : List (BitVec 8)) (i : Nat)
    (h : i + ns.length ≤ bs.length) :
    setBytes bs i ns = bs.take i ++ ns ++ bs.drop (i + ns.length) := by
  induction ns generalizing bs i with
  | nil => simp
  | cons b rest ih =>
    have hs : (bs.set i b).length = bs.length := List.length_set
    have h' := h
    simp only [List.length_cons] at h'
    have hb : i < bs.length := by omega
    have hle : (List.take i bs).length ≤ i := by simp
    have hlt : (List.take i bs).length = min i bs.length := List.length_take
    have heq : (List.take i bs).length = i := by omega
    have key := @ih (bs.set i b) (i + 1) (by rw [hs]; omega)
    rw [setBytes_cons, key, List.take_set, take_succ_set _ _ _ hb,
      List.drop_set, if_pos (by omega)]
    have hsimp : i + 1 + rest.length = i + (rest.length + 1) := by omega
    rw [hsimp]
    simp

/-- One 8-byte paste over a `(pre ++ suf)` splice keeps the prefix and the
    first 8 bytes of the suffix, dropping exactly those bytes of the suffix. -/
private theorem paste_boundary (pre suf c : List (BitVec 8)) (m : Nat)
    (hp : pre.length = m) (hc : c.length = 8)
    (hb : m + 8 ≤ pre.length + suf.length) :
    setBytes (pre ++ suf) m c = pre ++ c ++ suf.drop 8 := by
  have hg : m + c.length ≤ (pre ++ suf).length := by
    simp only [List.length_append, hp]; omega
  rw [win8_splice _ m hg,
    List.take_append_of_le_length (show m ≤ pre.length from hp ▸ le_refl m),
    show List.take m pre = pre from by simp [hp]]
  have hmc : m + c.length = m + 8 := by omega
  have hple : pre.length ≤ m + 8 := by omega
  rw [hmc, List.drop_append]
  rw [show List.drop (m + 8) pre = [] from List.drop_eq_nil_of_le hple, hp]
  simp

/-- Four whole-width pastes at offsets 0/8/16/24 over a 32-byte destination
    produce exactly the four chunks concatenated. -/
private theorem k73_splice4 (dst c0 c1 c2 c3 : List (BitVec 8))
    (hdst : dst.length = 32)
    (hl0 : c0.length = 8) (hl1 : c1.length = 8) (hl2 : c2.length = 8)
    (hl3 : c3.length = 8) :
    setBytes (setBytes (setBytes (setBytes dst 0 c0) 8 c1) 16 c2) 24 c3
      = c0 ++ c1 ++ c2 ++ c3 := by
  have s0 : setBytes dst 0 c0 = c0 ++ dst.drop 8 := by
    rw [win8_splice _ 0 (by simp [hdst, hl0]), hl0]; simp
  rw [s0]
  have hdn2 : List.drop 8 (List.drop 8 dst) = dst.drop 16 := List.drop_drop
  have hpb2 := paste_boundary (pre := c0) (suf := dst.drop 8) c1 8 hl0 hl1
    (by rw [hl0]; simp only [List.length_drop]; omega)
  rw [hpb2, hdn2]
  have hdn3 : List.drop 8 (List.drop 16 dst) = dst.drop 24 := by rw [List.drop_drop]
  have hpc : ((c0 ++ c1).length = 16) := by
    simp only [List.length_append, hl0, hl1]
  have hpb3 := paste_boundary (pre := c0 ++ c1) (suf := dst.drop 16) c2 16 hpc hl2
    (by rw [hpc]; simp only [List.length_drop]; omega)
  rw [hpb3, hdn3]
  have hdn4 : List.drop 8 (List.drop 24 dst) = dst.drop 32 := by rw [List.drop_drop]
  have hpd : ((c0 ++ c1 ++ c2).length = 24) := by
    simp only [List.length_append, List.length_append, hl0, hl1, hl2]
  have hpb4 := paste_boundary (pre := c0 ++ c1 ++ c2) (suf := dst.drop 24) c3 24 hpd hl3
    (by rw [hpd]; simp only [List.length_drop]; omega)
  rw [hpb4, hdn4,
    show List.drop 32 dst = [] from
      List.drop_eq_nil_of_le (show dst.length ≤ 32 from by simp [hdst])]
  simp

/-- The four equal-route source chunks concatenate back to the source. -/
private theorem k73_chunks_eq_self {src : List (BitVec 8)}
    (hsrc : src.length = 32) :
    (src.drop 0).take 8 ++ (src.drop 8).take 8 ++ (src.drop 16).take 8
      ++ (src.drop 24).take 8 = src := by
  have h32 : (src.drop 32) = [] :=
    List.drop_eq_nil_of_le (by simp [hsrc])
  have hd8 : (src.drop 8).drop 8 = src.drop 16 := List.drop_drop
  have hd16 : (src.drop 16).drop 8 = src.drop 24 := List.drop_drop
  have hd24 : (src.drop 24).drop 8 = [] := by rw [List.drop_drop]; exact h32
  have q1 := List.take_append_drop 8 src
  have q2 := List.take_append_drop 8 (src.drop 8)
  have q3 := List.take_append_drop 8 (src.drop 16)
  have q4 := List.take_append_drop 8 (src.drop 24)
  rw [hd8] at q2
  rw [hd16] at q3
  rw [hd24] at q4
  rw [← q2] at q1
  rw [← q3] at q1
  rw [← q4] at q1
  rw [List.append_nil] at q1
  simp only [List.drop_zero]
  rw [List.append_assoc, List.append_assoc]
  exact q1

/-- L1 for the Route-B composition (#12346 residual 2b): the equal route's
    four-dword copy output is byte-identical to the source when both windows
    are 32 bytes.  The existing `k73_equal_copy_spec_within` proves this only
    in existence form wrapped inside a triple postcondition - no reusable
    list-level lemma exists there, hence this fresh construction. -/
theorem k73_copyOut_eq_src {src out : List (BitVec 8)}
    (hsrc : src.length = 32) (_hout : out.length = 32) :
    k73CopyOut src out = src := by
  unfold k73CopyOut
  have l0 : ((src.drop 0).take 8).length = 8 := by simp; omega
  have l1 : ((src.drop 8).take 8).length = 8 := by simp; omega
  have l2 : ((src.drop 16).take 8).length = 8 := by simp; omega
  have l3 : ((src.drop 24).take 8).length = 8 := by simp; omega
  rw [dwordBytes_packBytes_eq_self (c := (src.drop 0).take 8) l0,
      dwordBytes_packBytes_eq_self (c := (src.drop 8).take 8) l1,
      dwordBytes_packBytes_eq_self (c := (src.drop 16).take 8) l2,
      dwordBytes_packBytes_eq_self (c := (src.drop 24).take 8) l3]
  exact Eq.trans (k73_splice4 out ((src.drop 0).take 8) ((src.drop 8).take 8)
    ((src.drop 16).take 8) ((src.drop 24).take 8) _hout l0 l1 l2 l3)
    (k73_chunks_eq_self hsrc)

/-- The equal-route written image is the entry content: with
    `gasUsed = gasLimit >>> 1` the recurrence's equal arm fires and returns
    the parent fee encoding, which for a 32-byte list is the list itself. -/
theorem hvbfWrittenImage_eq_self (gl gu : Word) {pb : List (BitVec 8)}
    (heqWord : gu = gl >>> 1) (hlen32 : pb.length = 32) :
    hvbfWrittenImage gl gu pb = pb := by
  have hguard : gu.toNat = gl.toNat / 2 := by rw [heqWord]; rfl
  have hrw : baseFeeRecurrenceWide gu.toNat (gl.toNat / 2) (bytesBEtoNat pb)
      = bytesBEtoNat pb := by
    rw [baseFeeRecurrenceWide, if_pos (by simp [hguard])]
  show natToBytesBE 32 (baseFeeRecurrenceWide gu.toNat (gl.toNat / 2) (bytesBEtoNat pb)) = pb
  rw [hrw]
  exact k73_fixed_bytes_repr pb hlen32

/-- Congruence for sepConj holds: pointwise implications on both factors
    lift to an implication of the conjunction (pair-rebuild idiom). -/
private theorem sep_pair_congr {A A' B B' : Assertion}
    (hA : ∀ q, A q → A' q) (hB : ∀ q, B q → B' q) :
    ∀ q, ((A ** B) q) → ((A' ** B' ) q) :=
  fun _ hp =>
    let ⟨h1, h2, hd, hunion, hl, hr⟩ := hp
    ⟨h1, h2, hd, hunion, hA _ hl, hB _ hr⟩

/-- A register pin entails ownership of that register (toy pair-lift). -/
private theorem sep_pin_lift {r v Z} :
    ∀ q : PartialState, ((r ↦ᵣ v) ** Z) q → ((regOwn r) ** Z) q :=
  fun _ hp =>
    let ⟨h1, h2, hd, hunion, hl, hr⟩ := hp
    ⟨h1, h2, hd, hunion, regIs_implies_regOwn (r := r) (v := v) _ hl, hr⟩

/-- Pointwise cast of the Expected-window list argument inside a hold. -/
private theorem sep_br_cast {le le' Z} (heq : le = le') :
    ∀ q : PartialState,
      ((bytesRegion Expected le ** Z) q) → ((bytesRegion Expected le' ** Z) q) :=
  fun _ hp => heq ▸ hp

/-- Pushes a hold-transformer one level under an unchanged prefix factor,
    enabling position-addressed lifts along a right-nested chain. -/
private theorem under_id {P P' B : Assertion} (hT : ∀ q, P q → P' q) :
    ∀ q, ((B ** P) q) → ((B ** P') q) :=
  fun q hp => sep_pair_congr (fun _ h => h) hT q hp

/-- The piggyback assertion carried through the source theorem's ambient
`F` slot (top-level def, NOT a body-local let: certificate tactics such as
`xperm_cert_eq` fail on let-zeta free variables). -/
private def k73_piggyback (spH old8 headerPtr : Word)
    (headerBytes : List (BitVec 8)) (F : Assertion) : Assertion :=
  frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
    bytesRegion headerPtr headerBytes ** F

/-- Equal-route shape adapter (#12346 residual 2b): the wrapper vocabulary
    instantiation of the premise-free equal-route triple
    `k73_equal_route_spec_within` yields EXACTLY the revised wrapper
    premise's success arm.  Guards match the wrapper's: `gasUsed =
    gasLimit >>> 1`, both byte lists length 32, aligned entry link fixed at
    the callsite `H + 40`.  This certifies the repaired Route-B contract is
    discharge-able, not merely well-typed.

    Proof notes: the source theorem's assertion parameter is set to the
    piggyback carrying the two atoms its pre/post omit but ours include
    (`frameSlotsSaved hvbfFrame …`, `bytesRegion headerPtr headerBytes`) —
    after that the PRE sides are the same atom multiset, so the premise-side
    conversion is an ASSERTION EQUALITY (`dsimp` + `xperm`), not an
    entailment; the return side lifts five status/data pins to ownerships
    and casts the window image. -/
theorem k73_equal_route_adapter {cr : CodeReq}
    (spH spK old8 headerPtr gasLimit gasUsed parentPtr : Word)
    (v9 old18 v19 v20 : Word)
    (parentBytes expectedBytes headerBytes : List (BitVec 8)) (F : Assertion)
    (hspK : spK = spH + signExtend12 (-56 : BitVec 12))
    (heqWord : gasUsed = gasLimit >>> 1)
    (hsrc : parentBytes.length = 32) (hout : expectedBytes.length = 32)
    (_hret : ((H + 40 : Word) &&& ~~~1) = H + 40)
    (hF : F.pcFree)
    (hk73Mono : ∀ a i, wholeCode a = some i → cr a = some i) :
    cpsTripleWithin 29 K73 (H + 40) cr
      ((.x1 ↦ᵣ (H + 40)) **
        k73PreRest spH spK headerPtr v9 old18 v19 v20 gasLimit gasUsed parentPtr
          parentBytes expectedBytes headerBytes (H + 40) old8 F)
      ((.x1 ↦ᵣ (H + 40)) **
        k73RouteBCallPost spH spK (H + 40) old8 headerPtr v9 old18 (gasLimit >>> 1)
          v19 v20 gasUsed gasLimit parentPtr parentBytes headerBytes F) := by
  have hGF : (k73_piggyback spH old8 headerPtr headerBytes F).pcFree := by
    pcf; exact hF
  have hsrc0 := k73_equal_route_spec_within (sp0 := spH) (spH := spK) (H + 40)
    gasLimit gasUsed parentPtr Expected (gasLimit >>> 1) headerPtr
    v9 old18 v19 v20 parentBytes expectedBytes
    (k73_piggyback spH old8 headerPtr headerBytes F)
    hspK rfl heqWord hsrc hout rfl hGF
  have hcr := cpsTripleWithin_extend_code hk73Mono hsrc0
  refine cpsTripleWithin_weaken (fun s hp => ?_) (fun s hq => ?_) hcr
  · have hpreEq :
        ((.x1 ↦ᵣ (H + 40)) ** k73PreRest spH spK headerPtr v9 old18 v19 v20
            gasLimit gasUsed parentPtr parentBytes expectedBytes headerBytes
            (H + 40) old8 F) =
          k73HeadPre spH spK (H + 40) gasLimit gasUsed parentPtr Expected
            headerPtr v9 old18 v19 v20 parentBytes expectedBytes
            (k73_piggyback spH old8 headerPtr headerBytes F) := by
      dsimp only [k73HeadPre, k73PreRest, k73_piggyback]
      xperm
    rw [hpreEq] at hp
    exact hp
  · show ((.x1 ↦ᵣ (H + 40)) ** k73RouteBCallPost spH spK (H + 40) old8 headerPtr
        v9 old18 (gasLimit >>> 1) v19 v20 gasUsed gasLimit parentPtr parentBytes
        headerBytes F) s
    have hw := hvbfWrittenImage_eq_self gasLimit gasUsed heqWord hsrc
    have hwin : k73CopyOut parentBytes expectedBytes
        = hvbfWrittenImage gasLimit gasUsed parentBytes := by
      rw [k73_copyOut_eq_src hsrc hout, hw]
    -- Bring the source post's x1 pin to the front (legal permutation).
    rw [sepConj_left_comm'
      (P := (.x2 ↦ᵣ spH)) (Q := (.x1 ↦ᵣ (H + 40)))
      (R := (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) **
        (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ 0) ** (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ parentPtr) **
        (.x13 ↦ᵣ Expected) ** (.x0 ↦ᵣ 0) **
        (.x5 ↦ᵣ packBytes ((parentBytes.drop 24).take 8)) **
        regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
        regOwn .x31 ** frameSlotsSaved k73Frame spK
          (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
        bytesRegion parentPtr parentBytes **
        bytesRegion Expected (k73CopyOut parentBytes expectedBytes) **
        k73_piggyback spH old8 headerPtr headerBytes F)] at hq
    obtain ⟨sa, sb, had, hud, hx1g, hbig⟩ := hq
    refine ⟨sa, sb, had, hud, hx1g, ?_⟩
    dsimp only [k73RouteBCallPost]
    refine Or.inl ?_
    show k73PostOwn spH spK headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed
      parentPtr parentBytes (hvbfWrittenImage gasLimit gasUsed parentBytes)
      headerBytes (H + 40) old8 F sb
    -- Pointwise: the pinned source chain entails the owned Route-B arm.
    have hpt : ∀ u : PartialState,
        (((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) **
            (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) ** (.x10 ↦ᵣ 0) ** (.x11 ↦ᵣ gasUsed) **
            (.x12 ↦ᵣ parentPtr) ** (.x13 ↦ᵣ Expected) ** (.x0 ↦ᵣ 0) **
            (.x5 ↦ᵣ packBytes ((parentBytes.drop 24).take 8)) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            bytesRegion parentPtr parentBytes **
            bytesRegion Expected (k73CopyOut parentBytes expectedBytes) **
            k73_piggyback spH old8 headerPtr headerBytes F) u →
          (k73PostOwn spH spK headerPtr v9 old18 (gasLimit >>> 1) v19 v20 gasUsed
            parentPtr parentBytes (hvbfWrittenImage gasLimit gasUsed parentBytes)
            headerBytes (H + 40) old8 F) u) :=
      by
        intro u hu
        -- Expand the piggyback into its atoms so the closing certificate can
        -- treat fsHvbf / brHeader / F as individual chain factors.
        dsimp only [k73_piggyback] at hu
        -- Positional transformer vocabulary: identity-congruence pushes a
        -- hold-transformer one level down the right-nested spine.
        -- Lifts, position-addressed (spine indices 7, 8, 9, 10, 12): each
        -- `under_id^k sep_pin_lift` turns the k-th factor's pin into an own.
        have hcur1 : ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
            (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
            regOwn .x10 ** (.x11 ↦ᵣ gasUsed) ** (.x12 ↦ᵣ parentPtr) **
            (.x13 ↦ᵣ Expected) ** (.x0 ↦ᵣ 0) **
            (.x5 ↦ᵣ packBytes ((parentBytes.drop 24).take 8)) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            bytesRegion parentPtr parentBytes **
            bytesRegion Expected (k73CopyOut parentBytes expectedBytes) **
            frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
            bytesRegion headerPtr headerBytes ** F) u :=
          under_id (under_id (under_id (under_id (under_id (under_id sep_pin_lift))))) u hu
        have hcur2 : ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
            (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
            regOwn .x10 ** regOwn .x11 ** (.x12 ↦ᵣ parentPtr) **
            (.x13 ↦ᵣ Expected) ** (.x0 ↦ᵣ 0) **
            (.x5 ↦ᵣ packBytes ((parentBytes.drop 24).take 8)) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            bytesRegion parentPtr parentBytes **
            bytesRegion Expected (k73CopyOut parentBytes expectedBytes) **
            frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
            bytesRegion headerPtr headerBytes ** F) u :=
          under_id (under_id (under_id (under_id (under_id (under_id (under_id sep_pin_lift)))))) u hcur1
        have hcur3 : ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
            (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
            regOwn .x10 ** regOwn .x11 ** regOwn .x12 **
            (.x13 ↦ᵣ Expected) ** (.x0 ↦ᵣ 0) **
            (.x5 ↦ᵣ packBytes ((parentBytes.drop 24).take 8)) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            bytesRegion parentPtr parentBytes **
            bytesRegion Expected (k73CopyOut parentBytes expectedBytes) **
            frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
            bytesRegion headerPtr headerBytes ** F) u :=
          under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id sep_pin_lift))))))) u hcur2
        have hcur4 : ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
            (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
            regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            (.x0 ↦ᵣ 0) **
            (.x5 ↦ᵣ packBytes ((parentBytes.drop 24).take 8)) **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            bytesRegion parentPtr parentBytes **
            bytesRegion Expected (k73CopyOut parentBytes expectedBytes) **
            frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
            bytesRegion headerPtr headerBytes ** F) u :=
          under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id sep_pin_lift)))))))) u hcur3
        have hcur5 : ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
            (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
            regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            (.x0 ↦ᵣ 0) ** regOwn .x5 **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            bytesRegion parentPtr parentBytes **
            bytesRegion Expected (k73CopyOut parentBytes expectedBytes) **
            frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
            bytesRegion headerPtr headerBytes ** F) u :=
          (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id sep_pin_lift))))))))))) u hcur4
        -- Window cast at its spine slot (bytesRegion Expected …).
        have hcur6 : ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
            (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
            regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
            (.x0 ↦ᵣ 0) ** regOwn .x5 **
            regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
            regOwn .x31 ** frameSlotsSaved k73Frame spK
              (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
            bytesRegion parentPtr parentBytes **
            bytesRegion Expected (hvbfWrittenImage gasLimit gasUsed parentBytes) **
            frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
            bytesRegion headerPtr headerBytes ** F) u :=
          (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (under_id (sep_br_cast hwin))))))))))))))))))))) u hcur5
        -- Reorder into the unfolded-goal spelling (pure permutation).
        dsimp only [k73PostOwn, tailRest, tailRestCore]
        exact (by
          xperm_cert_eq :
            ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) **
              (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
              regOwn .x10 ** regOwn .x11 ** regOwn .x12 ** regOwn .x13 **
              (.x0 ↦ᵣ 0) ** regOwn .x5 **
              regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
              regOwn .x31 ** frameSlotsSaved k73Frame spK
                (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
              bytesRegion parentPtr parentBytes **
              bytesRegion Expected (hvbfWrittenImage gasLimit gasUsed parentBytes) **
              frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
              bytesRegion headerPtr headerBytes ** F)
            =
            ((.x2 ↦ᵣ spH) ** (.x8 ↦ᵣ headerPtr) ** regOwn .x10 ** regOwn .x11 **
              (.x0 ↦ᵣ (0 : Word)) **
              frameSlotsSaved hvbfFrame spH (hvbfSaved (H + 40) old8) **
              (.x9 ↦ᵣ v9) ** (.x18 ↦ᵣ old18) ** (.x19 ↦ᵣ v19) ** (.x20 ↦ᵣ v20) **
              regOwn .x12 ** regOwn .x13 ** regOwn .x5 **
              regOwn .x6 ** regOwn .x7 ** regOwn .x28 ** regOwn .x29 ** regOwn .x30 **
              regOwn .x31 ** frameSlotsSaved k73Frame spK
                (k73Saved (H + 40) headerPtr v9 old18 v19 v20) **
              bytesRegion headerPtr headerBytes ** bytesRegion parentPtr parentBytes **
              bytesRegion Expected (hvbfWrittenImage gasLimit gasUsed parentBytes) ** F)) ▸
          hcur6
    exact hpt sb hbig

end EvmAsm.Codegen.HeaderValidateBaseFeeCompositionEqualRoute
