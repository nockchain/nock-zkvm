/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkKJ8.lean

  `walkJ8_records_genuine` / `atomWalk_records_genuine` decode a walk row's child handle with the
  two-kind `denH` (`WalkH.childHOf = (decide (k = 1), natOf v)`), over a ONE-provider accepted table
  (`TableAccepts`).  This module re-proves the walk records over the two-provider table
  at the wire kind:

  * `KidAtoms2` / `InS2` / `EncInj2` — the noun set the chain argument reads (decoded cells of the
    two-provider decode, inline small-atom children, rank-`(0,0)` external atom children) and the
    injectivity of the encoder `E` on it.
  * `row_kids2` — `row_genuine2` with each child's membership in `InS2` and its `denK` at the wire
    handle `hK c s`;
  * **`chain_sound2`** — T3 (`Chain.chain_sound`) over `TableAccepts2` with the encoder `E`;
  * **`walkK_of_reconGoal`** — `WalkH.walkH_of_reconGoal` at `denK` / `exportRecK`;
  * `childHOfK` — the wire child handle `(natOf k, natOf v)` of a walk row;
  * **`walkHQK_records_genuineK`** (chip form on `walkChipHQK`) and **`walkJ8_records_genuineK`**
    (on `walkChipJ8` through `bitFix`, at the UNCHANGED `walkEvent`): every walk record
    `(rootIdx, 2·prefix + b, k_b, v_b)` names `/[2·prefix + b]` of `denK (1, rootIdx)` with child
    `denK (k_b, v_b)`.
  * `recOK_p_of_genuine` — the ℕ-record form `RowSemChipX.RecOK (denK …) R limbA ([ri, ax, k, v],.p)`.

  The atom-walk instance keeps the two-kind lemma: its consumed
  key is `keyH = (idx, 0, aL, wR, valR)` with kinds in `{0, 1}` (g2), and its records go to the
  SERVICE balance (`.s`), not to `.p`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
import Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX
import Nock.NockVMROM.Thm54.P8Core.VclL.DecodeTree
import Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.ComputeTable (FP)
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The noun set and the two-provider chain -/

section Model
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp]

/-- The atom children of a two-provider table: an inline small atom (`w = 0`) or the external atom of a
weighted rank-`(0, 0)` child. -/
def KidAtoms2 (t : List (CellRow q Kfp)) (ext : ℕ → Option Noun) : Set Noun :=
  {n | ∃ c ∈ t, ∃ s : Side, (c.b0.wS s = false ∧ n = .atom (c.b0.aS s).val) ∨
    (c.b0.wS s = true ∧ c.b0.hiS s = 0 ∧ c.b0.loS s = 0 ∧ ext (c.b0.idS s) = some n)}

/-- The nouns the chain argument visits: decoded cells or atom children. -/
def InS2 (t : List (CellRow q Kfp)) (ext : ℕ → Option Noun) (n : Noun) : Prop :=
  n ∈ decodedNouns2 (t.map (·.b0)) ext ∨ n ∈ KidAtoms2 t ext

def EncInj2 (E : Noun → FP Kfp) (t : List (CellRow q Kfp)) (ext : ℕ → Option Noun) : Prop :=
  ∀ a, InS2 t ext a → ∀ b, InS2 t ext b → E a = E b → a = b

theorem decodeTree_idx_lt (t : List (CellRowB0 q)) (leaf : CellRowB0 q → Side → Option (Option Noun)) :
    ∀ f i n, decodeTree t leaf f i = some n → i < t.length
  | 0, _, _, h => by simp [decodeTree] at h
  | f + 1, i, n, h => by
    rw [decodeTree_succ] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, -⟩ := h
    exact (List.getElem?_eq_some_iff.mp hc).1

theorem mem_decodedNouns2_of {t : List (CellRowB0 q)} {ext : ℕ → Option Noun} {i : ℕ} {n : Noun}
    (h : preZNounOfTable2 t ext i = some n) : n ∈ decodedNouns2 t ext :=
  List.mem_filterMap.mpr ⟨i, List.mem_range.mpr (decodeTree_idx_lt t _ _ _ _ h), h⟩

theorem denK_one (t : List (CellRowB0 q)) (ext : ℕ → Option Noun) (i : ℕ) :
    denK t ext (1, i) = preZNounOfTable2 t ext i := rfl

variable [Fact q.Prime]

/-- **`row_genuine2` with the children's `InS2` membership and wire-handle denotation.** -/
theorem row_kids2 (hq : 2 ^ 63 < q) {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms q z E)
    {t : List (CellRow q Kfp)} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (h : TableAccepts2 z t vp) (hvp : AtomLeaves E vp ext) {c : CellRow q Kfp} (hc : c ∈ t) :
    ∃ L R, preZNounOfTable2 (t.map (·.b0)) ext c.b0.idx = some (.cell L R) ∧
      c.p = E (.cell L R) ∧ c.l = E L ∧ c.r = E R ∧
      ∀ s : Side, InS2 t ext (if s = .L then L else R) ∧
        denK (t.map (·.b0)) ext (hK c.b0 s) = some (if s = .L then L else R) := by
  obtain ⟨L, R, hd, hp, hl, hr, h0, h1, haL, haR⟩ := row_genuine2 hq hcons hE h hvp hc
  refine ⟨L, R, hd, hp, hl, hr, fun s => ?_⟩
  unfold hK kindS
  cases hw : c.b0.wS s with
  | true =>
    by_cases hr0 : c.b0.hiS s = 0 ∧ c.b0.loS s = 0
    · have hx := (h0 s hw hr0).1
      refine ⟨Or.inr ⟨c, hc, s, Or.inr ⟨hw, hr0.1, hr0.2, hx⟩⟩, ?_⟩
      simp only [hr0, and_self, if_true, denK]; exact hx
    · have hx := h1 s hw hr0
      refine ⟨Or.inl (mem_decodedNouns2_of hx), ?_⟩
      simp only [hr0, if_false, if_true, denK]; exact hx
  | false =>
    cases s
    · have hLa := haL hw
      refine ⟨Or.inr ⟨c, hc, .L, Or.inl ⟨hw, hLa⟩⟩, ?_⟩
      simp only [denK, if_true]
      exact congrArg some hLa.symm
    · have hRa := haR hw
      refine ⟨Or.inr ⟨c, hc, .R, Or.inl ⟨hw, hRa⟩⟩, ?_⟩
      simp only [denK]
      exact congrArg some hRa.symm

/-- **T3 over the two-provider table** (`Chain.chain_sound` with the encoder `E`): every linked chain of
exported edges from a node in `InS2` ends at the fingerprint of the slot `axisFold sides` of that node,
which is again in `InS2`. -/
theorem chain_sound2 (hq : 2 ^ 63 < q) {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms q z E)
    {t : List (CellRow q Kfp)} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (h : TableAccepts2 z t vp) (hvp : AtomLeaves E vp ext) (hinj : EncInj2 E t ext) :
    ∀ (es : List (Edge Kfp)) (root : Noun), InS2 t ext root →
      (∀ e ∈ es, EdgeExported t e) →
      ∀ ch, chainEnd (E root) es = some ch →
        ∃ n, E n = ch ∧ chainWalk root (es.map Edge.side) = some n ∧
          Noun.slot (axisFold (es.map Edge.side)) root = some n ∧ InS2 t ext n := by
  intro es
  induction es with
  | nil =>
    intro root hS _ ch hend
    simp only [chainEnd, Option.some.injEq] at hend
    exact ⟨root, hend, rfl, by rw [chain_slot]; rfl, hS⟩
  | cons e es ih =>
    intro root hS hexp ch hend
    obtain ⟨c, hc, hidx, hp, hl, hr⟩ := hexp e (by simp)
    obtain ⟨L, R, hd, hcp, hcl, hcr, hkid⟩ := row_kids2 hq hcons hE h hvp hc
    have hcellD : InS2 t ext (Noun.cell L R) := Or.inl (mem_decodedNouns2_of hd)
    simp only [chainEnd] at hend
    by_cases hpe : e.p = E root
    swap
    · rw [if_neg hpe] at hend; exact absurd hend (by simp)
    rw [if_pos hpe] at hend
    have hfp : E root = E (.cell L R) := by rw [← hpe, ← hp, hcp]
    have hroot : root = Noun.cell L R := hinj root hS _ hcellD hfp
    subst hroot
    have hchild : childOf e = E (if e.side then R else L) := by
      simp only [childOf, ← hl, ← hr, hcl, hcr]; split_ifs <;> rfl
    rw [hchild] at hend
    have hchS : InS2 t ext (if e.side then R else L) := by
      cases e.side
      · simpa using (hkid .L).1
      · simpa using (hkid .R).1
    obtain ⟨n, hfn, hwalk, -, hnS⟩ :=
      ih _ hchS (fun e' he' => hexp e' (by simp [he'])) ch hend
    refine ⟨n, hfn, ?_, ?_, hnS⟩
    · simp only [List.map_cons, chainWalk]; exact hwalk
    · rw [chain_slot]; simp only [List.map_cons, chainWalk]; exact hwalk

/-- **The walk records of a row at the wire kind, model form** (`WalkH.walkH_of_reconGoal` over the
two-provider table): under the walk's `ForestReconGoal`, the root gate and exported keys, and the census
conclusion `EncInj2`, every handle record `(rootIdx, 2·prefix + b, h_b)` whose wire export record
`(idx, hl, hr)` is a row's `exportRecK` names, through `denK`, the slot `/[2·prefix + b]` of its root
`denK (1, rootIdx)`. -/
theorem walkK_of_reconGoal (hq : 2 ^ 63 < q) {z : Kfp} {E : Noun → FP Kfp}
    (hcons : ∀ a b, E (.cell a b) = FP.cons z (E a) (E b)) (hE : InlineAtoms q z E)
    {tb : List (CellRow q Kfp)} {vp : List (VKey Kfp)} {ext : ℕ → Option Noun}
    (h : TableAccepts2 z tb vp) (hvp : AtomLeaves E vp ext) (hinj : EncInj2 E tb ext)
    {X : List (XKey Kfp)} (hX : KeysExported tb X)
    {lbl : ℕ → LT q Kfp} {kroots hh : ℕ} (hk : 1 ≤ kroots) (hRG : RootGate X lbl kroots)
    (hG : ForestReconGoal (stateSep (q := q) X 62) lbl kroots hh) :
    ∀ i, 1 ≤ i → i ≤ hh → ∀ k ∈ X, k.1 = (lbl i).2.node → ∀ hl hr : KHandle,
      (∃ c ∈ tb, (k.2.2.2, hl, hr) = exportRecK c.b0) → ∀ b : Bool,
      ∃ (ri : ℕ) (rt nn : Noun), (lbl i).2.ridx = (ri : ZMod q) ∧ ri < tb.length ∧
        denK (tb.map (·.b0)) ext (1, ri) = some rt ∧
        denK (tb.map (·.b0)) ext (if b then hr else hl) = some nn ∧
        Noun.slot (2 * (lbl i).2.pre + bitZ b).val rt = some nn := by
  have hq' : 2 ^ (62 + 1) ≤ q := by omega
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  intro i hi1 hih k hkX hki hl hr ⟨c', hc', hrec⟩ b
  obtain ⟨ρ, hρ1, hρk, es, hesX, -, hax, hroot, hridx, hend⟩ :=
    chain_tuple_of_reconGoal hq' hk (fun j hj1 hjk => (hRG j hj1 hjk).1) hG i hi1 hih k hkX hki b
  obtain ⟨-, k0, hk0, hk0n, hk0i⟩ := hRG ρ hρ1 hρk
  obtain ⟨c, hc, hci, hcp, -, -⟩ := hX k0 hk0
  obtain ⟨L, R, hdec, hp, -, -, -⟩ := row_kids2 hq hcons hE h hvp hc
  have hpe : (lbl ρ).2.node = E (.cell L R) := by
    rw [← hk0n, ← hcp, hp]
  rw [hpe] at hend
  have hexp : ∀ e ∈ es, EdgeExported tb e := by
    intro e he
    obtain ⟨c'', hc'', h1, h2, h3, h4⟩ := hX _ (hesX e he)
    exact ⟨c'', hc'', h1, h2, h3, h4⟩
  obtain ⟨nn, hnn, -, hslot, hmem⟩ := chain_sound2 hq hcons hE h hvp hinj es
    (.cell L R) (Or.inl (mem_decodedNouns2_of hdec)) hexp _ hend
  obtain ⟨c1, hc1, hc1i, -, hc1l, hc1r⟩ := hX k hkX
  have hidx : c'.b0.idx = k.2.2.2 := (congrArg Prod.fst hrec).symm
  have hcc : c1 = c' := serial_functional_rows h.serial hc1 hc' (by rw [hc1i, hidx])
  subst hcc
  have hlr : hl = hK c1.b0 .L ∧ hr = hK c1.b0 .R := by
    have := congrArg Prod.snd hrec
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨L1, R1, -, -, hl1, hr1, hkid⟩ := row_kids2 hq hcons hE h hvp hc1
  have hclt : c.b0.idx < tb.length := by
    have hs := serial_lookup h.serial (List.mem_map_of_mem (f := (·.b0)) hc)
    simpa using (List.getElem?_eq_some_iff.mp hs).1
  refine ⟨c.b0.idx, .cell L R, nn, by rw [hridx, hk0i, hci], hclt, by rw [denK_one]; exact hdec, ?_,
    by rw [hax]; exact hslot⟩
  rw [hlr.1, hlr.2]
  cases b
  · have htg : tgt k false = E L1 := by
      show k.2.1 = _; rw [← hc1l, hl1]
    have hL := hkid .L
    simp only [if_true] at hL
    have := hinj nn hmem L1 hL.1 (by rw [hnn, htg])
    simp only [Bool.false_eq_true, ↓reduceIte, this]
    exact hL.2
  · have htg : tgt k true = E R1 := by
      show k.2.2.1 = _; rw [← hc1r, hr1]
    have hR := hkid .R
    simp only [reduceCtorEq, if_false] at hR
    have := hinj nn hmem R1 hR.1 (by rw [hnn, htg])
    simp only [↓reduceIte, this]
    exact hR.2

end Model

/-! ## 2. The chip form on `walkChipHQK` and `walkChipJ8` -/

section Chip
variable {F : Type} [Field F] [DecidableEq F]

/-- **The wire child handle** of side `bb` a walk row carries: `(natOf k_b, natOf v_b)`, kinds `0 / 1 / 2`
read as they are (no `decide (k = 1)` collapse). -/
def childHOfK (eF : Env F) (bb : Bool) : KHandle :=
  if bb then (natOf (eF.trace WalkHC.kR), natOf (eF.trace WalkHC.vR))
  else (natOf (eF.trace WalkHC.kL), natOf (eF.trace WalkHC.vL))

end Chip

section Accept
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K)

section HQK
variable (Q : Fin (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
  (hsat : (walkChipHQK δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
  (hbind : (walkChipHQK δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
  (hinj : Function.Injective nodes)
  (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
  (hF : GeneratedField.PrimeFieldElems F)
  (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F)
  (hq : 2 ^ 63 < ringChar F)

open scoped Classical in
include hsat hbind hinj hadj hF hk hkn hkp hq in
/-- **`walkHQK_records_genuineK`** (the wire-kind twin of `AtomWalkAW.atomWalk_records_genuine`).  On a
trace accepted by `walkChipHQK`, at `(αW, γW) = (chals 0, chals 1)` outside the SAME `walkEvent`, over a
TWO-provider accepted cell table (`TableAccepts2` at `z`, atom-root external keys `AtomLeaves`, the encoder
facts, the census conclusion `EncInj2`), with every row's consumed wire export record `exportRecK` of a
table row (`hHX`): every walk record names `/[2·prefix + b]` of `denK (1, rootIdx)` with child
`denK (childHOfK b)`. -/
theorem walkHQK_records_genuineK {z : Quad (algebraMap F K δF)}
    {E : Noun → FP (Quad (algebraMap F K δF))}
    (hcons : ∀ a c, E (.cell a c) = FP.cons z (E a) (E c)) (hE : InlineAtoms (ringChar F) z E)
    {tb : List (CellRow (ringChar F) (Quad (algebraMap F K δF)))}
    {vp : List (VKey (Quad (algebraMap F K δF)))} {ext : ℕ → Option Noun}
    (htab : TableAccepts2 z tb vp) (hvp : AtomLeaves E vp ext) (hEinj : EncInj2 E tb ext)
    (hX : KeysExported tb (walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs Q)).X)
    (hHX : ∀ j < n, ∃ c ∈ tb,
      (natOf ((walkEnvFA δF kroots b hn nodes orbit chals pubs Q j).trace WChip.idx),
        childHOfK (walkEnvFA δF kroots b hn nodes orbit chals pubs Q j) false,
        childHOfK (walkEnvFA δF kroots b hn nodes orbit chals pubs Q j) true) = exportRecK c.b0)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs Q))) :
    let W := walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs Q)
    ∀ i, 1 ≤ i → i ≤ n → ∀ bb : Bool,
      ∃ (ri : ℕ) (rt nn : Noun), (W.lbl i).2.ridx = (ri : ZMod (ringChar F)) ∧ ri < tb.length ∧
        denK (tb.map (·.b0)) ext (1, ri) = some rt ∧
        denK (tb.map (·.b0)) ext (childHOfK (walkEnvFA δF kroots b hn nodes orbit chals pubs Q (i - 1)) bb)
          = some nn ∧
        Noun.slot (2 * (W.lbl i).2.pre + bitZ bb).val rt = some nn := by
  intro W i hi1 hin bb
  set Q0 := restrictWalkK δF kroots b hn nodes orbit chals pubs Q
  obtain ⟨hyp, hRG, hacc⟩ := atomWalk_W1 δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF
    hk hkn hkp hq
  have hG : ForestReconGoal (stateSep (q := ringChar F) W.X 62) W.lbl W.kroots W.h := by
    by_contra hng
    exact hout (by simp only [walkEvent, Finset.mem_filter, Finset.mem_univ, true_and]
                   exact ⟨hyp, hacc, hng⟩)
  have hj : i - 1 < n := by omega
  set eK := walkEnvK δF kroots b hn nodes orbit chals pubs Q0 (i - 1)
  set eF := walkEnvF b hn nodes orbit chals pubs Q0 (i - 1)
  have hkX : keyRow δF eK eF ∈ W.X := List.mem_ofFn.mpr ⟨⟨i - 1, hj⟩, rfl⟩
  have hki : (keyRow δF eK eF).1 = (W.lbl i).2.node := rfl
  obtain ⟨c, hc, hrec⟩ := hHX (i - 1) hj
  have hidx : natOf ((walkEnvFA δF kroots b hn nodes orbit chals pubs Q (i - 1)).trace WChip.idx) =
      (keyRow δF eK eF).2.2.2 := by
    show _ = natOf (eF.trace WChip.idx)
    rw [walkEnvFA_trace δF kroots b hn nodes orbit chals pubs Q (i - 1) (by decide)]
  rw [hidx] at hrec
  obtain ⟨ri, rt, nn, h1, h0, h2, h3, h4⟩ := walkK_of_reconGoal hq hcons hE htab hvp hEinj hX hk hRG hG i hi1 hin
    (keyRow δF eK eF) hkX hki _ _ ⟨c, hc, hrec⟩ bb
  exact ⟨ri, rt, nn, h1, h0, h2, by cases bb <;> simpa [childHOfK] using h3, h4⟩

end HQK

section J8
variable (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → F[X])
  (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
  (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
  (hinj : Function.Injective nodes)
  (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
  (hF : GeneratedField.PrimeFieldElems F)
  (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar F)
  (hq : 2 ^ 63 < ringChar F)

open scoped Classical in
include hsat hbind hinj hadj hF hk hkn hkp hq in
theorem walkJ8_records_genuineK {z : Quad (algebraMap F K δF)}
    {E : Noun → FP (Quad (algebraMap F K δF))}
    (hcons : ∀ a c, E (.cell a c) = FP.cons z (E a) (E c)) (hE : InlineAtoms (ringChar F) z E)
    {tb : List (CellRow (ringChar F) (Quad (algebraMap F K δF)))}
    {vp : List (VKey (Quad (algebraMap F K δF)))} {ext : ℕ → Option Noun}
    (htab : TableAccepts2 z tb vp) (hvp : AtomLeaves E vp ext) (hEinj : EncInj2 E tb ext)
    (hX : KeysExported tb (walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs
        (bitFix δF kroots b hn nodes orbit chals pubs Q))).X)
    (hHX : ∀ j < n, ∃ c ∈ tb,
      (natOf ((walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace WChip.idx),
        childHOfK (walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j) false,
        childHOfK (walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j) true) = exportRecK c.b0)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q)))) :
    let W := walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q))
    ∀ i, 1 ≤ i → i ≤ n → ∀ bb : Bool,
      ∃ (ri : ℕ) (rt nn : Noun), (W.lbl i).2.ridx = (ri : ZMod (ringChar F)) ∧ ri < tb.length ∧
        denK (tb.map (·.b0)) ext (1, ri) = some rt ∧
        denK (tb.map (·.b0)) ext (childHOfK (walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) (i - 1)) bb) = some nn ∧
        Noun.slot (2 * (W.lbl i).2.pre + bitZ bb).val rt = some nn := by
  have hp : 64 ≤ ringChar F := by
    have : (64 : ℕ) ≤ 2 ^ 63 := by norm_num
    omega
  obtain ⟨hs, hb⟩ := walkChipJ8_to_HQK δF kroots b hn nodes orbit chals pubs Q hsat hbind hF hp
  exact walkHQK_records_genuineK δF kroots b hn nodes orbit chals pubs _ hs hb hinj hadj hF
    hk hkn hkp hq hcons hE htab hvp hEinj hX hHX hout

/-! ### The `ℕ` walk record and `RecOK` at `.p` -/

/-- The bit of side `bb` in the base field. -/
def bitF (bb : Bool) : F := if bb then 1 else 0

/-- **The `ℕ` walk record** of side `bb` a row provides: `(rootIdx, 2·prefix + b, k_b, v_b)` through `natOf`. -/
def recNat (e : Env F) (bb : Bool) : List ℕ :=
  [natOf (e.trace WChip.ridx), natOf (2 * e.trace WChip.pre + bitF bb),
    (childHOfK e bb).1, (childHOfK e bb).2]

include hF in
theorem zq_val (x : F) : (zq x).val = natOf x := by
  haveI : NeZero (ringChar F) := ⟨(Fact.out : (ringChar F).Prime).ne_zero⟩
  rw [zq, ZMod.val_natCast, Nat.mod_eq_of_lt (natOf_lt hF x)]

include hF in
theorem zq_cast (x : F) : (ZMod.cast (zq x) : F) = x := by
  unfold zq
  rw [ZMod.cast_natCast (dvd_refl _), natOf_cast hF]

include hF in
/-- `zq` is additive on the axis expression (`zq` inverts the injective `ZMod p →+* F`). -/
theorem zq_axis (x : F) (bb : Bool) : zq (2 * x + bitF bb) = 2 * zq x + bitZ bb := by
  have hinj : Function.Injective (ZMod.castHom (dvd_refl (ringChar F)) F) := RingHom.injective _
  apply hinj
  rw [ZMod.castHom_apply, ZMod.castHom_apply, zq_cast hF, ZMod.cast_add (dvd_refl _),
    ZMod.cast_mul (dvd_refl _), zq_cast hF]
  have h2 : (ZMod.cast (2 : ZMod (ringChar F)) : F) = 2 := by
    have := ZMod.cast_natCast (R := F) (dvd_refl (ringChar F)) 2
    exact_mod_cast this
  cases bb <;> simp [bitF, bitZ, h2]

open scoped Classical in
include hsat hbind hinj hadj hF hk hkn hkp hq in
/-- **`RecOK` at `.p` for every provided walk record**: on the J-8 walk at `bitFix Q`, every row `j < n` and side
`bb` satisfies `RowSemChipX.RecOK (denK tb ext) R limbA (recNat (row j) bb,.p)`, under the hypotheses of
`walkJ8_records_genuineK` and `tb.length ≤ p`. -/
theorem recOK_p_row {z : Quad (algebraMap F K δF)}
    {E : Noun → FP (Quad (algebraMap F K δF))}
    (hcons : ∀ a c, E (.cell a c) = FP.cons z (E a) (E c)) (hE : InlineAtoms (ringChar F) z E)
    {tb : List (CellRow (ringChar F) (Quad (algebraMap F K δF)))}
    {vp : List (VKey (Quad (algebraMap F K δF)))} {ext : ℕ → Option Noun}
    (htab : TableAccepts2 z tb vp) (hvp : AtomLeaves E vp ext) (hEinj : EncInj2 E tb ext)
    (htb : tb.length ≤ ringChar F)
    (hX : KeysExported tb (walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs
        (bitFix δF kroots b hn nodes orbit chals pubs Q))).X)
    (hHX : ∀ j < n, ∃ c ∈ tb,
      (natOf ((walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace WChip.idx),
        childHOfK (walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j) false,
        childHOfK (walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j) true) = exportRecK c.b0)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q))))
    (R : Nock.Jet.Registry) (limbA : ℕ → ℕ → ℕ × ℕ) :
    ∀ j < n, ∀ bb : Bool, RecOK (denK (tb.map (·.b0)) ext) R limbA
      (recNat (walkEnvFA δF kroots b hn nodes orbit chals pubs
        (bitFix δF kroots b hn nodes orbit chals pubs Q) j) bb, .p) := by
  intro j hj bb
  haveI : NeZero (ringChar F) := ⟨(Fact.out : (ringChar F).Prime).ne_zero⟩
  obtain ⟨ri, rt, nn, h1, h0, h2, h3, h4⟩ := walkJ8_records_genuineK δF kroots b hn nodes orbit chals pubs Q
    hsat hbind hinj hadj hF hk hkn hkp hq hcons hE htab hvp hEinj hX hHX hout (j + 1) (by omega) (by omega) bb
  simp only [Nat.add_sub_cancel] at h3
  set eA := walkEnvFA δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q) j
  have hr : (walkEnvF b hn nodes orbit chals pubs (restrictWalkK δF kroots b hn nodes orbit chals pubs
      (bitFix δF kroots b hn nodes orbit chals pubs Q)) j).trace WChip.ridx = eA.trace WChip.ridx :=
    (walkEnvFA_trace δF kroots b hn nodes orbit chals pubs _ j (by decide)).symm
  have hpre : (walkEnvF b hn nodes orbit chals pubs (restrictWalkK δF kroots b hn nodes orbit chals pubs
      (bitFix δF kroots b hn nodes orbit chals pubs Q)) j).trace WChip.pre = eA.trace WChip.pre :=
    (walkEnvFA_trace δF kroots b hn nodes orbit chals pubs _ j (by decide)).symm
  have h1' : zq (eA.trace WChip.ridx) = (ri : ZMod (ringChar F)) := by
    rw [← hr]; exact h1
  have hri : natOf (eA.trace WChip.ridx) = ri := by
    have := congrArg ZMod.val h1'
    rw [zq_val hF, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
    exact this
  have hax : natOf (2 * eA.trace WChip.pre + bitF bb) =
      (2 * zq ((walkEnvF b hn nodes orbit chals pubs (restrictWalkK δF kroots b hn nodes orbit chals pubs
        (bitFix δF kroots b hn nodes orbit chals pubs Q)) j).trace WChip.pre) + bitZ bb).val := by
    rw [hpre, ← zq_axis hF, zq_val hF]
  show ∃ Rt C, _ = some Rt ∧ _ = some C ∧ _ = some C
  refine ⟨rt, nn, ?_, ?_, ?_⟩
  · rw [hri]; exact h2
  · exact h3
  · rw [hax]; exact h4


open scoped Classical in
include hsat hbind hinj hadj hF hk hkn hkp hq in
/-- **`AxOK` at `.p` for every provided walk record** (`walkJ8_axis_lt` on the `ℕ` record). -/
theorem axOK_p_row
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap F K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q)))) :
    ∀ j < n, ∀ bb : Bool, ServedJ8.AxOK
      (recNat (walkEnvFA δF kroots b hn nodes orbit chals pubs
        (bitFix δF kroots b hn nodes orbit chals pubs Q) j) bb, .p) := by
  intro j hj bb
  have hax := walkJ8_axis_lt δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn hkp hq
    hout (j + 1) (by omega) (by omega) bb
  have hpre : (walkEnvF b hn nodes orbit chals pubs (restrictWalkK δF kroots b hn nodes orbit chals pubs
      (bitFix δF kroots b hn nodes orbit chals pubs Q)) j).trace WChip.pre =
      (walkEnvFA δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace
        WChip.pre :=
    (walkEnvFA_trace δF kroots b hn nodes orbit chals pubs _ j (by decide)).symm
  have he : natOf (2 * (walkEnvFA δF kroots b hn nodes orbit chals pubs
      (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace WChip.pre + bitF bb) =
      (2 * zq ((walkEnvF b hn nodes orbit chals pubs (restrictWalkK δF kroots b hn nodes orbit chals pubs
        (bitFix δF kroots b hn nodes orbit chals pubs Q)) j).trace WChip.pre) + bitZ bb).val := by
    rw [hpre, ← zq_axis hF, zq_val hF]
  show 2 ≤ natOf _ ∧ natOf _ < 2 ^ 62
  rw [he]
  exact hax

/-- `bitFix` changes only the certificate columns `14..20`: off them, the row environment of `bitFix Q` is
the committed trace's. -/
theorem fa_trace_eq (j : ℕ) (hj : j < n) (c : ℕ) (hc : c < 14 ∨ 21 ≤ c) :
    (walkEnvFA δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace c =
      (TeleH.wEF b nodes orbit chals pubs Q ⟨j, hj⟩).trace c := by
  have hw1 := walkChipHQK_width δF kroots b hn nodes orbit chals pubs
  have hw2 := walkChipJ8_width δF kroots b hn nodes orbit chals pubs
  simp only [walkEnvFA, dif_pos hj, TeleH.wEF, Reify.envOfTrace]
  by_cases hc' : c < 166
  · rw [dif_pos (by rw [hw1]; exact hc'), dif_pos (by rw [hw2]; exact hc'),
      bitFix_off δF kroots b hn nodes orbit chals pubs Q ⟨c, by rw [hw1]; exact hc'⟩ hc]
  · rw [dif_neg (by rw [hw1]; exact hc'), dif_neg (by rw [hw2]; exact hc')]

end J8

end Accept

/-! ## 3. `ProvOK` at the path balance `.p` (field `ZMod p`) -/

section ProvP
variable {p : ℕ} [hpF : Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (δF : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δF))]
  (kroots : ℕ) (b : Basis (Fin 3) (ZMod p) K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p)
  (orbit : StrictOrbitDomain (ZMod p) 3 h) (chals pubs : ℕ → K)

/-- **A provided walk key names its `ℕ` record**: a 4-entry `ℕ` record (entries `< p`) whose `natKey 5` is the
provided key `keyVec5 recLH/recRH` of a row is that row's `recNat`. -/
theorem natKey_walk (e : Env (ZMod p)) (bb : Bool) (a0 a1 a2 a3 : ℕ)
    (hlt : ∀ x ∈ [a0, a1, a2, a3], x < p)
    (hkey : DenXJ8.natKey (p := p) (K := K) 5 [a0, a1, a2, a3] =
      ServeH.keyVec5 (if bb then WalkHC.recRH else WalkHC.recLH) e) :
    [a0, a1, a2, a3] = recNat e bb := by
  have hF := GeneratedField.primeFieldElems_zmod p
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have key : ∀ (a : ℕ) (y : ZMod p), a < p → (a : ZMod p) = y → a = natOf y := by
    intro a y ha hy
    exact natCast_inj_lt (F := ZMod p) (by rw [hrc]; exact ha) (natOf_lt hF y) (hy.trans (natOf_cast hF y).symm)
  have hin : ∀ k : Fin 5, ((([a0, a1, a2, a3].getD k 0 : ℕ)) : ZMod p) =
      ((if bb then WalkHC.recRH else WalkHC.recLH).getD k (.const 0)).eval e := by
    intro k
    exact (algebraMap (ZMod p) K).injective (congrFun hkey k)
  have e0 := hin 0
  have e1 := hin 1
  have e2 := hin 2
  have e3 := hin 3
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
  obtain ⟨l0, l1, l2, l3⟩ := hlt
  cases bb <;>
  · simp [WalkHC.recLH, WalkHC.recRH, CoeffExpr.eval, cv] at e0 e1 e2 e3
    simp only [recNat, childHOfK, bitF, Bool.false_eq_true, if_false, if_true, add_zero]
    rw [key _ _ l0 e0, key _ _ l1 (by simpa using e1), key _ _ l2 e2, key _ _ l3 e3]

open scoped Classical in
theorem provOK_p (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar (ZMod p))
    (hq : 2 ^ 63 < ringChar (ZMod p))
    {z : Quad (algebraMap (ZMod p) K δF)} {E : Noun → FP (Quad (algebraMap (ZMod p) K δF))}
    (hcons : ∀ a c, E (.cell a c) = FP.cons z (E a) (E c)) (hE : InlineAtoms (ringChar (ZMod p)) z E)
    {tb : List (CellRow (ringChar (ZMod p)) (Quad (algebraMap (ZMod p) K δF)))}
    {vp : List (VKey (Quad (algebraMap (ZMod p) K δF)))} {ext : ℕ → Option Noun}
    (htab : TableAccepts2 z tb vp) (hvp : AtomLeaves E vp ext) (hEinj : EncInj2 E tb ext)
    (htb : tb.length ≤ ringChar (ZMod p))
    (hX : KeysExported tb (walkDataOf δF kroots b hn nodes orbit chals pubs
      (restrictWalkK δF kroots b hn nodes orbit chals pubs
        (bitFix δF kroots b hn nodes orbit chals pubs Q))).X)
    (hHX : ∀ j < n, ∃ c ∈ tb,
      (natOf ((walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j).trace WChip.idx),
        childHOfK (walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j) false,
        childHOfK (walkEnvFA δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q) j) true) = exportRecK c.b0)
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap (ZMod p) K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q))))
    (R : Nock.Jet.Registry) (limbA : ℕ → ℕ → ℕ × ℕ) :
    ServedJ8.ProvOK (p := p) (K := K) (denK (tb.map (·.b0)) ext) R limbA Bal.p
      (ServeH.walkPProvs b nodes orbit chals pubs Q) := by
  have hF := GeneratedField.primeFieldElems_zmod p
  intro q hqm l hlen hlt hkey
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hqm
  have hrow := recOK_p_row δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn hkp hq
    hcons hE htab hvp hEinj htb hX hHX hout R limbA j j.2
  have heA : ∀ bb : Bool, ServeH.keyVec5 (if bb then WalkHC.recRH else WalkHC.recLH)
      (TeleH.wEF b nodes orbit chals pubs Q j) =
      ServeH.keyVec5 (K := K) (if bb then WalkHC.recRH else WalkHC.recLH)
      (walkEnvFA δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q) j) := by
    intro bb
    have ht := fun c hc => (fa_trace_eq δF kroots b hn nodes orbit chals pubs Q (j : ℕ) j.2 c hc).symm
    funext k
    fin_cases k <;> cases bb <;>
      simp [ServeH.keyVec5, WalkHC.recLH, WalkHC.recRH, CoeffExpr.eval, cv,
        ht WChip.ridx (by decide), ht WChip.pre (by decide), ht WalkHC.kL (by decide), ht WalkHC.vL (by decide),
        ht WalkHC.kR (by decide), ht WalkHC.vR (by decide)]
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, t⟩⟩⟩⟩⟩
  · trivial
  · trivial
  · trivial
  · trivial
  · have hj' := List.mem_cons.mp hj
    rcases hj' with hj' | hj'
    swap
    · rcases List.mem_cons.mp hj' with hj' | hj'
      · subst hj'
        have := natKey_walk (K := K) _ true a0 a1 a2 a3 hlt (hkey.trans (heA true))
        rw [this]; exact hrow true
      · exact absurd hj' List.not_mem_nil
    subst hj'
    have := natKey_walk (K := K) _ false a0 a1 a2 a3 hlt (hkey.trans (heA false))
    rw [this]; exact hrow false
  · rcases t with _ | ⟨a5, t⟩
    · simp [RecOK]
    · simp only [List.length_cons, DenXJ8.mOf] at hlen; omega

open scoped Classical in
/-- **`haxP` at `.p`**: every 4-entry record a `walkChipJ8` row provides into the path balance has its axis in
`[2, 2^62)` (`ServedJ8.AxOK`), outside the unchanged `walkEvent`. -/
theorem provAx_p (Q : Fin (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.w → (ZMod p)[X])
    (hsat : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).rap.Satisfies Q)
    (hbind : (walkChipJ8 δF kroots b hn nodes orbit chals pubs).BindsPreprocessing Q)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hk : 1 ≤ kroots) (hkn : kroots ≤ n) (hkp : kroots + n < ringChar (ZMod p))
    (hq : 2 ^ 63 < ringChar (ZMod p))
    (hout : (chals 0, chals 1) ∉ walkEvent (algebraMap (ZMod p) K δF)
      (walkDataOf δF kroots b hn nodes orbit chals pubs
        (restrictWalkK δF kroots b hn nodes orbit chals pubs
          (bitFix δF kroots b hn nodes orbit chals pubs Q)))) :
    ServedJ8.ProvP (p := p) (K := K) ServedJ8.AxOK Bal.p (ServeH.walkPProvs b nodes orbit chals pubs Q) := by
  have hF := GeneratedField.primeFieldElems_zmod p
  intro q hqm l hlen hlt hkey
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hqm
  have hrow := axOK_p_row δF kroots b hn nodes orbit chals pubs Q hsat hbind hinj hadj hF hk hkn hkp hq
    hout j j.2
  have heA : ∀ bb : Bool, ServeH.keyVec5 (if bb then WalkHC.recRH else WalkHC.recLH)
      (TeleH.wEF b nodes orbit chals pubs Q j) =
      ServeH.keyVec5 (K := K) (if bb then WalkHC.recRH else WalkHC.recLH)
      (walkEnvFA δF kroots b hn nodes orbit chals pubs (bitFix δF kroots b hn nodes orbit chals pubs Q) j) := by
    intro bb
    have ht := fun c hc => (fa_trace_eq δF kroots b hn nodes orbit chals pubs Q (j : ℕ) j.2 c hc).symm
    funext k
    fin_cases k <;> cases bb <;>
      simp [ServeH.keyVec5, WalkHC.recLH, WalkHC.recRH, CoeffExpr.eval, cv,
        ht WChip.ridx (by decide), ht WChip.pre (by decide), ht WalkHC.kL (by decide), ht WalkHC.vL (by decide),
        ht WalkHC.kR (by decide), ht WalkHC.vR (by decide)]
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, t⟩⟩⟩⟩⟩
  · trivial
  · trivial
  · trivial
  · trivial
  · have hj' := List.mem_cons.mp hj
    rcases hj' with hj' | hj'
    swap
    · rcases List.mem_cons.mp hj' with hj' | hj'
      · subst hj'
        have := natKey_walk (K := K) _ true a0 a1 a2 a3 hlt (hkey.trans (heA true))
        rw [this]; exact hrow true
      · exact absurd hj' List.not_mem_nil
    subst hj'
    have := natKey_walk (K := K) _ false a0 a1 a2 a3 hlt (hkey.trans (heA false))
    rw [this]; exact hrow false
  · trivial

end ProvP

end

end Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8
