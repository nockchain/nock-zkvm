/-
  Nock/NockVMROM/Thm54/VclL/Handle/RowSemIJ8.lean

  New module, additive (`LocalVSX`, `RowSemChipX`, `RecOKAJ8` are not edited).

  The kind-2 handles whose denotation the implication form asks for are the inc record's OLD handle
  (`sf1` of an `s4` row) and the `walkRecA` ROOTS (`f_tth`, `f_ttt` of an `s5` "≠" row under `pr2`).  Each is
  supplied by the compute tree itself, not by a provenance census:
  * `s4`: `sf1` is the result of the row's real child `(s, f_t, sf1)`, which denotes once the subject does
    (`defined_treeXI`, the definedness induction of `LocalVSX.defined_treeX` re-run);
  * `s5`: under `z1 = 1` the roots ARE `sf1` / `sf2` (child results, as above); under `z1 = 0` they are the
    children of the row's served path records (`.p`, existence form: `D ch = some C`);
  * `s11j` (step 3, the jet consume's SUBJECT): the row's own subject, which denotes at every tree node.

  * **`PreRow`**, **`FShape`**, **`RowSemX0I p D R r := (PreRow D r → RowSemX0 p D R r) ∧ FShape D r`**: the row
    semantics with the `s4` / `s5` clauses guarded by their children's results (the formula shape `Cell3 f fh ft`
    unguarded, for the chain roles).
  * Tree: `chain_iff_kindI`, `roles_ofI`, `preRow_of_kids`, `defined_stepXI`, `RowsOKXI`, `defined_treeXI`,
    **`rowsOKX_of_I`** (every node's `PreRow` from the definedness; then `RowsOKX`), **`holdsN_of_rowsVSXI`**.
  * Chip: `preI_active` (an active service record's antecedent from the row: the inc consume only at `s4`, the
    `walkRecA` pair only under `pr2`), **`rowSemXI_of_chip`**.
  * Re-threading: `RowsAccXI`, `halving_of_treeI`, `holdsN_of_walkJ8I`, **`acceptsJ8_holdsN_computeI`**.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8

open Nock Nock.Reified Nock.Edit Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8
open Nock.Jet (Registry)

noncomputable section

/-! ## 1. The guarded row semantics (noun level) -/

section Sem
variable (p : ℕ) (D : HX → Option Noun)

/-- The antecedent of a row: the `s4` / `s5` children's results denote; the `s11j` row's subject denotes. -/
def PreRow (r : RowVSX) : Prop :=
  match r.st with
  | .s4 => D r.sf1 ≠ none
  | .s5 => D r.sf1 ≠ none ∧ D r.sf2 ≠ none
  | .s11j => D r.s ≠ none
  | _ => True

/-- The unguarded formula shape of an `s4` / `s5` / `s11j` row. -/
def FShape (r : RowVSX) : Prop :=
  match r.st with
  | .s4 => Cell3 D r.f r.fh r.ft
  | .s5 => Cell3 D r.f r.fh r.ft
  | .s11j => Cell3 D r.f r.fh r.ft
  | _ => True

/-- **The guarded row semantics.** -/
def RowSemX0I (R : Registry) (r : RowVSX) : Prop := (PreRow D r → RowSemX0 p D R r) ∧ FShape D r

end Sem

section Local
variable {p : ℕ} {D : HX → Option Noun} {R : Registry}

theorem preRow_triv {r : RowVSX} (h4 : r.st ≠ .s4) (h5 : r.st ≠ .s5) (h11 : r.st ≠ .s11j) : PreRow D r := by
  unfold PreRow; split <;> simp_all

theorem chain_iff_kindI (hD : DenOKX p D) {r : RowVSX} (h : RowSemX0I p D R r) :
    r.st.isChain = true ↔ r.f.1 = 0 := by
  by_cases h4 : r.st = .s4
  · have hc : Cell3 D r.f r.fh r.ft := by have := h.2; simp only [FShape, h4] at this; exact this
    rw [h4]; simp only [StateX.isChain, Bool.false_eq_true, false_iff]; exact cell3_kind hD hc
  by_cases h5 : r.st = .s5
  · have hc : Cell3 D r.f r.fh r.ft := by have := h.2; simp only [FShape, h5] at this; exact this
    rw [h5]; simp only [StateX.isChain, Bool.false_eq_true, false_iff]; exact cell3_kind hD hc
  by_cases h11 : r.st = .s11j
  · have hc : Cell3 D r.f r.fh r.ft := by have := h.2; simp only [FShape, h11] at this; exact this
    rw [h11]; simp only [StateX.isChain, Bool.false_eq_true, false_iff]; exact cell3_kind hD hc
  exact chain_iff_kind hD (h.1 (preRow_triv h4 h5 h11))

theorem chainPos_kindI {r : RowVSX} (h : RowSemX0I p D R r) (i : ℕ)
    (hi : i < (kidsX r).length) (hc : chainPosX r.st i = true) : ((kidsX r)[i]'hi).2.1.1 = 0 := by
  by_cases h4 : r.st = .s4
  · exfalso; rw [h4] at hc; rcases i with _ | _ | _ | i <;> simp [chainPosX] at hc
  by_cases h5 : r.st = .s5
  · exfalso; rw [h5] at hc; rcases i with _ | _ | _ | i <;> simp [chainPosX] at hc
  by_cases h11 : r.st = .s11j
  · exfalso; rw [h11] at hc; rcases i with _ | _ | _ | i <;> simp [chainPosX] at hc
  exact chainPos_kind (h.1 (preRow_triv h4 h5 h11)) i hi hc

/-- **`roles_of` at the guarded semantics.** -/
theorem roles_ofI (hD : DenOKX p D) {r : RowVSX} (h : RowSemX0I p D R r)
    (hkk : KidKinds r) (ks : List RowVSX) (hk : ks.map RowVSX.trip = kidsX r)
    (hks : ∀ k ∈ ks, RowSemX0I p D R k) :
    ∀ i (hi : i < ks.length), (ks[i]'hi).st.isChain = chainPosX r.st i := by
  intro i hi
  have hlen : ks.length = (kidsX r).length := by rw [← hk, List.length_map]
  have hi' : i < (kidsX r).length := hlen ▸ hi
  have hfi : (ks[i]'hi).f = ((kidsX r)[i]'hi').2.1 := by
    have := congrArg (fun l => l[i]?) hk
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi',
      Option.map_some, Option.some.injEq] at this
    rw [← this]; rfl
  have hc := chain_iff_kindI hD (hks _ (List.getElem_mem hi))
  cases hpos : chainPosX r.st i
  · have := hkk i hi' hpos
    rw [← hfi] at this
    cases h' : (ks[i]'hi).st.isChain
    · rfl
    · have := hc.1 h'; omega
  · have := chainPos_kindI h i hi' hpos
    rw [← hfi] at this
    exact hc.2 this

/-- **The antecedent from the children**: an `s4` / `s5` row's guarded children are real, share the row's
subject, and their results denote once their subjects do. -/
theorem preRow_of_kids {r : RowVSX} (ks : List RowVSX) (hk : ks.map RowVSX.trip = kidsX r)
    (hrole : ∀ i (hi : i < ks.length), (ks[i]'hi).st.isChain = chainPosX r.st i)
    (hs : D r.s ≠ none)
    (hch : ∀ k ∈ ks, k.st.isChain = false → D k.s ≠ none → D k.e ≠ none) : PreRow D r := by
  by_cases h4 : r.st = .s4
  · simp only [PreRow, h4]
    simp only [kidsX, h4] at hk
    rcases ks with _ | ⟨k0, _ | ⟨k1, ks⟩⟩ <;>
      simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, and_false, false_and,
        List.nil_eq, List.cons_ne_nil, RowVSX.trip, Prod.mk.injEq, and_true] at hk
    obtain ⟨h0s, -, h0e⟩ := hk
    have e0 := hch k0 (by simp) (by simpa [chainPosX, h4] using hrole 0 (by simp)) (by rw [h0s]; exact hs)
    rw [← h0e]; exact e0
  by_cases h5 : r.st = .s5
  · simp only [PreRow, h5]
    simp only [kidsX, h5] at hk
    rcases ks with _ | ⟨k0, _ | ⟨k1, _ | ⟨k2, ks⟩⟩⟩ <;>
      simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq, and_false, false_and,
        List.nil_eq, List.cons_ne_nil, RowVSX.trip, Prod.mk.injEq, and_true] at hk
    obtain ⟨⟨h0s, -, h0e⟩, ⟨h1s, -, h1e⟩⟩ := hk
    have e0 := hch k0 (by simp) (by simpa [chainPosX, h5] using hrole 0 (by simp)) (by rw [h0s]; exact hs)
    have e1 := hch k1 (by simp) (by simpa [chainPosX, h5] using hrole 1 (by simp)) (by rw [h1s]; exact hs)
    rw [← h0e, ← h1e]; exact ⟨e0, e1⟩
  by_cases h11 : r.st = .s11j
  · simp only [PreRow, h11]; exact hs
  exact preRow_triv h4 h5 h11

/-- **`defined_stepX` at the guarded semantics.** -/
theorem defined_stepXI (hD : DenOKX p D) (r : RowVSX) (hsem : RowSemX0I p D R r)
    (ks : List RowVSX) (hk : ks.map RowVSX.trip = kidsX r)
    (hrole : ∀ i (hi : i < ks.length), (ks[i]'hi).st.isChain = chainPosX r.st i)
    (hs : D r.s ≠ none)
    (hch : ∀ k ∈ ks, k.st.isChain = false → D k.s ≠ none → D k.e ≠ none) :
    (∀ k ∈ ks, D k.s ≠ none) ∧ (r.st.isChain = false → D r.e ≠ none) :=
  defined_stepX hD r (hsem.1 (preRow_of_kids ks hk hrole hs hch)) ks hk hrole hs hch

end Local

/-! ## 2. The tree -/

section Tree
variable {p : ℕ} {D : HX → Option Noun} {R : Registry} {L : Type} (rw : L → RowVSX)

/-- **The tree hypotheses at the guarded semantics.** -/
structure RowsOKXI (p : ℕ) (D : HX → Option Noun) (R : Registry) (t : NTree L) : Prop where
  sem : ∀ u, InTree t u → RowSemX0I p D R (rw u.label) ∧ KidKinds (rw u.label)
  link : ∀ u, InTree t u → u.children.map (fun c => (rw c.label).trip) = kidsX (rw u.label)

theorem RowsOKXI.sub {t : NTree L} (h : RowsOKXI rw p D R t) {c : NTree L} (hc : c ∈ t.children) :
    RowsOKXI rw p D R c :=
  ⟨fun u hu => h.sem u (InTree.sub hc hu), fun u hu => h.link u (InTree.sub hc hu)⟩

theorem RowsOKXI.kids {t : NTree L} (h : RowsOKXI rw p D R t) {u : NTree L} (hu : InTree t u) :
    (u.children.map fun c => rw c.label).map RowVSX.trip = kidsX (rw u.label) := by
  rw [List.map_map]; exact h.link u hu

theorem RowsOKXI.roles (hD : DenOKX p D) {t : NTree L} (h : RowsOKXI rw p D R t) {u : NTree L}
    (hu : InTree t u) :
    ∀ i (hi : i < (u.children.map fun c => rw c.label).length),
      ((u.children.map fun c => rw c.label)[i]'hi).st.isChain = chainPosX (rw u.label).st i :=
  roles_ofI hD (h.sem u hu).1 (h.sem u hu).2 _ (h.kids rw hu) (by
    intro k hk
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
    exact (h.sem c (inTree_trans hu (InTree.sub hc (InTree.here _)))).1)

/-- **Definedness at the guarded semantics.** -/
theorem defined_treeXI (hD : DenOKX p D) : ∀ t : NTree L, RowsOKXI rw p D R t →
    D (rw t.label).s ≠ none → ∀ u, InTree t u →
      D (rw u.label).s ≠ none ∧ ((rw u.label).st.isChain = false → D (rw u.label).e ≠ none)
  | .node l cs, h, hs => by
    have ih : ∀ c ∈ cs, D (rw c.label).s ≠ none → ∀ u, InTree c u →
        D (rw u.label).s ≠ none ∧ ((rw u.label).st.isChain = false → D (rw u.label).e ≠ none) :=
      fun c hc => defined_treeXI hD c (h.sub rw (by simpa [NTree.children] using hc))
    have hu0 : InTree (NTree.node l cs) (NTree.node l cs) := InTree.here _
    have step := defined_stepXI hD (rw l) (h.sem _ hu0).1 (cs.map fun c => rw c.label)
      (h.kids rw hu0) (h.roles rw hD hu0) hs (by
        intro k hk hc hks
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk
        exact (ih c hc' hks c (InTree.here _)).2 hc)
    intro u hu
    cases hu with
    | here => exact ⟨hs, step.2⟩
    | sub hc hu' =>
      exact ih _ hc (step.1 _ (List.mem_map_of_mem hc)) u hu'

/-- **The guarded tree is a `RowsOKX` tree** once the root subject denotes: every node's antecedent comes
from its children's definedness. -/
theorem rowsOKX_of_I (hD : DenOKX p D) (t : NTree L) (h : RowsOKXI rw p D R t)
    (hs : D (rw t.label).s ≠ none) : RowsOKX rw p D R t := by
  refine ⟨fun u hu => ⟨(h.sem u hu).1.1 ?_, (h.sem u hu).2⟩, h.link⟩
  refine preRow_of_kids _ (h.kids rw hu) (h.roles rw hD hu) (defined_treeXI rw hD t h hs u hu).1 ?_
  intro k hk hc _
  obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hk
  exact (defined_treeXI rw hD t h hs c (inTree_trans hu (InTree.sub hc' (InTree.here _)))).2 hc

/-- **`holdsN_of_rowsVSX` at the guarded semantics.** -/
theorem holdsN_of_rowsVSXI (hR : R.Faithful) (hD : DenOKX p D) (t : NTree L)
    (h : RowsOKXI rw p D R t) (hreal : (rw t.label).st.isChain = false) (x : P8PublicClaim)
    (hs : D (rw t.label).s = some x.subject) (hf : D (rw t.label).f = some x.formula)
    (he : D (rw t.label).e = some x.result) : Nock.Jet.HoldsN x :=
  holdsN_of_rowsVSX rw hR hD t (rowsOKX_of_I rw hD t h (by simp [hs])) hreal x hs hf he

end Tree

/-! ## 3. One chip row -/

section Row
variable {p : ℕ} [Fact p.Prime] {env : Env (ZMod p)} {D : HX → Option Noun} {R : Registry}
  {comb : ℕ → Noun}

theorem recOK_of_I (hOK : ∀ r ∈ activeX env, RecOKI D R comb r) {r : List ℕ × Bal} (hr : r ∈ activeX env)
    (hs : r.2 ≠ .s) (limbA : ℕ → ℕ → HX) : RecOK D R limbA r := by
  obtain ⟨l, bl⟩ := r
  have hw : ¬ IsWalkA (l, bl) := fun hw => hs hw.1
  exact (recOKA_iff_off hw).mp (recOKI_off hs (hOK _ hr))

theorem cell_of_recI (hOK : ∀ r ∈ activeX env, RecOKI D R comb r) {P L Q : Hd}
    (hm : ((cellRecX P L Q).map (reVal env), Bal.x) ∈ activeX env) (hk : env.trace P.k = 1) :
    Cell3 D (hdV env P) (hdV env L) (hdV env Q) := by
  have := recOK_of_I hOK hm (by simp) (fun _ _ => (0, 0))
  simp only [cellRecX, recOf, cellRec, List.map_cons, List.map_nil, reVal, RecOK] at this
  rw [hdV_k1 hk]; exact this

theorem walk_of_recI (hOK : ∀ r ∈ activeX env, RecOKI D R comb r) {root ch : Hd} {ax : ℕ}
    (hm : ((walkRecX root ax ch).map (reVal env), Bal.p) ∈ activeX env) (hk : env.trace root.k = 1) :
    ∃ Rt C, D (hdV env root) = some Rt ∧ D (hdV env ch) = some C ∧
      Noun.slot (env.trace ax).val Rt = some C := by
  have := recOK_of_I hOK hm (by simp) (fun _ _ => (0, 0))
  simp only [walkRecX, recOf, walkRec, List.map_cons, List.map_nil, reVal, RecOK] at this
  rw [hdV_k1 hk]; exact this

theorem L0I (hB : BaseHoldsX env) (hOK : ∀ r ∈ activeX env, RecOKI D R comb r) {j : ℕ}
    (hOH : OneHotAt env j) (hj : j ∈ opStatesX) :
    Cell3 D (hdV env xF) (hdV env xFh) (hdV env xFt) := by
  have hj' : j ≠ 12 ∧ j ≠ 13 := by simp [opStatesX] at hj; omega
  exact cell_of_recI hOK (ent_active hOH (S := slot0X) (by simp [ChipHX.slotsX])
    (x := ⟨opStatesX, .const 1, cellRecX xF xFh xFt, .x⟩) (by simp [slot0X]) (by decide) (by decide)
    hj (by simp [evalQX])) (f_k1 hB hOH hj'.1 hj'.2)

/-- **The antecedent of every active service record**, from the row: the inc consume is active only at `s4`
(its old handle is `sf1`), the `walkRecA` pair only under `pr2` (its roots are `f_tth`, `f_ttt`). -/
theorem preI_active {st : StateX} (hOH : OneHotAt env (stIdx st))
    (h4 : st = .s4 → D (hdV env xSf1) ≠ none) (h11 : st = .s11j → D (hdV env xS) ≠ none)
    (h5 : env.trace pr2X = 1 →
      D (2, (env.trace xFtth.v).val) ≠ none ∧ D (2, (env.trace xFttt.v).val) ≠ none) :
    ∀ r ∈ activeX env, PreI D r := by
  intro r hr
  obtain ⟨S, hS, hr⟩ := List.mem_flatMap.mp hr
  simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  · rcases List.mem_append.mp hr with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      have hx' := (List.mem_filter.mp hx).1
      simp only [slot0X, List.mem_cons, List.not_mem_nil, or_false] at hx'
      subst hx'; exact preI_off (by decide)
    · simp [pairRecsX, slot0X] at h
  · rcases List.mem_append.mp hr with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      have hx' := List.mem_filter.mp hx
      obtain ⟨hx1, hx2⟩ := hx'
      simp only [slot1X, List.mem_cons, List.not_mem_nil, or_false] at hx1
      rcases hx1 with rfl | rfl | rfl
      · exact preI_off (by decide)
      · exact preI_off (by decide)
      · -- the inc consume: active only at `s4`
        have hsel := selS_onehot hOH [4] (by decide) (by decide)
        have hst : st = .s4 := by
          by_contra hne
          have h4' : stIdx st ∉ [4] := by
            intro hm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            exact hne (stIdx_injective (by rw [hm]; rfl))
          rw [if_neg h4'] at hsel
          simp only [EntX.act, evalQX, hsel, zero_mul, decide_eq_true_eq] at hx2
          exact zero_ne_one hx2
        have := h4 hst
        simp only [PreI, incRecX, List.map_cons, List.map_nil, reVal, if_pos rfl, PreS]
        exact this
    · simp [pairRecsX, slot1X] at h
  · rcases List.mem_append.mp hr with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      have hx' := (List.mem_filter.mp hx).1
      simp only [slot2X, List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl <;> exact preI_off (by decide)
    · simp only [pairRecsX, slot2X] at h
      split_ifs at h
      · rcases List.mem_pair.mp h with rfl | rfl <;> exact preI_off (by decide)
      · simp at h
  · rcases List.mem_append.mp hr with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
      have hx' := (List.mem_filter.mp hx).1
      simp only [slot3X, List.mem_cons, List.not_mem_nil, or_false] at hx'
      have hx2 := (List.mem_filter.mp hx).2
      rcases hx' with rfl | rfl
      · exact preI_off (by decide)
      · -- the jet consume: active only at `s11j`
        have hsel := selS_onehot hOH [sS11j] (by decide) (by decide)
        have hst : st = .s11j := by
          by_contra hne
          have h4' : stIdx st ∉ [sS11j] := by
            intro hm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            exact hne (stIdx_injective (by rw [hm]; rfl))
          rw [if_neg h4'] at hsel
          simp only [EntX.act, evalQX, hsel, zero_mul, decide_eq_true_eq] at hx2
          exact zero_ne_one hx2
        have := h11 hst
        simp only [PreI, jetRecX, List.map_cons, List.map_nil, reVal, if_pos rfl, PreS]
        exact this
    · simp only [pairRecsX, slot3X] at h
      split_ifs at h with h2
      · obtain ⟨e1, e2⟩ := h5 h2
        rcases List.mem_pair.mp h with rfl | rfl
        · simp only [PreI, walkRecAX, List.map_cons, List.map_nil, reVal, if_pos rfl, PreS]; exact e1
        · simp only [PreI, walkRecAX, List.map_cons, List.map_nil, reVal, if_pos rfl, PreS]; exact e2
      · simp at h

/-- **`rowSemX_of_chipA` at the implication form**: a chip row whose consumed records meet `RecOKI` satisfies
the guarded semantics (and the kid-kind clause). -/
theorem rowSemXI_of_chip (hD : DenOKX p D) (hp : 17 < p) (hB : BaseHoldsX env) (st : StateX)
    (hOH : OneHotAt env (stIdx st)) (hOK : ∀ r ∈ activeX env, RecOKI D R comb r)
    (hv : HalvingOK env st) : RowSemX0I p D R (rowOfX env st) ∧ KidKinds (rowOfX env st) := by
  refine ⟨⟨fun hpre => ?_, ?_⟩, kidKinds_of_gates hB st (oh_one hOH (stIdx_lt st))⟩
  · have h4 : st = .s4 → D (hdV env xSf1) ≠ none := by
      intro hst; subst hst; simpa [PreRow, rowOfX] using hpre
    have h5 : env.trace pr2X = 1 →
        D (2, (env.trace xFtth.v).val) ≠ none ∧ D (2, (env.trace xFttt.v).val) ≠ none := by
      intro h2
      have aP := arith_of_base hB (op5G_sub _ (by simp [op5G] : (pr2GateX : CoeffExpr ℚ) ∈ op5G))
      simp only [pr2GateX, prodL, List.foldr, cc, kbE, evalQX, Rat.cast_one, Rat.cast_ofNat, mul_one,
        h2] at aP
      have hprod : env.trace 5 * (env.trace betaX * (env.trace (kbX xFtth) * env.trace (kbX xFttt))) = 1 := by
        linear_combination -aP
      by_cases hst : st = .s5
      · subst hst
        have hpre' : D (hdV env xSf1) ≠ none ∧ D (hdV env xSf2) ≠ none := by simpa [PreRow, rowOfX] using hpre
        have h5' : env.trace 5 = 1 := oh_one hOH (by decide)
        have hβ : env.trace betaX = 1 := by
          rcases col_bool hB (i := betaX) (by simp [oneHotG]) with hb | hb
          · rw [hb] at hprod; simp at hprod
          · exact hb
        have kb1 : kbV env xFtth = 1 := by
          rcases kind_split hB xFtth (by decide) with ⟨-, hb⟩ | ⟨-, hb⟩ | ⟨-, hb⟩ <;>
            simp only [kbV] at hb <;> first | exact hb | (rw [hb] at hprod; simp at hprod)
        have kb2 : kbV env xFttt = 1 := by
          rcases kind_split hB xFttt (by decide) with ⟨-, hb⟩ | ⟨-, hb⟩ | ⟨-, hb⟩ <;>
            simp only [kbV] at hb <;> first | exact hb | (rw [hb] at hprod; simp at hprod)
        have hk1 : hdV env xFtth = (2, (env.trace xFtth.v).val) :=
          hdV_of_k (c := 2) (by omega) (by rw [k2_of_kb hB (by decide) kb1]; norm_num)
        have hk2 : hdV env xFttt = (2, (env.trace xFttt.v).val) :=
          hdV_of_k (c := 2) (by omega) (by rw [k2_of_kb hB (by decide) kb2]; norm_num)
        rw [← hk1, ← hk2]
        rcases col_bool hB (i := z1X) (by simp [oneHotG]) with hz | hz
        · -- `z1 = 0`: the roots are the children of the served path pair
          have aP' := arith_of_base hB (op5G_sub _ (by simp [op5G] : (prGateX : CoeffExpr ℚ) ∈ op5G))
          have aS1 := arith_of_base hB (op5G_sub _ (by simp [op5G] :
            (.mul (cc prX) (oneMinus (kcE xSf1)) : CoeffExpr ℚ) ∈ op5G))
          have aS2 := arith_of_base hB (op5G_sub _ (by simp [op5G] :
            (.mul (cc prX) (oneMinus (kcE xSf2)) : CoeffExpr ℚ) ∈ op5G))
          simp only [prGateX] at aP'
          gsimp at aP'; gsimp at aS1; gsimp at aS2
          have h12 : env.trace sS10L = 0 := oh_zero hOH (by decide) (by decide)
          rw [h12, h5', hβ, hz, one_mul, sub_zero, sub_zero] at aP'
          have hpr : env.trace prX = 1 := by linear_combination aP'
          rw [hpr, one_mul] at aS1 aS2
          have k1 := k1_of_kc hB (by decide) (show kcV env xSf1 = 1 by simp only [kcV]; linear_combination -aS1)
          have k2 := k1_of_kc hB (by decide) (show kcV env xSf2 = 1 by simp only [kcV]; linear_combination -aS2)
          have hpm := pair_mem (env := env) (S := slot2X) (fl := prX) (a := walkRecX xSf1 xM.v xFtth)
            (b := walkRecX xSf2 xM.v xFttt) (bl := .p) (by simp [ChipHX.slotsX]) rfl hpr
          obtain ⟨-, C1, -, hC1, -⟩ := walk_of_recI hOK hpm.1 k1
          obtain ⟨-, C2, -, hC2, -⟩ := walk_of_recI hOK hpm.2 k2
          exact ⟨ne_none_of hC1, ne_none_of hC2⟩
        · -- `z1 = 1`: the roots are `sf1`, `sf2`
          have q1 := hdEq hB (σ := prodL [cc 5, cc betaX, cc z1X]) (a := xFtth) (b := xSf1)
            (fun g hg => op5Eq_sub _ (by simp only [op5Eq, List.mem_append]; tauto))
            (by simp [prodL, cc, evalQX, h5', hβ, hz])
          have q2 := hdEq hB (σ := prodL [cc 5, cc betaX, cc z1X]) (a := xFttt) (b := xSf2)
            (fun g hg => op5Eq_sub _ (by simp only [op5Eq, List.mem_append]; tauto))
            (by simp [prodL, cc, evalQX, h5', hβ, hz])
          rw [q1, q2]; exact hpre'
      · exfalso
        have h0 : env.trace 5 = 0 := oh_zero hOH (by decide) (by
          intro h; apply hst; exact stIdx_injective (by rw [← h]; rfl))
        rw [h0, zero_mul] at hprod
        exact zero_ne_one hprod
    have h11 : st = .s11j → D (hdV env xS) ≠ none := by
      intro hst; subst hst; simpa [PreRow, rowOfX] using hpre
    have hA : ∀ r ∈ activeX env, RecOKA D R comb r := fun r hr => hOK r hr (preI_active hOH h4 h11 h5 r hr)
    exact (rowSemX_of_chipA hD hp hB st hOH hA hv).1
  · cases st <;> simp only [FShape, rowOfX]
    · exact L0I hB hOK hOH (by decide)
    · exact L0I hB hOK hOH (by decide)
    · exact L0I hB hOK hOH (by decide)

end Row

/-! ## 4. The tree and the compute half, re-threaded -/

section Tree2
open Nock.Walk Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.HalvingTreeJ8 (halvingOK_of_child)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]

/-- **`RowsAccXA` at the implication form `RecOKI`.** -/
structure RowsAccXI (n : ℕ) (E : ℕ → Env (ZMod p)) (st : ℕ → StateX) (D : HX → Option Noun)
    (R : Nock.Jet.Registry) (comb : ℕ → Noun) : Prop where
  base : ∀ r < n, BaseHoldsX (E r)
  oh : ∀ r < n, OneHotAt (E r) (stIdx (st r))
  served : ∀ r < n, ∀ x ∈ activeX (E r), RecOKI D R comb x
  ax : ∀ r < n, st r = .s10L → 2 ≤ ((E r).trace xM.v).val ∧ ((E r).trace xM.v).val < 2 ^ 62

variable {n : ℕ} {E : ℕ → Env (ZMod p)} {st : ℕ → StateX} {D : HX → Option Noun}
  {R : Nock.Jet.Registry} {comb : ℕ → Noun}

theorem halving_of_treeI (hp : 2 ^ 63 + 1 < p) (A : RowsAccXI n E st D R comb)
    {t : NTree (StateX × RowVSX)}
    (hrow : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i)
    (hlink : ∀ u, InTree t u → u.children.map (fun c => c.label.2.trip) = kidsX u.label.2)
    {u : NTree (StateX × RowVSX)} (hu : InTree t u) {i : ℕ} (hui : u.label = lblOf (rowsWX E st) i)
    (hs : st (i - 1) = .s10L) : HalvingOK (E (i - 1)) .s10L := by
  have hl := hlink u hu
  rw [hui] at hl
  simp only [lblOf, rowsWX, hs, kidsX_rowW_s10L] at hl
  have hlen := congrArg List.length hl
  simp only [List.length_map, List.length_cons, List.length_nil] at hlen
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hlen
  rw [hc] at hl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hl
  have hcin : InTree t c := inTree_trans hu (InTree.sub (by rw [hc]; simp) (InTree.here _))
  obtain ⟨j, hj1, hjn, hcj⟩ := hrow c hcin
  rw [hcj] at hl
  simp only [lblOf, rowsWX] at hl
  rw [rowW_trip] at hl
  simp only [rowOfX, RowVSX.trip, hdV, Prod.mk.injEq] at hl
  obtain ⟨-, ⟨hk, hv⟩, -⟩ := hl
  exact halvingOK_of_child hp (A.base _ (by omega)) (A.oh _ (by omega)) (ZMod.val_eq_zero _ |>.mp hk)
    (ZMod.val_injective _ hv) (A.ax _ (by omega))

/-- **`holdsN_of_walkJ8A` at the implication form.** -/
theorem holdsN_of_walkJ8I [CharP K p] (hp : 2 ^ 63 + 1 < p) (hR : R.Faithful) (hD : DenOKX p D)
    (hn : 1 ≤ n) (A : RowsAccXI n E st D R comb)
    (hG : ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n)
    (hreal : (st 0).isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (he : D (hdV (E 0) xE) = some x.result) : Nock.Jet.HoldsN x := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨t, hroot, hrow, hlink⟩ :=
    tree_of_goal (K := K) p hp0 (rowsWX E st) hn (fun i _ _ => smallR_rowW _ _) hG
  let rw : StateX × RowVSX → RowVSX := fun l =>
    if h : ∃ i, 1 ≤ i ∧ i ≤ n ∧ l = lblOf (rowsWX E st) i then
      rowOfX (E (Nat.find h - 1)) (st (Nat.find h - 1)) else l.2
  have rw_spec : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i ∧
      rw u.label = rowOfX (E (i - 1)) (st (i - 1)) := by
    intro u hu
    have h := hrow u hu
    exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2.1, (Nat.find_spec h).2.2,
      by simp only [rw, dif_pos h]⟩
  have hrt : rw t.label = rowOfX (E 0) (st 0) := by
    have h : ∃ i, 1 ≤ i ∧ i ≤ n ∧ t.label = lblOf (rowsWX E st) i := ⟨1, le_rfl, hn, hroot⟩
    have h1 : Nat.find h = 1 := le_antisymm (Nat.find_min' h ⟨le_rfl, hn, hroot⟩) (Nat.find_spec h).1
    simp only [rw, dif_pos h, h1]
  have hok : RowsOKXI rw p D R t := by
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      rw [hrw]
      exact rowSemXI_of_chip hD (by omega) (A.base _ (by omega)) (st (i - 1)) (A.oh _ (by omega))
        (A.served _ (by omega)) (fun hs => halving_of_treeI hp A hrow hlink hu hui hs rfl)
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      have hm : u.children.map (fun c => (rw c.label).trip) = u.children.map (fun c => c.label.2.trip) :=
        List.map_congr_left fun c hc => by
          obtain ⟨j, -, -, hcj, hrwc⟩ := rw_spec c (inTree_trans hu (InTree.sub hc (InTree.here _)))
          rw [hrwc, hcj]
          simp only [lblOf, rowsWX, rowW_trip]
      rw [hm, hlink u hu, hrw, hui]
      simp only [lblOf, rowsWX]
      by_cases hs : st (i - 1) = .s10L
      · have hH := halving_of_treeI hp A hrow hlink hu hui hs
        have hO := A.oh (i - 1) (by omega)
        rw [hs] at hO ⊢
        exact kidsX_rowW_of_halving (A.base _ (by omega)) hO hH
      · rw [rowW_of_ne _ hs]
  exact holdsN_of_rowsVSXI rw hR hD t hok (by rw [hrt]; exact hreal) x (by rw [hrt]; exact hs)
    (by rw [hrt]; exact hf) (by rw [hrt]; exact he)

end Tree2

section Accept
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (BCtx)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptJ8 (bctx_of_xctx goalJ8)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "EN" => envsN hn nodes chalV pubVal orbit P
local notation "CV" => coinsCV b δ chalV

/-- **`acceptsJ8_holdsN_computeA` at the implication form**: the provider obligation is
`hprov : ProvP (RecOKI D R comb)`. -/
theorem acceptsJ8_holdsN_computeI [CharP K p] [CharP 𝕂′ p] {α γ seed : K}
    (C : XCtx hn nodes b δ chalV pubVal orbit P α γ seed) (hp : 2 ^ 63 + 1 < p)
    {D : HX → Option Noun} {R : Nock.Jet.Registry} {comb : ℕ → Noun}
    (hR : R.Faithful) (hD : DenOKX p D)
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW (EN 0) (stX (EN 0))).trip) * α)
    (hα : α ∉ tileSet (foOf (rowsWX (fun r => EN r) (fun r => stX (EN r)))) n)
    (hw : (α, γ) ∉ cwEvent (K := K) (rowsWX (fun r => EN r) (fun r => stX (EN r))) n)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hout : ∀ bl, ((CV).gamma, (CV).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p)
    (hprov : ∀ bl, ProvP (p := p) (K := K) (RecOKI D R comb) bl (provs bl))
    (haxP : ∀ bl, ProvP (p := p) (K := K) AxOK bl (provs bl))
    (hreal : (stX (EN 0)).isChain = false) (x : P8PublicClaim)
    (hs : D (hdV (EN 0) xS) = some x.subject) (hf : D (hdV (EN 0) xF) = some x.formula)
    (he : D (hdV (EN 0) xE) = some x.result) : Nock.Jet.HoldsN x := by
  have hp4 : 4 < p := by omega
  have B := bctx_of_xctx C
  have hOK := servedP_of_balancesJ8 B hp4 hbal hout hcount hprov
  have hAx := servedP_of_balancesJ8 B hp4 hbal hout hcount haxP
  obtain ⟨hbase, hoh⟩ := base_oh_of_sat C
  have A : RowsAccXI n (fun r => EN r) (fun r => stX (EN r)) D R comb :=
    { base := hbase
      oh := hoh
      served := hOK
      ax := fun r hr hst => by
        have h12 := hoh r hr
        rw [hst] at h12
        exact ax_of_axOK (hbase r hr) h12 (hAx r hr) }
  exact holdsN_of_walkJ8I (K := K) hp hR hD hn A (goalJ8 C hseed hα hw) hreal x hs hf he

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8
