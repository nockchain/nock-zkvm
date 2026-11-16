/-
  Nock/NockVMROM/Thm54/VclL/Chips/MemSoundnessVCLW.lean

  **`MemSoundnessVCLW` — the memory soundness
  family at VCL with the paper's walk in place of the path chip.**  Twins of `MemSoundVCL.lean` §1–§5, `MemResponseVCL.lean` §5–§7 and `MemSoundnessVCL.lean` at
  `shapeVW` (cells `225`, walk `132`).  Same `frameVCL` (11 coins), same record view
  `RV.recordViewVCL` (record type `(root, child, axis, rootIdx)` at `m = 8`), same seed
  `seedSpecVCL`, same IO coins `ioSpecVCLQuad`.

  * §1 the B0 decode and the served-noun fields at `shapeVW` (`cellRowsB0W`, `decodedNounW`,
    `vclServedKeysW` / `vclServedRootW` / `vclServedW`, window `2^110`).
  * §4 **`memSoundnessVCLW`**: the `MemSoundnessFamily` at the same interface.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemFamilyVCLW
import Nock.NockVMROM.Thm54.VclL.Chips.MemResponseVCL
import Nock.NockVMROM.Thm54.VclL.Chips.HonestVCLW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.RecordCarrier
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The B0 decode and the served-noun fields at `shapeVW` -/

section Served
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates
  WChip.baseGates WChip.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr : ℕ) {hC : ℕ}

variable (V : VerifierData F K hC (shapeVW hT hP))
  (b : ∀ t : Fin (shapeVW hT hP).k, B0Cols F ((shapeVW hT hP).table t))

/-- The B0 message of both tables as traces. -/
def bTrW : ∀ t : Fin (shapeVW hT hP).k, Fin ((shapeVW hT hP).table t).width → F[X] :=
  fun t => b0Trace (b t)

/-- **The cell table's round-0 rows, from the B0 message alone.** -/
def cellRowsB0W : List (CellRowB0 (ringChar F)) :=
  List.ofFn fun i : Fin (V.memRows (tCW hT hP)) =>
    cellB0Of (cellEnvF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) 0 0
      (b0Trace (b (tCW hT hP))) i)

/-- **The noun at serial `i`**: the B0 decode, capped at the window. -/
def decodedNounW (i : ℕ) : Noun :=
  match preZNounOfTable (cellRowsB0W hT hP V b) i with
  | some n => capN n
  | none => .atom 0

theorem decodedNounW_leaves (i : ℕ) : (decodedNounW hT hP V b i).leaves ≤ fuelChip := by
  unfold decodedNounW; split
  · exact capN_leaves _
  · simp [Noun.leaves, fuelChip]

/-- **`servedKeys`**: the keys of the providers at the B0 message. -/
def vclServedKeysW : List RV.KeyVCL :=
  ((vclRespW δF hT hP kr V (bTrW hT hP b) 0).map fun r => RV.keyVCL 0 r.1) ++
  ((vclRespW δF hT hP kr V (bTrW hT hP b) 1).map fun r => RV.keyVCL 1 r.1) ++
  ((vclRespW δF hT hP kr V (bTrW hT hP b) 2).map fun r => RV.keyVCL 2 r.1)

theorem vclServedKeysW_length :
    (vclServedKeysW δF hT hP kr V b).length ≤ ∑ a, vclRespBoundW hT hP V a := by
  rw [Fin.sum_univ_three]
  simp only [vclServedKeysW, List.length_append, List.length_map]
  have h0 := vclRespW_length δF hT hP kr V (bTrW hT hP b) 0
  have h1 := vclRespW_length δF hT hP kr V (bTrW hT hP b) 1
  have h2 := vclRespW_length δF hT hP kr V (bTrW hT hP b) 2
  omega

/-- **`servedRoot`**. -/
def vclServedRootW : RV.KeyVCL → Noun
  | .valid i => decodedNounW hT hP V b i
  | .export i _ => decodedNounW hT hP V b i
  | .path ri _ => decodedNounW hT hP V b ri

/-- **`served`**. -/
def vclServedW : RV.KeyVCL → Noun
  | .valid i => decodedNounW hT hP V b i
  | .export i s => sideChild s (decodedNounW hT hP V b i)
  | .path ri ax => (Noun.slot ax (decodedNounW hT hP V b ri)).getD (.atom 0)

theorem vclServedW_leaves_le (κ : RV.KeyVCL) :
    (vclServedRootW hT hP V b κ).leaves ≤ vclWindow ∧ (vclServedW hT hP V b κ).leaves ≤ vclWindow := by
  cases κ with
  | valid i => exact ⟨decodedNounW_leaves hT hP V b i, decodedNounW_leaves hT hP V b i⟩
  | «export» i s =>
    exact ⟨decodedNounW_leaves hT hP V b i,
      (sideChild_leaves s _).trans (decodedNounW_leaves hT hP V b i)⟩
  | path ri ax =>
    refine ⟨decodedNounW_leaves hT hP V b ri, ?_⟩
    show ((Noun.slot ax (decodedNounW hT hP V b ri)).getD (.atom 0)).leaves ≤ fuelChip
    cases hs : Noun.slot ax (decodedNounW hT hP V b ri) with
    | none => simp [Noun.leaves, fuelChip]
    | some n =>
      exact (RootGoodF.slot_leaves_le' ax _ hs).trans (decodedNounW_leaves hT hP V b ri)

end Served

/-! ## 2. -/

theorem round1Coins_of_sampled0 :
    ∀ i : Fin frameVCL.n, frameVCL.sampledAfter i < 1 → i ∈ WalkVCL.round1Coins := by
  decide

section Summands
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates
  WChip.baseGates WChip.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP kr : ℕ) {hC : ℕ} {C : TableSpec}
  (V : VerifierData F K hC (shapeVW hT hP))

/-- The cell table's round-0 rows of a trace pair. -/
def rowsOfTrW (tr : Traces F C (shapeVW hT hP)) : List (CellRowB0 (ringChar F)) :=
  cellRowsB0W hT hP V (fun t => b0 (tr.2 t))

theorem rowsOfTrW_length (tr : Traces F C (shapeVW hT hP)) :
    (rowsOfTrW hT hP V tr).length = V.memRows (tCW hT hP) := by
  simp [rowsOfTrW, cellRowsB0W]

theorem rowsOfTrW_const (Q : Coins frameVCL K → Traces F C (shapeVW hT hP))
    (hQ : TracesStaged frameVCL C (shapeVW hT hP) Q) (χ χ' : Coins frameVCL K) :
    rowsOfTrW hT hP V (Q χ) = rowsOfTrW hT hP V (Q χ') := by
  have e : (fun t => b0 ((Q χ).2 t)) = (fun t => b0 ((Q χ').2 t)) := by
    funext t j
    show (Q χ).2 t j.1 = (Q χ').2 t j.1
    exact hQ.2 t j.1 χ χ' (fun i hi => absurd hi (by rw [j.2]; omega))
  simp only [rowsOfTrW, e]

/-- The census (T2, `skel := []`). -/
def vclCensusW : BadSummand frameVCL K (Traces F C (shapeVW hT hP)) (TracesStaged frameVCL C (shapeVW hT hP)) :=
  vclCensusSummand (algebraMap F K δF) (TracesStaged frameVCL C (shapeVW hT hP)) (rowsOfTrW hT hP V)
    (fun _ => []) (V.memRows (tCW hT hP)) V.N (fun tr => (rowsOfTrW_length hT hP V tr).le)
    (fun _ => by simp) (fun Q hQ χ χ' => ⟨rowsOfTrW_const hT hP V Q hQ χ χ', rfl⟩)

/-- The dyck-root event. -/
def vclDyckW : BadSummand frameVCL K (Traces F C (shapeVW hT hP)) (TracesStaged frameVCL C (shapeVW hT hP)) :=
  vclCellDyckRootSummand (algebraMap F K δF) (TracesStaged frameVCL C (shapeVW hT hP)) (rowsOfTrW hT hP V)
    (V.memRows (tCW hT hP)) (fun tr => (rowsOfTrW_length hT hP V tr).le)
    (fun Q hQ χ χ' => rowsOfTrW_const hT hP V Q hQ χ χ')

def walkOfTr (tr : Traces F C (shapeVW hT hP)) :
    WalkVCL.WalkData (ringChar F) (Quad (algebraMap F K δF)) :=
  walkDataOf δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP)) 0 0
    (tr.2 (tWW hT hP))

/-- **The summand's staging input `hconst`, proved**: along a staged strategy the walk data reads
only the round-1 coins `{z₁, z₂, a, b, c}` (it reads the walk table's round-`≤ 1` columns only). -/
theorem walkOfTr_readsOn (Q : Coins frameVCL K → Traces F C (shapeVW hT hP))
    (hQ : TracesStaged frameVCL C (shapeVW hT hP) Q) :
    ReadsOnC frameVCL WalkVCL.round1Coins (fun χ => walkOfTr δF hT hP kr V (Q χ)) := by
  intro χ χ' hχ
  refine walkDataOf_congr δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP))
    (V.orbitM (tWW hT hP)) _ _ (show 93 ≤ 132 by omega) (show 93 ≤ 132 by omega) ?_ 0 0 0 0
  intro j hj
  exact hQ.2 (tWW hT hP) ⟨j, by show j < 132; omega⟩ χ χ' (fun i hi =>
    hχ i (round1Coins_of_sampled0 i (lt_of_lt_of_le hi (round_walk hT hP j hj))))

variable [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]

def vclWalkSummandW : BadSummand frameVCL K (Traces F C (shapeVW hT hP)) (TracesStaged frameVCL C (shapeVW hT hP)) :=
  WalkVCL.vclWalkSummand (algebraMap F K δF) (TracesStaged frameVCL C (shapeVW hT hP))
    (walkOfTr δF hT hP kr V) (V.memRows (tWW hT hP)) (fun _ => le_refl _)
    (walkOfTr_readsOn δF hT hP kr V)

/-- **`summands`**: the zero seed, the census, the dyck-root event, and the walk summand. -/
def vclSummandsW (_x : Unit) :
    List (BadSummand frameVCL K (Traces F C (shapeVW hT hP)) (TracesStaged frameVCL C (shapeVW hT hP))) :=
  [zeroSummand (F := F) (C := C) (S := shapeVW hT hP) (Z := seedSpecVCL (algebraMap F K δF)),
    vclCensusW δF hT hP V, vclDyckW δF hT hP V, vclWalkSummandW δF hT hP kr V]

theorem vclWalkSummandW_shape :
    (vclWalkSummandW δF hT hP kr V (C := C)).coins.card = 2 ∧
      (vclWalkSummandW δF hT hP kr V (C := C)).dep = WalkVCL.round1Coins ∧
      (vclWalkSummandW δF hT hP kr V (C := C)).weight =
        Fintype.card K * (15 * V.memRows (tWW hT hP)) :=
  WalkVCL.vclWalkSummand_shape _ _ _ _ _ _

theorem vclSummandsW_good (x : Unit) (tr : Traces F C (shapeVW hT hP)) (χ : Coins frameVCL K)
    (h : ∀ s ∈ vclSummandsW δF hT hP kr V x, ¬ s.mem tr χ) :
    (seedSpecVCL (algebraMap F K δF)).seed χ ≠ 0 ∧
    (seedSpecVCL (algebraMap F K δF)).seed χ ∉
      tableBadSeeds (Kfp := Quad (algebraMap F K δF)) fuelChip (rowsOfTrW hT hP V tr) [] ∧
    (seedSpecVCL (algebraMap F K δF)).seed χ ∉
      cellDyckRootSeeds (Kfp := Quad (algebraMap F K δF)) fuelChip (rowsOfTrW hT hP V tr) ∧
    (χ ⟨0, by decide⟩, χ ⟨1, by decide⟩) ∉
      WalkVCL.walkEvent (algebraMap F K δF) (walkOfTr δF hT hP kr V tr) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    apply h _ (List.mem_cons_self ..)
    unfold zeroSummand
    rw [seedSummand_mem]
    simp [h0]
  · intro hm
    apply h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    unfold vclCensusW vclCensusSummand
    rw [tableCensusSummand_mem_iff]
    convert hm using 2
    rfl
  · intro hm
    apply h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    unfold vclDyckW
    rw [vclCellDyckRootSummand_mem_iff]
    convert hm using 2
    rfl
  · intro hm
    apply h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
    exact (WalkVCL.vclWalkSummand_mem_iff _ _ _ _ _ _ tr χ).mpr hm

end Summands

/-! ## 3. The walk records are genuine -/

section Decode
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp]

/-- **A decoded serial on an accepted table**: the serial is a row index and the noun is within the
window (`SerialOK` names the row; `preZNounOfTable_sound` bounds its leaves). -/
theorem preZ_some_facts [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {t : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z t vl) {ri : ℕ} {rt : Noun}
    (hd : preZNounOfTable (t.map (·.b0)) ri = some rt) : rt.leaves ≤ fuelChip ∧ ri < t.length := by
  have hlt : ri < t.length := by
    by_contra hge
    push Not at hge
    have hn : (t.map (·.b0))[ri]? = none := List.getElem?_eq_none (by simpa using hge)
    have : preZNounOfTable (t.map (·.b0)) ri = none := by
      unfold preZNounOfTable fuelChip
      rw [show (2 : ℕ) ^ 110 = (2 ^ 110 - 1) + 1 by norm_num]
      simp only [decodeB0, hn, Option.bind_none]
    rw [this] at hd; cases hd
  have hc : t[ri] ∈ t := List.getElem_mem hlt
  have hidx : t[ri].b0.idx = ri := by
    have e := congrArg (fun l => l[ri]?) h.serial
    simp only [List.map_map, List.getElem?_map, List.length_map, List.getElem?_range hlt] at e
    rw [List.getElem?_eq_getElem hlt] at e
    simpa using e
  obtain ⟨n, hn, -, -, hl, -⟩ := preZNounOfTable_sound hq hz h _ hc
  rw [hidx, hd] at hn
  cases hn
  exact ⟨hl, hlt⟩

end Decode

section Arith
variable {F : Type} [Field F] [DecidableEq F]

/-- **The record axis is the label's `2·prefix + b`**: `natOf (2x + b) = (2·zq x + bitZ b).val`. -/
theorem natOf_axis (hF : GeneratedField.PrimeFieldElems F) (hp : 1 < ringChar F) (x : F) (c : Bool) :
    natOf (2 * x + (if c then 1 else 0)) = (2 * zq x + WalkVCL.bitZ c : ZMod (ringChar F)).val := by
  set m := natOf x with hm
  have hx : (m : F) = x := natOf_cast hF x
  have e1 : (2 * zq x + WalkVCL.bitZ c : ZMod (ringChar F)) =
      ((2 * m + WalkVCL.bitN c : ℕ) : ZMod (ringChar F)) := by
    rw [zq, WalkVCL.bitZ_cast]; push_cast; ring
  have e2 : (2 * x + (if c then 1 else 0) : F) =
      (((2 * m + WalkVCL.bitN c) % ringChar F : ℕ) : F) := by
    rw [← CharP.cast_eq_mod F (ringChar F)]
    push_cast
    rw [hx]
    cases c <;> simp [WalkVCL.bitN]
  rw [e1, ZMod.val_natCast, e2, natOf_natCast hF (Nat.mod_lt _ (by omega))]

/-- A `zq` equation with both sides below `p` is a `natOf` equation. -/
theorem natOf_of_zq (hF : GeneratedField.PrimeFieldElems F) {x : F} {ri : ℕ} (hri : ri < ringChar F)
    (h : zq x = (ri : ZMod (ringChar F))) : natOf x = ri := by
  have e := congrArg ZMod.val h
  rw [zq, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (natOf_lt hF x),
    Nat.mod_eq_of_lt hri] at e
  exact e

end Arith

section Entries
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (eK : Env K) (eF : Env F)

theorem recL_root : RV.fpAt (keyVec δF 8 WChip.recL eK eF) 0 (by omega) = (QFP.var WChip.rootR).ev δF eK eF := by
  simp [RV.fpAt, keyVec, WChip.recL, QFP.var, QFP.entries, QFP.ev]
theorem recL_child : RV.fpAt (keyVec δF 8 WChip.recL eK eF) 3 (by omega) = (QFP.var WChip.lR).ev δF eK eF := by
  simp [RV.fpAt, keyVec, WChip.recL, QFP.var, QFP.entries, QFP.ev]
theorem recL_ax : keyVec δF 8 WChip.recL eK eF 6 = liftQ (K := K) δF (2 * eF.trace WChip.pre) := by
  simp [keyVec, WChip.recL, QFP.var, QFP.entries, ev_base, CoeffExpr.eval, cv, cst]
theorem recL_ridx : keyVec δF 8 WChip.recL eK eF 7 = liftQ (K := K) δF (eF.trace WChip.ridx) := by
  simp [keyVec, WChip.recL, QFP.var, QFP.entries, ev_base, CoeffExpr.eval, cv]
theorem recR_root : RV.fpAt (keyVec δF 8 WChip.recR eK eF) 0 (by omega) = (QFP.var WChip.rootR).ev δF eK eF := by
  simp [RV.fpAt, keyVec, WChip.recR, QFP.var, QFP.entries, QFP.ev]
theorem recR_child : RV.fpAt (keyVec δF 8 WChip.recR eK eF) 3 (by omega) = (QFP.var WChip.rR).ev δF eK eF := by
  simp [RV.fpAt, keyVec, WChip.recR, QFP.var, QFP.entries, QFP.ev]
theorem recR_ax : keyVec δF 8 WChip.recR eK eF 6 = liftQ (K := K) δF (2 * eF.trace WChip.pre + 1) := by
  simp [keyVec, WChip.recR, QFP.var, QFP.entries, ev_base, CoeffExpr.eval, cv, cst]
theorem recR_ridx : keyVec δF 8 WChip.recR eK eF 7 = liftQ (K := K) δF (eF.trace WChip.ridx) := by
  simp [keyVec, WChip.recR, QFP.var, QFP.entries, ev_base, CoeffExpr.eval, cv]

end Entries

section WalkRecords
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (kroots : ℕ) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs chals' pubs' : ℕ → K)

theorem walkEnvF_trace_congr {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) {B : ℕ} (hB : B ≤ w)
    (hB' : B ≤ w') (hQ : ∀ (j : ℕ) (hj : j < B), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) (i : ℕ) :
    ∀ j < B, (walkEnvF b hn nodes orbit chals pubs Q i).trace j =
      (walkEnvF b hn nodes orbit chals' pubs' Q' i).trace j := by
  intro j hj
  unfold walkEnvF
  rw [envOfTrace_trace Q _ _ _ _ (by omega : j < w), envOfTrace_trace Q' _ _ _ _ (by omega : j < w'),
    hQ j hj]

/-- The walk records' keys read only B0 entries (`2·prefix [+1]`, `rootIdx`). -/
theorem wPRec_keys_congr {w w' : ℕ} (Q : Fin w → F[X]) (Q' : Fin w' → F[X]) (hw : 21 ≤ w) (hw' : 21 ≤ w')
    (hQ : ∀ (j : ℕ) (hj : j < 21), Q ⟨j, by omega⟩ = Q' ⟨j, by omega⟩) :
    (walkPRecords δF kroots b hn nodes orbit chals pubs Q).map (fun r => RV.pathKey r.1) =
      (walkPRecords δF kroots b hn nodes orbit chals' pubs' Q').map (fun r => RV.pathKey r.1) := by
  have hE := fun j => walkEnvF_trace_congr b hn nodes orbit chals pubs chals' pubs' Q Q' hw hw' hQ j
  unfold walkPRecords
  simp only [List.map_flatMap, List.map_cons, List.map_nil]
  refine List.flatMap_congr fun j _ => ?_
  simp only [walkKey, RV.pathKey, recL_ax, recL_ridx, recR_ax, recR_ridx]
  rw [hE j WChip.pre (by decide), hE j WChip.ridx (by decide)]

/-- The four response conjuncts of one path record from its decoded pieces. -/
theorem path_record_core {z : Quad (algebraMap F K δF)} (dnn : ℕ → Noun) (SR SD : RV.KeyVCL → Noun)
    (hSR : ∀ ri ax, SR (.path ri ax) = dnn ri)
    (hSD : ∀ ri ax, SD (.path ri ax) = (Noun.slot ax (dnn ri)).getD (.atom 0))
    {r : Fin 8 → Quad (algebraMap F K δF)} {ri ax : ℕ} {rt nn : Noun}
    (hkey : RV.pathKey r = .path ri ax) (hax : RV.pathAxis r = ax)
    (hroot : RV.pathRoot r = GlobalCarryRecognizer.enc z rt)
    (hchild : RV.pathChild r = GlobalCarryRecognizer.enc z nn)
    (hslot : Noun.slot ax rt = some nn) (hdn : dnn ri = rt) :
    RV.pathRoot r = GlobalCarryRecognizer.enc z (SR (RV.pathKey r)) ∧
      RV.pathChild r = GlobalCarryRecognizer.enc z (SD (RV.pathKey r)) ∧
      Noun.slot (RV.pathAxis r) (SR (RV.pathKey r)) = some (SD (RV.pathKey r)) := by
  rw [hkey, hax, hSR, hSD, hdn, hslot]
  exact ⟨hroot, hchild, rfl⟩

theorem walk_records_sound (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
    {w : ℕ} (Q : Fin w → F[X]) {z : Quad (algebraMap F K δF)} (hz : z ≠ 0)
    {tb : List (CellRow (ringChar F) (Quad (algebraMap F K δF)))}
    {vl : List (VKey (Quad (algebraMap F K δF)))} (htab : TableAccepts z tb vl)
    (htlen : tb.length < ringChar F)
    (hAG : WalkVCL.AllRecordsGenuine z tb (walkDataOf δF kroots b hn nodes orbit chals pubs Q).X
      (walkDataOf δF kroots b hn nodes orbit chals pubs Q).lbl n)
    (dnn : ℕ → Noun)
    (hdn : ∀ idx m, preZNounOfTable (tb.map (·.b0)) idx = some m → m.leaves ≤ fuelChip → dnn idx = m)
    (SR SD : RV.KeyVCL → Noun) (SK : List RV.KeyVCL)
    (hSR : ∀ ri ax, SR (.path ri ax) = dnn ri)
    (hSD : ∀ ri ax, SD (.path ri ax) = (Noun.slot ax (dnn ri)).getD (.atom 0))
    (hSK : ∀ r ∈ walkPRecords δF kroots b hn nodes orbit chals pubs Q, RV.pathKey r.1 ∈ SK) :
    ∀ r ∈ walkPRecords δF kroots b hn nodes orbit chals pubs Q,
      RV.pathKey r.1 ∈ SK ∧ RV.pathRoot r.1 = GlobalCarryRecognizer.enc z (SR (RV.pathKey r.1)) ∧
      RV.pathChild r.1 = GlobalCarryRecognizer.enc z (SD (RV.pathKey r.1)) ∧
      Noun.slot (RV.pathAxis r.1) (SR (RV.pathKey r.1)) = some (SD (RV.pathKey r.1)) := by
  intro r hr
  refine ⟨hSK r hr, ?_⟩
  unfold walkPRecords at hr
  obtain ⟨j, hj, hrj⟩ := List.mem_flatMap.mp hr
  have hjn := List.mem_range.mp hj
  set eK := walkEnvK δF kroots b hn nodes orbit chals pubs Q j with heK
  set eF := walkEnvF b hn nodes orbit chals pubs Q j with heF
  have hp1 : 1 < ringChar F := by omega
  have hlbl : (walkDataOf δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1) = lblRow δF eK eF := by
    show lblRow δF (walkEnvK δF kroots b hn nodes orbit chals pubs Q (j + 1 - 1))
      (walkEnvF b hn nodes orbit chals pubs Q (j + 1 - 1)) = _
    rw [Nat.add_sub_cancel]
  have hkX : keyRow δF eK eF ∈ (walkDataOf δF kroots b hn nodes orbit chals pubs Q).X :=
    List.mem_ofFn.mpr ⟨⟨j, hjn⟩, rfl⟩
  have hk1 : (keyRow δF eK eF).1 = ((walkDataOf δF kroots b hn nodes orbit chals pubs Q).lbl (j + 1)).2.node := by
    rw [hlbl]; rfl
  -- the decoded pieces at side `c`
  have side : ∀ c : Bool, ∃ ri rt nn, natOf (eF.trace WChip.ridx) = ri ∧ dnn ri = rt ∧
      (QFP.var WChip.rootR).ev δF eK eF = GlobalCarryRecognizer.enc z rt ∧
      WalkVCL.tgt (keyRow δF eK eF) c = GlobalCarryRecognizer.enc z nn ∧
      Noun.slot (natOf (2 * eF.trace WChip.pre + (if c then 1 else 0))) rt = some nn := by
    intro c
    obtain ⟨ri, rt, nn, hri, hd, hroot, htgt, hslot⟩ :=
      hAG (j + 1) (by omega) (by omega) _ hkX hk1 c
    rw [hlbl] at hri hroot hslot
    obtain ⟨hleaf, hrlt⟩ := preZ_some_facts hq hz htab hd
    refine ⟨ri, rt, nn, natOf_of_zq hF (by omega) hri, hdn _ _ hd hleaf, hroot, htgt, ?_⟩
    rw [natOf_axis hF hp1]; exact hslot
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrj
  rcases hrj with rfl | rfl
  · obtain ⟨ri, rt, nn, hri, hd, hroot, htgt, hslot⟩ := side false
    simp only [Bool.false_eq_true, if_false, add_zero] at hslot
    refine path_record_core δF dnn SR SD hSR hSD (ri := ri) (ax := natOf (2 * eF.trace WChip.pre))
      ?_ ?_ ?_ ?_ hslot hd
    · simp only [walkKey, RV.pathKey, recL_ax, recL_ridx, natLift_liftQ δF hF, ← heK, ← heF, hri]
    · simp only [walkKey, RV.pathAxis, recL_ax, natLift_liftQ δF hF, ← heK, ← heF]
    · simp only [walkKey, RV.pathRoot, recL_root, ← heK, ← heF]; exact hroot
    · simp only [walkKey, RV.pathChild, recL_child, ← heK, ← heF]
      rw [← htgt]; simp [WalkVCL.tgt, WalkVCL.keyEdge, VclL.childOf, keyRow]
  · obtain ⟨ri, rt, nn, hri, hd, hroot, htgt, hslot⟩ := side true
    simp only [if_true] at hslot
    refine path_record_core δF dnn SR SD hSR hSD (ri := ri) (ax := natOf (2 * eF.trace WChip.pre + 1))
      ?_ ?_ ?_ ?_ hslot hd
    · simp only [walkKey, RV.pathKey, recR_ax, recR_ridx, natLift_liftQ δF hF, ← heK, ← heF, hri]
    · simp only [walkKey, RV.pathAxis, recR_ax, natLift_liftQ δF hF, ← heK, ← heF]
    · simp only [walkKey, RV.pathRoot, recR_root, ← heK, ← heF]; exact hroot
    · simp only [walkKey, RV.pathChild, recR_child, ← heK, ← heF]
      rw [← htgt]; simp [WalkVCL.tgt, WalkVCL.keyEdge, VclL.childOf, keyRow]

end WalkRecords

/-! ## 4. `response_sound` -/

section Response
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates
  WChip.baseGates WChip.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP kr : ℕ) {hC : ℕ} {C : TableSpec}
  (V : VerifierData F K hC (shapeVW hT hP))

/-- The bridge: the summands' round-0 rows are the chip's cell table's round-0 rows. -/
theorem rowsOfTrW_eq (Qc : Fin C.width → F[X])
    (Q : ∀ t : Fin (shapeVW hT hP).k, Fin ((shapeVW hT hP).table t).width → F[X])
    (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF)) (χ : Coins frameVCL K) :
    rowsOfTrW hT hP V (Qc, Q) =
      (cellTableOf δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q)).map (·.b0) := by
  unfold rowsOfTrW cellRowsB0W cellTableOf
  rw [List.map_ofFn]
  congr 1

/-- **`response_sound` with the walk** (the four conjuncts at every committed provider record of
every accumulator).  Hypotheses are the field's. -/
theorem vcl_response_soundW (ρ : Fin 3 → Quad (algebraMap F K δF)) (y : Quad (algebraMap F K δF))
    (χ : Coins frameVCL K) (Q : ∀ t : Fin (shapeVW hT hP).k, Fin ((shapeVW hT hP).table t).width → F[X])
    (h : ∀ t, RAP.SatisfiesWithPreprocessing (vclChipW δF hT hP kr ρ y V χ t)
      (fun j => Q t (Fin.cast (vclChipW_width δF hT hP kr ρ y V χ t) j)))
    (Qc : Fin C.width → F[X])
    (reqs : ∀ a : Fin 3, List (Fin (RV.mVCL a) → Quad (algebraMap F K δF)))
    (hsum : ∀ a, ((reqs a).map fun r =>
      (FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r)⁻¹).sum = ρ a)
    (hne : ∀ a, ∀ r ∈ reqs a,
      FiniteIO.compress (m := RV.mVCL a) ((ioSpecVCLQuad (algebraMap F K δF)).ioCoins χ) r ≠ 0)
    (hio : ∀ a, (ioSpecVCLQuad (algebraMap F K δF)).pair χ ∉ FiniteIO.IOFailureEventW
      (reqs a ++ vclInternalW δF hT hP kr V Q a) (liftWts (vclRespW δF hT hP kr V Q a)))
    (hcount : ∀ a, (reqs a ++ vclInternalW δF hT hP kr V Q a).length < ringChar (Quad (algebraMap F K δF)))
    (hsumm : ∀ s ∈ vclSummandsW δF hT hP kr V (C := C) (), ¬ s.mem (Qc, Q) χ) :
    ∀ a, ∀ r ∈ (vclIoFactsW h a).records,
      RV.keyVCL a r.1 ∈ vclServedKeysW δF hT hP kr V (fun t => b0 (Q t)) ∧
      RV.rootVCL a r.1 = GlobalCarryRecognizer.enc ((seedSpecVCL (algebraMap F K δF)).seed χ)
        (vclServedRootW hT hP V (fun t => b0 (Q t)) (RV.keyVCL a r.1)) ∧
      RV.childVCL a r.1 = GlobalCarryRecognizer.enc ((seedSpecVCL (algebraMap F K δF)).seed χ)
        (vclServedW hT hP V (fun t => b0 (Q t)) (RV.keyVCL a r.1)) ∧
      Noun.slot (RV.axisVCL a r.1) (vclServedRootW hT hP V (fun t => b0 (Q t)) (RV.keyVCL a r.1)) =
        some (vclServedW hT hP V (fun t => b0 (Q t)) (RV.keyVCL a r.1)) := by
  obtain ⟨⟨hgC, hsC⟩, ⟨hgW, hsW⟩⟩ := vcl_acceptedW h
  have hadjC := hgC.adj
  have hinjC := hgC.2.1
  have hF := hgC.2.2.1
  have hq := hgC.2.2.2.1
  have hnC := hgC.2.2.2.2
  have hadjW := hgW.1.adj
  have hinjW := hgW.1.2.1
  obtain ⟨-, hk1, hkn, hkp⟩ := hgW
  have hchar : ringChar (Quad (algebraMap F K δF)) = ringChar F := ringChar_quad_eq δF
  haveI hcp : CharP (Quad (algebraMap F K δF)) (ringChar F) := by
    rw [← hchar]; exact ringChar.charP _
  -- the seed and the walk coins outside the summands
  obtain ⟨hz0, hT2, hdy, hwalk⟩ := vclSummandsW_good δF hT hP kr V () (Qc, Q) χ hsumm
  have hrows := rowsOfTrW_eq δF hT hP V Qc Q ρ y χ
  rw [hrows] at hT2 hdy
  have hseed : (seedSpecVCL (algebraMap F K δF)).seed χ =
      Quad.mk (algebraMap F K δF) (chalsVCL δF χ 2) (chalsVCL δF χ 3) := by
    simp [seedSpecVCL, chalsVCL, c2, c3]; rfl
  rw [hseed] at hz0 hT2 hdy
  simp only [hseed]
  -- the cell table accepts (the validity lookup, a = 0)
  have hhio0 := hio 0
  have hhio1 := hio 1
  have hacc : TableAccepts (Quad.mk (algebraMap F K δF) (chalsVCL δF χ 2) (chalsVCL δF χ 3))
      (cellTableOf δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) (chalsVCL δF χ) (pubsC δF ρ y)
        (QCW δF hT hP ρ y V χ Q)) [] := by
    refine cellTable_accepts_of_lookup δF V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP))
      (V.orbitM (tCW hT hP)) (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) hF hq hz0 hsC.1 hsC.2
      hinjC hadjC (by omega) _ _ (chalsVCL_ok δF χ 11) (reqs 0) ?_ (hne 0) ?_ ?_ ?_ []
    · rw [pubsC_01]; exact hsum 0
    · rw [cellVInternal_eqW, cellVRecords_eqW]
      exact fun hc => hhio0 (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inl hc))
    · rw [cellVInternal_eqW, cellVRecords_eqW]
      exact fun hc => hhio0 (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc)))
    · rw [cellVInternal_eqW, ← hchar]; exact hcount 0
  -- the B0 decode through `decodedNounW`
  have hrows' : cellRowsB0W hT hP V (fun t => b0 (Q t)) =
      (cellTableOf δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) (chalsVCL δF χ) (pubsC δF ρ y)
        (QCW δF hT hP ρ y V χ Q)).map (·.b0) := hrows
  have hdn : ∀ idx m, preZNounOfTable ((cellTableOf δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP))
      (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q)).map (·.b0)) idx = some m →
      m.leaves ≤ fuelChip → decodedNounW hT hP V (fun t => b0 (Q t)) idx = m := by
    intro idx m hm hl
    simp only [decodedNounW, hrows', hm, capN_of_le hl]
  have G0 := fun i => cell_rows_genuine δF V.basis (V.memNodes (tCW hT hP))
    (V.orbitM (tCW hT hP)) (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) hq hz0 hacc
    (decodedNounW hT hP V (fun t => b0 (Q t))) hdn i
  -- the walk's keys are exported (the export lookup, a = 1)
  have hX := walk_keys_exported δF kr V.basis (V.hM (tCW hT hP)) (V.memNodes (tCW hT hP))
    (V.orbitM (tCW hT hP)) (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
    (chalsVCL δF χ) (pubsC δF ρ y) (pubsP δF ρ y) (QCW δF hT hP ρ y V χ Q) (QWW δF hT hP kr ρ y V χ Q)
    hsC.1 hsC.2 hinjC hadjC hsW.1 hsW.2 hinjW hadjW _ _ (chalsVCL_ok δF χ 11) (ρ 1)
    (by rw [pubsC_23, pubsP_01]) (reqs 1) (hsum 1) (hne 1)
    (by
      erw [walkXInternal_eqW, cellXRecords_eqW]
      exact fun hc => hhio1 (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inl hc)))
    (by
      erw [walkXInternal_eqW, cellXRecords_eqW]
      exact fun hc => hhio1 (FiniteIO.mem_IOFailureEventW_iff.mpr (Or.inr (Or.inr hc))))
    (by erw [walkXInternal_eqW]; rw [← hchar]; exact hcount 1)
  have hwd : walkDataOf δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
      (chalsVCL δF χ) (pubsP δF ρ y) (QWW δF hT hP kr ρ y V χ Q) = walkOfTr δF hT hP kr V (Qc, Q) :=
    walkDataOf_congr δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP)) _ _
      (show 93 ≤ 132 by omega) (show 93 ≤ 132 by omega) (fun j hj => rfl) _ _ _ _
  have hout : (chalsVCL δF χ 0, chalsVCL δF χ 1) ∉ WalkVCL.walkEvent (algebraMap F K δF)
      (walkDataOf δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
        (chalsVCL δF χ) (pubsP δF ρ y) (QWW δF hT hP kr ρ y V χ Q)) := by
    rw [hwd]
    have e0 : chalsVCL δF χ 0 = χ ⟨0, by decide⟩ := by simp [chalsVCL]; rfl
    have e1 : chalsVCL δF χ 1 = χ ⟨1, by decide⟩ := by simp [chalsVCL]; rfl
    rw [e0, e1]; exact hwalk
  have hAG := records_genuine_of_chip δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP))
    (V.orbitM (tWW hT hP)) (chalsVCL δF χ) (pubsP δF ρ y) (QWW δF hT hP kr ρ y V χ Q) hsW.1 hsW.2 hinjW
    hadjW hF hk1 hkn hkp hq hz0 hacc hT2 hdy hX hout
  -- the served keys contain the providers' keys (they read B0 entries only)
  have hbQ : ∀ (t : Fin (shapeVW hT hP).k) (j : ℕ) (hj : j < ((shapeVW hT hP).table t).width),
      ((shapeVW hT hP).table t).colRound ⟨j, hj⟩ = 0 →
      Q t ⟨j, hj⟩ = bTrW hT hP (fun t => b0 (Q t)) t ⟨j, hj⟩ :=
    fun t j hj h0 => (b0Trace_b0 (Q t) ⟨j, hj⟩ h0).symm
  intro a r hr
  rw [vclIoFactsW_records h a] at hr
  match a with
  | 0 =>
    have hr' : r ∈ cVRec δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) := by
      rw [← cellVRecords_eqW δF hT hP kr ρ y V χ Q] at hr; exact hr
    refine valid_records_sound δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) (chalsVCL δF χ)
      (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) _ (decodedNounW hT hP V (fun t => b0 (Q t))) hF
      (vclServedRootW hT hP V (fun t => b0 (Q t))) (vclServedW hT hP V (fun t => b0 (Q t)))
      (vclServedKeysW δF hT hP kr V (fun t => b0 (Q t)))
      (fun i => by obtain ⟨L, R, hd, hp, -⟩ := G0 i; exact ⟨L, R, hd, hp⟩)
      (fun i => rfl) (fun i => rfl) ?_ r hr'
    intro r' hr''
    have hk : RV.validKey r'.1 ∈ (cVRec δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP))
        (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q)).map (fun r => RV.validKey r.1) :=
      List.mem_map_of_mem hr''
    rw [cVRec_keys_congr δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) (chalsVCL δF χ)
      (pubsC δF ρ y) 0 0 (QCW δF hT hP ρ y V χ Q) (bTrW hT hP (fun t => b0 (Q t)) (tCW hT hP))
      (by rw [cellOkW_w' δF hT hP ρ y V χ]; show 129 ≤ 225; omega) (show 129 ≤ 225 by omega)
      (fun j hj => hbQ (tCW hT hP) j (by show j < 225; omega) (round_cell0 hT hP j hj))] at hk
    exact List.mem_append_left _ (List.mem_append_left _ hk)
  | 1 =>
    have hr' : r ∈ cXRec δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) := by
      rw [← cellXRecords_eqW δF hT hP kr ρ y V χ Q] at hr; exact hr
    have hSKx : ∀ r' ∈ cXRec δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q), RV.exportKey r'.1 ∈
        vclServedKeysW δF hT hP kr V (fun t => b0 (Q t)) := by
      intro r' hr''
      have hk : RV.exportKey r'.1 ∈ (cXRec δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP))
          (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q)).map (fun r => RV.exportKey r.1) :=
        List.mem_map_of_mem hr''
      rw [cXRec_keys_congr δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP)) (chalsVCL δF χ)
        (pubsC δF ρ y) 0 0 (QCW δF hT hP ρ y V χ Q) (bTrW hT hP (fun t => b0 (Q t)) (tCW hT hP))
        (by rw [cellOkW_w' δF hT hP ρ y V χ]; show 129 ≤ 225; omega) (show 129 ≤ 225 by omega)
        (fun j hj => hbQ (tCW hT hP) j (by show j < 225; omega) (round_cell0 hT hP j hj))] at hk
      exact List.mem_append_left _ (List.mem_append_right _ hk)
    have hres := export_records_sound δF V.basis (V.memNodes (tCW hT hP)) (V.orbitM (tCW hT hP))
      (chalsVCL δF χ) (pubsC δF ρ y) (QCW δF hT hP ρ y V χ Q) _ (decodedNounW hT hP V (fun t => b0 (Q t))) hF
      (vclServedRootW hT hP V (fun t => b0 (Q t))) (vclServedW hT hP V (fun t => b0 (Q t)))
      (vclServedKeysW δF hT hP kr V (fun t => b0 (Q t))) G0 (fun i s => rfl) (fun i s => rfl) hSKx r hr'
    exact ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2⟩
  | 2 =>
    have hr' : r ∈ walkPRecords δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP))
        (V.orbitM (tWW hT hP)) (chalsVCL δF χ) (pubsP δF ρ y) (QWW δF hT hP kr ρ y V χ Q) := by
      rw [walkPRecords_eqW δF hT hP kr ρ y V χ Q]; exact hr
    refine walk_records_sound δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
      (chalsVCL δF χ) (pubsP δF ρ y) hF hq (QWW δF hT hP kr ρ y V χ Q) hz0 hacc
      (by simp [cellTableOf]; omega) hAG (decodedNounW hT hP V (fun t => b0 (Q t))) hdn
      (vclServedRootW hT hP V (fun t => b0 (Q t))) (vclServedW hT hP V (fun t => b0 (Q t)))
      (vclServedKeysW δF hT hP kr V (fun t => b0 (Q t))) (fun ri ax => rfl) (fun ri ax => rfl) ?_ r hr'
    intro r' hr''
    have hk : RV.pathKey r'.1 ∈ (walkPRecords δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP))
        (V.orbitM (tWW hT hP)) (chalsVCL δF χ) (pubsP δF ρ y) (QWW δF hT hP kr ρ y V χ Q)).map
        (fun r => RV.pathKey r.1) := List.mem_map_of_mem hr''
    rw [wPRec_keys_congr δF kr V.basis (V.hM (tWW hT hP)) (V.memNodes (tWW hT hP)) (V.orbitM (tWW hT hP))
      (chalsVCL δF χ) (pubsP δF ρ y) 0 0 (QWW δF hT hP kr ρ y V χ Q) (bTrW hT hP (fun t => b0 (Q t)) (tWW hT hP))
      (by rw [walkOkW_w' δF hT hP kr ρ y V χ]; show 21 ≤ 132; omega) (show 21 ≤ 132 by omega)
      (fun j hj => hbQ (tWW hT hP) j (by show j < 132; omega) (round_walk0 hT hP j hj))] at hk
    exact List.mem_append_right _ hk

end Response

/-! ## 5. The family -/

section Family
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates
  WChip.baseGates WChip.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  (hT hP kr : ℕ) {hC : ℕ} {C : TableSpec}

def memSoundnessVCLW :
    MemSoundnessFamily F K (Quad (algebraMap F K δF)) (Quad (algebraMap F K δF)) RV.KeyVCL frameVCL hC
      (shapeVW hT hP) C 3 (m := RV.mVCL) (RV.recordViewVCL F K (Quad (algebraMap F K δF)) C (shapeVW hT hP) hC)
      (seedSpecVCL (algebraMap F K δF)) (ioSpecVCLQuad (algebraMap F K δF)) where
  Msg0 := Unit
  Msg2 := Quad (algebraMap F K δF)
  chip := fun V t _ ρ y χ => vclChipW δF hT hP kr ρ y V χ t
  chip_width := fun V t _ ρ y χ => vclChipW_width δF hT hP kr ρ y V χ t
  respBound := vclRespBoundW hT hP
  internal := fun V _ Q _ a => vclInternalW δF hT hP kr V Q a
  internalBound := vclInternalBoundW hT hP
  ioFacts := fun V _ ρ y χ Q h a => vclIoFactsW h a
  ioFacts_length := fun V _ ρ y χ Q h a => vclIoFactsW_length h a
  internal_length := fun V _ ρ y χ Q _ a => vclInternalW_length δF hT hP kr V Q a
  internal_ne_zero := fun V _ ρ y χ Q h a => vclInternalW_ne_zero h a
  respRecords := fun V _ Q _ a => vclRespW δF hT hP kr V Q a
  respRound := 1
  respRound_le_io := fun i hi => (ioSpecVCLQuad_round (algebraMap F K δF) i hi).ge
  respRecords_round := fun V _ Q Q' _ _ hQ _ => by
    funext a
    exact congrFun (vclRespW_round δF hT hP kr V Q Q' hQ) a
  ioFacts_records := fun V _ ρ y χ Q h a => vclIoFactsW_records h a
  internal_round := fun V _ Q Q' _ _ hQ _ => by
    funext a
    exact congrFun (vclInternalW_round δF hT hP kr V Q Q' hQ) a
  servedKeys := fun V _ b => vclServedKeysW δF hT hP kr V b
  servedRoot := fun V _ b => vclServedRootW hT hP V b
  served := fun V _ b => vclServedW hT hP V b
  servedKeys_length := fun V _ b => vclServedKeysW_length δF hT hP kr V b
  window := fun _ _ _ => vclWindow
  served_leaves_le := fun V _ b κ _ => vclServedW_leaves_le hT hP V b κ
  windowBound := fun _ _ => vclWindow
  window_le := fun _ _ _ => le_refl _
  summands := fun V x => vclSummandsW δF hT hP kr V x
  reqCond := fun _ reqs χ => reqCondVCL reqs χ
  serves := fun V _ ρ y χ Q h Qc reqs _ hsum hne hio hcount _ => vcl_servesW h reqs hsum hne hio hcount
  response_sound := fun V _ ρ y χ Q h Qc reqs _ hsum hne hio hcount hsumm =>
    vcl_response_soundW δF hT hP kr V ρ y χ Q h Qc reqs hsum hne hio hcount hsumm
  Honest := HonestVCLW (K := K) δF hT hP hC kr
  honestV := fun H => H.V
  honestMsg0 := fun _ => ()
  honestReq := fun H χ => H.req χ
  honestMsg2 := fun H χ => H.msg2 χ
  honestQ := fun H χ t => H.trace χ t
  honest_staged := fun H t => trace_stagedW H t
  honestBad := fun H => H.bad
  honest_accepted := fun H χ Qc hbad t => acceptedW H χ Qc hbad t

/-- **The walk summand is in the family's `summands`** (at every verifier datum and message). -/
theorem memSoundnessVCLW_walk_summand (V : VerifierData F K hC (shapeVW hT hP)) (x : Unit) :
    vclWalkSummandW δF hT hP kr V (C := C) ∈ (memSoundnessVCLW δF hT hP kr (C := C)).summands V x := by
  show vclWalkSummandW δF hT hP kr V ∈ vclSummandsW δF hT hP kr V x
  simp [vclSummandsW]

end Family

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
