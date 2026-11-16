/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestOfRunVSQ.lean

  Additive: a NEW module.

* `claimMsgOf` / `claimMsgOf_full`: the honest claim message (serial and rank limbs of each claim cell);
  * `vsVerifierOfRun`: the honest `VerifierData` (claim, `ω^i` compute nodes, memory rows = the run's cell
    and walk tables at `ω_k^i`, `Ksz = 0`, heights `hCq / hTq / hPq = heightOf` of the run's row counts, as
    the 39th's `vcl_completeness_of_run_chosen` chooses them); `vsV_adjC`, `vsV_injC`, `vsV_hsizeM`;
  * `hVSQ_of_run`: the honest datum at that verifier (`hVS_of_run`; `hmemC / hmemW` from rows `≤ 2^31`);
  * **`honest_accepted_VSQ_of_run_chosen`**: hypotheses only run facts, field facts, `hop5` and the coin event;
  * **`vsqV_checks`** (`hV`): `(vsqOf (vsVerifierOfRun …)).Checks` at `hsoundVSQ`'s bound vector.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestEpsVSQ
import Nock.NockVMROM.Thm54.VclL.Handle.HonestVSOfRun
import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointHonestW
import Nock.NockVMROM.Thm54.VclL.Compute.TowerChosen
import Nock.NockVMROM.Thm54.VclL.Handle.SoundVSQ

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.SVFrameG
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.GenWalk Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. Run facts: the root row, the claim binds, the deep reads -/

section RunFacts
variable {Kg : Type} [Field Kg] {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}

theorem bfsForest_root_get (hW : 0 < (bfsForest [airReorder t]).length) :
    (bfsForest [airReorder t])[0]'hW = airReorder t := by
  have h := bfsForest_cons_eq [airReorder t] (List.cons_ne_nil _ _)
  simp only [h, List.getElem_cons_zero, List.head_cons]
  rfl

/-- **`hroot` from the run**: the first compute row binds the claim. -/
theorem hroot_of_run (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result)) :
    (rowAtW (bfsForest [airReorder t]) 1).s = subject ∧
      (rowAtW (bfsForest [airReorder t]) 1).f = formula ∧
      (rowAtW (bfsForest [airReorder t]) 1).e = result := by
  have hW := VclL.Compute.TowerD.nRows_pos' (K := Kg) t
  rw [show (1 : ℕ) = 0 + 1 from rfl, rowAtW_eq _ 0 hW, bfsForest_root_get hW, airReorder_label]
  obtain ⟨h1, h2, h3⟩ := rowOfSkelH_sfe t.label.skel
  obtain ⟨g1, g2, g3⟩ := genComputeSkeleton_root_sfe hrun
  exact ⟨h1.trans g1, h2.trans g2, h3.trans g3⟩

/-- **`hslot` from the run**: every deep read of `demandH2` of the run's rows is a defined slot. -/
theorem hslot_of_run (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result)) :
    ∀ r ∈ pathReads (demandH2 (bfsRows (airReorder t))).preads, (Noun.slot r.2 r.1).isSome := by
  intro r hr
  unfold pathReads at hr
  have hr' : r ∈ walkReadsH (bfsRows (airReorder t)) := (List.mem_filter.mp (List.mem_dedup.mp hr)).1
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr'
  obtain ⟨g, hg, hxg⟩ := List.mem_flatMap.mp hx
  have := (row_cons_eq _ (rowOfSkelH_sem _ (run_rows_sem hrun g hg)) x hxg).2
  simp [this]

theorem root_mem_rows : t.label ∈ bfsRows (airReorder t) := by
  have hW := VclL.Compute.TowerD.nRows_pos' (K := Kg) t
  unfold bfsRows
  refine List.mem_map.mpr ⟨airReorder t, ?_, airReorder_label t⟩
  have h := List.getElem_mem hW
  rwa [bfsForest_root_get hW] at h

theorem rowOfSkel_sfe (sk : SemanticStrategy.ComputeRowSkeleton) :
    (rowOfSkel sk).s = sk.subject ∧ (rowOfSkel sk).f = sk.formula ∧ (rowOfSkel sk).e = sk.evaluation := by
  refine ⟨?_, rowOfSkel_f _, ?_⟩ <;> (unfold rowOfSkel; split <;> rfl)

/-- **`hbs` from the run**: the claim's cell nouns are rows of the cell table. -/
theorem hbs_of_run (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result)) :
    ∀ b ∈ (claimBinds ⟨subject, formula, result⟩).flatMap selfCell,
      b ∈ (demandH2 (bfsRows (airReorder t))).cells := by
  intro b hb
  obtain ⟨n, hn, hbn⟩ := List.mem_flatMap.mp hb
  have hroot : n ∈ handleNouns t.label := by
    obtain ⟨g1, g2, g3⟩ := genComputeSkeleton_root_sfe hrun
    obtain ⟨h1, h2, h3⟩ := rowOfSkel_sfe t.label.skel
    simp only [claimBinds, List.mem_cons, List.not_mem_nil, or_false] at hn
    simp only [handleNouns, List.mem_cons, List.not_mem_nil, or_false]
    rcases hn with rfl | rfl | rfl
    · exact Or.inl (h1.trans g1).symm
    · exact Or.inr (Or.inl (h2.trans g2).symm)
    · exact Or.inr (Or.inr (Or.inl (h3.trans g3).symm))
  have hbind : n ∈ (demandH2 (bfsRows (airReorder t))).binds :=
    List.mem_flatMap.mpr ⟨t.label, root_mem_rows, hroot⟩
  cases n with
  | atom v => simp [selfCell] at hbn
  | cell x y =>
    simp only [selfCell, List.mem_singleton] at hbn
    subst hbn
    simp only [Demand.cells, closureOf, List.mem_dedup, List.mem_flatMap]
    refine ⟨Noun.cell x y, ?_, by simp [cellsOf]⟩
    simp only [Demand.roots, List.mem_append]
    exact Or.inl (Or.inl hbind)

/-- The cell table of the run is non-empty (the claim formula is a cell). -/
theorem demandH2_cells_pos (hev : Nock.evalN fuel subject formula = some result)
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result)) :
    0 < (demandH2 (bfsRows (airReorder t))).cells.length := by
  obtain ⟨a, b, hab⟩ := VclL.Compute.TowerD.formula_cell_of_evalN hev
  refine List.length_pos_of_mem (a := Noun.cell a b) (hbs_of_run hrun _ ?_)
  simp [claimBinds, selfCell, hab]

end RunFacts

/-! ## 2. The honest claim message and the verifier from the run -/

section Claim

/-- **The honest claim message**: each claim cell's serial and rank limbs. -/
def claimMsgOf (cells : List Noun) (c : P8PublicClaim) : ClaimMsgVS := fun k =>
  (cells.idxOf (claimNoun c k), rankOf (claimNoun c k) / 2 ^ 62, rankOf (claimNoun c k) % 2 ^ 62)

theorem claimMsgOf_full (cells : List Noun) (c : P8PublicClaim) :
    HonestClaimMsgFull cells c (claimMsgOf cells c) := fun _ _ => rfl

end Claim

section Sizes
variable {Kg : Type} [Field Kg] (t : NTree (GenComputeRow Kg))

/-- The run's compute rows, cell rows and walk rows. -/
abbrev nNr : ℕ := (bfsForest [airReorder t]).length
abbrev nCr : ℕ := (demandH2 (bfsRows (airReorder t))).cells.length
abbrev nWr : ℕ :=
  (walkRows (demandH2 (bfsRows (airReorder t))).cells (demandH2 (bfsRows (airReorder t))).preads).length

/-- The heights chosen from the run (`heightOf`, as the 39th's `hCr / hTr / hPr`; the walk table at its own
length). -/
abbrev hCq : ℕ := VclL.Compute.TowerChosen.heightOf (nNr t)
abbrev hTq : ℕ := VclL.Compute.TowerChosen.heightOf (nCr t)
abbrev hPq : ℕ := VclL.Compute.TowerChosen.heightOf (nWr t)

theorem nWr_pos : 0 < nWr t := by
  have h1 := one_le_krW (demandH2 (bfsRows (airReorder t))).cells (demandH2 (bfsRows (airReorder t))).preads
  have h2 := krW_le_rows (demandH2 (bfsRows (airReorder t))).cells (demandH2 (bfsRows (airReorder t))).preads
  unfold nWr; omega

end Sizes

section Verifier
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kg]
  {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}

open VclL.Compute.TowerChosen VclL.Compute.TowerD in
/-- **The honest verifier data of a run** (at `shapeVW`; its VSQ form is `vsqOf`): the claim, the compute rows
`ω^i`, the memory rows = the run's cell table and walk table at `ω_k^i`, `Ksz = 0`, heights chosen from the run. -/
def vsVerifierOfRun (hev : Nock.evalN fuel subject formula = some result)
    (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
    (hK3 : Module.finrank F K = 3)
    (hFd : 3 * 2 ^ (max (hCq t) (max (hTq t) (hPq t))) ∣ Fintype.card F - 1) :
    VerifierData F K (hCq t) (shapeVW (hTq t) (hPq t)) where
  claim := ⟨subject, formula, result⟩
  N := nNr t
  hN := VclL.Compute.TowerD.nRows_pos' t
  Ksz := 0
  basis := Module.finBasisOfFinrankEq F K hK3
  orbitC := strictOrbitOf (hCq t) (one_le_heightOf _) (orbit_dvd_split hFd).1
  computeNodes i := (strictOrbitOf (hCq t) (one_le_heightOf _) (orbit_dvd_split hFd).1).ω ^ (i : ℕ)
  memRows k := if (k : ℕ) = 0 then nCr t else nWr t
  hM k := by
    split_ifs
    · exact demandH2_cells_pos hev hrun
    · exact nWr_pos t
  orbitM := orbitMOfW (hTq t) (hPq t) (one_le_heightOf _) (one_le_heightOf _) (orbit_dvd_split hFd).2.1
    (orbit_dvd_split hFd).2.2
  memNodes k i := (orbitMOfW (hTq t) (hPq t) (one_le_heightOf _) (one_le_heightOf _) (orbit_dvd_split hFd).2.1
    (orbit_dvd_split hFd).2.2 k).ω ^ (i : ℕ)

variable (hev : Nock.evalN fuel subject formula = some result)
  (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
  (hK3 : Module.finrank F K = 3)
  (hFd : 3 * 2 ^ (max (hCq t) (max (hTq t) (hPq t))) ∣ Fintype.card F - 1)

theorem vsV_hC0 : (vsVerifierOfRun hev hrun hK3 hFd).memRows (tCW (hTq t) (hPq t)) = nCr t := by
  show (if ((tCW (hTq t) (hPq t) : Fin 2) : ℕ) = 0 then nCr t else nWr t) = nCr t
  exact if_pos rfl
theorem vsV_hW0 : (vsVerifierOfRun hev hrun hK3 hFd).memRows (tWW (hTq t) (hPq t)) = nWr t := by
  show (if ((tWW (hTq t) (hPq t) : Fin 2) : ℕ) = 0 then nCr t else nWr t) = nWr t
  exact if_neg Nat.one_ne_zero

theorem vsV_hsizeM (k : Fin (shapeVW (hTq t) (hPq t)).k) :
    (vsVerifierOfRun hev hrun hK3 hFd).memRows k ≤ 2 ^ ((shapeVW (hTq t) (hPq t)).table k).height := by
  show (if (k : ℕ) = 0 then _ else _) ≤ _
  rw [VclL.Compute.TowerD.shapeVW_height]
  split_ifs
  · exact VclL.Compute.TowerChosen.le_two_pow_heightOf _
  · exact VclL.Compute.TowerChosen.le_two_pow_heightOf _

theorem vsV_adjC : (vsVerifierOfRun hev hrun hK3 hFd).AdjacentC := by
  intro i hi
  show _ ^ ((i : ℕ) + 1) = _ * _ ^ (i : ℕ)
  exact pow_succ' _ _

theorem vsV_injC : Function.Injective (vsVerifierOfRun hev hrun hK3 hFd).computeNodes := by
  intro a b hab
  have hord : orderOf ((vsVerifierOfRun hev hrun hK3 hFd).orbitC.ω) = 3 * 2 ^ hCq t :=
    (vsVerifierOfRun hev hrun hK3 hFd).orbitC.order_ω
  have hle : nNr t ≤ 2 ^ hCq t := VclL.Compute.TowerChosen.le_two_pow_heightOf _
  apply Fin.ext
  refine pow_injOn_Iio_orderOf ?_ ?_ hab
  · show (a : ℕ) < orderOf _
    erw [hord]; have : (a : ℕ) < nNr t := a.isLt
    omega
  · show (b : ℕ) < orderOf _
    erw [hord]; have : (b : ℕ) < nNr t := b.isLt
    omega

end Verifier

/-! ## 3. The honest datum of the run, `hV`, and honest acceptance from the run -/

section OfRun
variable {F K Kg : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Field Kg] {δF : F} [Fact (¬ IsSquare (algebraMap F K δF))] [DecidableEq (Quad (algebraMap F K δF))]
  {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}
  (hev : Nock.evalN fuel subject formula = some result)
  (hrun : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result))
  (hK3 : Module.finrank F K = 3)
  (hFd : 3 * 2 ^ (max (hCq t) (max (hTq t) (hPq t))) ∣ Fintype.card F - 1)
  (hF : GeneratedField.PrimeFieldElems F) (hq : 2 ^ 63 < ringChar F)
  {B : ℕ} (hB : programLeafBound (airReorder t) ≤ B) (hB2 : 2 * B ≤ 2 ^ 110)
  (haxis : Compute.programAxisBound (airReorder t) < 2 ^ 63) (hop5 : programOp5DepthOK t)
  (hnC : nCr t ≤ 2 ^ 31) (hnW : nWr t ≤ 2 ^ 31)

include hq hnC in
theorem memC_of_sizes : (demandH2 (runRowsH t)).cells.length + 1 < ringChar F := by
  show nCr t + 1 < _; omega

include hq hnW in
theorem memW_of_sizes :
    krW (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads +
      (walkRows (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads).length < ringChar F := by
  have := krW_le_rows (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads
  show _ + nWr t < _
  change _ ≤ nWr t at this
  omega

/-- **The honest VSQ datum of a run** (`hVS_of_run` at the verifier from the run). -/
def hVSQ_of_run : HonestVCLW (K := K) δF (hTq t) (hPq t) (hCq t)
    (krW (demandH2 (runRowsH t)).cells (demandH2 (runRowsH t)).preads) :=
  hVS_of_run (δF := δF) hrun (vsVerifierOfRun hev hrun hK3 hFd) hF hq (fun _ _ => rfl)
    (vsV_hsizeM hev hrun hK3 hFd) (vsV_hC0 hev hrun hK3 hFd) (vsV_hW0 hev hrun hK3 hFd) hB hB2 haxis hop5
    (memC_of_sizes hq hnC) (memW_of_sizes hq hnW)

/-- The honest claim message of the run. -/
abbrev xOfRun : ClaimMsgVS :=
  claimMsgOf (demandH2 (bfsRows (airReorder t))).cells ⟨subject, formula, result⟩

/-- **`honest_accepted_VSQ_of_run_chosen`: completeness at VSQ with the verifier built from the run.**
For every coin outside the priced honest bad event (`HonestGoodVSQ`, probability `≤ epsCVSQ < 2^-126` at
Goldilocks), the honest messages are accepted at `frameVSQ` by the verifier from the run.  Hypotheses:
run facts (`hev hbound hs hf hrun hB hB2 haxis hnC hnW`), field facts (`hK3 hFd hF hq`, the instances), the
OP5 depth binder `hop5`, and the coin event `hχ`. -/
theorem honest_accepted_VSQ_of_run_chosen
    {sumC : VerifierData F K (hCq t) (shapeVSQ (hTq t) (hPq t)) → ClaimMsgVS →
      SummandsVSQ (F := F) (K := K) (hTq t) (hPq t) (hCq t)}
    {sumM : VerifierData F K (hCq t) (shapeVSQ (hTq t) (hPq t)) → Unit →
      SummandsVSQ (F := F) (K := K) (hTq t) (hPq t) (hCq t)}
    (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar F) subject) (hf : FieldEmbedding.BoundedBy (ringChar F) formula)
    (χ : Coins frameVSQ K)
    (hχ : HonestGoodVSQ (hVSQ_of_run (δF := δF) hev hrun hK3 hFd hF hq hB hB2 haxis hop5 hnC hnW) t
      (xOfRun (t := t) (subject := subject) (formula := formula) (result := result)) χ) :
    AcceptsG (vsqOf (vsVerifierOfRun hev hrun hK3 hFd))
      (msgVSQ (sumC := sumC) (sumM := sumM) (hVSQ_of_run (δF := δF) hev hrun hK3 hFd hF hq hB hB2 haxis hop5 hnC hnW) t
        (xOfRun (t := t) (subject := subject) (formula := formula) (result := result))) χ :=
  honest_accepted_VSQ_whp (hVSQ_of_run (δF := δF) hev hrun hK3 hFd hF hq hB hB2 haxis hop5 hnC hnW) t _ hrun rfl
    (claimMsgOf_full _ _) rfl (vsV_injC hev hrun hK3 hFd) (vsV_adjC hev hrun hK3 hFd) (hroot_of_run hrun)
    (hbs_of_run hrun) (hslot_of_run hrun) (hat_of_run (by have := hq; omega) hev hbound hs hf hrun) χ hχ

omit [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K] [DecidableEq K] [DecidableEq F] in
theorem orbit_cast_ω {a b : ℕ} (e : a = b) (o : StrictOrbitDomain F 3 a) : (e ▸ o).ω = o.ω := by
  subst e; rfl

include hF hq hnC hnW in
/-- **`hV` at the verifier from the run**: the public checks of `hsoundVSQ` pass (any summand lists; the
bounds do not read them), when every table has `≤ 2^31` rows. -/
theorem vsqV_checks (hbound : RunBoundedBy (ringChar F) fuel subject formula)
    (hs : FieldEmbedding.BoundedBy (ringChar F) subject) (hf : FieldEmbedding.BoundedBy (ringChar F) formula)
    (hN : nNr t ≤ 2 ^ 31)
    (sumC : VerifierData F K (hCq t) (shapeVSQ (hTq t) (hPq t)) → ClaimMsgVS →
      SummandsVSQ (F := F) (K := K) (hTq t) (hPq t) (hCq t))
    (sumM : VerifierData F K (hCq t) (shapeVSQ (hTq t) (hPq t)) → Unit →
      SummandsVSQ (F := F) (K := K) (hTq t) (hPq t) (hCq t)) (kr : ℕ) :
    (vsqOf (vsVerifierOfRun hev hrun hK3 hFd)).Checks
      (fun a => (compCoreVSQ δF (hTq t) (hPq t) (hCq t) sumC).reqBound (vsqOf (vsVerifierOfRun hev hrun hK3 hFd)) a +
        (memCoreVSQ δF (hTq t) (hPq t) kr (hCq t) sumM).internalBound (vsqOf (vsVerifierOfRun hev hrun hK3 hFd)) a)
      (ringChar (Quad (algebraMap F K δF))) where
  hcapC := VclL.Compute.TowerChosen.le_two_pow_heightOf _
  hcapM k := by
    have hh := height_eq_VSQ (hT := hTq t) (hP := hPq t) k
    erw [hh]
    exact vsV_hsizeM hev hrun hK3 hFd k
  hrowsC := by
    rw [SoundVS.ringChar_KF (F := F) (K := K)]
    show 3 * nNr t < _; omega
  hrowsM k := by
    rw [SoundVS.ringChar_KF (F := F) (K := K)]
    show (if (k : ℕ) = 0 then nCr t else nWr t) < _
    split_ifs <;> omega
  hKsz := by
    rw [SoundVS.ringChar_KF (F := F) (K := K)]
    show 0 < _; omega
  hF := hF
  hp := by omega
  hclaim := ⟨hs, hf, result_boundedBy_of_hyps (by omega) (evalGRom_of_runBounded hev hbound) hs hf⟩
  computeNodes_injective := vsV_injC hev hrun hK3 hFd
  memNodes_injective := memInj_of (vsVerifierOfRun hev hrun hK3 hFd) (fun _ _ => rfl)
    (vsV_hsizeM hev hrun hK3 hFd)
  hcons a := by
    rw [ringChar_quad_eq δF]
    have hC0 := vsV_hC0 hev hrun hK3 hFd
    have hW0 := vsV_hW0 hev hrun hK3 hFd
    fin_cases a <;>
      simp only [compCoreVSQ, memCoreVSQ, reqBoundVSQ, internalBoundVSQ, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Fin.isValue] <;>
      first
        | (show 3 + 2 * nCr t < _; omega)
        | (show 0 + nWr t < _; omega)
        | (show 0 + 0 < _; omega)
        | (show 3 * nNr t + nWr t < _; omega)
        | (show 2 * nNr t + 0 < _; omega)
  hadjC := vsV_adjC hev hrun hK3 hFd
  hadjM k := by
    intro i hi
    show (vsVerifierOfRun hev hrun hK3 hFd).memNodes k _ = (vsVerifierOfRun hev hrun hK3 hFd).memNodes k i *
      ((height_eq_VSQ (hT := hTq t) (hP := hPq t) k).symm ▸ (vsVerifierOfRun hev hrun hK3 hFd).orbitM k).ω
    rw [orbit_cast_ω]
    exact memAdj_of (vsVerifierOfRun hev hrun hK3 hFd) (fun _ _ => rfl) k i hi

end OfRun

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ
