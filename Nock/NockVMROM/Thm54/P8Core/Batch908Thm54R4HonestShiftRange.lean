/-
  Nock/NockVMROM/Thm54/P8Core/Batch908Thm54R4HonestShiftRange.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch908Thm54R4HonestShiftRange`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch908Thm54R4HonestShiftRange.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch806Thm54FormRRepairSound
import Nock.NockVMROM.Thm54.P8Core.Batch824Thm54R4Bridge
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch908

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.RedTeam.Batch824

noncomputable section

section Embed

variable {F K : Type} [Field F] [Field K] (f : F →+* K) (hf : Function.Injective f) {N : ℕ}
include hf

/-- The trace columns `decodedShift` reads. -/
def ReadCols (j : ℕ) : Prop :=
  j = 0 ∨ j = 2 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ (202 ≤ j ∧ j ≤ 270)

/-- `envsK` is the image of `envsF` on every column `decodedShift` reads. -/
def Embeds (envsK : Fin N → Env K) (envsF : Fin N → Env F) : Prop :=
  ∀ i j, ReadCols j → (envsK i).trace j = f ((envsF i).trace j)

theorem eq_one_iff (x : F) (y : K) (h : y = f x) : y = 1 ↔ x = 1 := by
  rw [h, ← map_one f, hf.eq_iff]

theorem computeArity_embed (e' : Env K) (e : Env F)
    (h0 : e'.trace 0 = f (e.trace 0)) (h2 : e'.trace 2 = f (e.trace 2))
    (h5 : e'.trace 5 = f (e.trace 5)) (h6 : e'.trace 6 = f (e.trace 6))
    (h7 : e'.trace 7 = f (e.trace 7)) (h8 : e'.trace 8 = f (e.trace 8))
    (h9 : e'.trace 9 = f (e.trace 9)) :
    computeArity e' = computeArity e := by
  have k1 : (e'.trace 0 + (e'.trace 2 + (e'.trace 5 + (e'.trace 6 + (e'.trace 7 +
      (e'.trace 8 + e'.trace 9)))))) = 1 ↔ (e.trace 0 + (e.trace 2 + (e.trace 5 +
      (e.trace 6 + (e.trace 7 + (e.trace 8 + e.trace 9)))))) = 1 := by
    rw [h0, h2, h5, h6, h7, h8, h9, ← map_add, ← map_add, ← map_add, ← map_add, ← map_add,
      ← map_add, ← map_one f, hf.eq_iff]
  have k2 : e'.trace 6 + e'.trace 9 = 1 ↔ e.trace 6 + e.trace 9 = 1 := by
    rw [h6, h9, ← map_add, ← map_one f, hf.eq_iff]
  unfold computeArity
  by_cases a1 : (e.trace 0 + (e.trace 2 + (e.trace 5 + (e.trace 6 + (e.trace 7 +
      (e.trace 8 + e.trace 9)))))) = 1 <;>
  by_cases a2 : e.trace 6 + e.trace 9 = 1 <;>
  simp [a1, a2, k1.mpr, k2.mpr, (not_congr k1).mpr, (not_congr k2).mpr]

theorem rowShift_embed (e' : Env K) (e : Env F)
    (h : ∀ k, k < 6 → e'.trace (265 + k) = f (e.trace (265 + k))) :
    rowShift e' = rowShift e := by
  unfold rowShift
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < 6 := Finset.mem_range.mp hk
  by_cases hx : e.trace (265 + k) = 1
  · have : e'.trace (265 + k) = 1 := (eq_one_iff f hf _ _ (h k hk')).mpr hx
    simp [hx, this]
  · have : ¬ e'.trace (265 + k) = 1 := fun h' => hx ((eq_one_iff f hf _ _ (h k hk')).mp h')
    simp [hx, this]

theorem decodedShift_embed {envsK : Fin N → Env K} {envsF : Fin N → Env F}
    (hE : Embeds f envsK envsF) (e : ℕ) :
    decodedShift envsK e = decodedShift envsF e := by
  have har : ∀ i, computeArity (envsK i) = computeArity (envsF i) := fun i =>
    computeArity_embed f hf _ _ (hE i 0 (by simp [ReadCols])) (hE i 2 (by simp [ReadCols]))
      (hE i 5 (by simp [ReadCols])) (hE i 6 (by simp [ReadCols])) (hE i 7 (by simp [ReadCols]))
      (hE i 8 (by simp [ReadCols])) (hE i 9 (by simp [ReadCols]))
  have hpre : ∀ i, computePrefix envsK i = computePrefix envsF i := fun i => by
    unfold computePrefix
    exact Finset.sum_congr rfl fun i' _ => har i'
  have hloc : locateExp envsK e = locateExp envsF e := by
    unfold locateExp
    simp only [hpre, har]
  have hshift : ∀ i, rowShift (envsK i) = rowShift (envsF i) := fun i =>
    rowShift_embed f hf _ _ fun k hk => hE i (265 + k) (by unfold ReadCols; omega)
  have h0 : ∀ i, ((envsK i).trace 0 = 1 ↔ (envsF i).trace 0 = 1) := fun i =>
    eq_one_iff f hf _ _ (hE i 0 (by simp [ReadCols]))
  have h9 : ∀ i, ((envsK i).trace 9 = 1 ↔ (envsF i).trace 9 = 1) := fun i =>
    eq_one_iff f hf _ _ (hE i 9 (by simp [ReadCols]))
  have hslot : ∀ i j, (slotCert envsK i j).1 = (slotCert envsF i j).1 := by
    intro i j
    unfold slotCert
    split
    · rfl
    · by_cases hz : (envsF i).trace 0 = 1
      · have hz' := (h0 i).mpr hz
        simp [hz, hz', hshift i]
      · have hz' : ¬ (envsK i).trace 0 = 1 := fun h => hz ((h0 i).mp h)
        simp [hz, hz']
    · by_cases hz : (envsF i).trace 9 = 1
      · have hz' := (h9 i).mpr hz
        simp [hz, hz', hshift i]
      · have hz' : ¬ (envsK i).trace 9 = 1 := fun h => hz ((h9 i).mp h)
        simp [hz, hz']
  unfold decodedShift
  rw [hloc]
  cases locateExp envsF e with
  | none => rfl
  | some p => exact hslot p.1 p.2

end Embed

section FromAcceptance

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])

/-- The family compute row environments over the base field. -/
def envsFam : Fin P.optimized.family.problem.cfg.compRows → Env F := fun a =>
  envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes a)
    (DeployedChipFamily.computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)

/-- The gathered source environment embeds the base columns `0..12` and `202..295`. -/
theorem toSourceEnv_gather_trace (b : Module.Basis (Fin 3) F K) (env' : Env F) (j : ℕ)
    (hj : j < 13 ∨ (202 ≤ j ∧ j < 296)) :
    (CorrectedFinalTypedEnv.toSourceEnv (gatherCorrectedFinalTypedEnv b env')).trace j =
      algebraMap F K (env'.trace j) := by
  rcases hj with h13 | h202
  · dsimp only [CorrectedFinalTypedEnv.toSourceEnv]
    rw [dif_pos h13]
    rfl
  · have h13 : ¬ j < 13 := by omega
    have h76 : ¬ j < 76 := by omega
    dsimp only [CorrectedFinalTypedEnv.toSourceEnv]
    rw [dif_neg h13, dif_neg h76, dif_pos h202]
    have : 202 + (j - 202) = j := by omega
    show algebraMap F K (env'.trace (202 + (j - 202))) = _
    rw [this]

/-- The decoded event's `𝕂` environments embed the family rows' base traces on every column the
decoder reads. -/
theorem envsCR_embeds : Embeds (algebraMap F K) (envsCR P c Qc) (envsFam P c Qc) := by
  intro i j hj
  have htr := congrFun (FamilyIOChain.computeBaseEnv_honestQc_trace P c Qc i) j
  have hcase : j < 13 ∨ (202 ≤ j ∧ j < 296) := by unfold ReadCols at hj; omega
  have h := toSourceEnv_gather_trace (K := K) P.optimized.basis
    (P.computeBaseEnv (honestQc P c Qc) i) j hcase
  rw [htr] at h
  exact h

theorem formRN_agree : OptimizedComputeRangeCertificate.formRN F = FormRAxisEvent.formRN K := by
  unfold OptimizedComputeRangeCertificate.formRN FormRAxisEvent.formRN
  rw [Algebra.ringChar_eq F K]

/-- **`hA` of `r4_path_valid_at` from acceptance at the family compute chip.**  Premise
`2 ≤ formRN` (a fragment of `hp : 25 ≤ p`; `FormRWidth` gives `3 < ringChar F`). -/
theorem hA_of_acceptance (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (hn : 2 ≤ OptimizedComputeRangeCertificate.formRN F) :
    ∀ e, decodedShift (envsCR P c Qc) e ≤ FormRAxisEvent.formRN K - 1 := by
  have hform : ∀ a g, g ∈ formRCertificateGates (F := F) → g.eval (envsFam P c Qc a) = 0 :=
    fun a g hg => (row_obligations_at P c Qc hsat a).formR99 g hg
  have hb : ∀ a, ∀ k, k < 6 → (bbool (colM (F := F) k)).eval (envsFam P c Qc a) = 0 := by
    intro a k hk
    refine hform a _ ?_
    simp only [formRCertificateGates, booleanGates, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨k, hk, rfl⟩))))
  have hp : ∀ a, (pPin (F := F)).eval (envsFam P c Qc a) = 0 := fun a =>
    hform a _ (by simp [formRCertificateGates, formRPins])
  have ht : ∀ a, (topPin (F := F)).eval (envsFam P c Qc a) = 0 := fun a =>
    hform a _ (by simp [formRCertificateGates, formRPins])
  have hr : ∀ a, (rangeGate (F := F)).eval (envsFam P c Qc a) = 0 := fun a =>
    hform a _ (by simp [formRCertificateGates, formRNamed])
  have hF := Batch806.decodedShift_in_range_of_U1 (envsFam P c Qc) hn hb hp ht hr
  intro e
  rw [decodedShift_embed (algebraMap F K) (algebraMap F K).injective (envsCR_embeds P c Qc) e,
    ← formRN_agree (F := F) (K := K)]
  exact hF e

end FromAcceptance

end

end Nock.RedTeam.Batch908
