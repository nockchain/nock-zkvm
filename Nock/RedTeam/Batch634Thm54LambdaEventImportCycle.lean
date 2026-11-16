/-
  Nock/RedTeam/Batch634Thm54LambdaEventImportCycle.lean

  * **Step 2, in production.**  `FormRAxisEvent.formRGuard` (`∃ k ≤ E', P.coeff k ≠ 0`),
    `formRGuardedBad E i E' := if formRGuard (formRTemplatePolynomial E i) E' then
    formRGuardedAxisFailureEvent E i E' else ∅` and `formRGuardedUnion`.  The guard reads only
    the template polynomial (`guard_reads_template`: `formRGuardedBad` is a function of
    `formRTemplatePolynomial E i` and the unguarded event alone).
  * **Step 1, measured and reverted.**
  * **R1 / R2 on the production guarded set** (below): `lifted_guarded_readsOn_seed`,
    `guarded_union_card_le`, and the soundness of the drop `guarded_excludes` — the `Batch641`
    shapes, now at `FormRAxisEvent.formRGuardedBad`.
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Nock.RedTeam.Batch634

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.RedTeam.Batch575
open Nock.AxisBatching
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open scoped Classical Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K] [Fintype F]

/-! ## The guard reads only the template -/

/-- `formRGuardedBad` depends on the template only through `formRTemplatePolynomial E i` (the
guard) and the unguarded event: two templates with the same polynomial and the same unguarded
event give the same guarded set. -/
theorem guard_reads_template {T T' : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (E₂ : ExactExecutionTemplate T') (i : Fin T.kMem) (j : Fin T'.kMem) (E' : ℕ)
    (hP : formRTemplatePolynomial E i = formRTemplatePolynomial E₂ j)
    (hB : formRGuardedAxisFailureEvent E i E' = formRGuardedAxisFailureEvent E₂ j E') :
    formRGuardedBad E i E' = formRGuardedBad E₂ j E' := by
  unfold formRGuardedBad; rw [hP, hB]

/-- The unguarded event itself is a function of the template polynomial. -/
theorem unguarded_reads_template {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (i : Fin T.kMem) (E' : ℕ) :
    formRGuardedAxisFailureEvent E i E' =
      Finset.univ.filter fun c : OptimizedProductionChallengeTuple K F =>
        (landedVec c alphaMIdx, landedVec c lamIdx) ∈ formRRootBad (formRTemplatePolynomial E i) E' := by
  ext c; simp [formRGuardedAxisFailureEvent, formRBadAt_eq_template]

/-- The guard drops a zero tree: no coefficient is nonzero. -/
theorem guardedBad_zero {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T)
    (i : Fin T.kMem) (E' : ℕ) (h : formRTemplatePolynomial E i = 0) :
    formRGuardedBad E i E' = ∅ := by
  simp [formRGuardedBad, formRGuard, h]

/-- `P ≠ 0` and `natDegree P ≤ E'` give the guard (`Batch641.guard_of_ne_zero`). -/
theorem guard_of_ne_zero (P : Polynomial (Polynomial K)) (E' : ℕ) (hE : P.natDegree ≤ E')
    (hP : P ≠ 0) : formRGuard P E' :=
  ⟨P.natDegree, hE, Polynomial.leadingCoeff_ne_zero.mpr hP⟩

/-! ## The event is typable as a parameter (no `JointCoins` change) -/

/-- The per-seed λ-event over a template-adapter strategy, on the production tuple. -/
def liftedEvent {p : ℕ} [CharP K p] (V : ProductionAxisStructureVerifier.ProductionStrategy (F := F) (K := K) (p := p))
    (E' : ℕ) : Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    ∃ hz : nprSeed c.1 ≠ 0,
      c ∈ formRGuardedUnion (ProductionAxisStructureVerifier.committedTemplate V (nprSeed c.1) hz) E'

/-- **The event can enter `OptimizedHostileProductionFailureEvent` as a parameter** of its own
type (the last nine parameters are `Finset (JointCoins K)`; this one is on the full tuple). -/
theorem event_typable {p : ℕ} [CharP K p]
    (V : ProductionAxisStructureVerifier.ProductionStrategy (F := F) (K := K) (p := p)) (E' : ℕ) :
    ∃ S : Finset (OptimizedProductionChallengeTuple K F), S = liftedEvent V E' :=
  ⟨_, rfl⟩

/-! ## R1 (production guarded set) -/

/-- The lifted guarded set over the strategy's post-seed template, as `Batch641.liftedGuarded`,
at the production `formRGuardedBad` (its guard unfolded to read the bad set at `x`). -/
def liftedGuarded (S : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)) (E' : ℕ)
    (x : Fin 11 → K) : Finset (K × K) :=
  if hz : x seedIdx ≠ 0 then
    Finset.univ.biUnion fun i : Fin (S.afterSeed ⟨x seedIdx, hz⟩).configTemplate.kMem =>
      if formRGuard (formRTemplatePolynomial (S.afterSeed ⟨x seedIdx, hz⟩).executionTemplate i) E'
      then formRBadAt (S.afterSeed ⟨x seedIdx, hz⟩).executionTemplate i E' x else ∅
  else ∅

/-- **R1.**  `ReadsOn {seedIdx}`: the guard reads only the template. -/
theorem lifted_guarded_readsOn_seed
    (S : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)) (E' : ℕ) :
    ReadsOn (C := K) (n := 11) ({seedIdx} : Finset (Fin 11)) (liftedGuarded S E') := by
  intro x y hxy
  have hz : x seedIdx = y seedIdx := hxy seedIdx (Finset.mem_singleton_self _)
  unfold liftedGuarded
  by_cases h : x seedIdx ≠ 0
  · have h' : y seedIdx ≠ 0 := hz ▸ h
    rw [dif_pos h, dif_pos h']
    have hc : (⟨x seedIdx, h⟩ : { z : K // z ≠ 0 }) = ⟨y seedIdx, h'⟩ := Subtype.ext hz
    generalize hs : (⟨x seedIdx, h⟩ : { z : K // z ≠ 0 }) = s at hc ⊢
    generalize hs' : (⟨y seedIdx, h'⟩ : { z : K // z ≠ 0 }) = s' at hc ⊢
    subst hc
    apply Finset.biUnion_congr rfl
    intro i _
    split_ifs
    · rw [formRBadAt_eq_template, formRBadAt_eq_template]
    · rfl
  · have h' : ¬ y seedIdx ≠ 0 := hz ▸ h
    rw [dif_neg h, dif_neg h']

/-- **R1, positive control 1** (re-run): a set reading the landed `λ` fails the prior-round
check. -/
theorem positive_control_lambda :
    ¬ ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx)
      (fun x : Fin 11 → K => ({x lamIdx} : Finset K)) :=
  lambdaBad_not_readsOn

/-- **R1, positive control 2** (re-run): a set reading the encode's OUTPUT `T = λ^m` fails. -/
theorem positive_control_encodedT (row : MemoryRowTemplate (K := K))
    (ha : memoryMemRecKind row.timestamp.state = .active)
    (hax : row.placeholder.2.2.mem.axis = ((2 : ℕ) : K)) (h2 : 2 < ringChar K) :
    ¬ ReadsOn (C := K) (n := 11) (priorCoords landedRound lamIdx) (encodedTBad row) :=
  encodedTBad_not_readsOn row ha hax h2

/-! ## R2 (production guarded union), nonzero premise from the guard -/

theorem guarded_union_card_le {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (E' : ℕ)
    (hA : ∀ i, CertInRange K (templateCertAxis (templateMemoryTreeAt E i))) :
    (formRGuardedUnion E E').card ≤
      Fintype.card K ^ 9 * ∑ i : Fin T.kMem,
        Fintype.card K * (2 * (formRN K - 1) +
          nodeCount (templateAxisTree (templateMemoryTreeAt E i)) + E') := by
  refine Finset.card_biUnion_le.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  unfold formRGuardedBad
  split_ifs with hg
  · obtain ⟨e₀, he₀, hB⟩ := hg
    refine (formRGuardedAxisFailureEvent_card_le E i E').trans (Nat.mul_le_mul_left _ ?_)
    have h1 := formRRootBad_card_le (templateCertAxis (templateMemoryTreeAt E i))
      (templateAxisTree (templateMemoryTreeAt E i)) e₀ E' hB he₀
    have h2 := degY_le (K := K) (formRN K) (certShiftOf (templateCertAxis (templateMemoryTreeAt E i)))
      (certBitsOf (templateCertAxis (templateMemoryTreeAt E i))) (hA i) e₀
      (templateAxisTree (templateMemoryTreeAt E i))
    simp only [formRTemplatePolynomial, formRPolyOfCert] at h1 h2 ⊢
    calc _ ≤ _ := h1
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  · simp

/-- The approved worst-case numeral at `n = 64`, `E' = 3N + 3` (`Batch641.worst_case_figure`). -/
theorem worst_case_64 (N M kMem : ℕ) (hk : kMem ≤ M) :
    M + kMem * (2 * (64 - 1) + (3 * N + 3)) ≤ M * (3 * N + 130) := by
  nlinarith [Nat.mul_le_mul_right (2 * (64 - 1) + (3 * N + 3)) hk]

/-- **Soundness of the drop** at the production guarded union (`Batch641.guarded_excludes`). -/
theorem guarded_excludes {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (E' : ℕ)
    (hdeg : ∀ i, (formRTemplatePolynomial E i).natDegree ≤ E')
    (hU : ∀ i, UniqueExponents (templateAxisTree (templateMemoryTreeAt E i)))
    (hA : ∀ i, CertInRange K (templateCertAxis (templateMemoryTreeAt E i)))
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : ∀ i, formREnvelope (formRTemplatePolynomial E i) E'
      (landedVec c alphaMIdx) (landedVec c lamIdx) = 0)
    (hout : c ∉ formRGuardedUnion E E') :
    ∀ i, FormRPathValid (templateCertAxis (templateMemoryTreeAt E i))
      (templateAxisTree (templateMemoryTreeAt E i)) := by
  intro i
  have hnot : ¬ formRGuard (formRTemplatePolynomial E i) E' := by
    intro hg
    apply hout
    simp only [formRGuardedUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨i, ?_⟩
    simp only [formRGuardedBad, if_pos hg, formRGuardedAxisFailureEvent, Finset.mem_filter,
      Finset.mem_univ, true_and, formRBadAt_eq_template, formRRootBad]
    exact hacc i
  have h0 : formRTemplatePolynomial E i = 0 := by
    by_contra hP
    exact hnot (guard_of_ne_zero _ E' (hdeg i) hP)
  exact (formRTemplate_identity_iff_path E i (hU i) (hA i)).1 h0

end

end Nock.RedTeam.Batch634

#print axioms Nock.RedTeam.Batch634.guard_reads_template
#print axioms Nock.RedTeam.Batch634.guardedBad_zero
#print axioms Nock.RedTeam.Batch634.event_typable
#print axioms Nock.RedTeam.Batch634.lifted_guarded_readsOn_seed
#print axioms Nock.RedTeam.Batch634.positive_control_lambda
#print axioms Nock.RedTeam.Batch634.positive_control_encodedT
#print axioms Nock.RedTeam.Batch634.guarded_union_card_le
#print axioms Nock.RedTeam.Batch634.worst_case_64
#print axioms Nock.RedTeam.Batch634.guarded_excludes
