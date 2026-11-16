/-
  Nock/RedTeam/Batch641Thm54LambdaEventGuarded.lean

  * `rootBad_univ_of_zero`: when the polynomial is `0` the
    envelope is identically `0` and `formRRootBad 0 E' = univ`; `event_univ`: the per-tree event is
    then the whole tuple space; so is any union containing it, and no `|𝕂|¹⁰ · X` with `X < |𝕂|`
    bounds it (`no_bound`).  The zero case is the HONEST case: A2 says `P = 0 ↔ FormRPathValid`, and
    `formRCounts _ _ _.halt = 0`.  So the
    authorized set prices the honest prover's acceptance as a failure.  Non-vacuity: `.halt` is a
    closed term of `MTree K` (`halt_zero`), and `templateAxisTree` sends a `halt` root row to it
    (lane, `Batch633.templateAxisTree_halt`); generated `halt` rows exist.
  * **Q2, the guarded form.**  `guardOf P E' := ∃ k ≤ E', P.coeff k ≠ 0` — NOT `P ≠ 0`: a `P ≠ 0`
    whose nonzero coefficients all sit above `E'` has an identically-zero truncated envelope and
    the same total event (`pneq_guard_insufficient`).  `formRGuardedBad E i E' := if guardOf … then
    formRGuardedAxisFailureEvent E i E' else ∅`.
    - **Sound.**  `guarded_excludes`: if every tree's envelope vanishes at the sampled pair
      (what acceptance of the identity gives) and the pair is outside the guarded union, then every
      tree has `P = 0`, hence (A2, under `UniqueExponents` and `CertInRange`) `FormRPathValid`.
      The dropped (unguarded) trees are exactly the trees with no nonzero coefficient `≤ E'`; with
      `E' ≥ natDegree P` that is `P = 0`, i.e. the valid-path trees — nothing the soundness argument
      needs excluded is lost (`guard_of_ne_zero`).
    - `Σ_i (2(n−1) + M_i + E') = M + kMem·(2(n−1) + E')`
      (`Batch628.sum_figure`); at `kMem ≤ M`, `≤ M·(2(n−1) + E' + 1)`, i.e. **`M·(3N + 130)`** at
      `n = 64`, `E' = 3N + 3` (`worst_case_figure`), the value `Batch628.figure_122_true/_120_true`
      already certify.
    - **R1 survives**: the guard reads only the template, so the lifted guarded set is
      `ReadsOn {seedIdx}` (`lifted_guarded_readsOn_seed`).
  * **Obstacle 3 (`CertInRange`).**  Needed in BOTH places: `degY_le` takes `mm e ≤ n − 1` (so R2
    needs it), and A2's iff takes it (so the soundness of dropping the zero trees needs it).  It is
    NOT free: `nockAxisOf` is an `ε` with a residue only for prime-subfield elements
    (`MemoryTable.lean:133`); a hostile template may carry an axis outside `𝔽`.  For the PACKAGE
    strategy's own templates it is a package theorem to prove (honest axes are nat-casts below `p`,
    `hΛp` / the deployed `genComputeRows_rowsFormRAxisBound`); for the hostile side it is the form R
    residue gate (`cert < p`) carried through the transport (R4).
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.RedTeam.Batch628Thm54LambdaEventLift

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Nock.RedTeam.Batch641

open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.RoundFibred
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.RedTeam.Batch575
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open scoped Classical Polynomial

noncomputable section


section Stop
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem envelope_zero (E' : ℕ) (α lmb : K) : formREnvelope (0 : Polynomial (Polynomial K)) E' α lmb = 0 := by
  simp [formREnvelope, Batch556.F]

theorem rootBad_univ_of_zero (E' : ℕ) :
    formRRootBad (0 : Polynomial (Polynomial K)) E' = (Finset.univ : Finset (K × K)) := by
  ext p; simp [formRRootBad, envelope_zero]

theorem halt_zero (A : ℕ → ℕ) : formRPolyOfCert A (MTree.halt : MTree K) = 0 := by
  simp [formRPolyOfCert, formRCounts]

variable {F : Type} [Field F] [Algebra F K] [Fintype F]

theorem event_univ {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem)
    (E' : ℕ) (h : formRTemplatePolynomial E i = 0) :
    formRGuardedAxisFailureEvent E i E' = Finset.univ := by
  ext c
  simp [formRGuardedAxisFailureEvent, formRBadAt_eq_template, h, rootBad_univ_of_zero]

theorem no_bound (S : Finset (OptimizedProductionChallengeTuple K F)) (hS : S = Finset.univ)
    (X : ℕ) (hX : X < Fintype.card K) : ¬ S.card ≤ Fintype.card K ^ 10 * X := by
  intro h
  rw [hS, Finset.card_univ, card_optimizedProductionChallengeTuple] at h
  have : Fintype.card K ^ 10 * Fintype.card K ≤ Fintype.card K ^ 10 * X := by
    simpa [pow_succ] using h
  have hpos : 0 < Fintype.card K ^ 10 := pow_pos Fintype.card_pos 10
  exact absurd (Nat.le_of_mul_le_mul_left this hpos) (not_le.mpr hX)

end Stop

/-! ## Q2 — the guarded form -/

section Guarded
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The guard: some coefficient at an exponent `≤ E'` is nonzero. -/
def guardOf (P : Polynomial (Polynomial K)) (E' : ℕ) : Prop := ∃ k ≤ E', P.coeff k ≠ 0

/-- `P ≠ 0` alone is NOT the right guard: `Y^{E'+1}` (as a constant-in-`λ` polynomial) is nonzero,
its truncated envelope at `E'` is identically zero, and its root set is total. -/
theorem pneq_guard_insufficient (E' : ℕ) :
    (Polynomial.X ^ (E' + 1) : Polynomial (Polynomial K)) ≠ 0 ∧
      formRRootBad (Polynomial.X ^ (E' + 1) : Polynomial (Polynomial K)) E' = Finset.univ := by
  refine ⟨pow_ne_zero _ Polynomial.X_ne_zero, ?_⟩
  ext p
  simp only [formRRootBad, formREnvelope, Batch556.F, Finset.mem_filter, Finset.mem_univ, true_and,
    iff_true]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' : k < E' + 1 := Finset.mem_range.mp hk
  rw [Polynomial.coeff_X_pow]
  simp [show k ≠ E' + 1 by omega]

/-- With `E'` at or above the degree, `P ≠ 0` does give the guard. -/
theorem guard_of_ne_zero (P : Polynomial (Polynomial K)) (E' : ℕ) (hE : P.natDegree ≤ E')
    (hP : P ≠ 0) : guardOf P E' :=
  ⟨P.natDegree, hE, Polynomial.leadingCoeff_ne_zero.mpr hP⟩

theorem not_guard_zero (P : Polynomial (Polynomial K)) (E' : ℕ) (hE : P.natDegree ≤ E')
    (h : ¬ guardOf P E') : P = 0 := by
  by_contra hP
  exact h (guard_of_ne_zero P E' hE hP)

variable {F : Type} [Field F] [Algebra F K] [Fintype F]

/-- **The guarded per-tree event.** -/
def formRGuardedBad {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (i : Fin T.kMem)
    (E' : ℕ) : Finset (OptimizedProductionChallengeTuple K F) :=
  if guardOf (formRTemplatePolynomial E i) E' then formRGuardedAxisFailureEvent E i E' else ∅

/-- The guarded union over the template's trees. -/
def guardedUnion {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (E' : ℕ) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.biUnion fun i : Fin T.kMem => formRGuardedBad E i E'

/-- **Soundness of dropping the unguarded trees.**  If every tree's envelope vanishes at the
sampled pair (the Form R identity accepted at every root) and the tuple is outside the guarded
union, every tree has `P = 0`, hence a valid path (A2). -/
theorem guarded_excludes {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (E' : ℕ)
    (hdeg : ∀ i, (formRTemplatePolynomial E i).natDegree ≤ E')
    (hU : ∀ i, UniqueExponents (templateAxisTree (templateMemoryTreeAt E i)))
    (hA : ∀ i, CertInRange K (templateCertAxis (templateMemoryTreeAt E i)))
    (c : OptimizedProductionChallengeTuple K F)
    (hacc : ∀ i, formREnvelope (formRTemplatePolynomial E i) E'
      (landedVec c alphaMIdx) (landedVec c lamIdx) = 0)
    (hout : c ∉ guardedUnion E E') :
    ∀ i, FormRPathValid (templateCertAxis (templateMemoryTreeAt E i))
      (templateAxisTree (templateMemoryTreeAt E i)) := by
  intro i
  have hnot : ¬ guardOf (formRTemplatePolynomial E i) E' := by
    intro hg
    apply hout
    simp only [guardedUnion, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨i, ?_⟩
    simp only [formRGuardedBad, if_pos hg, formRGuardedAxisFailureEvent, Finset.mem_filter,
      Finset.mem_univ, true_and, formRBadAt_eq_template, formRRootBad]
    exact hacc i
  have h0 := not_guard_zero _ E' (hdeg i) hnot
  exact (formRTemplate_identity_iff_path E i (hU i) (hA i)).1 h0

/-- **R2 on the guarded union.** -/
theorem guarded_union_card_le {T : ExactConfigTemplate F K} (E : ExactExecutionTemplate T) (E' : ℕ)
    (hA : ∀ i, CertInRange K (templateCertAxis (templateMemoryTreeAt E i))) :
    (guardedUnion E E').card ≤
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

/-- The figure: `Σ_i (2(n−1) + M_i + E') = M + kMem·(2(n−1) + E')`, and at `kMem ≤ M`
`≤ M·(2(n−1) + E' + 1)`. -/
theorem worst_case_figure (n E' M kMem : ℕ) (hk : kMem ≤ M) :
    M + kMem * (2 * (n - 1) + E') ≤ M * (2 * (n - 1) + E' + 1) := by
  nlinarith [Nat.mul_le_mul_right (2 * (n - 1) + E') hk]

theorem worst_case_64 (N M : ℕ) : M * (2 * (64 - 1) + (3 * N + 3) + 1) = M * (3 * N + 130) := by
  ring_nf

/-- The worst-case figure is exactly the value `Batch628.figure_122_true` certifies. -/
theorem worst_case_is_batch628 (N M : ℕ) : Batch628.trueFigure N M M = M * (3 * N + 130) := by
  unfold Batch628.trueFigure; ring

/-! ### R1 survives the guard -/

/-- The lifted guarded set over the strategy's post-seed template. -/
def liftedGuarded (S : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K)) (E' : ℕ)
    (x : Fin 11 → K) : Finset (K × K) :=
  if hz : x seedIdx ≠ 0 then
    Finset.univ.biUnion fun i : Fin (S.afterSeed ⟨x seedIdx, hz⟩).configTemplate.kMem =>
      if guardOf (formRTemplatePolynomial (S.afterSeed ⟨x seedIdx, hz⟩).executionTemplate i) E'
      then formRBadAt (S.afterSeed ⟨x seedIdx, hz⟩).executionTemplate i E' x else ∅
  else ∅

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

end Guarded

end

end Nock.RedTeam.Batch641
