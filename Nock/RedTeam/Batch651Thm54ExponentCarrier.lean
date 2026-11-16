/-
  Nock/RedTeam/Batch651Thm54ExponentCarrier.lean

  * **Q1(c), the mechanism, compiled at the Form R polynomial level.**  A tree whose `read` carries
    exponent `e₁` and whose `verify` carries `e₂ ≠ e₁` (a cross-paired labeling: the record of request
    `e₂` placed where request `e₁`'s belongs) has `formRCounts = scale·X^{e₂} − (Tpoly·C'poly)·X^{e₁}`
    (`crossPair_counts`), a NONZERO polynomial (`crossPair_ne_zero`) whose envelope nonetheless
    vanishes at the pair `(α, λ)` with `α^{e₂−e₁} = T(λ)C'(λ)/λ^{n−1}` (`crossPair_root_exists`: for
    `e₂ = e₁ + 1` and `λ ≠ 0`, `α := T(λ)C'(λ)/λ^{n−1}`).  For a FIXED labeling this is a Schwartz–Zippel
    root like any other; the gap is that the labeling is chosen AFTER `α`: with `m` records sharing a
    root fingerprint the prover selects among `m!` labelings (`labelings_card`), so the per-labeling
    count does not bound the adaptive one.
  * **Q2, compute side.**  The round-0 compute columns are exactly the selectors/masks `0..12` and the
    certificate block `202..295` (`compute_round0_cols`); no integer counter column is round 0, so the
    structural exponent `S(i) + j + 1` (`OptimizedHostileTimestamps.prefixExp`) has no deployed
    carrier either — option (a) (a running-sum column) is required if the pairing is to be committed
    pre-`α` on both sides.
  * **Q8(i), harmlessness refuted.**  `UniqueExponents` + A2 make the identity equivalent to path
    validity only for a labeling in which each exponent's read and verify sit in the same tree; a
    cross-paired labeling satisfies `UniqueExponents` on each tree yet breaks `Paired`
    (`crossPair_not_paired`), so A2's premise set does not exclude it — the exclusion is the
    strategy model's `recordExponent`, i.e. an assumption.
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch651

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.RedTeam.Batch575
open Polynomial
open scoped Polynomial

noncomputable section

section CrossPair
variable {K : Type} [Field K]

/-- The cross-paired tree: a `read` labelled `e₁` wrapping a `verify` labelled `e₂` over a leaf. -/
def crossTree (e₁ e₂ : ℕ) (a : K) : MTree K := .read e₁ (.verify e₂ a .halt)

/-- Its Form R polynomial: `scale·X^{e₂} − (Tpoly m · C'poly c)·X^{e₁}` (`formRCounts` on the three
constructors; `formRCounts.halt = 0`). -/
theorem crossPair_counts (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (e₁ e₂ : ℕ) (a : K) :
    formRCounts n mm cc (crossTree e₁ e₂ a) =
      C (scale n) * X ^ e₂ - C (Tpoly (mm e₁) * C'poly n (cc e₁)) * X ^ e₁ := by
  simp [crossTree, formRCounts]

/-- Each tree of a cross-paired pair has unique exponents … -/
theorem crossPair_unique (e₁ e₂ : ℕ) (a : K) : UniqueExponents (crossTree e₁ e₂ a) := by
  intro e
  simp only [crossTree, readCount, verifyCount]
  constructor <;> split_ifs <;> omega

/-- … but the read exponent is NOT paired within the tree when `e₁ ≠ e₂`. -/
theorem crossPair_not_paired (e₁ e₂ : ℕ) (a : K) (h : e₁ ≠ e₂) : ¬ Paired e₁ (crossTree e₁ e₂ a) := by
  intro hp
  have hv := hp.2
  simp [crossTree, verifyCount, Ne.symm h] at hv

/-- The polynomial is nonzero when `e₁ ≠ e₂` (its `X^{e₂}` coefficient is `scale n ≠ 0`). -/
theorem crossPair_ne_zero (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (e₁ e₂ : ℕ) (a : K)
    (h : e₁ ≠ e₂) : formRCounts n mm cc (crossTree e₁ e₂ a) ≠ 0 := by
  intro h0
  have hc := congrArg (fun P : (Polynomial K)[X] => P.coeff e₂) h0
  simp only [crossPair_counts, coeff_sub, coeff_C_mul, coeff_X_pow, if_true, coeff_zero] at hc
  rw [if_neg (Ne.symm h)] at hc
  simp [scale, Y] at hc

/-- **The adaptive root.**  With `e₂ = e₁ + 1` and `λ ≠ 0`, the pair `(α, λ)` with
`α = T(λ)·C'(λ)/λ^{n−1}` makes the cross-paired identity vanish: evaluating the polynomial
coefficient-wise at `λ` and then at `α`. -/
theorem crossPair_root_exists (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (e₁ : ℕ) (a lmb : K)
    (hl : lmb ≠ 0) :
    ∃ α : K,
      ((formRCounts n mm cc (crossTree e₁ (e₁ + 1) a)).map (Polynomial.evalRingHom lmb)).eval α = 0 := by
  refine ⟨(Tpoly (mm e₁) * C'poly n (cc e₁)).eval lmb / (scale n).eval lmb, ?_⟩
  have hs : (scale n).eval lmb ≠ 0 := by simp [scale, Y, hl]
  simp only [crossPair_counts, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
    coe_evalRingHom]
  rw [pow_succ]
  field_simp
  ring

/-- The number of labelings of `m` records with a common root fingerprint: `m!`. -/
theorem labelings_card (m : ℕ) : Fintype.card (Equiv.Perm (Fin m)) = m.factorial := by
  simp [Fintype.card_perm]

end CrossPair

/-! ## The Lean model fixes the exponent before `α`; the chip does not -/

section Model
variable {K : Type} [Field K]

/-- `specializeA` writes `ts := α^{recordExponent}` on an active row and leaves the rest of the
record alone: the exponent is TEMPLATE data in the strategy model. -/
theorem specializeA_ts (α : K) (row : MemoryRowTemplate (K := K))
    (ha : memoryMemRecKind row.timestamp.state = .active) :
    (row.specializeA α).2.2.mem.ts = α ^ row.timestamp.recordExponent ∧
      (row.specializeA α).2.2.mem.root = row.placeholder.2.2.mem.root ∧
      (row.specializeA α).2.2.mem.child = row.placeholder.2.2.mem.child ∧
      (row.specializeA α).2.2.mem.axis = row.placeholder.2.2.mem.axis := by
  simp [MemoryRowTemplate.specializeA, specializeMemRec, ha]

theorem ts_round2 : memoryColRound 84 = 2 ∧ memoryColRound 85 = 2 ∧ memoryColRound 86 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [memoryColRound, memoryRoleRound]

/-- The compute chip's round-0 columns are the selectors/masks and the certificate block only —
no integer counter is committed before `α`. -/
theorem compute_round0_cols (c : ℕ) (hc : c < 302) :
    computeColRound c = 0 ↔ (c < 13 ∨ (202 ≤ c ∧ c < 296)) := by
  unfold computeColRound computeRoleRound
  split_ifs <;> simp_all

end Model

end

end Nock.RedTeam.Batch651
