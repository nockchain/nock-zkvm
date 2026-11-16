/-
  Nock/RedTeam/Batch271Thm54AnchoringReview.lean

  Paper: the paper (`RAP_prog-IO`), `:544-550` (`RAP_mem-IO` inputs, the `responses`
  seed), `:577-599` (accumulation step, terminal, IO consistency checks).

  Compiled here:

  * **§A `hchar`.**  `hchar_of_charP`: the hostile theorems' hypothesis
    `∀ n ≤ 11, (n : 𝕂) = 1 → n = 1` holds in every field of characteristic `0` or `≥ 11`; it holds
    at `K73cubic` and at the Goldilocks extension `Nock.Field.K`; it **fails exactly in
    characteristics `2, 3, 5, 7`** (`hchar_fails_char2/3/5/7`, `decide`) — not only in
    characteristic `2` as `OptimizedComputeHostileAccumulator`'s docstring says.
  * **§B wrong layer / vacuity at a REAL package.**  `FoldCollisionExcluded` is satisfiable at the
    honest trace of every package (`canonical_fold_excluded`); the memory hostile telescoping
    `hostile_requests_eq_sum_memRowTerms` is instantiated at `package73`'s honest trace with all
    hypotheses discharged; `hostile_logUp_sums_agree` at `package73` with **only** the active-slot
    pole-hit exclusion left open (`package73_logUp_sums_agree_of_pole` — the tree has no lemma
    connecting `slotDenominator` on the canonical row to the sampled witness's nonzero
    denominators, F-B-3).  The three rejection theorems are instantiated at `package73` with the
    concrete nonzero `c = Pi.single 0 1` and `i₀ = 1` (`package73_*_rejected`).
  * **§C definitional drift vs the paper.**  The paper seeds `acc_mem` from `responses` and counts
    DOWN to `out_mem = 0` (`:549`, `:577-586`, `:598`); the tree counts UP from `0` to the shared
    public `requests`.  `paper_countdown_iff_sum` / `tree_countup_iff_sum` /
    **`countdown_iff_countup`**: with boolean `ver` and nonzero active denominators both say
    exactly `Σ ver(i)/denom(i) = responses`, so the layouts are equivalent **under those two
    hypotheses and no others**.  `paper_prog_step_*`: the compute chip's `FoldedProgStep3` with
    `SafeDenom` masks is the paper's `:526-527` gate for `io = 0` and for one, two, three active
    records **when the activity masks are boolean** (`activeMask_bool` supplies that from
    `hchar`); `char2_selector_not_oneHot` exhibits the boolean, sum-to-one, non-one-hot selector
    `hchar` is there to exclude.
  **Those two theorems
    are unstatable now.**  Since A-mem-2 committed the denominator pin
    `OptimizedMemoryGateBasis.denominatorPinMixed`: `attackTrace_all_but_pin`
    (every committed gate but the pin is still blind to the swap — the repair is one gate wide),
    `denominatorPin_shifted` (the pin moves by `d₁' − d₁` at `i₁`),
    **`repaired_chip_rejects_denominator_swap`** (for any accepted trace and any `d₁' ≠ d₁` the
    attack trace is REJECTED — no hypothesis on `d₂'`, `ver`, the fold or the compensation),
    `attackTrace_values` (its denominators ARE `d₁'`, `d₂'` while every record field, the `ver`
    flags and the terminal are unchanged), `exists_compensating_pair` (such pairs exist in every
    field of characteristic `∉ {2, 3}`), and **`packageM_denominator_attack_rejected`** at the
    honest trace of the real F97 package `packageM` (14 memory rows, rows `0` and `1` are
    `read_root` with `ver = 1`), with `packageM_honest_accepted` as the non-vacuity control. The
    F73 fixture has ONE response (`derived_response_singleton`), so the two-row witness is
    unstatable there.
  * **§F read sets, own instrument.**  `role37_readers`, `role39_readers` (**`ver` is read only by
    its booleanity, the contribution and the safe normalisation — nothing binds it to the row's
    state**, F-5-2), `memory_public2_readers`, `compute_extPublic2_readers`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.MultiRootHonestCommitment
import Nock.Field
import Nock.RedTeam.Batch266Thm54UnchainedMemoryAccumulator
import Nock.RedTeam.Batch268Thm54MemoryTerminalBoundToRequests
import Nock.RedTeam.Batch269Thm54ComputeAccumulatorAnchored
import Mathlib.LinearAlgebra.Lagrange

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch271

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemorySemanticRealization
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Module
open scoped Polynomial

/-! ## A. The characteristic hypothesis `hchar` -/

section Hchar

/-- `hchar` holds in characteristic `0` or `≥ 11`: `(n : K) = 1` with `1 ≤ n ≤ 11` means
`p ∣ n − 1` with `n − 1 ≤ 10`. -/
theorem hchar_of_charP {K : Type*} [Field K] {p : ℕ} [CharP K p] (hp : p = 0 ∨ 11 ≤ p) :
    ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1 := by
  intro n hn h
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd h (by simp)
  · have h' : ((n - 1 : ℕ) : K) = 0 := by
      rw [Nat.cast_sub hpos, Nat.cast_one, h, sub_self]
    have hdvd := (CharP.cast_eq_zero_iff K p (n - 1)).mp h'
    rcases hp with rfl | hp
    · rw [zero_dvd_iff] at hdvd; omega
    · rcases hdvd with ⟨m, hm⟩
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · omega
      · have : p * 1 ≤ p * m := Nat.mul_le_mul_left p hm0
        omega

/-- `hchar` at the F73 fixture field. -/
theorem hchar_K73cubic :
    ∀ n : ℕ, n ≤ 11 → (n : ConcreteStrictPackage.K73cubic) = 1 → n = 1 :=
  hchar_of_charP (p := 73) (Or.inr (by norm_num))

/-- `hchar` at the Goldilocks extension `Nock.Field.K` (the `Field` instance rests on
`goldilocks_prime`, hence that axiom appears in `#print axioms`). -/
theorem hchar_goldilocks : ∀ n : ℕ, n ≤ 11 → (n : Nock.Field.K) = 1 → n = 1 :=
  hchar_of_charP (p := Nock.Field.p) (Or.inr (by rw [Nock.Field.p_eq]; norm_num))

/-- **`hchar` fails in characteristics 2, 3, 5 and 7** — not only 2. -/
theorem hchar_fails_char2 : ¬ (∀ n : ℕ, n ≤ 11 → (n : ZMod 2) = 1 → n = 1) := by decide
theorem hchar_fails_char3 : ¬ (∀ n : ℕ, n ≤ 11 → (n : ZMod 3) = 1 → n = 1) := by decide
theorem hchar_fails_char5 : ¬ (∀ n : ℕ, n ≤ 11 → (n : ZMod 5) = 1 → n = 1) := by decide
theorem hchar_fails_char7 : ¬ (∀ n : ℕ, n ≤ 11 → (n : ZMod 7) = 1 → n = 1) := by decide

/-- What `hchar` excludes: in characteristic `2` the selector `(1, 1, 1, 0, …)` is boolean and
sums to `1` without being one-hot, so the selector gates alone do not make the activity masks
boolean. -/
theorem char2_selector_not_oneHot :
    ∃ sel : Fin 11 → ZMod 2, (∀ i, sel i = 0 ∨ sel i = 1) ∧ (∑ i, sel i) = 1 ∧
      ∀ s : Fin 11, sel ≠ Pi.single s 1 := by
  refine ⟨fun i => if (i : ℕ) < 3 then 1 else 0, fun i => by dsimp only; split_ifs <;> simp, by decide, ?_⟩
  intro s h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Fin.isValue, Fin.val_zero, Nat.zero_lt_succ, if_true, Fin.val_one,
    Nat.one_lt_succ_succ] at h0 h1
  rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨t, rfl⟩
  · simp at h1
  · simp at h0

end Hchar

noncomputable section


variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## C. Definitional drift: count-down to `out_mem = 0` vs count-up to `requests` -/

section Drift

variable {L : Type*} [Field L]

/-- the paper (and the seed `:549` with `acc(0) := responses`): one paper step of the
memory accumulator. -/
def PaperMemStep (ver denom accPrev accCur : L) : Prop :=
  ver * denom * (accPrev - accCur) = (accPrev - accCur) * (1 - ver) + ver

theorem paperMemStep_iff (ver denom accPrev accCur : L) (hbool : ver = 0 ∨ ver = 1)
    (hd : ver = 1 → denom ≠ 0) :
    PaperMemStep ver denom accPrev accCur ↔ accPrev - accCur = ver * denom⁻¹ := by
  rcases hbool with rfl | rfl
  · simp [PaperMemStep]; constructor <;> intro h <;> linear_combination -h
  · have hd := hd rfl
    simp only [PaperMemStep, one_mul, sub_self, mul_zero, zero_add]
    constructor
    · intro h; field_simp; linear_combination h
    · intro h; rw [h]; field_simp

/-- The row terms, `ℕ`-indexed (zero off the table). -/
def rowTermsN (h : ℕ) (ver denom : Fin h → L) (k : ℕ) : L :=
  if hk : k < h then ver ⟨k, hk⟩ * (denom ⟨k, hk⟩)⁻¹ else 0

theorem rowTermsN_lt (h : ℕ) (ver denom : Fin h → L) (i : Fin h) :
    rowTermsN h ver denom i = ver i * (denom i)⁻¹ := by
  simp [rowTermsN, i.isLt]

theorem sum_rowTermsN_succ (h : ℕ) (ver denom : Fin h → L) (m : ℕ) :
    (∑ x : Fin (m + 1), rowTermsN h ver denom x) =
      (∑ x : Fin m, rowTermsN h ver denom x) + rowTermsN h ver denom m := by
  rw [Fin.sum_univ_castSucc]; rfl

theorem sum_rowTermsN_all (h : ℕ) (ver denom : Fin h → L) :
    (∑ x : Fin h, rowTermsN h ver denom x) = ∑ i, ver i * (denom i)⁻¹ :=
  Finset.sum_congr rfl fun i _ => rowTermsN_lt h ver denom i

/-- **The paper's layout** (`:549` seed, `:577-579` step, `:586` terminal, `:598` `out_mem = 0`)
over `h` rows says exactly `Σ ver(i)/denom(i) = responses`. -/
theorem paper_countdown_iff_sum (h : ℕ) (ver denom : Fin h → L)
    (hbool : ∀ i, ver i = 0 ∨ ver i = 1) (hd : ∀ i, ver i = 1 → denom i ≠ 0) (responses : L) :
    (∃ acc : Fin (h + 1) → L, acc 0 = responses ∧
        (∀ i : Fin h, PaperMemStep (ver i) (denom i) (acc i.castSucc) (acc i.succ)) ∧
        acc (Fin.last h) = 0) ↔
      (∑ i, ver i * (denom i)⁻¹) = responses := by
  constructor
  · rintro ⟨acc, h0, hstep, hend⟩
    have key : ∀ m : ℕ, (hm : m ≤ h) →
        acc ⟨m, by omega⟩ = responses - ∑ x : Fin m, rowTermsN h ver denom x := by
      intro m
      induction m with
      | zero => intro _; simpa using h0
      | succ m ih =>
          intro hm
          have hs := (paperMemStep_iff _ _ _ _ (hbool ⟨m, by omega⟩) (hd ⟨m, by omega⟩)).mp
            (hstep ⟨m, by omega⟩)
          simp only [Fin.castSucc_mk, Fin.succ_mk] at hs
          rw [sum_rowTermsN_succ, rowTermsN_lt h ver denom ⟨m, by omega⟩]
          linear_combination ih (by omega) - hs
    have hl := key h le_rfl
    rw [show (⟨h, by omega⟩ : Fin (h + 1)) = Fin.last h from rfl, hend, sum_rowTermsN_all] at hl
    linear_combination hl
  · intro hsum
    refine ⟨fun m => responses - ∑ x : Fin (m : ℕ), rowTermsN h ver denom x, by simp <;> exact Finset.sum_eq_zero (fun x _ => absurd x.2 (by simp)), ?_, ?_⟩
    · intro i
      rw [paperMemStep_iff _ _ _ _ (hbool i) (hd i)]
      show responses - ∑ x : Fin (i : ℕ), rowTermsN h ver denom x -
        (responses - ∑ x : Fin ((i : ℕ) + 1), rowTermsN h ver denom x) = _
      rw [sum_rowTermsN_succ, rowTermsN_lt]
      ring
    · show responses - ∑ x : Fin h, rowTermsN h ver denom x = 0
      rw [sum_rowTermsN_all, hsum, sub_self]

/-- **The tree's layout** (`first · acc_before = 0`, `acc_after = acc_before + ver · denom⁻¹`,
the chain, `last · (acc_after − requests) = 0`) over `h` rows says exactly
`Σ ver(i)/denom(i) = requests`. -/
theorem tree_countup_iff_sum (h : ℕ) (ver denom : Fin h → L) (requests : L) :
    (∃ acc : Fin (h + 1) → L, acc 0 = 0 ∧
        (∀ i : Fin h, acc i.succ = acc i.castSucc + ver i * (denom i)⁻¹) ∧
        acc (Fin.last h) = requests) ↔
      (∑ i, ver i * (denom i)⁻¹) = requests := by
  constructor
  · rintro ⟨acc, h0, hstep, hend⟩
    have key : ∀ m : ℕ, (hm : m ≤ h) →
        acc ⟨m, by omega⟩ = ∑ x : Fin m, rowTermsN h ver denom x := by
      intro m
      induction m with
      | zero => intro _; simpa using h0
      | succ m ih =>
          intro hm
          have hs := hstep ⟨m, by omega⟩
          simp only [Fin.castSucc_mk, Fin.succ_mk] at hs
          rw [hs, ih (by omega), sum_rowTermsN_succ, rowTermsN_lt h ver denom ⟨m, by omega⟩]
    have hl := key h le_rfl
    rw [show (⟨h, by omega⟩ : Fin (h + 1)) = Fin.last h from rfl, hend, sum_rowTermsN_all] at hl
    exact hl.symm
  · intro hsum
    refine ⟨fun m => ∑ x : Fin (m : ℕ), rowTermsN h ver denom x, by simp <;> exact Finset.sum_eq_zero (fun x _ => absurd x.2 (by simp)), ?_, ?_⟩
    · intro i
      show (∑ x : Fin ((i : ℕ) + 1), rowTermsN h ver denom x) =
        (∑ x : Fin (i : ℕ), rowTermsN h ver denom x) + _
      rw [sum_rowTermsN_succ, rowTermsN_lt]
    · show (∑ x : Fin h, rowTermsN h ver denom x) = requests
      rw [sum_rowTermsN_all, hsum]

/-- **Count-down and count-up are equivalent** — under boolean `ver` and nonzero active
denominators, and with the paper's IO check `requests = responses` (`:597`) folded in as the
shared value.  No other hypothesis is involved. -/
theorem countdown_iff_countup (h : ℕ) (ver denom : Fin h → L)
    (hbool : ∀ i, ver i = 0 ∨ ver i = 1) (hd : ∀ i, ver i = 1 → denom i ≠ 0) (shared : L) :
    (∃ acc : Fin (h + 1) → L, acc 0 = shared ∧
        (∀ i : Fin h, PaperMemStep (ver i) (denom i) (acc i.castSucc) (acc i.succ)) ∧
        acc (Fin.last h) = 0) ↔
    (∃ acc : Fin (h + 1) → L, acc 0 = 0 ∧
        (∀ i : Fin h, acc i.succ = acc i.castSucc + ver i * (denom i)⁻¹) ∧
        acc (Fin.last h) = shared) := by
  rw [paper_countdown_iff_sum h ver denom hbool hd, tree_countup_iff_sum]

open OptimizedComputeFiniteIOGates in
/-- the paper with `io = 0`: the accumulator is constant.  The tree's gate with all
three masks `0` (safe denominators `1`) says the same. -/
theorem paper_prog_step_inactive (acc acc' d0 d1 d2 : L) :
    FoldedProgStep3 acc acc' (SafeDenom 0 d0) (SafeDenom 0 d1) (SafeDenom 0 d2) 0 0 0 ↔
      acc' - acc = 0 := by
  simp [FoldedProgStep3, SafeDenom]

open OptimizedComputeFiniteIOGates in
/-- `:526-527` with one active record (`regs = 1`): `d₀ · Δ = 1`. -/
theorem paper_prog_step_one (acc acc' d0 d1 d2 : L) :
    FoldedProgStep3 acc acc' (SafeDenom 1 d0) (SafeDenom 0 d1) (SafeDenom 0 d2) 1 0 0 ↔
      d0 * (acc' - acc) = 1 := by
  simp only [FoldedProgStep3, SafeDenom]
  constructor <;> intro h <;> linear_combination h

open OptimizedComputeFiniteIOGates in
/-- `:526-527` with two active records (`regs = 2`): `d₀ d₁ · Δ = d₁ + d₀`. -/
theorem paper_prog_step_two (acc acc' d0 d1 d2 : L) :
    FoldedProgStep3 acc acc' (SafeDenom 1 d0) (SafeDenom 1 d1) (SafeDenom 0 d2) 1 1 0 ↔
      d0 * d1 * (acc' - acc) = d1 + d0 := by
  simp only [FoldedProgStep3, SafeDenom]
  constructor <;> intro h <;> linear_combination h

open OptimizedComputeFiniteIOGates in
/-- `:526-527` with three active records (`regs = 3`): `d₀ d₁ d₂ · Δ = d₁ d₂ + d₀ d₂ + d₀ d₁`. -/
theorem paper_prog_step_three (acc acc' d0 d1 d2 : L) :
    FoldedProgStep3 acc acc' (SafeDenom 1 d0) (SafeDenom 1 d1) (SafeDenom 1 d2) 1 1 1 ↔
      d0 * d1 * d2 * (acc' - acc) = d1 * d2 + d0 * d2 + d0 * d1 := by
  simp only [FoldedProgStep3, SafeDenom]
  constructor <;> intro h <;> linear_combination h

open OptimizedComputeFiniteIOGates in
/-- **Where the paper and the tree both go silent**: with two active records whose denominators
BOTH vanish (a double pole hit) the gate is `0 = 0` and the accumulator step is free — in the
paper's form (`:526-527`) exactly as in the tree's.  This is why `hpole` is a hypothesis of the
hostile theorems and not a consequence of acceptance. -/
theorem double_pole_frees_step (acc acc' : L) :
    FoldedProgStep3 acc acc' (SafeDenom 1 0) (SafeDenom 1 0) (SafeDenom 0 0) 1 1 0 := by
  simp [FoldedProgStep3, SafeDenom]

end Drift


/-! ## B. Wrong layer / vacuity at real packages -/

section Honest

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem rowEnvK_eq_memorySourceEnv (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    rowEnvK P Qm i = P.memorySourceEnv Qm i := by
  unfold rowEnvK rowEnvF projOf OptimizedFullStrictNockVMROMPackage.memorySourceEnv
    OptimizedFullStrictNockVMROMPackage.memoryBaseEnv
    OptimizedFullStrictNockVMROMPackage.memorySourceTrace
  rfl

/-- **`FoldCollisionExcluded` is satisfiable at the honest trace of every package** — the
hypothesis of `hostile_requests_eq_sum_memRowTerms` / `hostile_logUp_sums_agree` is not vacuous. -/
theorem canonical_fold_excluded [Fintype F] [DecidableEq F] (i : Fin (rows P))
    (hinter : P.optimized.sampled.interPole ≠ 0) :
    FoldCollisionExcluded (rowEnvK P (canonicalMemoryTrace P) i) := by
  rw [rowEnvK_eq_memorySourceEnv]
  exact (canonical_memory_collision_good P i hinter).1

/-- Where `ver = 1` the committed denominator is nonzero (`safe · inv = 1`, `safe = denom`). -/
theorem denom_ne_zero_of_ver (Qm : Fin P.memoryChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm) (i : Fin (rows P))
    (hver : (rowEnvK P Qm i).trace 39 = 1) :
    (rowEnvK P Qm i).trace 37 ≠ 0 :=
  OptimizedMemoryHostileAccumulator.denom_ne_zero_of_ver P Qm hsat i hver

end Honest

section F73

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildableConcrete
open Nock.NockVMROM.Thm54.BuildablePackage.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

variable (hmore : BuildableAxisWitness.LaterSeedZeros (F := F73) (K := K73cubic)
  BuildableConcrete.concreteExecution)

abbrev honest73M : Fin (package73 hmore).memoryChip.rap.w → F73[X] :=
  canonicalMemoryTrace (package73 hmore)
abbrev honest73C : Fin (package73 hmore).computeChip.rap.w → F73[X] :=
  canonicalComputeTrace (package73 hmore)

theorem package73_memRows : (package73 hmore).optimized.family.problem.cfg.memRows = 6 := rfl

/-- **`LP`'s memory telescoping at a real package with every hypothesis discharged**: at the
honest F73 memory trace, `requests = Σ ver(i)·denom(i)⁻¹`. -/
theorem package73_hostile_memory_sum :
    (rowEnvK (package73 hmore) (honest73M hmore) (lastRow (package73 hmore))).pub 2 =
      ∑ i, memRowTerm (rowEnvK (package73 hmore) (honest73M hmore) i) :=
  hostile_requests_eq_sum_memRowTerms (package73 hmore) (honest73M hmore)
    (canonicalMemoryTrace_satisfies (package73 hmore) hmore
        (ConcreteStrictPackage.execution_cprimeCoherent ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha))

/-- `LP`'s cross-chip identity at the honest F73 traces: `hchar`, both acceptances and the fold
exclusion are discharged; **only the active-slot pole-hit exclusion `hpole` is left open** — the
tree has no lemma tying `slotDenominator` on the canonical compute row to the sampled witness's
nonzero denominators (F-B-3). -/
theorem package73_logUp_sums_agree_of_pole
    (hax : FormRAxisBound (package73 hmore).optimized.sampled
      (package73 hmore).optimized.basis)
    (hbasis : FormRBasis (package73 hmore).optimized.basis)
    (hwidth : FormRWidth F73)
    (hpole : ∀ (i : Fin (OptimizedComputeHostileAccumulator.rows (package73 hmore))) (j : Fin 3),
      OptimizedComputeHostileAccumulator.activeMask
        (OptimizedComputeHostileAccumulator.rowEnv (package73 hmore) (honest73C hmore) i) j = 1 →
      OptimizedComputeHostileAccumulator.slotDenominator
        (OptimizedComputeHostileAccumulator.rowEnv (package73 hmore) (honest73C hmore) i) j ≠ 0) :
    (∑ i, OptimizedComputeHostileAccumulator.logUpRowTerm
        (OptimizedComputeHostileAccumulator.rowEnv (package73 hmore) (honest73C hmore) i)) =
      ∑ i, memRowTerm (rowEnvK (package73 hmore) (honest73M hmore) i) :=
  hostile_logUp_sums_agree (package73 hmore) (honest73M hmore)
    (canonicalMemoryTrace_satisfies (package73 hmore) hmore
        (ConcreteStrictPackage.execution_cprimeCoherent ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha)) (honest73C hmore)
    (canonicalComputeTrace_satisfies (package73 hmore) hax hbasis hwidth) hchar_K73cubic hpole

/-- The concrete nonzero coordinate vector `(1, 0, 0)`. -/
def c0 : Fin 3 → F73 := Pi.single 0 1

theorem c0_ne_zero : c0 ≠ 0 := by
  intro h; have := congrFun h 0; simp [c0] at this

/-- `Batch268.moved_terminal_rejected` at the honest F73 trace with `c = (1,0,0)`. -/
theorem package73_terminal_rejected :
    ¬ RAP.SatisfiesWithPreprocessing (package73 hmore).memoryChip (Batch268.bumpTerminal c0 (honest73M hmore)) :=
  Batch268.moved_terminal_rejected (package73 hmore) (honest73M hmore)
    (canonicalMemoryTrace_satisfies (package73 hmore) hmore
        (ConcreteStrictPackage.execution_cprimeCoherent ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha)) c0 c0_ne_zero

/-- `Batch269.moved_accumulator_rejected` at the honest F73 trace with `c = (1,0,0)`. -/
theorem package73_accumulator_rejected
    (hax : FormRAxisBound (package73 hmore).optimized.sampled
      (package73 hmore).optimized.basis)
    (hbasis : FormRBasis (package73 hmore).optimized.basis)
    (hwidth : FormRWidth F73) :
    ¬ RAP.SatisfiesWithPreprocessing (package73 hmore).computeChip (Batch269.bumpAcc c0 (honest73C hmore)) :=
  Batch269.moved_accumulator_rejected (package73 hmore) (honest73C hmore)
    (canonicalComputeTrace_satisfies (package73 hmore) hax hbasis hwidth) hax hbasis hwidth c0
    c0_ne_zero

/-- `Batch266.repaired_chip_rejects_shifted_accumulator` at the honest F73 trace, row `1` of `5`,
`δ = (1,0,0)`. -/
theorem package73_shift_rejected :
    ¬ RAP.SatisfiesWithPreprocessing (package73 hmore).memoryChip
      (Batch266.shiftTrace (package73 hmore).optimized.memoryNodes
        ⟨1, by
          change 1 < (package73 hmore).optimized.family.problem.cfg.memRows
          rw [package73_memRows hmore]; decide⟩ c0 (honest73M hmore)) :=
  Batch266.repaired_chip_rejects_shifted_accumulator (package73 hmore) (honest73M hmore)
    (canonicalMemoryTrace_satisfies (package73 hmore) hmore
        (ConcreteStrictPackage.execution_cprimeCoherent ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha))
    ⟨1, by
      change 1 < (package73 hmore).optimized.family.problem.cfg.memRows
      rw [package73_memRows hmore]; decide⟩
    (Nat.succ_ne_zero 0) c0
    (Batch266.gatherShift_ne_zero _ c0 c0_ne_zero)

end F73

/-! ## E1. Row-local perturbation of a trace through Lagrange bases -/

section Perturb

variable {n : ℕ} (nodes : Fin n → F)

/-- `Q` with `δ c i` added to column `c` at row `i` (and nothing else at the row nodes). -/
def perturb (δ : ℕ → Fin n → F) {w : ℕ} (Q : Fin w → F[X]) : Fin w → F[X] :=
  fun c => Q c + ∑ i : Fin n, Polynomial.C (δ (c : ℕ) i) * Lagrange.basis Finset.univ nodes i

theorem perturb_eval (hinj : Function.Injective nodes) (δ : ℕ → Fin n → F) {w : ℕ}
    (Q : Fin w → F[X]) (c : Fin w) (j : Fin n) :
    (perturb nodes δ Q c).eval (nodes j) = (Q c).eval (nodes j) + δ (c : ℕ) j := by
  simp only [perturb, Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C]
  congr 1
  rw [Finset.sum_eq_single j]
  · rw [Lagrange.eval_basis_self hinj.injOn (Finset.mem_univ _), mul_one]
  · intro i _ hij
    rw [Lagrange.eval_basis_of_ne hij (Finset.mem_univ _), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem perturb_off (δ : ℕ → Fin n → F) {w : ℕ} (Q : Fin w → F[X]) (c : Fin w)
    (hc : ∀ i, δ (c : ℕ) i = 0) : perturb nodes δ Q c = Q c := by
  simp [perturb, hc]

theorem projectTrace_perturb (δ : ℕ → Fin n → F) (R : RAP F) (extra : Fin R.k → ℕ)
    (Q : Fin (R.w + RAPPadding.extraWidth extra) → F[X]) :
    RAPPadding.projectTrace R extra (perturb nodes δ Q) =
      perturb nodes δ (RAPPadding.projectTrace R extra Q) := by
  funext c
  simp [RAPPadding.projectTrace, perturb, RAPPadding.columnInclusion] <;> rfl

end Perturb

/-! ## E2. The role-level shift and its column image -/

section Shift

variable (b : Basis (Fin 3) F K) {n : ℕ}

/-- The `𝕂`-level change per extension role and row: denominators `d₁ ↦ d₁'` at `i₁`,
`d₂ ↦ d₂'` at `i₂` (roles `37`, `50`), their inverses (roles `38`, `42`), and the running
accumulator shifted by `Δ = 1/d₁' − 1/d₁` between the two rows (roles `44`, `43`). -/
def roleShift (i₁ i₂ : Fin n) (d₁ d₂ d₁' d₂' : K) (r : ℕ) (i : Fin n) : K :=
  if r = 37 ∨ r = 50 then (if i = i₁ then d₁' - d₁ else if i = i₂ then d₂' - d₂ else 0)
  else if r = 38 ∨ r = 42 then
    (if i = i₁ then d₁'⁻¹ - d₁⁻¹ else if i = i₂ then d₂'⁻¹ - d₂⁻¹ else 0)
  else if r = 44 then (if (i₁ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (i₂ : ℕ) then d₁'⁻¹ - d₁⁻¹ else 0)
  else if r = 43 then (if (i₁ : ℕ) < (i : ℕ) ∧ (i : ℕ) ≤ (i₂ : ℕ) then d₁'⁻¹ - d₁⁻¹ else 0)
  else 0

/-- The base-field column image of a role-level shift under the deployed layout
`col = 6 + 3·role + k`. -/
def colShift (S : ℕ → Fin n → K) (c : ℕ) (i : Fin n) : F :=
  if 6 ≤ c then coord b (S ((c - 6) / 3) i) ⟨(c - 6) % 3, Nat.mod_lt _ (by norm_num)⟩ else 0

theorem colShift_role (S : ℕ → Fin n → K) (r : ℕ) (k : Fin 3) (i : Fin n) :
    colShift b S (6 + 3 * r + (k : ℕ)) i = coord b (S r i) k := by
  simp only [colShift, if_pos (show 6 ≤ 6 + 3 * r + (k : ℕ) by omega)]
  congr 1
  · congr 1; omega
  · apply Fin.ext; simp only; omega

theorem colShift_base (S : ℕ → Fin n → K) (c : ℕ) (hc : c < 6) (i : Fin n) :
    colShift b S c i = 0 := by
  simp [colShift, show ¬ 6 ≤ c by omega]

theorem colShift_role_zero (S : ℕ → Fin n → K) (r : ℕ) (k : Fin 3) (hr : ∀ i, S r i = 0)
    (i : Fin n) : colShift b S (6 + 3 * r + (k : ℕ)) i = 0 := by
  rw [colShift_role, hr]; simp [coord]

variable (i₁ i₂ : Fin n) (d₁ d₂ d₁' d₂' : K)

theorem roleShift_off (r : ℕ)
    (hr : r ≠ 37 ∧ r ≠ 38 ∧ r ≠ 42 ∧ r ≠ 43 ∧ r ≠ 44 ∧ r ≠ 50) (i : Fin n) :
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' r i = 0 := by
  obtain ⟨h37, h38, h42, h43, h44, h50⟩ := hr
  simp [roleShift, h37, h38, h42, h43, h44, h50]

theorem roleShift_ge (r : ℕ) (hr : 55 ≤ r) (i : Fin n) :
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' r i = 0 :=
  roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' r (by omega) i

theorem colShift_roleShift_base (c : ℕ) (hc : c < 6) (i : Fin n) :
    colShift b (roleShift i₁ i₂ d₁ d₂ d₁' d₂') c i = 0 := colShift_base b _ c hc i

variable (hlt : (i₁ : ℕ) < (i₂ : ℕ))
variable (hsum : d₁'⁻¹ + d₂'⁻¹ = d₁⁻¹ + d₂⁻¹)
include hlt

theorem roleShift_at₁ :
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 37 i₁ = d₁' - d₁ ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 50 i₁ = d₁' - d₁ ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 38 i₁ = d₁'⁻¹ - d₁⁻¹ ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 42 i₁ = d₁'⁻¹ - d₁⁻¹ ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 43 i₁ = 0 ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 44 i₁ = d₁'⁻¹ - d₁⁻¹ := by
  simp [roleShift, hlt]

theorem roleShift_at₂ :
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 37 i₂ = d₂' - d₂ ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 50 i₂ = d₂' - d₂ ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 38 i₂ = d₂'⁻¹ - d₂⁻¹ ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 42 i₂ = d₂'⁻¹ - d₂⁻¹ ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 43 i₂ = d₁'⁻¹ - d₁⁻¹ ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 44 i₂ = 0 := by
  have hne : i₂ ≠ i₁ := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  simp [roleShift, hne, hlt]

theorem roleShift_other (j : Fin n) (hj₁ : j ≠ i₁) (hj₂ : j ≠ i₂) :
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 37 j = 0 ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 50 j = 0 ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 38 j = 0 ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 42 j = 0 ∧
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 43 j = roleShift i₁ i₂ d₁ d₂ d₁' d₂' 44 j := by
  have h1 : (j : ℕ) ≠ (i₁ : ℕ) := fun h => hj₁ (Fin.ext h)
  have h2 : (j : ℕ) ≠ (i₂ : ℕ) := fun h => hj₂ (Fin.ext h)
  refine ⟨by simp [roleShift, hj₁, hj₂], by simp [roleShift, hj₁, hj₂],
    by simp [roleShift, hj₁, hj₂], by simp [roleShift, hj₁, hj₂], ?_⟩
  simp only [roleShift]
  simp only [show (43 : ℕ) = 37 ∨ 43 = 50 ↔ False by decide, show (43 : ℕ) = 38 ∨ 43 = 42 ↔ False by decide,
    show (44 : ℕ) = 37 ∨ 44 = 50 ↔ False by decide, show (44 : ℕ) = 38 ∨ 44 = 42 ↔ False by decide,
    if_false]
  simp only [show (43 : ℕ) ≠ 44 by decide, if_true, if_false]
  by_cases hin : (i₁ : ℕ) < (j : ℕ) ∧ (j : ℕ) < (i₂ : ℕ)
  · rw [if_pos ⟨hin.1, hin.2.le⟩, if_pos ⟨hin.1.le, hin.2⟩]
  · rw [if_neg (by omega), if_neg (by omega)]

include hsum in
/-- The committed step `acc_after − acc_before − contribution` is invariant: the shifts cancel
at every row. -/
theorem roleShift_step (j : Fin n) :
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 44 j - roleShift i₁ i₂ d₁ d₂ d₁' d₂' 43 j -
      roleShift i₁ i₂ d₁ d₂ d₁' d₂' 42 j = 0 := by
  by_cases hj₁ : j = i₁
  · rw [hj₁]
    obtain ⟨-, -, -, h42, h43, h44⟩ := roleShift_at₁ i₁ i₂ d₁ d₂ d₁' d₂' hlt
    rw [h42, h43, h44]; ring
  by_cases hj₂ : j = i₂
  · rw [hj₂]
    obtain ⟨-, -, -, h42, h43, h44⟩ := roleShift_at₂ i₁ i₂ d₁ d₂ d₁' d₂' hlt
    rw [h42, h43, h44]; linear_combination (-1 : K) * hsum
  · obtain ⟨-, -, -, h42, h4344⟩ := roleShift_other i₁ i₂ d₁ d₂ d₁' d₂' hlt j hj₁ hj₂
    rw [h42, h4344]; ring

/-- The chain `acc_after(i) = acc_before(i+1)` is invariant. -/
theorem roleShift_chain (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 44 j = roleShift i₁ i₂ d₁ d₂ d₁' d₂' 43 ⟨(j : ℕ) + 1, hj⟩ := by
  simp only [roleShift]
  simp only [show (43 : ℕ) = 37 ∨ 43 = 50 ↔ False by decide, show (43 : ℕ) = 38 ∨ 43 = 42 ↔ False by decide,
    show (44 : ℕ) = 37 ∨ 44 = 50 ↔ False by decide, show (44 : ℕ) = 38 ∨ 44 = 42 ↔ False by decide,
    if_false]
  simp only [show (43 : ℕ) ≠ 44 by decide, if_true, if_false]
  by_cases hin : (i₁ : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i₂ : ℕ)
  · rw [if_pos hin, if_pos (by omega)]
  · rw [if_neg hin, if_neg (by omega)]

omit hlt in
theorem roleShift_43_first (j : Fin n) (hj : (j : ℕ) = 0) :
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 43 j = 0 := by
  simp only [roleShift]
  simp only [show (43 : ℕ) = 37 ∨ 43 = 50 ↔ False by decide, show (43 : ℕ) = 38 ∨ 43 = 42 ↔ False by decide,
    show (43 : ℕ) ≠ 44 by decide, if_false, if_true]
  rw [if_neg (by omega)]

omit hlt in
theorem roleShift_44_last (j : Fin n) (hj : (j : ℕ) + 1 = n) :
    roleShift i₁ i₂ d₁ d₂ d₁' d₂' 44 j = 0 := by
  have := i₂.isLt
  simp only [roleShift]
  simp only [show (44 : ℕ) = 37 ∨ 44 = 50 ↔ False by decide, show (44 : ℕ) = 38 ∨ 44 = 42 ↔ False by decide,
    if_false, if_true]
  rw [if_neg (by omega)]

end Shift

/-! ## E3. One row of the perturbed trace, abstractly -/

section Row

variable (b : Basis (Fin 3) F K) {n : ℕ}

/-- The base-field row environment `envF'` is `envF` with the column shift `δ` applied at row
`j` (this row) and at row `j + 1` (the next-row read, when there is one); columns `δ` never
touches are untouched at the next row whatever the row. -/
structure ShiftedRowF (envF envF' : Env F) (δ : ℕ → Fin n → F) (j : Fin n) : Prop where
  cur : ∀ c, envF'.trace c = envF.trace c + δ c j
  next_on : ∀ (hj : (j : ℕ) + 1 < n) (c : ℕ), envF'.traceNext c = envF.traceNext c + δ c ⟨(j : ℕ) + 1, hj⟩
  next_off : ∀ c, (∀ i, δ c i = 0) → envF'.traceNext c = envF.traceNext c
  chal : ∀ c, envF'.chal c = envF.chal c
  pub : ∀ c, envF'.pub c = envF.pub c

variable {envF envF' : Env F} (S : ℕ → Fin n → K) {j : Fin n}
  (h : ShiftedRowF envF envF' (colShift b S) j)
include h

theorem gather_cur (r : ℕ) :
    (gatherEnv b memoryCol0 envF').trace r = (gatherEnv b memoryCol0 envF).trace r + S r j := by
  simp only [gatherEnv, memoryCol0]
  rw [show S r j = ∑ k : Fin 3, coord b (S r j) k • b k from (reconstruct_coord b _).symm,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h.cur, colShift_role, add_smul]

theorem gather_next_on (hj : (j : ℕ) + 1 < n) (r : ℕ) :
    (gatherEnv b memoryCol0 envF').traceNext r =
      (gatherEnv b memoryCol0 envF).traceNext r + S r ⟨(j : ℕ) + 1, hj⟩ := by
  simp only [gatherEnv, memoryCol0]
  rw [show S r ⟨(j : ℕ) + 1, hj⟩ = ∑ k : Fin 3, coord b (S r ⟨(j : ℕ) + 1, hj⟩) k • b k from
    (reconstruct_coord b _).symm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h.next_on hj, colShift_role, add_smul]

theorem gather_next_off (r : ℕ) (hr : ∀ i, S r i = 0) :
    (gatherEnv b memoryCol0 envF').traceNext r = (gatherEnv b memoryCol0 envF).traceNext r := by
  simp only [gatherEnv, memoryCol0]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h.next_off _ (colShift_role_zero b S r k hr)]

theorem gather_chal (r : ℕ) :
    (gatherEnv b memoryCol0 envF').chal r = (gatherEnv b memoryCol0 envF).chal r := by
  simp only [gatherEnv, memoryCol0, h.chal]

theorem gather_pub (r : ℕ) :
    (gatherEnv b memoryCol0 envF').pub r = (gatherEnv b memoryCol0 envF).pub r := by
  simp only [gatherEnv, memoryCol0, h.pub]

end Row

/-! ### The `𝕂`-level sources at a shifted row -/

section RowK

variable (b : Basis (Fin 3) F K) {n : ℕ} (i₁ i₂ : Fin n) (d₁ d₂ d₁' d₂' : K)

/-- The twelve variables the shift can touch. -/
def touchedVars : Finset (VarKind × ℕ) :=
  {(VarKind.traceCur, 37), (VarKind.traceCur, 38), (VarKind.traceCur, 42),
   (VarKind.traceCur, 43), (VarKind.traceCur, 44), (VarKind.traceCur, 50),
   (VarKind.traceNext, 37), (VarKind.traceNext, 38), (VarKind.traceNext, 42),
   (VarKind.traceNext, 43), (VarKind.traceNext, 44), (VarKind.traceNext, 50)}

/-- **Independent read-set measurement** (own instrument, `decide`): the forty non-sampled
sources, the two degree-one and the two degree-three endpoints read none of the twelve. -/
local instance : FiniteDimensional (ZMod 31) (ZMod 31) := inferInstance

theorem blind_sources_off_touched :
    ∀ e ∈ memoryRowSources (K := ZMod 31) ++ [memoryChainSource] ++ walkBoundarySources ++
        walkTransitionSources ++ degreeOneEndpoints ++ degreeThreeEndpoints,
      ∀ v ∈ touchedVars, v ∉ exprVariableSupport e := by
  set_option maxRecDepth 100000 in decide

/-- Same read-set at a general carrier: support of `memoryRowSources` is K-independent. -/
theorem blind_sources_off_touched_any {L : Type} [Field L] :
    ∀ e ∈ memoryRowSources (K := L) ++ [memoryChainSource] ++ walkBoundarySources ++
        walkTransitionSources ++ degreeOneEndpoints ++ degreeThreeEndpoints,
      ∀ v ∈ touchedVars, v ∉ exprVariableSupport e := by
  intro e he v hv
  simp only [List.mem_append, List.mem_singleton] at he
  rcases he with ((((hr | rfl) | hb) | ht) | hd1) | hd3
  · obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hr
    have hn31 : n < (memoryRowSources (K := ZMod 31)).length := by
      rw [memoryRowSources_length] at hn ⊢
      exact hn
    have hsupp := memoryRowSource_support_carrier (K₁ := L) (K₂ := ZMod 31) n hn hn31
    rw [hsupp]
    exact blind_sources_off_touched _ (by
      simp [List.mem_append, List.getElem_mem]) v hv
  · exact blind_sources_off_touched memoryChainSource (by
      simp [List.mem_append, List.mem_singleton]) v hv
  · exact blind_sources_off_touched e (by
      simp [List.mem_append, hb]) v hv
  · exact blind_sources_off_touched e (by
      simp [List.mem_append, ht]) v hv
  · exact blind_sources_off_touched e (by
      simp [List.mem_append, hd1]) v hv
  · exact blind_sources_off_touched e (by
      simp [List.mem_append, hd3]) v hv

variable {envF envF' : Env F} {j : Fin n}
  (h : ShiftedRowF envF envF' (colShift b (roleShift i₁ i₂ d₁ d₂ d₁' d₂')) j)
include h


theorem eval_blind (e : Expr) (hsupp : ∀ v ∈ touchedVars, v ∉ exprVariableSupport e) :
    e.eval (gatherEnv b memoryCol0 envF') = e.eval (gatherEnv b memoryCol0 envF) := by
  apply Batch266.eval_congr_of_disjoint touchedVars _ _ _ e hsupp
  rintro ⟨k, r⟩ hv
  cases k
  · have hr : r ≠ 37 ∧ r ≠ 38 ∧ r ≠ 42 ∧ r ≠ 43 ∧ r ≠ 44 ∧ r ≠ 50 := by
      simpa [touchedVars] using hv
    simp only [Batch266.envAt]
    rw [gather_cur b _ h, roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' r hr, add_zero]
  · have hr : r ≠ 37 ∧ r ≠ 38 ∧ r ≠ 42 ∧ r ≠ 43 ∧ r ≠ 44 ∧ r ≠ 50 := by
      simpa [touchedVars] using hv
    simp only [Batch266.envAt]
    exact gather_next_off b _ h r (roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' r hr)
  · exact gather_chal b _ h r
  · exact gather_pub b _ h r

variable (hlt : (i₁ : ℕ) < (i₂ : ℕ)) (hsum : d₁'⁻¹ + d₂'⁻¹ = d₁⁻¹ + d₂⁻¹)
  (hd₁' : d₁' ≠ 0) (hd₂' : d₂' ≠ 0)
  (hall : ∀ e ∈ transitionSources (K := K), e.eval (gatherEnv b memoryCol0 envF) = 0)
  (hj₁ : j = i₁ → (gatherEnv b memoryCol0 envF).trace 39 = 1 ∧ (gatherEnv b memoryCol0 envF).trace 37 = d₁)
  (hj₂ : j = i₂ → (gatherEnv b memoryCol0 envF).trace 39 = 1 ∧ (gatherEnv b memoryCol0 envF).trace 37 = d₂)
  (h47 : (j : ℕ) ≠ 0 → (gatherEnv b memoryCol0 envF).trace 47 = 0)
  (h48 : (j : ℕ) + 1 ≠ n → (gatherEnv b memoryCol0 envF).trace 48 = 0)
include hlt hsum hd₁' hd₂' hall hj₁ hj₂ h47 h48

set_option maxHeartbeats 800000 in
/-- **The six sampled fold sources vanish at the shifted row.** -/
theorem sampled_fold_sources_shifted :
    ∀ e ∈ sampledFoldSources, e.eval (gatherEnv b memoryCol0 envF') = 0 := by
  have hs : ∀ e ∈ sampledSources, e.eval (gatherEnv b memoryCol0 envF) = 0 := fun e he => hall e (sampledSources_mem e he)
  have s0 := hs _ (show (Expr.Sub (.Mul (extVar .traceCur 50) (extVar .traceCur 38)) (.Const 1)) ∈ sampledSources by simp [sampledSources])
  have s1 := hs _ (show (Expr.Mul (extVar .traceCur 39) (.Sub (extVar .traceCur 39) (.Const 1))) ∈ sampledSources by simp [sampledSources])
  have s2 := hs _ (show (Expr.Sub (extVar .traceCur 42) (.Mul (extVar .traceCur 39) (extVar .traceCur 38))) ∈ sampledSources by simp [sampledSources])
  have s4 := hs _ (show (Expr.Sub (extVar .traceCur 50) (.Add (.Mul (extVar .traceCur 39) (extVar .traceCur 37)) (.Sub (.Const 1) (extVar .traceCur 39)))) ∈ sampledSources by simp [sampledSources])
  have s7 := hs _ (show (Expr.Mul (extVar .traceCur 47) (extVar .traceCur 43)) ∈ sampledSources by simp [sampledSources])
  have s8 := hs _ (show (Expr.Mul (extVar .traceCur 48) (.Sub (extVar .traceCur 44) (extVar .traceCur 40))) ∈ sampledSources by simp [sampledSources])
  simp only [extVar, Expr.eval, Int.cast_one] at s0 s1 s2 s4 s7 s8
  have c37 := gather_cur b _ h 37
  have c38 := gather_cur b _ h 38
  have c39 := gather_cur b _ h 39
  have c40 := gather_cur b _ h 40
  have c42 := gather_cur b _ h 42
  have c43 := gather_cur b _ h 43
  have c44 := gather_cur b _ h 44
  have c47 := gather_cur b _ h 47
  have c48 := gather_cur b _ h 48
  have c50 := gather_cur b _ h 50
  rw [roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 39 (by decide) j, add_zero] at c39
  rw [roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 40 (by decide) j, add_zero] at c40
  rw [roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 47 (by decide) j, add_zero] at c47
  rw [roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 48 (by decide) j, add_zero] at c48
  -- the row-type case split
  have key : ∀ (dj dj' : K), dj' ≠ 0 →
      (gatherEnv b memoryCol0 envF).trace 39 = 1 → (gatherEnv b memoryCol0 envF).trace 37 = dj →
      roleShift i₁ i₂ d₁ d₂ d₁' d₂' 37 j = dj' - dj → roleShift i₁ i₂ d₁ d₂ d₁' d₂' 50 j = dj' - dj → roleShift i₁ i₂ d₁ d₂ d₁' d₂' 38 j = dj'⁻¹ - dj⁻¹ → roleShift i₁ i₂ d₁ d₂ d₁' d₂' 42 j = dj'⁻¹ - dj⁻¹ →
      ((gatherEnv b memoryCol0 envF').trace 50 * (gatherEnv b memoryCol0 envF').trace 38 - 1 = 0) ∧ ((gatherEnv b memoryCol0 envF').trace 42 - (gatherEnv b memoryCol0 envF').trace 39 * (gatherEnv b memoryCol0 envF').trace 38 = 0) ∧
      ((gatherEnv b memoryCol0 envF').trace 50 - ((gatherEnv b memoryCol0 envF').trace 39 * (gatherEnv b memoryCol0 envF').trace 37 + (1 - (gatherEnv b memoryCol0 envF').trace 39)) = 0) := by
    intro dj dj' hdj' hver hd h37 h50 h38 h42
    rw [hver] at s2 s4
    simp only [one_mul, sub_self, add_zero] at s2 s4
    have h50v : (gatherEnv b memoryCol0 envF).trace 50 = dj := by rw [sub_eq_zero.mp s4, hd]
    have hdj : dj ≠ 0 := by
      intro h0
      rw [h50v, h0, zero_mul] at s0
      exact one_ne_zero (by linear_combination -s0)
    have h38v : (gatherEnv b memoryCol0 envF).trace 38 = dj⁻¹ := by
      rw [h50v] at s0
      exact eq_inv_of_mul_eq_one_right (sub_eq_zero.mp s0)
    refine ⟨?_, ?_, ?_⟩
    · rw [c50, c38, h50, h38, h50v, h38v]
      rw [show dj + (dj' - dj) = dj' by ring, show dj⁻¹ + (dj'⁻¹ - dj⁻¹) = dj'⁻¹ by ring]
      exact sub_eq_zero.mpr (mul_inv_cancel₀ hdj')
    · rw [c42, c39, c38, h42, h38, hver, sub_eq_zero.mp s2]
      ring
    · rw [c50, c39, c37, h50, h37, hver, h50v, hd]
      ring
  intro e he
  simp only [sampledFoldSources, List.mem_cons, List.not_mem_nil, or_false] at he
  have e0 : sampledSources.get ⟨0, by decide⟩ = .Sub (.Mul (extVar .traceCur 50) (extVar .traceCur 38)) (.Const 1) := rfl
  have e1 : sampledSources.get ⟨1, by decide⟩ = .Mul (extVar .traceCur 39) (.Sub (extVar .traceCur 39) (.Const 1)) := rfl
  have e2 : sampledSources.get ⟨2, by decide⟩ = .Sub (extVar .traceCur 42) (.Mul (extVar .traceCur 39) (extVar .traceCur 38)) := rfl
  have e4 : sampledSources.get ⟨4, by decide⟩ = .Sub (extVar .traceCur 50) (.Add (.Mul (extVar .traceCur 39) (extVar .traceCur 37)) (.Sub (.Const 1) (extVar .traceCur 39))) := rfl
  have e7 : sampledSources.get ⟨7, by decide⟩ = .Mul (extVar .traceCur 47) (extVar .traceCur 43) := rfl
  have e8 : sampledSources.get ⟨8, by decide⟩ = .Mul (extVar .traceCur 48) (.Sub (extVar .traceCur 44) (extVar .traceCur 40)) := rfl
  rw [e0, e1, e2, e4, e7, e8] at he
  -- source 1 (booleanity of `ver`) and the two masked ones first; then the three denominator ones
  have hver_bool : (gatherEnv b memoryCol0 envF').trace 39 * ((gatherEnv b memoryCol0 envF').trace 39 - 1) = 0 := by rw [c39]; exact s1
  have h7 : (gatherEnv b memoryCol0 envF').trace 47 * (gatherEnv b memoryCol0 envF').trace 43 = 0 := by
    rw [c47, c43]
    by_cases hz : (j : ℕ) = 0
    · rw [roleShift_43_first i₁ i₂ d₁ d₂ d₁' d₂' j hz, add_zero]; exact s7
    · rw [h47 hz, zero_mul]
  have h8 : (gatherEnv b memoryCol0 envF').trace 48 * ((gatherEnv b memoryCol0 envF').trace 44 - (gatherEnv b memoryCol0 envF').trace 40) = 0 := by
    rw [c48, c44, c40]
    by_cases hl : (j : ℕ) + 1 = n
    · rw [roleShift_44_last i₁ i₂ d₁ d₂ d₁' d₂' j hl, add_zero]; exact s8
    · rw [h48 hl, zero_mul]
  have hden : ((gatherEnv b memoryCol0 envF').trace 50 * (gatherEnv b memoryCol0 envF').trace 38 - 1 = 0) ∧ ((gatherEnv b memoryCol0 envF').trace 42 - (gatherEnv b memoryCol0 envF').trace 39 * (gatherEnv b memoryCol0 envF').trace 38 = 0) ∧
      ((gatherEnv b memoryCol0 envF').trace 50 - ((gatherEnv b memoryCol0 envF').trace 39 * (gatherEnv b memoryCol0 envF').trace 37 + (1 - (gatherEnv b memoryCol0 envF').trace 39)) = 0) := by
    by_cases hj₁' : j = i₁
    · obtain ⟨hv, hd⟩ := hj₁ hj₁'
      obtain ⟨a37, a50, a38, a42, -, -⟩ := roleShift_at₁ i₁ i₂ d₁ d₂ d₁' d₂' hlt
      subst hj₁'
      exact key d₁ d₁' hd₁' hv hd a37 a50 a38 a42
    by_cases hj₂' : j = i₂
    · obtain ⟨hv, hd⟩ := hj₂ hj₂'
      obtain ⟨a37, a50, a38, a42, -, -⟩ := roleShift_at₂ i₁ i₂ d₁ d₂ d₁' d₂' hlt
      subst hj₂'
      exact key d₂ d₂' hd₂' hv hd a37 a50 a38 a42
    · obtain ⟨a37, a50, a38, a42, -⟩ := roleShift_other i₁ i₂ d₁ d₂ d₁' d₂' hlt j hj₁' hj₂'
      rw [c50, c38, c42, c39, c37, a37, a50, a38, a42, add_zero, add_zero, add_zero, add_zero]
      exact ⟨s0, s2, s4⟩
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [extVar, Expr.eval, Int.cast_one]
  · exact hden.1
  · exact hver_bool
  · exact hden.2.1
  · exact hden.2.2
  · exact h7
  · exact h8

/-- **All forty fold sources and the four endpoints vanish at the shifted row.** -/
theorem fold_sources_shifted
    (hend : ∀ e ∈ degreeOneEndpoints ++ degreeThreeEndpoints, e.eval (gatherEnv b memoryCol0 envF) = 0) :
    (∀ e ∈ extensionFoldSources (K := K), e.eval (gatherEnv b memoryCol0 envF') = 0) ∧
      (∀ e ∈ degreeOneEndpoints ++ degreeThreeEndpoints, e.eval (gatherEnv b memoryCol0 envF') = 0) := by
  constructor
  · intro e he
    have he' := he
    simp only [extensionFoldSources, List.mem_append] at he
    rcases he with ((hrow | hb) | ht) | hs
    · rw [eval_blind b i₁ i₂ d₁ d₂ d₁' d₂' h e (blind_sources_off_touched_any (L := K) e (by
        simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_of_mem_drop hrow)))))))]
      exact hall e (extensionFoldSources_subset_transitionSources e he')
    · rw [eval_blind b i₁ i₂ d₁ d₂ d₁' d₂' h e (blind_sources_off_touched_any (L := K) e (by
        simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hb)))))]
      exact hall e (extensionFoldSources_subset_transitionSources e he')
    · rw [eval_blind b i₁ i₂ d₁ d₂ d₁' d₂' h e (blind_sources_off_touched_any (L := K) e (by
        simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inr ht))))]
      exact hall e (extensionFoldSources_subset_transitionSources e he')
    · exact sampled_fold_sources_shifted b i₁ i₂ d₁ d₂ d₁' d₂' h hlt hsum hd₁' hd₂' hall hj₁ hj₂
        h47 h48 e hs
  · intro e he
    have hmem : e ∈ memoryRowSources (K := K) ++ [memoryChainSource] ++ walkBoundarySources ++
        walkTransitionSources ++ degreeOneEndpoints ++ degreeThreeEndpoints := by
      simp only [List.mem_append] at he ⊢
      rcases he with h1 | h1
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h1
    rw [eval_blind b i₁ i₂ d₁ d₂ d₁' d₂' h e (blind_sources_off_touched_any (L := K) e hmem)]
    -- the endpoints vanish on the original row: they are in the committed `𝕂` gate list
    exact hend e he

end RowK

/-! ### The base gates, equality checks and mixed gates at a shifted row -/

section RowF

variable (b : Basis (Fin 3) F K) {n : ℕ} (i₁ i₂ : Fin n) (d₁ d₂ d₁' d₂' : K)
variable {envF envF' : Env F} {j : Fin n}
  (h : ShiftedRowF envF envF' (colShift b (roleShift i₁ i₂ d₁ d₂ d₁' d₂')) j)
  (hlt : (i₁ : ℕ) < (i₂ : ℕ)) (hsum : d₁'⁻¹ + d₂'⁻¹ = d₁⁻¹ + d₂⁻¹)
include h

theorem cur_base (c : ℕ) (hc : c < 6) : envF'.trace c = envF.trace c := by
  rw [h.cur, colShift_base b _ c hc, add_zero]

theorem cur_role_off (r : ℕ) (k : Fin 3)
    (hr : r ≠ 37 ∧ r ≠ 38 ∧ r ≠ 42 ∧ r ≠ 43 ∧ r ≠ 44 ∧ r ≠ 50) :
    envF'.trace (6 + 3 * r + (k : ℕ)) = envF.trace (6 + 3 * r + (k : ℕ)) := by
  rw [h.cur, colShift_role, roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' r hr]; simp [coord]

/-- **The five paper base gates are unchanged** (four booleanities and the one-hot sum on
columns `0..3`; W2 stage 2, `paperBaseGates`).  The pre-swap eleven-gate list
(`foldedBaseTransitionGates`, last) also contained the sampled terminal and
accumulator coordinate folds, which now live in `paperKGates`. -/
theorem base_gates_shifted :
    ∀ g ∈ baseTransitionGates b, g.eval envF' = g.eval envF := by
  intro g hg
  simp only [baseTransitionGates, List.mem_append, List.mem_singleton] at hg
  rcases hg with hp | heq
  · simp only [paperBaseGates, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · simp [bbool, bcur, CoeffExpr.eval, cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 0 (by norm_num)]
    · simp [bbool, bcur, CoeffExpr.eval, cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 1 (by norm_num)]
    · simp [bbool, bcur, CoeffExpr.eval, cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 2 (by norm_num)]
    · simp [bbool, bcur, CoeffExpr.eval, cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 3 (by norm_num)]
    · simp [bsum4, CoeffExpr.eval, cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 0 (by norm_num),
        cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 1 (by norm_num),
        cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 2 (by norm_num),
        cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 3 (by norm_num)]
  · rw [heq]
    have h2 := cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 2 (by norm_num)
    have h39 := cur_role_off b i₁ i₂ d₁ d₂ d₁' d₂' h 39 (0 : Fin 3)
      (by decide : (39 : ℕ) ≠ 37 ∧ 39 ≠ 38 ∧ 39 ≠ 42 ∧ 39 ≠ 43 ∧ 39 ≠ 44 ∧ 39 ≠ 50)
    simp [readRootVerGate, bcur, extCoord, CoeffExpr.eval, h2]
    refine Or.inl ?_
    convert h39 <;> norm_num

/-- **Equality checks are empty after W2 stage 2.**  The twelve selector-mirror checks last
statable (`foldedEqualityChecks`). -/
theorem equality_checks_shifted :
    ∀ g ∈ equalityChecks b, g.eval envF' = g.eval envF := by
  intro g hg
  simp [equalityChecks] at hg

include hlt in
/-- **The four pre-W2 mixed gates other than the denominator pin vanish at the shifted row**
whenever they vanish at the original, read against `foldedMixedTransitionGates` (last
statable as a live-bucket claim).  W2 stage 2's live mixed bucket is
`paperKGates` (45); the pin itself still sees the swap (`denominatorPin_shifted`). -/
theorem other_mixed_gates_shifted
    (hlast : (j : ℕ) + 1 = n → envF.trace 5 = 1)
    (horig : ∀ g ∈ foldedMixedTransitionGates (F := F),
      g.eval (gatherEnv b memoryCol0 envF) envF = 0) :
    ∀ g ∈ foldedMixedTransitionGates (F := F), g ≠ denominatorPinMixed →
      g.eval (gatherEnv b memoryCol0 envF') envF' = 0 := by
  intro g hg hne
  have ho := horig g hg
  simp only [foldedMixedTransitionGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [firstMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval] at ho ⊢
    rw [gather_cur b _ h, roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 47 (by decide), add_zero,
      cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 4 (by norm_num)]
    exact ho
  · simp only [lastMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval] at ho ⊢
    rw [gather_cur b _ h, roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 48 (by decide), add_zero,
      cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 5 (by norm_num)]
    exact ho
  · simp only [chainMixed, MixedExpr.eval, bcur, CoeffExpr.eval] at ho ⊢
    rw [gather_cur b _ h, roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 28 (by decide), add_zero,
      gather_next_off b _ h 27 (roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 27 (by decide)),
      cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 5 (by norm_num)]
    exact ho
  · simp only [accChainMixed, MixedExpr.eval, bcur, CoeffExpr.eval] at ho ⊢
    rw [cur_base b i₁ i₂ d₁ d₂ d₁' d₂' h 5 (by norm_num)]
    by_cases hj : (j : ℕ) + 1 < n
    · rw [gather_cur b _ h, gather_next_on b _ h hj, roleShift_chain i₁ i₂ d₁ d₂ d₁' d₂' hlt j hj]
      rw [show (gatherEnv b memoryCol0 envF).trace 44 +
          roleShift i₁ i₂ d₁ d₂ d₁' d₂' 43 ⟨(j : ℕ) + 1, hj⟩ -
          ((gatherEnv b memoryCol0 envF).traceNext 43 +
            roleShift i₁ i₂ d₁ d₂ d₁' d₂' 43 ⟨(j : ℕ) + 1, hj⟩) =
          (gatherEnv b memoryCol0 envF).trace 44 - (gatherEnv b memoryCol0 envF).traceNext 43 by
        ring]
      exact ho
    · have hl : (j : ℕ) + 1 = n := by have := j.isLt; omega
      rw [hlast hl]; simp
  · exact absurd rfl hne
  · simp only [dequeueMaskMixed, MixedExpr.eval, bcur, CoeffExpr.eval] at ho ⊢
    have h154 : envF'.trace 154 = envF.trace 154 := by
      rw [h.cur]
      have hz : colShift b (roleShift i₁ i₂ d₁ d₂ d₁' d₂') 154 j = 0 := by
        rw [show (154 : ℕ) = 6 + 3 * 49 + (1 : ℕ) by norm_num]
        exact colShift_role_zero b _ 49 ⟨1, by decide⟩
          (fun i => roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 49 (by decide) i) j
      rw [hz, add_zero]
    rw [gather_cur b _ h, roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 56 (by decide), add_zero, h154]
    exact ho

/-- **The denominator pin sees the swap.**  At the shifted row the pin moves by exactly the
denominator's shift `roleShift … 37 j` (`d₁' − d₁` at `i₁`, `d₂' − d₂` at `i₂`, `0` elsewhere):
the record roles `19..26` and the two coin slots are untouched by the attack. -/
theorem denominatorPin_shifted :
    (denominatorPinMixed (F := F)).eval (gatherEnv b memoryCol0 envF') envF' =
      (denominatorPinMixed (F := F)).eval (gatherEnv b memoryCol0 envF) envF +
        roleShift i₁ i₂ d₁ d₂ d₁' d₂' 37 j := by
  simp only [denominatorPinMixed, recordRLC, recordRLCExpr, reqIdxRLCTerm, reqIdxCol, bcur,
    CoeffExpr.eval, MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.eval]
  have h181 : envF'.trace 181 = envF.trace 181 := by
    rw [h.cur]
    have hz : colShift b (roleShift i₁ i₂ d₁ d₂ d₁' d₂') 181 j = 0 := by
      rw [show (181 : ℕ) = 6 + 3 * 58 + (1 : ℕ) by norm_num]
      exact colShift_role_zero b _ 58 ⟨1, by decide⟩
        (fun i => roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 58 (by decide) i) j
    rw [hz, add_zero]
  rw [h181]
  rw [gather_cur b _ h 37, gather_chal b _ h 4, gather_chal b _ h 5]
  rw [gather_cur b _ h 19, gather_cur b _ h 20, gather_cur b _ h 21, gather_cur b _ h 22,
    gather_cur b _ h 23, gather_cur b _ h 24, gather_cur b _ h 25, gather_cur b _ h 26,
    gather_cur b _ h 57]
  rw [roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 19 (by decide), roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 20 (by decide),
    roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 21 (by decide), roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 22 (by decide),
    roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 23 (by decide), roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 24 (by decide),
    roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 25 (by decide), roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 26 (by decide),
    roleShift_off i₁ i₂ d₁ d₂ d₁' d₂' 57 (by decide)]
  ring

end RowF

/-! ## E5. At the consumed chip `P.memoryChip` -/

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem colShift_roleShift_ge171 (b : Basis (Fin 3) F K) {n : ℕ} (i₁ i₂ : Fin n)
    (d₁ d₂ d₁' d₂' : K) (c : ℕ) (hc : 171 ≤ c) (i : Fin n) :
    colShift b (roleShift i₁ i₂ d₁ d₂ d₁' d₂') c i = 0 := by
  simp only [colShift, if_pos (show 6 ≤ c by omega)]
  rw [roleShift_ge i₁ i₂ d₁ d₂ d₁' d₂' _ (by omega)]
  simp [coord]

/-- The perturbed source row is a `ShiftedRowF` of the original. -/
theorem shiftedRowF_perturb (b : Basis (Fin 3) F K) {n : ℕ} (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (i₁ i₂ : Fin n) (d₁ d₂ d₁' d₂' : K)
    {w : ℕ} (hw : w = 182) (Q : Fin w → F[X]) (ω : F) (chal pub : ℕ → F) (j : Fin n)
    (hsucc : ∀ (hj : (j : ℕ) + 1 < n), nodes ⟨(j : ℕ) + 1, hj⟩ = nodes j * ω) :
    ShiftedRowF (envOfTrace Q ω (nodes j) chal pub)
      (envOfTrace (perturb nodes (colShift b (roleShift i₁ i₂ d₁ d₂ d₁' d₂')) Q) ω (nodes j)
        chal pub)
      (colShift b (roleShift i₁ i₂ d₁ d₂ d₁' d₂')) j where
  cur c := by
    simp only [envOfTrace]
    split_ifs with hc
    · exact perturb_eval nodes hinj _ Q ⟨c, hc⟩ j
    · rw [colShift_roleShift_ge171 b i₁ i₂ d₁ d₂ d₁' d₂' c (by omega), add_zero]
  next_on hj c := by
    simp only [envOfTrace]
    split_ifs with hc
    · rw [mul_comm, ← hsucc hj]
      exact perturb_eval nodes hinj _ Q ⟨c, hc⟩ ⟨(j : ℕ) + 1, hj⟩
    · rw [colShift_roleShift_ge171 b i₁ i₂ d₁ d₂ d₁' d₂' c (by omega), add_zero]
  next_off c h0 := by
    simp only [envOfTrace]
    split_ifs with hc
    · rw [perturb_off nodes _ Q ⟨c, hc⟩ h0]
    · rfl
  chal _ := rfl
  pub _ := rfl

variable (i₁ i₂ : Fin (rows P)) (d₁' d₂' : K) (Qm : Fin P.memoryChip.rap.w → F[X])

/-- The column shift of the attack, at the package's basis, with `d₁`, `d₂` read off `Qm`. -/
abbrev attackShift : ℕ → Fin (rows P) → F :=
  colShift P.optimized.basis
    (roleShift i₁ i₂ ((rowEnvK P Qm i₁).trace 37) ((rowEnvK P Qm i₂).trace 37) d₁' d₂')

/-- **The attack trace**: `Qm` with the two verify rows' denominators replaced by `d₁'`, `d₂'`
(roles `37`, `50`), their inverses (roles `38`, `42`) and the running sum between them
(roles `44`, `43`) adjusted. -/
def attackTrace : Fin P.memoryChip.rap.w → F[X] :=
  perturb P.optimized.memoryNodes (attackShift P i₁ i₂ d₁' d₂' Qm) Qm

theorem proj_attackTrace :
    projOf P (attackTrace P i₁ i₂ d₁' d₂' Qm) =
      perturb P.optimized.memoryNodes (attackShift P i₁ i₂ d₁' d₂' Qm) (projOf P Qm) :=
  projectTrace_perturb _ _ _ _ Qm

theorem rowEnvF_attack (j : Fin (rows P)) :
    rowEnvF P (attackTrace P i₁ i₂ d₁' d₂' Qm) j =
      envOfTrace (perturb P.optimized.memoryNodes (attackShift P i₁ i₂ d₁' d₂' Qm) (projOf P Qm))
        P.optimized.orbit.ω (P.optimized.memoryNodes j) P.optimized.memoryChallenge
        P.optimized.memoryPublic := by
  simp only [rowEnvF, proj_attackTrace]

theorem shiftedRow_attack (j : Fin (rows P)) :
    ShiftedRowF (rowEnvF P Qm j) (rowEnvF P (attackTrace P i₁ i₂ d₁' d₂' Qm) j)
      (attackShift P i₁ i₂ d₁' d₂' Qm) j := by
  rw [rowEnvF_attack]
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).1
  exact shiftedRowF_perturb P.optimized.basis P.optimized.memoryNodes
    P.optimized.memoryNodes_injective i₁ i₂ _ _ d₁' d₂' hw (projOf P Qm) _ _ _ j
    (fun hj => P.optimized.memoryOrbitAligned j hj)

variable (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
  (hlt : (i₁ : ℕ) < (i₂ : ℕ))
include hsat hlt

/-- **The paper base gates, the empty equality-check bucket, and the empty extension
buckets are blind to the swap** (W2 stage 2). The live rejection is `repaired_chip_rejects_denominator_swap`. -/
theorem attackTrace_all_but_pin
    (j : Fin (rows P)) :
    (∀ g ∈ baseTransitionGates P.optimized.basis,
        g.eval (rowEnvF P (attackTrace P i₁ i₂ d₁' d₂' Qm) j) = 0) ∧
    (∀ g ∈ equalityChecks P.optimized.basis,
        g.eval (rowEnvF P (attackTrace P i₁ i₂ d₁' d₂' Qm) j) = 0) ∧
    (∀ g ∈ (memorySourceTemplate P.optimized.basis).extTransition ++
        (memorySourceTemplate P.optimized.basis).extDeg1 ++
        (memorySourceTemplate P.optimized.basis).extDeg3,
        g.eval (rowEnvK P (attackTrace P i₁ i₂ d₁' d₂' Qm) j) = 0) := by
  have h := shiftedRow_attack P i₁ i₂ d₁' d₂' Qm j
  obtain ⟨hbase, heq, _hext, _hmix⟩ := row_parts P Qm hsat j
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rw [base_gates_shifted P.optimized.basis i₁ i₂ _ _ d₁' d₂' h g hg]
    exact hbase g hg
  · intro g hg
    rw [equality_checks_shifted P.optimized.basis i₁ i₂ _ _ d₁' d₂' h g hg]
    exact heq g hg
  · intro g hg
    simp [memorySourceTemplate, degreeOneEndpoints, degreeThreeEndpoints] at hg

/-- **The repaired chip REJECTS the denominator swap**.  For any trace
`P.memoryChip` accepts and any `d₁' ≠ d₁`, the attack trace — the very trace
`attackTrace_accepted` proved ACCEPTED under the compensating-pair hypotheses —
is rejected, with **no** hypothesis on `d₂'`, `ver`, the fold or the compensation: the
denominator pin at row `i₁` evaluates to `d₁' − d₁ ≠ 0` (`denominatorPin_shifted`), and it is a
committed gate of the source chip (`mixedTransitionGates`).  The memory twin of
`Batch269.moved_accumulator_rejected` / `Batch266.repaired_chip_rejects_shifted_accumulator`. -/
theorem repaired_chip_rejects_denominator_swap
    (hne : d₁' ≠ (rowEnvK P Qm i₁).trace 37) :
    ¬ RAP.SatisfiesWithPreprocessing P.memoryChip (attackTrace P i₁ i₂ d₁' d₂' Qm) := by
  intro hsat'
  have hpin := (row_parts P Qm hsat i₁).2.2.2 _
    (denominatorPinMixed_mem P.optimized.basis)
  have hpin' := (row_parts P (attackTrace P i₁ i₂ d₁' d₂' Qm) hsat' i₁).2.2.2 _
    (denominatorPinMixed_mem P.optimized.basis)
  have h := shiftedRow_attack P i₁ i₂ d₁' d₂' Qm i₁
  have hshift := denominatorPin_shifted P.optimized.basis i₁ i₂ _ _ d₁' d₂' h
  change (denominatorPinMixed (F := F)).eval (rowEnvK P (attackTrace P i₁ i₂ d₁' d₂' Qm) i₁)
    (rowEnvF P (attackTrace P i₁ i₂ d₁' d₂' Qm) i₁) =
    (denominatorPinMixed (F := F)).eval (rowEnvK P Qm i₁) (rowEnvF P Qm i₁) + _ at hshift
  rw [hpin', hpin, zero_add, (roleShift_at₁ i₁ i₂ _ _ d₁' d₂' hlt).1] at hshift
  exact hne (sub_eq_zero.mp hshift.symm)

omit hsat hlt in
/-- What the attack trace commits: the denominator at `i₁` **is** `d₁'`, at `i₂` **is** `d₂'`,
and every role outside `{37, 38, 42, 43, 44, 50}` — the record fields `19..26`, the `ver`
flag `39`, the terminal `40` — is unchanged at every row. -/
theorem attackTrace_values (hlt : (i₁ : ℕ) < (i₂ : ℕ)) :
    (rowEnvK P (attackTrace P i₁ i₂ d₁' d₂' Qm) i₁).trace 37 = d₁' ∧
    (rowEnvK P (attackTrace P i₁ i₂ d₁' d₂' Qm) i₂).trace 37 = d₂' ∧
    ∀ (j : Fin (rows P)) (r : ℕ), r ≠ 37 → r ≠ 38 → r ≠ 42 → r ≠ 43 → r ≠ 44 → r ≠ 50 →
      (rowEnvK P (attackTrace P i₁ i₂ d₁' d₂' Qm) j).trace r = (rowEnvK P Qm j).trace r := by
  refine ⟨?_, ?_, ?_⟩
  · have h := shiftedRow_attack P i₁ i₂ d₁' d₂' Qm i₁
    show (gatherEnv P.optimized.basis memoryCol0 _).trace 37 = _
    rw [gather_cur P.optimized.basis _ h 37, (roleShift_at₁ i₁ i₂ _ _ d₁' d₂' hlt).1]
    exact add_sub_cancel _ _
  · have h := shiftedRow_attack P i₁ i₂ d₁' d₂' Qm i₂
    show (gatherEnv P.optimized.basis memoryCol0 _).trace 37 = _
    rw [gather_cur P.optimized.basis _ h 37, (roleShift_at₂ i₁ i₂ _ _ d₁' d₂' hlt).1]
    exact add_sub_cancel _ _
  · intro j r h37 h38 h42 h43 h44 h50
    have h := shiftedRow_attack P i₁ i₂ d₁' d₂' Qm j
    show (gatherEnv P.optimized.basis memoryCol0 _).trace r = _
    rw [gather_cur P.optimized.basis _ h r, roleShift_off i₁ i₂ _ _ d₁' d₂' r ⟨h37, h38, h42, h43, h44, h50⟩,
      add_zero]

end Deployed


/-! ## E6. Non-vacuity of the compensating pair, and the F97 instantiation -/

section Nonvacuous

/-- In characteristic `∉ {2, 3}` every pair of nonzero denominators admits a compensating
replacement `d₁' ≠ d₁`. -/
theorem exists_compensating_pair {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0)
    (d₁ d₂ : L) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    ∃ d₁' d₂' : L, d₁' ≠ 0 ∧ d₂' ≠ 0 ∧ d₁' ≠ d₁ ∧ d₁'⁻¹ + d₂'⁻¹ = d₁⁻¹ + d₂⁻¹ := by
  by_cases hc : d₂ = -2 * d₁
  · -- `d₁' = 3 d₁`, `1/d₂' = 1/d₁ + 1/d₂ − 1/(3 d₁) = 1/(6 d₁)`
    have h6 : (6 : L) ≠ 0 := by
      have : (6 : L) = 2 * 3 := by norm_num
      rw [this]; exact mul_ne_zero h2 h3
    refine ⟨3 * d₁, 6 * d₁, mul_ne_zero h3 hd₁, mul_ne_zero h6 hd₁, ?_, ?_⟩
    · intro h
      have : (3 - 1) * d₁ = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact h2 (by linear_combination h')
      · exact hd₁ h'
    · subst hc
      field_simp
      ring
  · -- `d₁' = 2 d₁`, `1/d₂' = 1/d₁ + 1/d₂ − 1/(2 d₁) = 1/(2 d₁) + 1/d₂ ≠ 0`
    have hs : (2 * d₁)⁻¹ + d₂⁻¹ ≠ 0 := by
      intro h
      apply hc
      have h2d : (2 * d₁) ≠ 0 := mul_ne_zero h2 hd₁
      field_simp at h
      linear_combination h
    refine ⟨2 * d₁, ((2 * d₁)⁻¹ + d₂⁻¹)⁻¹, mul_ne_zero h2 hd₁, inv_ne_zero hs, ?_, ?_⟩
    · intro h
      have : (2 - 1) * d₁ = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · norm_num at h'
      · exact hd₁ h'
    · rw [inv_inv]
      have h2d : (2 * d₁) ≠ 0 := mul_ne_zero h2 hd₁
      field_simp
      ring

end Nonvacuous

section F97

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.BuildableChips

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance fintype97 : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance deq97 : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance charRing97 : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hmoreM : BuildableAxisWitness.LaterSeedZeros (F := F97) (K := K97cubic) multiRootExecution)

/-- The honest memory trace of the real F97 package `packageM` (`memRows = 14`). -/
abbrev honestM : Fin (packageM hmoreM).memoryChip.rap.w → F97[X] := canonicalMemoryTrace (packageM hmoreM)

theorem packageM_memRows : (packageM hmoreM).optimized.family.problem.cfg.memRows = 15 := rfl

abbrev rowM0 : Fin (rows (packageM hmoreM)) := ⟨1, by
  change 1 < (packageM hmoreM).optimized.family.problem.cfg.memRows
  rw [packageM_memRows hmoreM]; decide⟩
abbrev rowM1 : Fin (rows (packageM hmoreM)) := ⟨2, by
  change 2 < (packageM hmoreM).optimized.family.problem.cfg.memRows
  rw [packageM_memRows hmoreM]; decide⟩

/-- `ver` at a canonical row is `responseActive` of the row's state. -/
theorem packageM_ver (i : Fin (rows (packageM hmoreM))) :
    (rowEnvK (packageM hmoreM) (honestM hmoreM) i).trace 39 =
      responseActive (K := K97cubic) (execS.memoryPubAt i).ver := by
  have h := canonical_memorySourceEnv (packageM hmoreM) i
  show ((packageM hmoreM).memorySourceEnv (canonicalMemoryTrace (packageM hmoreM)) i).trace 39 = _
  rw [h]
  exact canonical_gather_sampled_index (packageM hmoreM).optimized.sampled (packageM hmoreM).optimized.memoryNodes
    (packageM hmoreM).optimized.memoryNodes_injective (packageM hmoreM).optimized.basis
    (packageM hmoreM).optimized.memoryChallenge (packageM hmoreM).optimized.memoryPublic (packageM hmoreM).optimized.orbit i 2
    (by decide)

/-- Rows `0` and `1` of the F97 fixture are `read_root` rows with `ver = 1`. -/
theorem packageM_two_verify_rows :
    (rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM0 hmoreM)).trace 39 = 1 ∧ (rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM1 hmoreM)).trace 39 = 1 := by
  constructor
  · rw [packageM_ver hmoreM]
    change responseActive (execS.memoryPubAt ⟨1, by norm_num [cfgS]⟩).ver = 1
    rw [memoryPubAtS_1]; rfl
  · rw [packageM_ver hmoreM]
    change responseActive (execS.memoryPubAt ⟨2, by norm_num [cfgS]⟩).ver = 1
    rw [memoryPubAtS_2]; rfl

theorem packageM_interPole_ne : (packageM hmoreM).optimized.sampled.interPole ≠ 0 := by
  change inputsM.memoryExtensionFold ≠ 0
  exact interPoleOfE_ne_zero multiRootExecution ioCoinsM.gamma inputsM_interCard

theorem packageM_fold_excluded (i : Fin (rows (packageM hmoreM))) :
    FoldCollisionExcluded (rowEnvK (packageM hmoreM) (honestM hmoreM) i) :=
  canonical_fold_excluded (packageM hmoreM) i (packageM_interPole_ne hmoreM)

/-- The honest denominators at rows `0`, `1` are nonzero (from the committed inverse column). -/
theorem packageM_honest_denoms_ne_zero :
    (rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM0 hmoreM)).trace 37 ≠ 0 ∧ (rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM1 hmoreM)).trace 37 ≠ 0 := by
  obtain ⟨hv0, hv1⟩ := packageM_two_verify_rows hmoreM
  have hsat := canonicalMemoryTrace_satisfies (packageM hmoreM) hmoreM
      MultiRootServedFixture.execS_cprimeCoherent
  constructor
  · exact denom_ne_zero_of_ver (packageM hmoreM) (honestM hmoreM) hsat (rowM0 hmoreM) hv0
  · exact denom_ne_zero_of_ver (packageM hmoreM) (honestM hmoreM) hsat (rowM1 hmoreM) hv1

/-- The same compensating pair still exists
(`exists_compensating_pair`; characteristic `97`) and the attack trace still commits `d₁'` at row
`0` with every record field of the honest trace — and the repaired chip **rejects** it
(`repaired_chip_rejects_denominator_swap`): `denominatorPinMixed` at row `0` reads `d₁' − d₁ ≠ 0`. -/
theorem packageM_denominator_attack_rejected :
    ∃ d₁' d₂' : K97cubic, d₁' ≠ 0 ∧ d₂' ≠ 0 ∧
      d₁' ≠ (rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM0 hmoreM)).trace 37 ∧
      d₁'⁻¹ + d₂'⁻¹ = ((rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM0 hmoreM)).trace 37)⁻¹ +
        ((rowEnvK (packageM hmoreM) (honestM hmoreM) (rowM1 hmoreM)).trace 37)⁻¹ ∧
      ¬ RAP.SatisfiesWithPreprocessing (packageM hmoreM).memoryChip
        (attackTrace (packageM hmoreM) (rowM0 hmoreM) (rowM1 hmoreM) d₁' d₂' (honestM hmoreM)) ∧
      (rowEnvK (packageM hmoreM) (attackTrace (packageM hmoreM) (rowM0 hmoreM) (rowM1 hmoreM) d₁' d₂' (honestM hmoreM)) (rowM0 hmoreM)).trace 37 = d₁' ∧
      (∀ (j : Fin (rows (packageM hmoreM))) (r : ℕ), 19 ≤ r → r ≤ 26 →
        (rowEnvK (packageM hmoreM) (attackTrace (packageM hmoreM) (rowM0 hmoreM) (rowM1 hmoreM) d₁' d₂' (honestM hmoreM)) j).trace r =
          (rowEnvK (packageM hmoreM) (honestM hmoreM) j).trace r) := by
  obtain ⟨hd0, hd1⟩ := packageM_honest_denoms_ne_zero hmoreM
  have h2 : (2 : K97cubic) ≠ 0 := by
    intro hk
    have hbase : (2 : F97) ≠ 0 := by decide
    apply hbase
    apply (algebraMap F97 K97cubic).injective
    simpa only [map_ofNat, map_zero] using hk
  have h3 : (3 : K97cubic) ≠ 0 := by
    intro hk
    have hbase : (3 : F97) ≠ 0 := by decide
    apply hbase
    apply (algebraMap F97 K97cubic).injective
    simpa only [map_ofNat, map_zero] using hk
  obtain ⟨d₁', d₂', hd₁', hd₂', hne, hsum⟩ := exists_compensating_pair h2 h3 _ _ hd0 hd1
  have hlt : ((rowM0 hmoreM) : ℕ) < ((rowM1 hmoreM) : ℕ) := Nat.lt_succ_self 1
  refine ⟨d₁', d₂', hd₁', hd₂', hne, hsum, ?_, ?_, ?_⟩
  · exact repaired_chip_rejects_denominator_swap (packageM hmoreM) (rowM0 hmoreM) (rowM1 hmoreM) d₁' d₂' (honestM hmoreM)
      (canonicalMemoryTrace_satisfies (packageM hmoreM) hmoreM
          MultiRootServedFixture.execS_cprimeCoherent) hlt hne
  · exact (attackTrace_values (packageM hmoreM) (rowM0 hmoreM) (rowM1 hmoreM) d₁' d₂' (honestM hmoreM) hlt).1
  · intro j r h19 h26
    exact (attackTrace_values (packageM hmoreM) (rowM0 hmoreM) (rowM1 hmoreM) d₁' d₂' (honestM hmoreM) hlt).2.2 j r
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The honest trace itself is still accepted (non-vacuity of the rejection). -/
theorem packageM_honest_accepted :
    RAP.SatisfiesWithPreprocessing (packageM hmoreM).memoryChip (honestM hmoreM) :=
  canonicalMemoryTrace_satisfies (packageM hmoreM) hmoreM
      MultiRootServedFixture.execS_cprimeCoherent

end F97

/-! ## F. Read sets, own instrument -/

section ReadSets

/-- All `(kind, index)` leaves of an `Expr`, as a list (own instrument, independent of
`exprVariableSupport`). -/
def leaves : Expr → List (VarKind × ℕ)
  | .Const _ => []
  | .Var k i => [(k, i)]
  | .Add x y | .Sub x y | .Mul x y => leaves x ++ leaves y
  | .Neg x | .Pow x _ => leaves x

def readsCur (r : ℕ) (e : Expr) : Bool := (leaves e).any (fun v => v.1 == .traceCur && v.2 == r)
def readsPub (r : ℕ) (e : Expr) : Bool := (leaves e).any (fun v => v.1 == .publicVal && v.2 == r)

/-- Role `37` (the response denominator) is read by exactly one of the fifty **sources**, the safe
normalisation — reproducing `Batch270.role37_read_only_by_safe_normalisation` on a second
instrument.  Unchanged by A-mem-2, whose pin is a mixed gate, not a source; the pin's read of
role `37` is `Batch270.denominatorPin_reads_role37`. -/
theorem role37_readers :
    (transitionSources (K := ZMod 31)).filter (readsCur 37) =
      [.Sub (extVar .traceCur 50)
        (.Add (.Mul (extVar .traceCur 39) (extVar .traceCur 37))
          (.Sub (.Const 1) (extVar .traceCur 39)))] := by
  set_option maxRecDepth 100000 in decide

/-- **Role `39` (`ver`) is read by exactly three sources — its booleanity, the contribution
`42 = ver · inv` and the safe normalisation — and by nothing that mentions the row's state
(base columns `0..3`, selector mirrors `51..54`, or any memory-table role `< 37`).**  `ver` is a
free boolean column; the paper's `ver` is likewise constrained by
booleanity only. -/
theorem role39_readers :
    (transitionSources (K := ZMod 31)).filter (readsCur 39) =
      [.Mul (extVar .traceCur 39) (.Sub (extVar .traceCur 39) (.Const 1)),
       .Sub (extVar .traceCur 42) (.Mul (extVar .traceCur 39) (extVar .traceCur 38)),
       .Sub (extVar .traceCur 50)
        (.Add (.Mul (extVar .traceCur 39) (extVar .traceCur 37))
          (.Sub (.Const 1) (extVar .traceCur 39)))] := by
  set_option maxRecDepth 100000 in decide

theorem role39_readers_touch_no_state :
    ∀ e ∈ (transitionSources (K := ZMod 31)).filter (readsCur 39),
      ∀ v ∈ leaves e, v.1 = .traceCur ∧ 37 ≤ v.2 := by
  set_option maxRecDepth 100000 in decide

/-- Memory `𝕂` public `2` (`requests`, base publics `12..14`) is read by exactly one source: the
terminal binding `40 − public 2`. -/
theorem memory_public2_readers :
    (transitionSources (K := ZMod 31)).filter (readsPub 2) =
      [.Sub (extVar .traceCur 40) (extVar .publicVal 2)] := by
  set_option maxRecDepth 100000 in decide

/-- Typed leaves of a compute gate. -/
def tReadsExtPub (i : Fin 3) : OptimizedComputeCorrectedFinal.CorrectedFinalTypedExpr → Bool
  | .extensionPublic j => decide (j = i)
  | .add x y | .sub x y | .mul x y => tReadsExtPub i x || tReadsExtPub i y
  | .neg x | .pow x _ => tReadsExtPub i x
  | _ => false

open OptimizedComputeCorrectedFinal in
/-- Compute `𝕂` public `2` (`requests`, base publics `6..8`) is read by exactly one typed gate of
the committed lists: the terminal anchor `isLast · (acc_after − requests)`. -/
theorem compute_extPublic2_readers :
    (correctedLoweredExt ++ correctedEndpoint2 ++ correctedEndpoint4 ++
        [correctedAccAfterStep, accAfterChain]).filter (tReadsExtPub 2) =
      [(correctedLowerFinal finalAccTerminal).getD (.const 0)] := by
  set_option maxRecDepth 300000 in decide

end ReadSets

end

end Nock.RedTeam.Batch271

#print axioms Nock.RedTeam.Batch271.hchar_of_charP
#print axioms Nock.RedTeam.Batch271.hchar_K73cubic
#print axioms Nock.RedTeam.Batch271.hchar_goldilocks
#print axioms Nock.RedTeam.Batch271.hchar_fails_char7
#print axioms Nock.RedTeam.Batch271.char2_selector_not_oneHot
#print axioms Nock.RedTeam.Batch271.countdown_iff_countup
#print axioms Nock.RedTeam.Batch271.paper_prog_step_two
#print axioms Nock.RedTeam.Batch271.double_pole_frees_step
#print axioms Nock.RedTeam.Batch271.canonical_fold_excluded
#print axioms Nock.RedTeam.Batch271.package73_hostile_memory_sum
#print axioms Nock.RedTeam.Batch271.package73_logUp_sums_agree_of_pole
#print axioms Nock.RedTeam.Batch271.package73_terminal_rejected
#print axioms Nock.RedTeam.Batch271.package73_accumulator_rejected
#print axioms Nock.RedTeam.Batch271.package73_shift_rejected
#print axioms Nock.RedTeam.Batch271.attackTrace_all_but_pin
#print axioms Nock.RedTeam.Batch271.denominatorPin_shifted
#print axioms Nock.RedTeam.Batch271.repaired_chip_rejects_denominator_swap
#print axioms Nock.RedTeam.Batch271.attackTrace_values
#print axioms Nock.RedTeam.Batch271.exists_compensating_pair
#print axioms Nock.RedTeam.Batch271.packageM_denominator_attack_rejected
#print axioms Nock.RedTeam.Batch271.packageM_honest_accepted
#print axioms Nock.RedTeam.Batch271.role37_readers
#print axioms Nock.RedTeam.Batch271.role39_readers
#print axioms Nock.RedTeam.Batch271.role39_readers_touch_no_state
#print axioms Nock.RedTeam.Batch271.memory_public2_readers
#print axioms Nock.RedTeam.Batch271.compute_extPublic2_readers
