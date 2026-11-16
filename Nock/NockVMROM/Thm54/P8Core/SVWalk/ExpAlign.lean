/-
  Nock/NockVMROM/Thm54/P8Core/SVWalk/ExpAlign.lean

  At any `SVIO.IORows` (in particular `SVIO.rows309` at the un-hosted
  compute chip with any nodes / basis / orbit / public map / tuple) carrying the two round-0 carrier
  gates `isFirst·S = 0`, `(1 − isLast)(S(i+1) − S(i) − arity(i)) = 0` (`ExpRows`):

  * `expCol_eq_prefixExp` : `S(m) = (prefixExp m : 𝔽)` on every row;
  * `natLift_expCol` : `natLift S(m) = prefixExp m` under `3·n < ringChar F` (no wraparound);
  * `computeArity_eq`, `computePrefix_eq` : the exponent locator's arity / prefix sums
    (`DecodedLambdaEvent.computeArity` on the source environments, what `certAxisOfEnvs` reads) are
    `rowArity` / `prefixExp`;
  * `ExpRows.of309` / `expRows309` : the carrier bundle at `computeChipAt309` from acceptance.

  Package twin: `FamilyIOChain.expCol_eq_prefixExp_at` (the 303 family chip, package-indexed).
-/
import Nock.NockVMROM.Thm54.P8Core.SVIOCompute
import Nock.NockVMROM.Thm54.P8Core.FamilyIOChainCompute

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVWalk

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open OptimizedStrictPackage
open OptimizedComputeCorrectedFinal
open OptimizedComputeSemanticRealization
open OptimizedComputeSubstitution
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open StrictExtension
open DeployedChipFamily
open Unhosted309
open SVIO
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- **The carrier bundle** over an `IORows`: the two carrier gates on every row, the gathered
`expCol` is base column `302`, and the next-row reading of column `302` is the successor's. -/
structure ExpRows (R : IORows F K) : Prop where
  gates : ∀ i, ∀ g ∈ computeExpGates (F := F), g.eval (R.envF i) = 0
  expCol_eq : ∀ i, (R.env i).expCol = (R.envF i).trace computeExpCol
  next : ∀ (i : Fin R.n) (hi : (i : ℕ) + 1 < R.n),
    (R.envF i).traceNext computeExpCol = (R.envF ⟨(i : ℕ) + 1, hi⟩).trace computeExpCol

namespace ExpRows

variable {R : IORows F K} (E : ExpRows R)

theorem opCol_eq_stateIndex_iff (st s : ComputeTable.State) :
    opCol st = (OptimizedComputeCodec.stateIndex s : ℕ) ↔ st = s := by
  cases st <;> cases s <;> decide

variable [DecidableEq K]

/-- The base-field selectors are the one-hot vector of the row's state. -/
theorem base_selector (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin R.n) :
    ∃ s, (∀ st, (R.env i).toSourceEnv.trace (opCol st) = ComputeTable.opSel s st) ∧
      ∀ k : ℕ, k < 11 →
        (R.envF i).trace k = if k = (OptimizedComputeCodec.stateIndex s : ℕ) then 1 else 0 := by
  obtain ⟨s, hsel⟩ := R.source_selector hchar i
  refine ⟨s, hsel, fun k hk => ?_⟩
  have hF : ∀ st, (R.envF i).trace (opCol st) = ComputeTable.opSel s st := by
    intro st
    have h := hsel st
    rw [source_trace_base _ (opCol st) (by cases st <;> decide)] at h
    rw [(R.obl i).base_eq (opCol st) (by cases st <;> decide)] at h
    apply (algebraMap F K).injective
    rw [h]
    simp only [ComputeTable.opSel]
    split_ifs <;> simp
  obtain ⟨st, rfl⟩ : ∃ st : ComputeTable.State, opCol st = k := by
    interval_cases k
    exacts [⟨.s0, rfl⟩, ⟨.s1, rfl⟩, ⟨.s2, rfl⟩, ⟨.s3, rfl⟩, ⟨.s4, rfl⟩, ⟨.s5, rfl⟩,
      ⟨.s6, rfl⟩, ⟨.s7, rfl⟩, ⟨.s8, rfl⟩, ⟨.s9, rfl⟩, ⟨.cons, rfl⟩]
  rw [hF st]
  by_cases h : st = s
  · subst h; simp [ComputeTable.opSel, (opCol_eq_stateIndex_iff st st).2 rfl]
  · have h' : opCol st ≠ (OptimizedComputeCodec.stateIndex s : ℕ) :=
      fun he => h ((opCol_eq_stateIndex_iff st s).1 he)
    simp [ComputeTable.opSel, h, h']

include E in
/-- `S(0) = 0`. -/
theorem expCol_first : (R.env R.firstRow).expCol = 0 := by
  have h := E.gates R.firstRow expInitGate (by simp [computeExpGates])
  have hm := R.first R.firstRow
  have hb : (R.env R.firstRow).baseTrace 11 = (R.envF R.firstRow).trace 11 :=
    (R.obl R.firstRow).base_eq 11 (by norm_num)
  rw [hb] at hm
  simp only [expInitGate, CoeffExpr.eval] at h
  have h11 : (R.envF R.firstRow).trace 11 = 1 := by simpa using hm
  rw [E.expCol_eq]
  simpa [h11] using h

include E in
/-- `S(i + 1) = S(i) + arity(i)` off the last row. -/
theorem expCol_step (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin R.n) (hi : (i : ℕ) + 1 < R.n) :
    (R.env ⟨(i : ℕ) + 1, hi⟩).expCol = (R.env i).expCol + ((rowArity (R.env i) : ℕ) : F) := by
  have h := E.gates i expStepGate (by simp [computeExpGates])
  have hm := R.last i
  have hb : (R.env i).baseTrace 12 = (R.envF i).trace 12 := (R.obl i).base_eq 12 (by norm_num)
  rw [hb] at hm
  have h12 : (R.envF i).trace 12 = 0 := by
    rw [hm, if_neg (by omega)]
  obtain ⟨s, hsel, hselF⟩ := base_selector hchar i
  have harity : (arityForm (F := F)).eval (R.envF i) = ((arity s : ℕ) : F) := by
    simp only [arityForm, List.range, List.range.loop, List.foldr, CoeffExpr.eval]
    rw [hselF 0 (by omega), hselF 1 (by omega), hselF 2 (by omega), hselF 3 (by omega),
      hselF 4 (by omega), hselF 5 (by omega), hselF 6 (by omega), hselF 7 (by omega),
      hselF 8 (by omega), hselF 9 (by omega), hselF 10 (by omega)]
    cases s <;> simp [OptimizedComputeCodec.stateIndex, arityCoeff, arity]
  have hra := R.rowArity_eq_arity i s hsel
  simp only [expStepGate, CoeffExpr.eval] at h
  rw [h12, sub_zero, one_mul, harity, E.next i hi] at h
  rw [hra, E.expCol_eq, E.expCol_eq]
  linear_combination h

include E in
/-- **`S(m) = (prefixExp m : 𝔽)`** on every row. -/
theorem expCol_eq_prefixExp (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) :
    ∀ (m : ℕ) (hm : m < R.n), (R.env ⟨m, hm⟩).expCol = ((R.prefixExp m : ℕ) : F) := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [IORows.prefixExp, Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
      exact E.expCol_first
  | succ m ih =>
      intro hm
      have hm' : m < R.n := by omega
      rw [E.expCol_step hchar ⟨m, hm'⟩ hm, ih hm', R.prefixExp_succ m hm']
      push_cast
      ring

theorem prefixExp_le (m : ℕ) : R.prefixExp m ≤ 3 * m := by
  unfold IORows.prefixExp
  calc (∑ k ∈ Finset.range m, if h : k < R.n then rowArity (R.env ⟨k, h⟩) else 0)
      ≤ ∑ _k ∈ Finset.range m, 3 :=
        Finset.sum_le_sum fun k _ => by split_ifs <;> [exact rowArity_le _; omega]
    _ = 3 * m := by simp [mul_comm]

include E in
/-- **The record exponent slot, lifted**: `natLift (S(m) + j + 1) = prefixExp m + j + 1`, under the
row budget `3·n < ringChar K` (`VerifierData.Checks.hrowsC`). -/
theorem natLift_slot9 (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hrows : 3 * R.n < ringChar K) (m : ℕ) (hm : m < R.n) (j : Fin 3) :
    RecordCarrier.natLift (algebraMap F K (R.env ⟨m, hm⟩).expCol + (((j : ℕ) + 1 : ℕ) : K)) =
      R.prefixExp m + (j : ℕ) + 1 := by
  rw [E.expCol_eq_prefixExp hchar m hm, map_natCast, ← Nat.cast_add]
  have h1 : R.prefixExp m ≤ 3 * m := prefixExp_le m
  have h2 := j.isLt
  rw [RecordCarrier.natLift_natCast (by omega)]
  omega

/-- The locator's arity on the source environment is `rowArity`. -/
theorem computeArity_eq (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (i : Fin R.n) :
    DecodedLambdaEvent.computeArity (R.env i).toSourceEnv = rowArity (R.env i) := by
  obtain ⟨s, hsel⟩ := R.source_selector hchar i
  rw [R.rowArity_eq_arity i s hsel]
  have s0 := hsel .s0; have s2 := hsel .s2; have s5 := hsel .s5; have s6 := hsel .s6
  have s7 := hsel .s7; have s8 := hsel .s8; have s9 := hsel .s9
  simp only [Nock.Reified.opCol, ComputeTable.opSel] at s0 s2 s5 s6 s7 s8 s9
  unfold DecodedLambdaEvent.computeArity
  cases s <;> simp [s0, s2, s5, s6, s7, s8, s9, arity]

/-- The locator's prefix sums are `prefixExp`. -/
theorem computePrefix_eq (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1) (a : Fin R.n) :
    DecodedLambdaEvent.computePrefix (fun i => (R.env i).toSourceEnv) a = R.prefixExp a := by
  unfold DecodedLambdaEvent.computePrefix IORows.prefixExp
  have hg : ∀ i : Fin R.n, DecodedLambdaEvent.computeArity (R.env i).toSourceEnv =
      (fun k => if h : k < R.n then rowArity (R.env ⟨k, h⟩) else 0) (i : ℕ) := by
    intro i
    rw [computeArity_eq hchar i]
    simp [i.isLt]
  rw [Finset.sum_filter]
  simp_rw [hg]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < (a : ℕ) then
    (if h : k < R.n then rowArity (R.env ⟨k, h⟩) else 0) else 0) R.n]
  rw [← Finset.sum_filter]
  have hfil : (Finset.range R.n).filter (fun k => k < (a : ℕ)) = Finset.range a := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; have := a.isLt; omega
  rw [hfil]

end ExpRows

/-! ## The un-hosted 309 compute chip -/

section At309

variable [Fintype K] [Fintype F] [DecidableEq K]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (hinj : Function.Injective nodes)
  (b : Basis (Fin 3) F K) (pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h)
  (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
  (c : OptimizedProductionChallengeTuple K F)

/-- **The carrier bundle at `computeChipAt309`**, from acceptance (any nodes / basis / orbit /
public map / tuple). -/
theorem expRows309 (Qc : Fin (computeChipAt309 hn nodes b pubVal orbit c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (computeChipAt309 hn nodes b pubVal orbit c) Qc) :
    ExpRows (rows309 hn nodes hinj b pubVal orbit hadj c Qc hsat) where
  gates := fun i => by
    have hl := (satisfies309_iff_sourceLanguage hn nodes b (computeChalValOfTuple b c) pubVal
      orbit Qc).1 hsat
    exact (hl.2 _ (by simp [rowNodeSet] <;> exact ⟨i, rfl⟩)).expGates
  expCol_eq := fun _ => rfl
  next := fun i hi => by
    have hlt : computeExpCol < (computeChipAt309 hn nodes b pubVal orbit c).rap.w := by
      rw [computeChipAt309_w]; change 302 < 309; norm_num
    show (envOfTrace Qc orbit.ω (nodes i) (computeChalValOfTuple b c) pubVal).traceNext
        computeExpCol =
      (envOfTrace Qc orbit.ω (nodes ⟨(i : ℕ) + 1, hi⟩) (computeChalValOfTuple b c) pubVal).trace
        computeExpCol
    simp only [envOfTrace, dif_pos hlt]
    rw [hadj i hi]

end At309

end

end Nock.NockVMROM.Thm54.SVWalk
