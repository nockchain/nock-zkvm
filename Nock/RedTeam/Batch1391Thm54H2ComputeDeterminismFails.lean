/-
  Nock/RedTeam/Batch1391Thm54H2ComputeDeterminismFails.lean

  **It fails at roles `6`, `7` of every `s2` (`OP2`) row.**  `DeployedStaging.computeRoleRound 6 = 2` and
  `… 7 = 2`: the columns are committed after the walk coins `αC`, `γ` (they host `walkCount` /
  `walkAcc` on `s1` rows).  So the shift `K6 ↦ K6 + γ·d`, `K7 ↦ K7 − d` is invisible
  to every gate.

  **`s2_shift_accepted`**: for EVERY tuple `c`, EVERY trace `Qc` accepted at `computeChipAt c`,
  every non-first, non-last row `i` of state `s2` and every `d : 𝕂`, the trace `pertQc … i d`
  (`Qc` plus `d`-scaled Lagrange bumps on the six physical columns `31..36` at row `i` only) is
  ALSO accepted at `computeChipAt c`.  `pertQc_off` / `pert_columns_round_two`: every column other
  than `31..36` is the same POLYNOMIAL, and `31..36` are round-`2` columns
  (`DeployedStaging.computeColRound`).  `pert_role6` / `pert_role7`: the row's role `6` moves by
  `γ·d`, role `7` by `−d` (`γ = gamma c.1`).  `determinism_fails`: two accepted traces at the
  same `c`, equal on every round-`0`/`1` column, with different role `6` at row `i` — so roles
  `6`, `7` of `s2` rows are NOT a function of the round-`≤1` columns on accepted traces, at any
  coin.  (Not an attack on the claim: the moved cells feed only the walk, and only through the
  unchanged RLC.  What it breaks is the H2.1 locality argument for summands 5 and 8 as defined,
  whose bad sets read the label VECTORS — the perturbed row's label vector differs from its parent's
  committed payload while the two RLCs at the sampled `γ` agree.)
-/
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.RedTeam.Batch1390Thm54H2CellReadInstrument
import Mathlib.LinearAlgebra.Lagrange
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1391

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.RedTeam.Batch1390

/-! ## A. Base-field gates read no column of `31..36` -/

section BaseReads

variable {F : Type*} [Field F]

/-- The physical columns of roles `6`, `7` (`13 + 3r + k`). -/
def movedCols : List ℕ := [31, 32, 33, 34, 35, 36]

theorem coeff_eval_congr (envF envF' : Env F)
    (ht : ∀ col, col ∉ movedCols → envF'.trace col = envF.trace col)
    (hn : ∀ col, col ∉ movedCols → envF'.traceNext col = envF.traceNext col)
    (hc : envF'.chal = envF.chal) (hp : envF'.pub = envF.pub) :
    ∀ g : CoeffExpr F, (∀ col ∈ DeployedStaging.coeffTraceCols g, col ∉ movedCols) →
      g.eval envF' = g.eval envF
  | .const _, _ => rfl
  | .var .traceCur i, h => by
      simp only [CoeffExpr.eval]; exact ht i (h i (by simp [DeployedStaging.coeffTraceCols]))
  | .var .traceNext i, h => by
      simp only [CoeffExpr.eval]; exact hn i (h i (by simp [DeployedStaging.coeffTraceCols]))
  | .var .challenge i, _ => by simp only [CoeffExpr.eval, hc]
  | .var .publicVal i, _ => by simp only [CoeffExpr.eval, hp]
  | .add a b, h => by
      simp only [CoeffExpr.eval]
      rw [coeff_eval_congr envF envF' ht hn hc hp a
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc'])),
        coeff_eval_congr envF envF' ht hn hc hp b
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc']))]
  | .sub a b, h => by
      simp only [CoeffExpr.eval]
      rw [coeff_eval_congr envF envF' ht hn hc hp a
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc'])),
        coeff_eval_congr envF envF' ht hn hc hp b
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc']))]
  | .mul a b, h => by
      simp only [CoeffExpr.eval]
      rw [coeff_eval_congr envF envF' ht hn hc hp a
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc'])),
        coeff_eval_congr envF envF' ht hn hc hp b
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc']))]
  | .neg a, h => by
      simp only [CoeffExpr.eval]
      rw [coeff_eval_congr envF envF' ht hn hc hp a
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc']))]
  | .pow a _, h => by
      simp only [CoeffExpr.eval]
      rw [coeff_eval_congr envF envF' ht hn hc hp a
          (fun c hc' => h c (by simp [DeployedStaging.coeffTraceCols, hc']))]

theorem le_maxRound (rnd : ℕ → ℕ) : ∀ (l : List ℕ) (x : ℕ), x ∈ l →
    rnd x ≤ DeployedStaging.maxRound rnd l
  | [], _, h => absurd h (by simp)
  | y :: ys, x, h => by
      simp only [DeployedStaging.maxRound, List.foldr_cons] at *
      rcases List.mem_cons.mp h with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (le_maxRound rnd ys x hx) (le_max_right _ _)

theorem maxRound_le (rnd : ℕ → ℕ) (b : ℕ) (hb : ∀ x, rnd x ≤ b) :
    ∀ l : List ℕ, DeployedStaging.maxRound rnd l ≤ b
  | [] => Nat.zero_le _
  | y :: ys => by
      simp only [DeployedStaging.maxRound, List.foldr_cons]
      exact max_le (hb y) (maxRound_le rnd b hb ys)

theorem rawChalRound_le_one (j : ℕ) : DeployedStaging.computeRawChalRound j ≤ 1 := by
  unfold DeployedStaging.computeRawChalRound DeployedStaging.computeSlotRound
  split_ifs <;> omega

theorem movedCols_round (col : ℕ) (h : col ∈ movedCols) : DeployedStaging.computeColRound col = 2 := by
  simp only [movedCols, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A class-`0` compute gate reads no round-`2` column, hence none of `31..36`. -/
theorem avoid_of_class0 (g : CoeffExpr F) (h0 : DeployedStaging.computeCoeffClass g = 0) :
    ∀ col ∈ DeployedStaging.coeffTraceCols g, col ∉ movedCols := by
  intro col hcol hm
  unfold DeployedStaging.computeCoeffClass DeployedStaging.failClass at h0
  have hnot : DeployedStaging.gateReadsLaterColumn DeployedStaging.computeColRound
      DeployedStaging.computeRawChalRound (DeployedStaging.coeffTraceCols g)
        (DeployedStaging.coeffChals g) = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    rw [if_pos hc] at h0
    split_ifs at h0
  unfold DeployedStaging.gateReadsLaterColumn at hnot
  simp only [decide_eq_false_iff_not, not_lt] at hnot
  have h1 := le_maxRound DeployedStaging.computeColRound _ col hcol
  have h2 := maxRound_le DeployedStaging.computeRawChalRound 1 rawChalRound_le_one
    (DeployedStaging.coeffChals g)
  rw [movedCols_round col hm] at h1
  omega

theorem base_avoid (n : ℕ) :
    ∀ g ∈ OptimizedComputeFinal.finalBaseTransitionGates (F := F) n,
      ∀ col ∈ DeployedStaging.coeffTraceCols g, col ∉ movedCols := by
  intro g hg
  have hcl := DeployedStaging.compute_base_classes (F := F) n
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  apply avoid_of_class0
  have := congrArg (fun l => l[k]?) hcl
  simp only [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some] at this
  rw [List.getElem?_replicate] at this
  have hk15 : k < 15 := by
    simpa [OptimizedComputeFinal.finalBaseTransitionGates_length] using hk
  simpa [hk15] using this

theorem equality_avoid :
    ∀ g ∈ OptimizedComputeFinal.finalEndpointEqualityChecks (F := F),
      ∀ col ∈ DeployedStaging.coeffTraceCols g, col ∉ movedCols := by
  intro g hg
  have hcl := DeployedStaging.compute_equality_classes (F := F)
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  apply avoid_of_class0
  have := congrArg (fun l => l[k]?) hcl
  simp only [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some] at this
  rw [List.getElem?_replicate] at this
  have hk22 : k < 22 := by
    simpa [OptimizedComputeFinal.finalEndpointEqualityChecks_length] using hk
  simpa [hk22] using this

set_option maxRecDepth 100000 in
theorem cert_avoid :
    ∀ g ∈ OptimizedComputeRangeCertificate.formRCertificateGates (F := F),
      ∀ col ∈ DeployedStaging.coeffTraceCols g, col ∉ movedCols := by
  intro g hg
  have hsplit : OptimizedComputeRangeCertificate.formRCertificateGates (F := F) =
      (OptimizedComputeRangeCertificate.booleanGates (F := F) ++
        OptimizedComputeRangeCertificate.powerPins ++ OptimizedComputeRangeCertificate.formRPins ++
        OptimizedComputeRangeCertificate.helperPins ++
        [OptimizedComputeRangeCertificate.comparisonGate,
          OptimizedComputeRangeCertificate.rangeGate]) ++
        [OptimizedComputeRangeCertificate.axisEquation] := by
    simp [OptimizedComputeRangeCertificate.formRCertificateGates,
      OptimizedComputeRangeCertificate.formRNamed]
  rw [hsplit, List.mem_append] at hg
  rcases hg with hg | hg
  · intro col hcol hm
    have hloc := (DeployedStaging.certLocal_first96 (F := F) g hg).2 col hcol
    simp only [movedCols, List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  · rw [List.mem_singleton] at hg
    subst hg
    intro col hcol hm
    have hr := congrArg Prod.fst (DeployedStaging.axisEquation_reads (F := F))
    simp only at hr
    rw [hr] at hcol
    simp only [DeployedStaging.axisEquationReads] at hcol
    simp only [movedCols, List.mem_cons, List.not_mem_nil, or_false] at hm
    have : ∀ c ∈ ([0, 136, 272] ++ (List.range 63).foldl (fun acc j => acc ++ [202 + j]) [] ++
        [9, 145, 272] ++ (List.range 63).foldl (fun acc j => acc ++ [202 + j]) [] : List ℕ),
        c ∉ movedCols := by decide
    exact this col hcol (by simp only [movedCols]; rcases hm with h | h | h | h | h | h <;> simp [h])

theorem exp_avoid :
    ∀ g ∈ computeExpGates (F := F),
      ∀ col ∈ DeployedStaging.coeffTraceCols g, col ∉ movedCols := by
  intro g hg col hcol hm
  simp only [computeExpGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  simp only [movedCols, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hg with rfl | rfl
  · simp only [expInitGate, DeployedStaging.coeffTraceCols, computeExpCol, List.mem_cons,
      List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hcol
    omega
  · simp only [expStepGate, arityForm, DeployedStaging.coeffTraceCols, computeExpCol,
      List.range, List.range.loop, List.foldr, List.mem_cons,
      List.not_mem_nil, or_false, List.cons_append, List.nil_append, List.append_nil] at hcol
    omega

theorem baseLists_avoid (n : ℕ) :
    ∀ g ∈ baseLists (F := F) n, ∀ col ∈ DeployedStaging.coeffTraceCols g, col ∉ movedCols := by
  intro g hg
  simp only [baseLists, List.mem_append] at hg
  rcases hg with ((hb | he) | hc) | hx
  · exact base_avoid n g hb
  · exact equality_avoid g he
  · exact cert_avoid g hc
  · exact exp_avoid g hx

end BaseReads


/-! ## B. The row-local perturbation of an accepted trace -/

noncomputable section Pert

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

/-- Every point a row environment evaluates a column at: the row nodes and their successors. -/
def evalSupport : Finset F :=
  rowNodeSet P.optimized.computeNodes ∪
    (rowNodeSet P.optimized.computeNodes).image (fun x => P.optimized.orbit.ω * x)

/-- The `𝕂`-shift per role: `+γ·d` on role `6`, `−d` on role `7` (`γ = gamma c.1`). -/
def roleShiftK (d : K) (r : ℕ) : K :=
  if r = 6 then gamma c.1 * d else if r = 7 then -d else 0

/-- Its physical-column image (`13 + 3r + k ↦ coord k`). -/
def colShift (d : K) (col : ℕ) : F :=
  if 13 ≤ col ∧ col < 202 then
    coord P.optimized.basis (roleShiftK c d ((col - 13) / 3))
      ⟨(col - 13) % 3, Nat.mod_lt _ (by norm_num)⟩
  else 0

/-- The Lagrange bump at row node `i` over the evaluation support. -/
def bump (i : Fin P.optimized.family.problem.cfg.compRows) : F[X] :=
  Lagrange.basis (evalSupport P) id (P.optimized.computeNodes i)

/-- **The perturbed trace.** -/
def pertQc (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) (d : K) :
    Fin (P.computeChipAt c).rap.w → F[X] :=
  fun col => Qc col + Polynomial.C (colShift P c d col) * bump P i

theorem node_mem_support (j : Fin P.optimized.family.problem.cfg.compRows) :
    P.optimized.computeNodes j ∈ evalSupport P := by
  simp [evalSupport, rowNodeSet]

theorem succ_mem_support (j : Fin P.optimized.family.problem.cfg.compRows) :
    P.optimized.orbit.ω * P.optimized.computeNodes j ∈ evalSupport P := by
  simp only [evalSupport, Finset.mem_union, Finset.mem_image]
  exact Or.inr ⟨_, by simp [rowNodeSet], rfl⟩

theorem bump_eval (i : Fin P.optimized.family.problem.cfg.compRows) {y : F}
    (hy : y ∈ evalSupport P) :
    (bump P i).eval y = if y = P.optimized.computeNodes i then 1 else 0 := by
  unfold bump
  split_ifs with h
  · subst h
    exact Lagrange.eval_basis_self (v := id) (Set.injOn_id _) (node_mem_support P i)
  · exact Lagrange.eval_basis_of_ne (v := id) (Ne.symm h) hy

theorem colShift_small (d : K) (col : ℕ) (h : col < 13) : colShift P c d col = 0 := by
  simp [colShift, show ¬ (13 ≤ col) by omega]

theorem colShift_large (d : K) (col : ℕ) (h : 202 ≤ col) : colShift P c d col = 0 := by
  simp [colShift, show ¬ (col < 202) by omega]

theorem colShift_off (d : K) (col : ℕ) (h : col ∉ movedCols) : colShift P c d col = 0 := by
  unfold colShift
  split_ifs with hc
  · have hr : (col - 13) / 3 ≠ 6 ∧ (col - 13) / 3 ≠ 7 := by
      simp only [movedCols, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      omega
    simp [roleShiftK, hr.1, hr.2, coord]
  · rfl

theorem colShift_role (d : K) (r : ℕ) (hr : r < 63) (k : Fin 3) :
    colShift P c d (13 + 3 * r + k) = coord P.optimized.basis (roleShiftK c d r) k := by
  unfold colShift
  rw [if_pos (by omega)]
  have h1 : (13 + 3 * r + (k : ℕ) - 13) / 3 = r := by omega
  have h2 : (13 + 3 * r + (k : ℕ) - 13) % 3 = k := by omega
  simp only [h1]
  congr 1
  exact Fin.ext h2

/-- The evaluation of the perturbed trace at a support point. -/
theorem pertQc_eval (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) (d : K)
    (col : Fin (P.computeChipAt c).rap.w) {y : F} (hy : y ∈ evalSupport P) :
    (pertQc P c Qc i d col).eval y =
      (Qc col).eval y + if y = P.optimized.computeNodes i then colShift P c d col else 0 := by
  simp only [pertQc, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    bump_eval P i hy]
  split_ifs <;> simp

theorem chipAt_w : (P.computeChipAt c).rap.w = 303 := by
  simp only [OptimizedFullStrictNockVMROMPackage.computeChipAt,
    DeployedChipFamily.computeChipAt, ProductionNamedComputeRAP]
  exact (corrected_rap_fingerprint P.optimized.basis
    (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)
    P.optimized.orbit (rowNodeSet P.optimized.computeNodes)).1

/-- The base environment of the perturbed trace at row node `j`. -/
theorem pert_env_trace (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.compRows) (d : K) (col : ℕ) :
    (envOfTrace (pertQc P c Qc i d) P.optimized.orbit.ω (P.optimized.computeNodes j)
        (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).trace col =
      (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes j)
        (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).trace col +
      if j = i then colShift P c d col else 0 := by
  simp only [envOfTrace]
  split_ifs with hw hji hji
  · subst hji; rw [pertQc_eval P c Qc j d _ (node_mem_support P j)]; simp
  · rw [pertQc_eval P c Qc i d _ (node_mem_support P j)]
    have : P.optimized.computeNodes j ≠ P.optimized.computeNodes i :=
      fun h => hji (P.optimized.computeNodes_injective h)
    simp [this]
  · subst hji; rw [colShift_large P c d col (by rw [chipAt_w P c] at hw; omega)]; simp
  · simp

theorem pert_env_traceNext (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.compRows) (d : K) (col : ℕ) :
    (envOfTrace (pertQc P c Qc i d) P.optimized.orbit.ω (P.optimized.computeNodes j)
        (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).traceNext col =
      (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes j)
        (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).traceNext col +
      if P.optimized.orbit.ω * P.optimized.computeNodes j = P.optimized.computeNodes i then
        colShift P c d col else 0 := by
  simp only [envOfTrace]
  split_ifs with hw hji hji
  · rw [pertQc_eval P c Qc i d _ (succ_mem_support P j), if_pos hji]
  · rw [pertQc_eval P c Qc i d _ (succ_mem_support P j), if_neg hji]
  · rw [colShift_large P c d col (by rw [chipAt_w P c] at hw; omega)]; simp
  · simp

theorem pert_env_chal (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.compRows) (d : K) :
    (envOfTrace (pertQc P c Qc i d) P.optimized.orbit.ω (P.optimized.computeNodes j)
        (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).chal =
      (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes j)
        (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).chal := rfl

theorem pert_env_pub (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.compRows) (d : K) :
    (envOfTrace (pertQc P c Qc i d) P.optimized.orbit.ω (P.optimized.computeNodes j)
        (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).pub =
      (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes j)
        (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).pub := rfl


/-! ### The gathered typed environment of the perturbed trace -/

theorem gather_ext (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.compRows) (d : K) (r : Fin 63) :
    (rowEnvAt P c (pertQc P c Qc i d) j).extTrace r =
      (rowEnvAt P c Qc j).extTrace r + if j = i then roleShiftK c d r else 0 := by
  simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, correctedFinalExtCoordIndex]
  simp only [pert_env_trace P c Qc i j d]
  have hr := r.isLt
  split_ifs with hji
  · simp only [add_smul, Finset.sum_add_distrib]
    congr 1
    have := reconstruct_coord P.optimized.basis (roleShiftK c d r)
    simp only [reconstruct] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [colShift_role P c d r hr k]
  · simp

theorem gather_extNext (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.compRows) (d : K) (r : Fin 63) :
    (rowEnvAt P c (pertQc P c Qc i d) j).extTraceNext r =
      (rowEnvAt P c Qc j).extTraceNext r +
        if P.optimized.orbit.ω * P.optimized.computeNodes j = P.optimized.computeNodes i then
          roleShiftK c d r else 0 := by
  simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, correctedFinalExtCoordIndex]
  simp only [pert_env_traceNext P c Qc i j d]
  have hr := r.isLt
  split_ifs with hji
  · simp only [add_smul, Finset.sum_add_distrib]
    congr 1
    have := reconstruct_coord P.optimized.basis (roleShiftK c d r)
    simp only [reconstruct] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [colShift_role P c d r hr k]
  · simp

theorem gather_base (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.compRows) (d : K) :
    (rowEnvAt P c (pertQc P c Qc i d) j).baseTrace = (rowEnvAt P c Qc j).baseTrace := by
  funext k
  simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, pert_env_trace P c Qc i j d,
    colShift_small P c d k k.isLt]
  simp

theorem gather_baseNext (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.compRows) (d : K) :
    (rowEnvAt P c (pertQc P c Qc i d) j).baseTraceNext = (rowEnvAt P c Qc j).baseTraceNext := by
  funext k
  simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, pert_env_traceNext P c Qc i j d,
    colShift_small P c d k k.isLt]
  simp

/-- All the remaining fields agree. -/
theorem gather_rest (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.compRows) (d : K) :
    (rowEnvAt P c (pertQc P c Qc i d) j).chal = (rowEnvAt P c Qc j).chal ∧
    (rowEnvAt P c (pertQc P c Qc i d) j).extensionPublic =
      (rowEnvAt P c Qc j).extensionPublic ∧
    (rowEnvAt P c (pertQc P c Qc i d) j).scalarPublic = (rowEnvAt P c Qc j).scalarPublic ∧
    (rowEnvAt P c (pertQc P c Qc i d) j).certBase = (rowEnvAt P c Qc j).certBase ∧
    (rowEnvAt P c (pertQc P c Qc i d) j).certExt = (rowEnvAt P c Qc j).certExt ∧
    (rowEnvAt P c (pertQc P c Qc i d) j).expCol = (rowEnvAt P c Qc j).expCol := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · funext k
    simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, pert_env_trace P c Qc i j d,
      colShift_large P c d (202 + (k : ℕ)) (by omega)]
    simp
  · funext k
    simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, pert_env_trace P c Qc i j d]
    refine Finset.sum_congr rfl fun kk _ => ?_
    rw [colShift_large P c d _ (by omega)]
    simp
  · simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, pert_env_trace P c Qc i j d,
      colShift_large P c d 302 (by omega)]
    simp

/-- The typed `γ` slot of the family environment is `gamma c.1`. -/
theorem rowEnvAt_chal10 (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (j : Fin P.optimized.family.problem.cfg.compRows) :
    (rowEnvAt P c Qc j).chal 10 = gamma c.1 := by
  have h := rowEnvAt_chal P c Qc j ⟨10, by decide⟩
  simpa [CorrectedFinalTypedEnv.toSourceEnv, computeKOfTuple_walkGamma] using h


/-! ### The three row cases, as full agreements -/

theorem roleShiftK_6 (d : K) : roleShiftK c d 6 = gamma c.1 * d := by simp [roleShiftK]
theorem roleShiftK_7 (d : K) : roleShiftK c d 7 = -d := by simp [roleShiftK]
theorem roleShiftK_off (d : K) (r : ℕ) (h6 : r ≠ 6) (h7 : r ≠ 7) : roleShiftK c d r = 0 := by
  simp [roleShiftK, h6, h7]

/-- At the perturbed row itself: the perturbed gather IS the current-row shift. -/
theorem agree_at_row (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) (d : K)
    (hω : P.optimized.orbit.ω * P.optimized.computeNodes i ≠ P.optimized.computeNodes i) :
    AgreeOff (shiftCur (rowEnvAt P c Qc i) d) (rowEnvAt P c (pertQc P c Qc i d) i) [] [] := by
  obtain ⟨hch, hep, hsp, hcb, hce, hex⟩ := gather_rest P c Qc i i d
  refine ⟨gather_base P c Qc i i d, gather_baseNext P c Qc i i d, ?_, ?_, hch, hep, hsp, hcb,
    hce, hex⟩
  · intro r _
    rw [gather_ext P c Qc i i d r, if_pos rfl]
    simp only [shiftCur]
    split_ifs with h6 h7
    · subst h6; simp [roleShiftK, rowEnvAt_chal10]
    · subst h7; simp [roleShiftK, sub_eq_add_neg]
    · rw [roleShiftK_off c d r (fun h => h6 (Fin.ext h)) (fun h => h7 (Fin.ext h)), add_zero]
  · intro r _
    rw [gather_extNext P c Qc i i d r, if_neg hω, add_zero]
    rfl

/-- At the row above the perturbed one: the perturbed gather IS the successor shift. -/
theorem agree_above_row (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.compRows) (d : K) (hji : j ≠ i)
    (hω : P.optimized.orbit.ω * P.optimized.computeNodes j = P.optimized.computeNodes i) :
    AgreeOff (shiftNext (rowEnvAt P c Qc j) d) (rowEnvAt P c (pertQc P c Qc i d) j) [] [] := by
  obtain ⟨hch, hep, hsp, hcb, hce, hex⟩ := gather_rest P c Qc i j d
  refine ⟨gather_base P c Qc i j d, gather_baseNext P c Qc i j d, ?_, ?_, hch, hep, hsp, hcb,
    hce, hex⟩
  · intro r _
    rw [gather_ext P c Qc i j d r, if_neg hji, add_zero]
    rfl
  · intro r _
    rw [gather_extNext P c Qc i j d r, if_pos hω]
    simp only [shiftNext]
    split_ifs with h6 h7
    · subst h6; simp [roleShiftK, rowEnvAt_chal10]
    · subst h7; simp [roleShiftK, sub_eq_add_neg]
    · rw [roleShiftK_off c d r (fun h => h6 (Fin.ext h)) (fun h => h7 (Fin.ext h)), add_zero]

/-- Every other row: nothing moved. -/
theorem agree_other_row (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i j : Fin P.optimized.family.problem.cfg.compRows) (d : K) (hji : j ≠ i)
    (hω : P.optimized.orbit.ω * P.optimized.computeNodes j ≠ P.optimized.computeNodes i) :
    AgreeOff (rowEnvAt P c Qc j) (rowEnvAt P c (pertQc P c Qc i d) j) [] [] := by
  obtain ⟨hch, hep, hsp, hcb, hce, hex⟩ := gather_rest P c Qc i j d
  refine ⟨gather_base P c Qc i j d, gather_baseNext P c Qc i j d, ?_, ?_, hch, hep, hsp, hcb,
    hce, hex⟩
  · intro r _
    rw [gather_ext P c Qc i j d r, if_neg hji, add_zero]
  · intro r _
    rw [gather_extNext P c Qc i j d r, if_neg hω, add_zero]

theorem eval_of_full_agree {env env' : CorrectedFinalTypedEnv F K} (h : AgreeOff env env' [] [])
    (t : TE) : t.eval env' = t.eval env :=
  eval_congr_of_reads h t (by simp) (by simp)

/-! ### Base facts at the perturbed row and the row above it -/

theorem carries_cur (env : CorrectedFinalTypedEnv F K)
    (hsel : ∀ k : Fin 13, (k : ℕ) < 11 → env.baseTrace k = if (k : ℕ) = 2 then 1 else 0)
    (h11 : env.baseTrace 11 = 0) (h12 : env.baseTrace 12 = 0) :
    CarriesBase env curS2 noBase := by
  refine ⟨fun k v hv => ?_, fun k v hv => by simp [noBase] at hv⟩
  unfold curS2 oneHotSel at hv
  by_cases hk : (k : ℕ) < 11
  · rw [if_pos hk, if_pos hk] at hv
    cases hv
    rw [hsel k hk]
    split_ifs <;> simp
  · rw [if_neg hk] at hv
    by_cases hk2 : (k : ℕ) = 11 ∨ (k : ℕ) = 12
    · rw [if_pos hk2] at hv
      cases hv
      rcases hk2 with h | h
      · have : k = 11 := Fin.ext h
        subst this; rw [h11]; simp
      · have : k = 12 := Fin.ext h
        subst this; rw [h12]; simp
    · rw [if_neg hk2] at hv; cases hv

theorem carries_next (env : CorrectedFinalTypedEnv F K)
    (hsel : ∀ k : Fin 13, (k : ℕ) < 11 → env.baseTraceNext k = if (k : ℕ) = 2 then 1 else 0) :
    CarriesBase env noBase (oneHotSel 2) := by
  refine ⟨fun k v hv => by simp [noBase] at hv, fun k v hv => ?_⟩
  unfold oneHotSel at hv
  by_cases hk : (k : ℕ) < 11
  · rw [if_pos hk] at hv
    cases hv
    rw [hsel k hk]
    split_ifs <;> simp
  · rw [if_neg hk] at hv; cases hv


/-- The successor of a non-last row node is the next row node, never itself. -/
theorem succ_ne_self (i : Fin P.optimized.family.problem.cfg.compRows)
    (hilast : (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows) :
    P.optimized.orbit.ω * P.optimized.computeNodes i ≠ P.optimized.computeNodes i := by
  intro h
  have hadj := P.optimized.computeAdjacentOrbit i hilast
  rw [h] at hadj
  have := congrArg Fin.val (P.optimized.computeNodes_injective hadj)
  simp at this

theorem pertQc_small (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) (d : K)
    (col : Fin (P.computeChipAt c).rap.w) (hcol : (col : ℕ) < 13) :
    pertQc P c Qc i d col = Qc col := by
  simp [pertQc, colShift_small P c d col hcol]

/-! ### Facts at an accepted trace -/

section Accepted

variable (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

/-- Base slots `11`/`12` are the fixed masks at the family chip (`masks_at_row`'s proof). -/
theorem masks_at (i : Fin P.optimized.family.problem.cfg.compRows) :
    (rowEnvAt P c Qc i).baseTrace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (rowEnvAt P c Qc i).baseTrace 12 =
        (if i = ⟨P.optimized.family.problem.cfg.compRows - 1,
          Nat.sub_lt P.optimized.family.problem.cfg.compRows_pos (by omega)⟩ then 1 else 0) := by
  have hbind := ((productionNamedComputeRAP_satisfies_iff_sourceLanguage
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
    (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)
    P.optimized.orbit Qc).1 hsat).1
  have hinj := P.optimized.computeNodes_injective
  have h0 := hbind ⟨0, by change 0 < 2; norm_num⟩
  have h1 := hbind ⟨1, by change 1 < 2; norm_num⟩
  have h11 : 11 < (P.computeChipAt c).rap.w := by rw [chipAt_w P c]; norm_num
  have h12 : 12 < (P.computeChipAt c).rap.w := by rw [chipAt_w P c]; norm_num
  have hc0 : (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis (computeChalValOfTuple P.optimized.basis c)
      (P.familyComputePublic c) P.optimized.orbit).preprocessingColumn
        ⟨0, by change 0 < 2; norm_num⟩ = ⟨11, h11⟩ := rfl
  have hc1 : (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis (computeChalValOfTuple P.optimized.basis c)
      (P.familyComputePublic c) P.optimized.orbit).preprocessingColumn
        ⟨1, by change 1 < 2; norm_num⟩ = ⟨12, h12⟩ := rfl
  rw [hc0] at h0
  rw [hc1] at h1
  constructor
  · show (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).trace 11 = _
    simp only [envOfTrace, dif_pos h11]
    rw [show (Qc ⟨11, h11⟩) = Nock.Framework.firstRowMask P.optimized.computeNodes from h0,
      Nock.Framework.firstRowMask_eval _ hinj]
  · show (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).trace 12 = _
    simp only [envOfTrace, dif_pos h12]
    rw [show (Qc ⟨12, h12⟩) = Nock.Framework.lastRowMask
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes from h1,
      Nock.Framework.lastRowMask_eval _ _ hinj]

/-- A row whose `s2` selector is set has the one-hot `s2` selector vector. -/
theorem oneHot_s2 (i : Fin P.optimized.family.problem.cfg.compRows)
    (hs2 : (rowEnvAt P c Qc i).baseTrace 2 = 1) :
    ∀ k : Fin 13, (k : ℕ) < 11 →
      (rowEnvAt P c Qc i).baseTrace k = if (k : ℕ) = 2 then 1 else 0 := by
  obtain ⟨s, hs⟩ := rowSelector_oneHot_at P c Qc hsat (DeployedComputeRows.pkgHchar P) i
  have hval : ∀ st : Nock.ComputeTable.State,
      algebraMap F K ((rowEnvAt P c Qc i).baseTrace
        ⟨Nock.Reified.opCol st, by cases st <;> decide⟩) = if st = s then 1 else 0 := by
    intro st
    have := congrFun hs st
    simpa [OptimizedComputeHostileAccumulator.rowSelector, Nock.ComputeTable.opSel] using this
  have hss : s = .s2 := by
    have h2 := hval .s2
    have hb : (rowEnvAt P c Qc i).baseTrace ⟨Nock.Reified.opCol .s2, by decide⟩ = 1 := hs2
    rw [hb, map_one] at h2
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h2
    exact one_ne_zero h2
  subst hss
  have hF : ∀ st : Nock.ComputeTable.State,
      (rowEnvAt P c Qc i).baseTrace ⟨Nock.Reified.opCol st, by cases st <;> decide⟩ =
        if st = .s2 then 1 else 0 := by
    intro st
    apply (algebraMap F K).injective
    rw [hval st]
    split_ifs <;> simp
  intro k hk
  have key : ∀ m : ℕ, (hm : m < 11) → (rowEnvAt P c Qc i).baseTrace ⟨m, by omega⟩ =
      if m = 2 then 1 else 0 := by
    intro m hm
    interval_cases m
    · exact hF .s0
    · exact hF .s1
    · exact hF .s2
    · exact hF .s3
    · exact hF .s4
    · exact hF .s5
    · exact hF .s6
    · exact hF .s7
    · exact hF .s8
    · exact hF .s9
    · exact hF .cons
  exact key k hk

/-- **THE COUNTEREXAMPLE.**  The `s2` shift of an accepted trace is accepted, at the same tuple. -/
theorem s2_shift_accepted (i : Fin P.optimized.family.problem.cfg.compRows)
    (hi0 : (i : ℕ) ≠ 0) (hilast : (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows)
    (hs2 : (rowEnvAt P c Qc i).baseTrace 2 = 1) (d : K) :
    RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (pertQc P c Qc i d) := by
  have hiff := productionNamedComputeRAP_satisfies_iff_sourceLanguage
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
    (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c) P.optimized.orbit
  have hsrc := (hiff Qc).1 hsat
  refine (hiff (pertQc P c Qc i d)).2 ⟨?_, ?_⟩
  · intro jj
    have hj := hsrc.1 jj
    have hcol : ((ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
        P.optimized.computeNodes P.optimized.basis (computeChalValOfTuple P.optimized.basis c)
        (P.familyComputePublic c) P.optimized.orbit).preprocessingColumn jj : ℕ) < 13 := by
      fin_cases jj
      · change (11 : ℕ) < 13; norm_num
      · change (12 : ℕ) < 13; norm_num
    show pertQc P c Qc i d _ = _
    rw [pertQc_small P c Qc i d _ hcol]
    exact hj
  · intro x hx
    simp only [rowNodeSet, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    have hobl := row_obligations_at P c Qc hsat j
    have hmask := masks_at P c Qc hsat i
    have hlast : i ≠ ⟨P.optimized.family.problem.cfg.compRows - 1,
        Nat.sub_lt P.optimized.family.problem.cfg.compRows_pos (by omega)⟩ := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have hcar : CarriesBase (rowEnvAt P c Qc i) curS2 noBase :=
      carries_cur _ (oneHot_s2 P c Qc hsat i hs2)
        (by rw [hmask.1, if_neg hi0]) (by rw [hmask.2, if_neg hlast])
    refine obligations_transfer (env := rowEnvAt P c Qc j)
      (env' := rowEnvAt P c (pertQc P c Qc i d) j) ?_ ?_ ?_ ?_ hobl
    · intro t ht
      by_cases hji : j = i
      · subst hji
        exact (eval_of_full_agree (agree_at_row P c Qc j d (succ_ne_self P j hilast)) t).trans
          (typed_cur_invariant _ hcar d t ht)
      · by_cases hω : P.optimized.orbit.ω * P.optimized.computeNodes j =
            P.optimized.computeNodes i
        · have hcarN : CarriesBase (rowEnvAt P c Qc j) noBase (oneHotSel 2) := by
            refine carries_next _ fun k hk => ?_
            have hnx : (rowEnvAt P c Qc j).baseTraceNext k = (rowEnvAt P c Qc i).baseTrace k := by
              simp only [rowEnvAt, gatherCorrectedFinalTypedEnv, envOfTrace, hω]
            rw [hnx]
            exact oneHot_s2 P c Qc hsat i hs2 k hk
          exact (eval_of_full_agree (agree_above_row P c Qc i j d hji hω) t).trans
            (typed_next_invariant _ hcarN d t ht)
        · exact eval_of_full_agree (agree_other_row P c Qc i j d hji hω) t
    · rw [gather_base P c Qc i j d]
    · intro jj
      rw [gather_ext P c Qc i j d]
      have hr : (residualWitnessRole jj : ℕ) ≠ 6 ∧ (residualWitnessRole jj : ℕ) ≠ 7 := by
        fin_cases jj <;> decide
      rw [roleShiftK_off c d _ hr.1 hr.2]
      simp
    · intro g hg
      refine coeff_eval_congr
        (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes j)
          (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c))
        (envOfTrace (pertQc P c Qc i d) P.optimized.orbit.ω (P.optimized.computeNodes j)
          (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c))
        ?_ ?_ rfl rfl g (baseLists_avoid _ g hg)
      · intro col hcol
        rw [pert_env_trace P c Qc i j d col, colShift_off P c d col hcol]; simp
      · intro col hcol
        rw [pert_env_traceNext P c Qc i j d col, colShift_off P c d col hcol]; simp

end Accepted

/-! ### What the perturbation did -/

theorem pertQc_off (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) (d : K)
    (col : Fin (P.computeChipAt c).rap.w) (hcol : (col : ℕ) ∉ movedCols) :
    pertQc P c Qc i d col = Qc col := by
  simp [pertQc, colShift_off P c d col hcol]

/-- Every column the perturbation touches is a round-`2` column (`DeployedStaging` B1). -/
theorem pert_columns_round_two (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) (d : K)
    (col : Fin (P.computeChipAt c).rap.w)
    (hround : DeployedStaging.computeColRound (col : ℕ) ≤ 1) :
    pertQc P c Qc i d col = Qc col := by
  refine pertQc_off P c Qc i d col fun hm => ?_
  rw [movedCols_round _ hm] at hround
  omega

theorem pert_role6 (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) (d : K) :
    (rowEnvAt P c (pertQc P c Qc i d) i).extTrace 6 =
      (rowEnvAt P c Qc i).extTrace 6 + gamma c.1 * d := by
  rw [gather_ext, if_pos rfl]; simp [roleShiftK]

theorem pert_role7 (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) (d : K) :
    (rowEnvAt P c (pertQc P c Qc i d) i).extTrace 7 = (rowEnvAt P c Qc i).extTrace 7 - d := by
  rw [gather_ext, if_pos rfl]; simp [roleShiftK, sub_eq_add_neg]

/-- **Determinism fails.**  At every tuple, from any accepted trace with a non-first, non-last
`s2` row, there are two accepted traces that agree, polynomial for polynomial, on every
round-`0`/`1` column and differ in role `7` (`e.dyck`) of that row. -/
theorem determinism_fails (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
    (i : Fin P.optimized.family.problem.cfg.compRows)
    (hi0 : (i : ℕ) ≠ 0) (hilast : (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows)
    (hs2 : (rowEnvAt P c Qc i).baseTrace 2 = 1) :
    ∃ Qc' : Fin (P.computeChipAt c).rap.w → F[X],
      RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc' ∧
      (∀ col : Fin (P.computeChipAt c).rap.w,
        DeployedStaging.computeColRound (col : ℕ) ≤ 1 → Qc' col = Qc col) ∧
      (rowEnvAt P c Qc' i).extTrace 7 ≠ (rowEnvAt P c Qc i).extTrace 7 := by
  refine ⟨pertQc P c Qc i 1, s2_shift_accepted P c Qc hsat i hi0 hilast hs2 1,
    fun col h => pert_columns_round_two P c Qc i 1 col h, ?_⟩
  rw [pert_role7]
  simp

end Pert

end Nock.RedTeam.Batch1391

#print axioms Nock.RedTeam.Batch1391.s2_shift_accepted
#print axioms Nock.RedTeam.Batch1391.determinism_fails
#print axioms Nock.RedTeam.Batch1391.pert_columns_round_two
#print axioms Nock.RedTeam.Batch1391.pert_role6
