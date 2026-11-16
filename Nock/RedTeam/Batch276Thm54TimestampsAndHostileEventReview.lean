/-
  Nock/RedTeam/Batch276Thm54TimestampsAndHostileEventReview.lean

  Every claim below is a
  compiled theorem at the consumed objects (`P.computeChip`, `P.optimizedFailureEvent`,
  `OptimizedFullStrictThm54Statement`), for arbitrary packages `P` unless a fixture is named.

  Paper lines re-read at source: the paper (commit `Com(IO_prog)` before `α, β`),
  `:557` (one record per memory row), `:594-599`, `:603-613` (`Def:unique_request`,
  `cor_uni_req_uni_resp`), `:626-634`, `:1413`, `:1441`, `:1697-1699` (`Lem:equiv_compute`, an
  iff), `:1728-1742` (`V_comp`), `:1852-1887` (timestamps `ln(i−1)·α^k`, the `ln` recurrence),
  `:2213` (the log-derivative multiplicity argument).

  ## What is compiled here

  §A (attack 1, `MA` wrong layer).  The request timestamps are **not columns**: slot `j`'s
  timestamp is decoded as `ln_prev · α^{j+1}` (`rowRecord_ts_zero/one/two`, restated as
  `timestamps_are_decoded`), so the only prover-controlled input is the `ln_prev` column
  (role `54`).  `bumped_lnPrev_rejected`: for ANY accepted trace and ANY row `i`, adding a
  polynomial `d` with `d(node i) ≠ 0` to the first coordinate column of `ln_prev` is REJECTED
  by the consumed `P.computeChip` — at row `0` by the origin gate (`MB`), at row `i+1` by the
  hand-off gate `ln(i) = ln_prev(i+1)`.  No `hchar`, no fold hypothesis.  `timestamps_determined`:
  two accepted traces agreeing on the `ln` column (role `55`) and the selector columns agree on
  every emitted timestamp.

  §B (attack 2, the event).  `active_exponent_range`: every active slot's exponent lies in
  `[1, |hostileRequests|]` (so `D = |hostileRequests|` is the right event parameter);
  `active_exponents_injective`: distinct active slots have distinct exponents, under `hchar`
  alone (no coin).

  §C (attack 3).

  §D (attack 4, `MB`).  `compute_firstMask_column_is_preprocessing`: column `11` IS
  `firstRowMask computeNodes` for every accepted trace (preprocessing, not a prover column);
  `zero_firstMask_rejected`; `rescaled_ln_rejected` instantiated at F73 (`c = 2`) and at the
  real F97 package `packageM` (`c = 2`), both on the honest accepted trace.

  §E (attack 5, `MC`).  `sampled_io_event_good_is_package_field`: the honest-record exclusion is the
  package's own `coins_not_failure` read through `sampled_io_coins` (a note, not a finding).

  §F (attack 6).  `two_hostileTotalWork_exact`: at uniform size `S`, `2·hostileTotalWork = 311S² +
  1117S + 6` EXACTLY (the docstring of `two_hostileTotalWork_le_of_size` says "exact sum … + 4;
  the 6 is slack" — the slack is `3S` in the linear term, the constant is exact: F-6-2, note);
  `figures_at_two_pow_31`: the numerals behind `122`.

  §G (attack 7).  `capstone_hostile_LIO_hypotheses`: the full hypothesis set of
  `optimizedFullStrict_hostile_LIO`, restated; `optimizedFailureEvent_padPerturbed` and
  **`concrete73_capstone_hostile_LIO_padPerturbed`**: the capstone's hostile IO conclusion at a
  NON-honest accepted pair (`Batch274.padPerturbed`) at F73, through `concrete_full_statement`.

  Not claimed: anything about the memory side's ordering; any change to a production statement.
-/
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.OptimizedCanonicalHostileLists
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.RedTeam.Batch274Thm54AnchorsAndAssemblyReview
import Nock.RedTeam.Batch275Thm54LnOriginPinned
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch276

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.OptimizedHostileIOAssembly
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## A. Attack 1 — the timestamps are decoded, and the one column they read is rigid -/

/-- **The three request timestamps are decoded, not committed**: on any
typed row, slot `0`'s is `ln_prev·α`, slot `1`'s is `a₁·ln_prev·α²`, slot `2`'s is
`a₂·ln_prev·α³`.  There is no timestamp column a hostile prover could perturb independently. -/
theorem timestamps_are_decoded (env : CorrectedFinalTypedEnv F K) :
    rowRecord env 0 7 = lnPrevAt env * alphaAt env ∧
      rowRecord env 1 7 = activeMask env 1 * (lnPrevAt env * alphaAt env ^ 2) ∧
      rowRecord env 2 7 = activeMask env 2 * (lnPrevAt env * alphaAt env ^ 3) :=
  ⟨rowRecord_ts_zero env, rowRecord_ts_one env, rowRecord_ts_two env⟩

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- `Q` with column `col` moved by the polynomial `d`. -/
def bumpCol (col : ℕ) (d : F[X]) {w : ℕ} (Q : Fin w → F[X]) : Fin w → F[X] :=
  fun c => if (c : ℕ) = col then Q c + d else Q c

theorem bumpCol_eval_at (col : ℕ) (d : F[X]) {w : ℕ} (Q : Fin w → F[X]) (c : Fin w) (x : F) :
    (bumpCol col d Q c).eval x =
      (Q c).eval x + (if (c : ℕ) = col then d.eval x else 0) := by
  unfold bumpCol
  split_ifs <;> simp

theorem computeChip_w : P.computeChip.rap.w = 303 := rfl

/-- The first coordinate column of `ln_prev` (role `54`) is column `175`.  Bumping it by `d`
moves the gathered `ln_prev` of row `i` by `d(node i) • basis 0`; the `ln` column (role `55`,
columns `178..180`) is untouched. -/
theorem bumped_lnPrev (d : F[X]) (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    lnPrevAt (rowEnv P (bumpCol 175 d Qc) i) =
      lnPrevAt (rowEnv P Qc i) + d.eval (P.optimized.computeNodes i) • P.optimized.basis 0 := by
  simp only [lnPrevAt, rowEnv, gatherCorrectedFinalTypedEnv, Fin.sum_univ_three]
  have hidx : ∀ k : Fin 3, correctedFinalExtCoordIndex (e := 3) (54 : Fin 63) k = 175 + (k : ℕ) := by
    intro k; simp [correctedFinalExtCoordIndex]
  have hw := computeChip_w P
  have h0 : 175 < P.computeChip.rap.w := by omega
  have h1 : 176 < P.computeChip.rap.w := by omega
  have h2 : 177 < P.computeChip.rap.w := by omega
  simp only [hidx, Fin.val_zero, Fin.val_one, Fin.val_two, add_zero, envOfTrace, dif_pos h0,
    dif_pos h1, dif_pos h2, bumpCol_eval_at]
  simp only [if_true, show (176 : ℕ) ≠ 175 by norm_num,
    show (177 : ℕ) ≠ 175 by norm_num, if_false, add_zero, add_smul]
  ring

theorem bumped_lnCur (d : F[X]) (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    lnCurAt (rowEnv P (bumpCol 175 d Qc) i) = lnCurAt (rowEnv P Qc i) := by
  simp only [lnCurAt, rowEnv, gatherCorrectedFinalTypedEnv]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hidx : correctedFinalExtCoordIndex (e := 3) (55 : Fin 63) k = 178 + (k : ℕ) := by
    simp [correctedFinalExtCoordIndex]
  have hw := computeChip_w P
  have hlt : 178 + (k : ℕ) < P.computeChip.rap.w := by have := k.isLt; omega
  simp only [hidx, envOfTrace, dif_pos hlt, bumpCol_eval_at]
  have hne : (178 + (k : ℕ)) ≠ 175 := by omega
  simp [hne]

/-- **Bumping `ln_prev` at ANY single row is REJECTED at the consumed compute chip**, with no
`hchar` and no fold hypothesis: at row `0` the origin gate `isFirst·(ln_prev − 1)` (`MB`) refuses
it, at row `i+1` the hand-off `ln(i) = ln_prev(i+1)` (`Trans.lnChainExpr`) refuses it because the
`ln` column did not move.  Since every request timestamp is `ln_prev·α^{j+1}` (§A), this is the
"perturb one slot's timestamp on an accepted trace" attack, at the only column it can reach. -/
theorem bumped_lnPrev_rejected (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (i : Fin P.optimized.family.problem.cfg.compRows) (d : F[X])
    (hd : d.eval (P.optimized.computeNodes i) ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing P.computeChip (bumpCol 175 d Qc) := by
  intro hsat'
  have hb0 : P.optimized.basis 0 ≠ 0 := P.optimized.basis.ne_zero 0
  have hsmul : d.eval (P.optimized.computeNodes i) • P.optimized.basis 0 ≠ 0 :=
    smul_ne_zero hd hb0
  obtain ⟨m, hm⟩ := i
  cases m with
  | zero =>
      have h1 := hostile_ln0_eq_one P Qc hsat
      have h2 := hostile_ln0_eq_one P (bumpCol 175 d Qc) hsat'
      unfold ln0 at h1 h2
      rw [bumped_lnPrev] at h2
      have : lnPrevAt (rowEnv P Qc (firstRow P)) =
          lnPrevAt (rowEnv P Qc ⟨0, hm⟩) := rfl
      rw [this] at h1
      have hfr : (firstRow P : Fin P.optimized.family.problem.cfg.compRows) = ⟨0, hm⟩ := rfl
      rw [hfr, h1] at h2
      exact hsmul (by linear_combination h2)
  | succ m =>
      have hm' : m < P.optimized.family.problem.cfg.compRows := by omega
      have hc1 := ln_chain_at P Qc hsat ⟨m, hm'⟩ hm
      have hc2 := ln_chain_at P (bumpCol 175 d Qc) hsat' ⟨m, hm'⟩ hm
      rw [bumped_lnCur, bumped_lnPrev, ← hc1] at hc2
      exact hsmul (by linear_combination hc2.symm)

/-- Non-vacuity of the bump: the constant polynomial `1` bumps every row. -/
theorem bumped_one_rejected (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    ¬ RAP.SatisfiesWithPreprocessing P.computeChip (bumpCol 175 (1 : F[X]) Qc) :=
  bumped_lnPrev_rejected P Qc hsat i 1 (by simp)

/-- **The emitted timestamps are determined by the `ln` column and the selectors.**  Two
accepted traces with the same `ln` (role `55`) at every row have the same `ln_prev` at every row
(origin + hand-off), hence the same decoded timestamp at every active slot whose mask agrees. -/
theorem timestamps_determined (Qc Qc' : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hsat' : RAP.SatisfiesWithPreprocessing P.computeChip Qc')
    (hln : ∀ i, lnCurAt (rowEnv P Qc i) = lnCurAt (rowEnv P Qc' i)) :
    (∀ i, lnPrevAt (rowEnv P Qc i) = lnPrevAt (rowEnv P Qc' i)) ∧
      ∀ (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3),
        activeMask (rowEnv P Qc i) j = 1 → activeMask (rowEnv P Qc' i) j = 1 →
        rowRecord (rowEnv P Qc i) j 7 = rowRecord (rowEnv P Qc' i) j 7 := by
  have hprev : ∀ i, lnPrevAt (rowEnv P Qc i) = lnPrevAt (rowEnv P Qc' i) := by
    rintro ⟨m, hm⟩
    cases m with
    | zero =>
        have h1 := hostile_ln0_eq_one P Qc hsat
        have h2 := hostile_ln0_eq_one P Qc' hsat'
        unfold ln0 at h1 h2
        exact h1.trans h2.symm
    | succ m =>
        have hm' : m < P.optimized.family.problem.cfg.compRows := by omega
        rw [← ln_chain_at P Qc hsat ⟨m, hm'⟩ hm, ← ln_chain_at P Qc' hsat' ⟨m, hm'⟩ hm]
        exact hln _
  refine ⟨hprev, fun i j ha ha' => ?_⟩
  rw [rowRecord_ts_active _ j ha, rowRecord_ts_active _ j ha', alphaAt_rowEnv, alphaAt_rowEnv,
    hprev i]

/-! ## B. Attack 2 — the event's exponent range, injectivity, and `hchar` -/

variable (Qc : Fin P.computeChip.rap.w → F[X])

/-- **Every active slot's exponent lies in `[1, |hostileRequests P Qc|]`** — so
`TimestampCollisionEvent |hostileRequests|` covers every pair of committed exponents; `D` is the
right parameter (`totalRequests_eq_length` under `hchar`). -/
theorem active_exponent_range
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (i : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : activeMask (rowEnv P Qc i) j = 1) :
    1 ≤ expOf P Qc i j ∧
      expOf P Qc i j ≤ (OptimizedComputeHostileAccumulator.hostileRequests P Qc).length := by
  refine ⟨expOf_pos P Qc i j, ?_⟩
  rw [← totalRequests_eq_length P Qc hsat hchar]
  exact expOf_le_total P Qc i j hact

/-- **Distinct active slots have distinct exponents**, with no coin involved: within a row the
slot index separates them, across rows the prefix sum strictly increases.  So a hostile prover
cannot make two committed timestamps coincide through the selector pattern alone — only through
`α`, which is what the priced event covers. -/
theorem active_exponents_injective {i i' : Fin P.optimized.family.problem.cfg.compRows}
    {j j' : Fin 3}
    (hact : activeMask (rowEnv P Qc i) j = 1) (hact' : activeMask (rowEnv P Qc i') j' = 1)
    (h : expOf P Qc i j = expOf P Qc i' j') : i = i' ∧ j = j' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (expOf_lt_of_row_lt P Qc hlt j j' hact))
  · subst heq
    exact ⟨rfl, expOf_inj_row P Qc i h⟩
  · exact absurd h (Nat.ne_of_gt (expOf_lt_of_row_lt P Qc hgt j' j hact'))

omit [FiniteDimensional F K] [Fintype K] [CharP K (ringChar K)] in
/-- The row arity is one of `{1, 2, 3}` on every typed row (no hypothesis), so exponents never
skip more than the paper's `regs(op)` allows. -/
theorem rowArity_mem (env : CorrectedFinalTypedEnv F K) :
    rowArity env = 1 ∨ rowArity env = 2 ∨ rowArity env = 3 := by
  have h1 := rowArity_pos env
  have h2 := rowArity_le env
  omega

end Deployed

/-- **`hchar` is a characteristic fact**: it follows from `11 < ringChar K`.  At the `nockCompiles`
layer it is therefore a configuration premise (`p > 11`), not a trace or coin event. -/
theorem hchar_of_lt_ringChar (h : 11 < ringChar K) :
    ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1 := by
  intro n hn heq
  haveI : CharP K (ringChar K) := ringChar.charP K
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd heq (by simp)
  · have h' : ((n - 1 : ℕ) : K) = 0 := by
      rw [Nat.cast_sub hpos, Nat.cast_one, heq, sub_self]
    have hdvd := (CharP.cast_eq_zero_iff K (ringChar K) (n - 1)).mp h'
    rcases hdvd with ⟨m, hm⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · omega
    · have : ringChar K * 1 ≤ ringChar K * m := Nat.mul_le_mul_left _ hm0
      omega

/-- Negative control: in characteristic `2` the hypothesis is false (`3 = 1`).  This is the only
regime in which a non-one-hot selector could survive the base gates; `hchar` is an explicit
premise of every `MA`/`MC` theorem, so the regime is excluded, not priced. -/
theorem hchar_fails_in_char_two : ¬ (∀ n : ℕ, n ≤ 11 → (n : ZMod 2) = 1 → n = 1) := by
  intro h
  have := h 3 (by norm_num) (by decide)
  omega

/-! ## C. Attack 3 — `hrespnd` is derivable from the identity -/

section Identity

variable {m : ℕ} [Fintype K] [DecidableEq K] {p : ℕ} [CharP K p]

/-- `finiteIO_sound_of_identity'` implies the response `Nodup` it dropped: the conclusion
`IO.LIO` contains it.  (Type-level check that no premise of the primed theorem is a disguised
response-side `Nodup`.) -/
theorem responses_nodup_from_identity {Ksz : ℕ} (records : FiniteIO.PreChallengeRecords K m)
    (coins : FiniteIO.IOCoins K)
    (hdA : ∀ i, coins.pole + FiniteIO.reqVals records coins.gamma i ≠ 0)
    (hdB : ∀ j, coins.pole + FiniteIO.respVals records coins.gamma j ≠ 0)
    (hend : (∑ i, (coins.pole + FiniteIO.reqVals records coins.gamma i)⁻¹) =
      ∑ j, (coins.pole + FiniteIO.respVals records coins.gamma j)⁻¹)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup)
    (hγ : coins.gamma ∉ FiniteIO.IORLCCollisionEvent records)
    (hpole : coins.pole ∉ FiniteIO.IOLogDerivEvent records coins.gamma) :
    records.responses.Nodup :=
  FiniteIO.responses_nodup_of_identity records coins hdA hdB hend hKp hKreq hKresp hreqnd hγ hpole

/-- The counted event (3) is bounded by the degree of its certificate `ioQP`
(`ioQP_natDegree_le`), which is the count `IOLogDerivEvent_card_le` charges — the lift from the
one-pole identity to the rational-function identity (`frac_identity_of_pole_identity`) is priced
by exactly this event. -/
theorem logDeriv_event_le_degree (records : FiniteIO.PreChallengeRecords K m) (γ : K) :
    (FiniteIO.IOLogDerivEvent records γ).card ≤
        records.requests.length + records.responses.length ∧
      (FiniteIO.ioQP records γ).natDegree ≤
        records.requests.length + records.responses.length :=
  ⟨FiniteIO.IOLogDerivEvent_card_le records γ, FiniteIO.ioQP_natDegree_le records γ⟩

end Identity

/-! ## D. Attack 4 — the mask is preprocessing; `rescaled_ln_rejected` at F73 and F97 -/

section Masks

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin P.computeChip.rap.w → F[X])

theorem eleven_lt_w : 11 < P.computeChip.rap.w := by rw [computeChip_w]; norm_num

/-- **The compute first-row mask is preprocessing** (`Batch274` F-1-1's shape, compute side):
for any accepted trace, column `11` IS `firstRowMask computeNodes` — the `BindsPreprocessing`
half of `SatisfiesWithPreprocessing`, not a prover column. -/
theorem compute_firstMask_column_is_preprocessing
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc) :
    Qc ⟨11, eleven_lt_w P⟩ = Nock.Framework.firstRowMask P.optimized.computeNodes := by
  have hbind := ((productionNamedComputeRAP_satisfies_iff_sourceLanguage
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
    P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit Qc).1 hsat).1
  exact hbind ⟨0, by change 0 < 2; norm_num⟩

/-- A trace whose column `11` is the zero polynomial is REJECTED (the origin gate would then bind
nothing — `anchor_void_without_mask` shape — but the mask is not the prover's to zero). -/
theorem zero_firstMask_rejected (hz : Qc ⟨11, eleven_lt_w P⟩ = 0) :
    ¬ RAP.SatisfiesWithPreprocessing P.computeChip Qc := by
  intro hsat
  have h := (masks_at_row P Qc hsat (firstRow P)).1
  simp only [firstRow, if_true] at h
  change (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes (firstRow P))
    P.optimized.computeChallenge P.optimized.computePublic).trace 11 = 1 at h
  simp only [envOfTrace, dif_pos (eleven_lt_w P), hz, Polynomial.eval_zero] at h
  exact zero_ne_one h

end Masks

section F73

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildablePackage.Concrete
open OptimizedStrictFullPackage.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- `rescaled_ln_rejected` at the real F73 package, honest accepted trace, `c = 2`. -/
theorem rescaled_ln_rejected_F73
    (hax : FormRAxisBound
      concreteOptimizedFullStrictPackage.optimized.sampled
      concreteOptimizedFullStrictPackage.optimized.basis)
    (hbasis : FormRBasis concreteOptimizedFullStrictPackage.optimized.basis)
    (hwidth : FormRWidth F73) :
    ¬ RAP.SatisfiesWithPreprocessing concreteOptimizedFullStrictPackage.computeChip
      (Batch275.rescaleLn (2 : F73) concreteComputeTrace) := by
  rw [concreteComputeTrace_eq]
  exact Batch275.rescaled_ln_rejected _ _
    (canonicalComputeTrace_satisfies _ hax hbasis hwidth) 2 (by decide)

/-- The honest F73 compute trace is accepted (completeness half). -/
theorem F73_honest_accepted
    (hax : FormRAxisBound
      concreteOptimizedFullStrictPackage.optimized.sampled
      concreteOptimizedFullStrictPackage.optimized.basis)
    (hbasis : FormRBasis concreteOptimizedFullStrictPackage.optimized.basis)
    (hwidth : FormRWidth F73) :
    RAP.SatisfiesWithPreprocessing concreteOptimizedFullStrictPackage.computeChip
      concreteComputeTrace := by
  rw [concreteComputeTrace_eq]; exact canonicalComputeTrace_satisfies _ hax hbasis hwidth

end F73

section F97

open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.MultiRootServedFixture

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance fintype97 : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance deq97 : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance charRing97 : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-- `rescaled_ln_rejected` at the real F97 package `packageM` (two compute rows), honest
accepted trace, `c = 2`. -/
theorem rescaled_ln_rejected_F97
    (haxP : FormRAxisBound (packageM hmoreM).optimized.sampled
      (packageM hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageM hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97) :
    ¬ RAP.SatisfiesWithPreprocessing (packageM hmoreM).computeChip
      (Batch275.rescaleLn (2 : F97) (canonicalComputeTrace (packageM hmoreM))) :=
  Batch275.rescaled_ln_rejected _ _
    (canonicalComputeTrace_satisfies _ haxP hbasisP hwidthP) 2 (by decide)

/-- And the zero-origin trace at F97 (`MA` §2's witness) is rejected. -/
theorem zero_origin_rejected_F97
    (haxP : FormRAxisBound (packageM hmoreM).optimized.sampled
      (packageM hmoreM).optimized.basis)
    (hbasisP : FormRBasis (packageM hmoreM).optimized.basis)
    (hwidthP : FormRWidth F97) :
    ¬ RAP.SatisfiesWithPreprocessing (packageM hmoreM).computeChip
      (Batch275.rescaleLn (0 : F97) (canonicalComputeTrace (packageM hmoreM))) :=
  Batch275.zero_origin_rejected _ _
    (canonicalComputeTrace_satisfies _ haxP hbasisP hwidthP)

end F97

/-- The deviation exhibit is still a theorem about `ComputeTable.Vcomp`: the verifier accepts the row with `ln_prev`, `ln`, `mr1.ts` rescaled. -/
theorem vcomp_exhibit_still_about_Vcomp
    (inp : ComputeTable.Inputs K) (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K)
    (hstate : pub.state = .s1) (h : ComputeTable.Vcomp inp pub dec) (lnPrev' : K) :
    ComputeTable.Vcomp inp
      { pub with
        ln_prev := lnPrev'
        ln := lnPrev' * inp.α
        mr1 := { pub.mr1 with ts := lnPrev' * inp.α } }
      dec :=
  GenericHonestCommitment.vcomp_s1_ignores_first_ln_prev inp pub dec hstate h lnPrev'

/-! ## E. -/

section Uniform

variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **The consumed failure event's cardinality is bounded by a function of `(N, M)` alone, for
EVERY `(Qc, Qm)`.** -/
theorem optimizedFailureEvent_card_le_uniform
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    (P.optimizedFailureEvent Qc Qm).card ≤
      OptimizedStrictPackage.optimizedHostileProductionFailureCardBound
        (Fintype.card K) (Fintype.card F)
        (ProductionP8Containment.workload P.strategy P.optimized.Λ
          (ProductionP8Containment.fixedTopologyWorkload P.strategy)
          (ProductionP8Containment.fixedAxisWorkload P.strategy))
        P.hostileIOWork
        P.optimized.family.problem.cfg.compRows P.optimized.family.problem.cfg.memRows := by
  -- The IO summand is the family event, priced premise-free at the row-count
  -- majorants (`famIOEventOf_card_le`), so no `ioFailureUnionBound` monotonicity step.
  exact OptimizedStrictPackage.optimizedHostileProductionFailureEvent_card_le
    (OptimizedFullStrictNockVMROMPackage.two_ne_zero P) P.strategy P.optimized.census
    P.objects.cfg.challenges.lam
    (ProductionP8Containment.fixedTopologyWorkload P.strategy)
    (ProductionP8Containment.fixedAxisWorkload P.strategy)
    P.optimized.sizeWindowBound
    (ProductionP8Containment.topologyWorkload_le_fixedTopologyWorkload P.strategy)
    (ProductionP8Containment.templateAxisWorkload_le_fixedAxisWorkload P.strategy)
    (P.famIOEventOf Qc Qm) (P.famIOEventOf_card_le Qc Qm)
    (P.hostileRequests Qc).length (P.hostileRequests_length_le Qc)
    (P.computeSourceEnv Qc) (P.computeWalkEnv Qc) (P.computeScalarEnv Qc)
    (P.memorySourceEnv Qm) (P.memoryScalarFamilies Qm)
    (P.hostileInterRecords Qm) (P.memoryBaseEnv Qm) (P.hostileInterReads_length_le Qm)
    (P.hostileInterVerifies_length_le Qm)
    (P.computeWalkRootEvent Qc) (P.computeTilingEventOf Qc) (P.memoryTilingEventOf Qm)
    (P.computePrefixGammaEventOf Qc) (P.memoryPrefixGammaEventOf Qm)
    (P.memoryForestAlphaEventOf Qm)
    (P.computeWalkRootEvent_card_le Qc) (P.computeTilingEventOf_card_le Qc)
    (P.memoryTilingEventOf_card_le Qm)
    (P.computePrefixGammaEventOf_card_le Qc) (P.memoryPrefixGammaEventOf_card_le Qm)
    (P.memoryForestAlphaEventOf_card_le Qm)
    (P.decodedLambdaEventOf Qc Qm)
    (P.decodedLambdaEventOf_card_le Qc Qm)
    (PreSeedCensus.reqPairEventOfEnvs K P.q P.optimized.family.problem.cfg.kMem
      (P.optimized.family.problem.cfg.memRows ⊔ P.optimized.Λ) (P.memoryBaseEnv Qm)
      P.optimized.family.problem.cfg.memRows_pos
      (PreSeedCensus.requestTargets P.strategy.skeleton))
    (by
      have h := P.reqPairEventOf_card_le Qm
      unfold OptimizedFullStrictNockVMROMPackage.reqPairEventOf OptimizedStrictPackage.liftP8Failure at h
      rw [Finset.card_product, Finset.card_univ] at h
      have hrest :
          Fintype.card ((K × K) ×
            Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound.FinalComputeChallengeTuple K ×
            Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting.MemoryChallengeTuple K) =
            Fintype.card K ^ 7 := by
        simp only [Fintype.card_prod, OptimizedStrictPackage.card_finalComputeChallengeTuple,
          OptimizedStrictPackage.card_memoryChallengeTuple]
        ring
      rw [hrest] at h
      refine Nat.le_of_mul_le_mul_right ?_ (pow_pos (Fintype.card_pos (α := K)) 7)
      calc _ ≤ Fintype.card K ^ 10 *
            ProductionP8Containment.reqPairWorkload P.strategy P.optimized.Λ := h
        _ = _ := by ring)

/-- **The honest-record exclusion is a package field, not a derived fact about coins**: acceptance
pins `c.2.1` to the package's own coins (`sampled_io_coins`) and the package asserts those coins
are outside its own honest event (`FiniteIOStrategy.coins_not_failure`).  So
`sampled_io_event_good_of_acceptance` is genuinely derivable — from a field.  (Note F-5-2: the
`MC` sentence "the honest records need no pricing" is true relative to that field.) -/
theorem sampled_io_event_good_is_package_field
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c) :
    c.2.1 = (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole) ∧
      (P.optimized.sampled.sampled.coins.gamma, P.optimized.sampled.sampled.coins.pole) ∉
        FiniteIO.IOFailureEvent P.optimized.sampled.sampled.records :=
  ⟨hacc.sampled_io_coins, P.optimized.sampled.sampled.coins_not_failure⟩

end Uniform

/-! ## F. Attack 6 — the figures, recomputed on the Lean side -/

/-- **The live majorant at uniform size `S`: `2·hostileTotalWork ≤ 367S² + 110S + 24`.** -/
theorem two_hostileTotalWork_exact (S : ℕ) :
    2 * RealProgramSoundness.hostileTotalWork (RealProgramSoundness.p8Majorant S S S S) S S ≤
      447 * (S * S) + 152 * S + 288 :=
  RealProgramSoundness.two_hostileTotalWork_le_of_size S S S S S _
    (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _)

theorem figures_at_two_pow_31 :
    2 * RealProgramSoundness.hostileTotalWork
        (RealProgramSoundness.p8Majorant (2 ^ 31) (2 ^ 31) (2 ^ 31) (2 ^ 31)) (2 ^ 31) (2 ^ 31)
      ≤ 447 * (2 ^ 31 * 2 ^ 31) + 152 * 2 ^ 31 + 288 :=
  two_hostileTotalWork_exact (2 ^ 31)

/-- The three real-program / paper-configuration figures, as the tree states them (`MC`):
`122` at `2^31`, `120` at `2^32`, `123` under the `16^65` ceiling, `121` at the symmetric
majorant; the `184 − 2r` majorant is sharp. -/
theorem figures_restated :
    (∀ R M Λ A p8Work : ℕ, R ≤ 2 ^ 31 → M ≤ 2 ^ 31 → Λ ≤ 2 ^ 31 → A ≤ 2 ^ 31 →
      p8Work ≤ RealProgramSoundness.p8Majorant R M Λ A →
      GoldilocksParameters.goldilocksHostileFailureBound p8Work
        (FiniteIO.ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        < 1 / (2 : ℚ) ^ 122) ∧
    (∀ R M Λ A p8Work : ℕ, R ≤ 2 ^ 32 → M ≤ 2 ^ 32 → Λ ≤ 2 ^ 32 → A ≤ 2 ^ 32 →
      p8Work ≤ RealProgramSoundness.p8Majorant R M Λ A →
      GoldilocksParameters.goldilocksHostileFailureBound p8Work
        (FiniteIO.ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        < 1 / (2 : ℚ) ^ 120) ∧
    (∀ p8Work ioWork : ℕ, p8Work ≤ 2 ^ 60 → ioWork ≤ 16 ^ 65 →
      GoldilocksParameters.goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31)
        < 1 / (2 : ℚ) ^ 123) ∧
    (∀ p8Work ioWork : ℕ,
      1 / (2 : ℚ) ^ 128 <
        GoldilocksParameters.goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31)) ∧
    (∀ r b : ℕ, 2 * r + b = 184 →
      ¬ ((447 * (2 ^ r * 2 ^ r) + 152 * 2 ^ r + 288) * 2 ^ (b + 1) <
        2 * GoldilocksParameters.cardKGold)) :=
  ⟨fun R M Λ A p8 hR hM hΛ hA hp8 =>
      RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31 R M Λ A p8 hR hM hΛ hA hp8,
   fun R M Λ A p8 hR hM hΛ hA hp8 =>
      RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_32 R M Λ A p8 hR hM hΛ hA hp8,
   fun p8 io hp8 hio => GoldilocksParameters.hostile_soundness_at_paper_configuration p8 io hp8 hio,
   fun p8 io => GoldilocksParameters.hostile_lower_bound_at_paper_configuration p8 io,
   fun r b hb => RealProgramSoundness.hostileSizeWork_not_lt_cardK r b hb⟩

/-! ## G. Attack 7 — the capstone's hostile IO conclusion at a non-honest accepted pair -/

section Capstone

variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **The full hypothesis set of `optimizedFullStrict_hostile_LIO`, restated**: the statement
`S`, the acceptance, `c ∉ optimizedFailureEvent Qc Qm`, `hchar`,
`hKp`, the two range premises.  `hz0` is derived (`hz0_of_good`).
Nothing honest-side: `S` is used only through `acceptance_to_target`, which is `∀ Qc Qm c`. -/
theorem capstone_hostile_LIO_hypotheses {Ksz : ℕ}
    (S : OptimizedFullStrictThm54Statement P)
    (Qc : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hio : c.2.1 ∉ FiniteIO.IOFailureEvent (hostileRecords P Qc Qm))
    (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (hKp : Ksz < ringChar K)
    (hKreq : IO.InRange Ksz (OptimizedComputeHostileAccumulator.hostileRequests P Qc).length)
    (hKresp : (OptimizedMemoryHostileAccumulator.hostileResponses P Qm).length ≤ Ksz) :
    IO.LIO Ksz (OptimizedComputeHostileAccumulator.hostileRequests P Qc)
      (OptimizedMemoryHostileAccumulator.hostileResponses P Qm) :=
  optimizedFullStrict_hostile_LIO_historical P Qc Qm c hacc hgood hio hchar hKp hKreq hKresp

/-! `capstone_hostile_LIO_from_acceptance_to_target`
(its premise was the old package-width `acceptance_to_target`; the family route is
`FamilyIOChainRouteB.optimizedFullStrict_hostile_LIO_at`) and `optimizedFailureEvent_padPerturbed`
(the event's IO summand is now `famIOEventOf`, read at the family-width traces, for which no
padding-invariance lemma is in the tree). -/

end Capstone

section F73Capstone

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildablePackage.Concrete
open OptimizedStrictFullPackage.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic


/-- The pair is not the honest one. -/
theorem F73_pair_not_honest :
    Batch274.padPerturbed concreteOptimizedFullStrictPackage concreteMemoryTrace ≠
      canonicalMemoryTrace concreteOptimizedFullStrictPackage :=
  Batch274.padPerturbed_concrete_ne_canonical

end F73Capstone

end

end Nock.RedTeam.Batch276

-- MA
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_timestamp_eq
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.rowRecord_ts_at
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.TimestampCollisionEvent_card_le
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_requests_nodup
#print axioms Nock.NockVMROM.Thm54.FiniteIO.finiteIO_sound_of_identity'
#print axioms Nock.NockVMROM.Thm54.FiniteIO.responses_nodup_of_identity
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_LIO'
-- MB
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.hostile_ln0_eq_one
#print axioms Nock.RedTeam.Batch275.rescaled_ln_rejected
#print axioms Nock.NockVMROM.Thm54.GenericHonestCommitment.vcomp_s1_ignores_first_ln_prev
-- MC
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictPackage.optimizedHostileProductionFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictPackage.optimizedHostileProductionFailureProbability_le
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.sampled_io_event_good_of_historical
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.hostile_soundness_at_paper_configuration
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_32
#print axioms Nock.NockVMROM.Thm54.OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
-- this file
#print axioms Nock.RedTeam.Batch276.timestamps_are_decoded
#print axioms Nock.RedTeam.Batch276.bumped_lnPrev_rejected
#print axioms Nock.RedTeam.Batch276.bumped_one_rejected
#print axioms Nock.RedTeam.Batch276.timestamps_determined
#print axioms Nock.RedTeam.Batch276.active_exponent_range
#print axioms Nock.RedTeam.Batch276.active_exponents_injective
#print axioms Nock.RedTeam.Batch276.hchar_of_lt_ringChar
#print axioms Nock.RedTeam.Batch276.hchar_fails_in_char_two
#print axioms Nock.RedTeam.Batch276.responses_nodup_from_identity
#print axioms Nock.RedTeam.Batch276.logDeriv_event_le_degree
#print axioms Nock.RedTeam.Batch276.compute_firstMask_column_is_preprocessing
#print axioms Nock.RedTeam.Batch276.zero_firstMask_rejected
#print axioms Nock.RedTeam.Batch276.rescaled_ln_rejected_F73
#print axioms Nock.RedTeam.Batch276.rescaled_ln_rejected_F97
#print axioms Nock.RedTeam.Batch276.zero_origin_rejected_F97
#print axioms Nock.RedTeam.Batch276.vcomp_exhibit_still_about_Vcomp
#print axioms Nock.RedTeam.Batch276.optimizedFailureEvent_card_le_uniform
#print axioms Nock.RedTeam.Batch276.sampled_io_event_good_is_package_field
#print axioms Nock.RedTeam.Batch276.two_hostileTotalWork_exact
#print axioms Nock.RedTeam.Batch276.figures_at_two_pow_31
#print axioms Nock.RedTeam.Batch276.figures_restated
#print axioms Nock.RedTeam.Batch276.capstone_hostile_LIO_hypotheses
#print axioms Nock.RedTeam.Batch276.F73_pair_not_honest
