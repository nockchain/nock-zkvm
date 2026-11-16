import Nock.NockVMROM.Thm54.VclL.Compute.LayoutVCLD
import Nock.NockVMROM.Thm54.BelowDefs.P8Core.WalkQueueDeployed
import Nock.NockVMROM.Thm54.P8Core.SVCompute.WalkTwins

/-!
# V4c items 5–6: the whole-trace compute walk at VCL semantics (`W0`/`W1`)

**1751).

The VCL walk differs from the 303-hosted one only in WHERE `count` / `acc` live: the dedicated
columns `W0` / `W1` (VCL `208..213`, the 309 source columns `303` / `306`), not the hosted
overlay.  Labels (`cur`, `cc`, `cm`), the walk line `ln`, the coins and the publics are read from
the same decoded `𝕂` roles as at 303 — at the row's 309-shaped pull-back.  So:

* every label / line / coin lemma is ported at the base source env `SB i` (the gathered
  pull-back), the one-hot state coming from `VclSourceObligations.base15` (`oneHot_of_base15`);
* `count i := SR(i).trace 303`, `acc i := SR(i).trace 306` on the mixed 309 source env `SR i`;
  label reads transfer `SR ↔ SB` through `eval_toSourceEnv309_of_noWalkVars`;
* the row-0 identities come from the retargeted endpoints `endpoint2_309` / `endpoint4_309`, the
  steps from `conditional_transition_soundness_vcl`, the queue from
  `queue_sources_vcl`.

Results: **`vcl_walkSat`** (`WalkSat` of the VCL walk, `α = alphaC`, `seed = seedOfClaim`,
`initial_count = alphaC`, over `D.N` rows), **`vcl_walk_out`** (`acc(N) = 0`),
**`vcl_bfsValid`** and **`vcl_tiling`** (outside `computeTilingEvent`).

Paper: the paper (walk), `:962`, `:966`, `:1906`, `:2263`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace WalkVCL

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SVCompute
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.Framework
open Nock.Framework.Reify
open Module
open MonolithicRAP
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open Nock.RedTeam.Batch438
open Nock.RedTeam.Batch478
open Nock.NockVMROM.Thm54.WalkQueueDeployed

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 300000

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {h : ℕ}
  (D : ChipData F K h) (γc ρc : ℕ)
  (c : OptimizedProductionChallengeTuple K F)
  (Q : Fin (chipOfP D (layoutVCLD (F := F) (K := K) (h := h) γc ρc) c).rap.w → F[X])

/-! ## 1. The row environments -/

/-- The pulled-back base row env (309 layout) of VCL row `i`. -/
abbrev envP (i : Fin D.N) : Env F := pullEnv (envFAtD D c Q i)
/-- The gathered typed base env of row `i` (the decoder's view; `count`/`acc` not read). -/
abbrev BV (i : Fin D.N) : CorrectedFinalTypedEnv F K := gatherCorrectedFinalTypedEnv D.basis (envP D γc ρc c Q i)
/-- The width-309 typed env of row `i` (base plus `W0`/`W1`). -/
abbrev EV (i : Fin D.N) : Env309 F K := gather309 D.basis (envP D γc ρc c Q i)
/-- The base source env. -/
abbrev SB (i : Fin D.N) : Env K := (BV D γc ρc c Q i).toSourceEnv
/-- The mixed 309 source env (`303 ↦ W0`, `306 ↦ W1`). -/
abbrev SR (i : Fin D.N) : Env K := (EV D γc ρc c Q i).toSourceEnv

theorem EV_base (i : Fin D.N) : (EV D γc ρc c Q i).base = BV D γc ρc c Q i := rfl

theorem envP_chal (i : Fin D.N) : (envP D γc ρc c Q i).chal = computeChalValOfTuple D.basis c := rfl
theorem envP_pub (i : Fin D.N) :
    (envP D γc ρc c Q i).pub = computePublicOfTuple D.basis D.claim D.pub c := rfl

/-- Slot `q` of the challenge map is `computeKOfTuple c q` (`rowEnvAtD_chal` at the pull-back). -/
theorem SB_chal (i : Fin D.N) (q : Fin 12) :
    (SB D γc ρc c Q i).chal q.val = computeKOfTuple c q.val := by
  have hq : (q : ℕ) < 12 := q.isLt
  simp only [SB, BV, CorrectedFinalTypedEnv.toSourceEnv, gatherCorrectedFinalTypedEnv, hq,
    ↓reduceDIte]
  change (∑ k : Fin 3,
      computeChalValOfTuple D.basis c (3 * (q : ℕ) + (k : ℕ)) • D.basis k) =
    computeKOfTuple c q.val
  have hslot : ∀ k : Fin 3, 3 * (q : ℕ) + (k : ℕ) < 36 := by
    intro k; omega
  have hcoord : ∀ k : Fin 3,
      computeChalValOfTuple D.basis c (3 * (q : ℕ) + (k : ℕ)) =
        coord D.basis (computeKOfTuple c q.val) k := by
    intro k
    simp only [computeChalValOfTuple, hslot k, ↓reduceIte]
    have hdiv : (3 * (q : ℕ) + (k : ℕ)) / 3 = (q : ℕ) := by omega
    have hmod : (3 * (q : ℕ) + (k : ℕ)) % 3 = (k : ℕ) := by omega
    rw [hdiv]
    apply congrArg
    exact Fin.ext hmod
  simp_rw [hcoord]
  exact reconstruct_coord D.basis (computeKOfTuple c q.val)

/-- **The `z·z⁻¹` pin holds at every row** (`nprSeed c.1 ≠ 0`): `rowFactsP_vcomp`'s `hzZ` is a
theorem at the layout. -/
theorem zZinv_at (i : Fin D.N) (hz : nprSeed c.1 ≠ 0) :
    (zZinvExpr.subst computeSubst).eval (SB D γc ρc c Q i) = 0 := by
  have h1 := SB_chal D γc ρc c Q i ⟨1, by decide⟩
  have h5 := SB_chal D γc ρc c Q i ⟨5, by decide⟩
  simp [zZinvExpr, Expr.subst, computeSubst, computeTraceSubst, chl, tc, Expr.eval, h1, h5]
  show nprSeed c.1 * (nprSeed c.1)⁻¹ - 1 = 0
  rw [mul_inv_cancel₀ hz, sub_self]

theorem walkGamma_at (i : Fin D.N) : walkGammaChallenge.eval (SB D γc ρc c Q i) = gamma c.1 := by
  have h := SB_chal D γc ρc c Q i ⟨10, by decide⟩
  rw [show computeKOfTuple c 10 = gamma c.1 from rfl] at h
  simpa [walkGammaChallenge, walkGammaChallengeIndex, Expr.eval] using h

theorem walkAlpha_at (i : Fin D.N) : (walkChallenge 0).eval (SB D γc ρc c Q i) = alphaC c.1 := by
  have h := SB_chal D γc ρc c Q i ⟨6, by decide⟩
  rw [show computeKOfTuple c 6 = alphaC c.1 from rfl] at h
  simpa [walkChallenge, walkChallengeBase, Expr.eval] using h

theorem walkAlphaChal_at (i : Fin D.N) : walkAlphaChallenge.eval (SB D γc ρc c Q i) = alphaC c.1 :=
  walkAlpha_at D γc ρc c Q i

theorem family_seed_at (i : Fin D.N) : (SB D γc ρc c Q i).pub 1 = seedOfClaim D.claim c := by
  have h1 : (1 : ℕ) < 3 := by norm_num
  simp only [SB, BV, CorrectedFinalTypedEnv.toSourceEnv, dif_pos h1]
  change (∑ k : Fin 3, (computePublicOfTuple D.basis D.claim D.pub c) (3 * 1 + (k : ℕ)) • D.basis k) = _
  have hcoord : ∀ k : Fin 3, (computePublicOfTuple D.basis D.claim D.pub c) (3 * 1 + (k : ℕ)) =
      coord D.basis (seedOfClaim D.claim c) k := by
    intro k
    have := computePublicOfTuple_seed_coord D.basis D.claim D.pub c k
    simpa [show 3 * 1 + (k : ℕ) = 3 + (k : ℕ) by ring] using this
  simp_rw [hcoord]
  exact reconstruct_coord D.basis _

theorem family_initialCount_at (i : Fin D.N) : (SB D γc ρc c Q i).pub 0 = alphaC c.1 := by
  have h0 : (0 : ℕ) < 3 := by norm_num
  simp only [SB, BV, CorrectedFinalTypedEnv.toSourceEnv, dif_pos h0]
  change (∑ k : Fin 3, (computePublicOfTuple D.basis D.claim D.pub c) (3 * 0 + (k : ℕ)) • D.basis k) = _
  have hcoord : ∀ k : Fin 3, (computePublicOfTuple D.basis D.claim D.pub c) (3 * 0 + (k : ℕ)) =
      coord D.basis (alphaC c.1) k := by
    intro k
    have := computePublicOfTuple_alpha_coord D.basis D.claim D.pub c k
    simpa using this
  simp_rw [hcoord]
  exact reconstruct_coord D.basis _

/-! ## 2. The shift (row adjacency) -/

variable (hadj : D.Adjacent)

include hadj in
theorem envF_traceNext_eq (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) (j : ℕ) :
    (envFAtD D c Q i).traceNext j = (envFAtD D c Q ⟨(i : ℕ) + 1, hi⟩).trace j := by
  have hadj := hadj i hi
  simp only [envOfTrace]
  split_ifs with h
  · rw [hadj]
  · rfl

include hadj in
theorem envP_traceNext_eq (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) (j : ℕ) :
    (envP D γc ρc c Q i).traceNext j = (envP D γc ρc c Q ⟨(i : ℕ) + 1, hi⟩).trace j := by
  simp only [envP, pullEnv]
  exact envF_traceNext_eq D γc ρc c Q hadj i hi _

include hadj in
theorem shift_trace (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) (j : ℕ) :
    (SB D γc ρc c Q i).traceNext j = (SB D γc ρc c Q ⟨(i : ℕ) + 1, hi⟩).trace j := by
  simp only [SB, BV, CorrectedFinalTypedEnv.toSourceEnv]
  split_ifs <;> simp only [gatherCorrectedFinalTypedEnv] <;>
    first
    | rw [envP_traceNext_eq D γc ρc c Q hadj i hi]
    | (refine Finset.sum_congr rfl fun k _ => ?_; rw [envP_traceNext_eq D γc ρc c Q hadj i hi])
    | rfl

include hadj in
theorem shift_trace71 (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    ∀ j, j < 71 → (shiftNext (SB D γc ρc c Q i)).trace j = (SB D γc ρc c Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  fun j _ => shift_trace D γc ρc c Q hadj i hi j

include hadj in
/-- The walk columns shift: `W(i).next = W(i+1)`. -/
theorem shift_walk (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) (j : ℕ) (hj : j = 303 ∨ j = 306) :
    (SR D γc ρc c Q i).traceNext j = (SR D γc ρc c Q ⟨(i : ℕ) + 1, hi⟩).trace j := by
  rcases hj with rfl | rfl <;>
  · simp only [SR, EV, Env309.toSourceEnv, gather309, if_true, if_false]
    try simp only [show (306 : ℕ) ≠ 303 by norm_num, if_false, if_true]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [envP_traceNext_eq D γc ρc c Q hadj i hi]

/-! ## 3. The row facts, the one-hot state and the decoded labels -/

variable (RF : RowFactsP D (layoutVCLD (F := F) (K := K) (h := h) γc ρc) c Q)
variable (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)

include RF

theorem obl (i : Fin D.N) : VclSourceObligations D.N (EV D γc ρc c Q i) (envP D γc ρc c Q i) := RF.obl i

omit RF in
theorem baseTrace_eq (i : Fin D.N) (k : ℕ) (hk : k < 13) :
    (BV D γc ρc c Q i).baseTrace ⟨k, hk⟩ = (rowEnvAtD D c Q i).baseTrace ⟨k, hk⟩ := by
  change (envP D γc ρc c Q i).trace k = (envFAtD D c Q i).trace k
  exact pullEnv_trace_lt _ k (by omega)

theorem masks (i : Fin D.N) :
    (BV D γc ρc c Q i).baseTrace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (BV D γc ρc c Q i).baseTrace 12 = (if i = lastRowD D then 1 else 0) := by
  refine ⟨(baseTrace_eq D γc ρc c Q i 11 (by norm_num)).trans (RF.masks i).1, ?_⟩
  rw [show (12 : Fin 13) = ⟨12, by norm_num⟩ from rfl, baseTrace_eq D γc ρc c Q i 12 (by norm_num)]
  have := (RF.masks i).2
  rw [show (⟨12, by norm_num⟩ : Fin 13) = 12 from rfl, this]
  simp only [lastRowD, Fin.ext_iff]

include hchar

theorem one_hot (i : Fin D.N) : ∃ st : State, OneHotSelector (SB D γc ρc c Q i) st :=
  oneHot_of_base15 D.N D.basis _ (RF.obl i).base15 hchar

/-- The one-hot state of row `i`. -/
noncomputable def stAt (i : Fin D.N) : State := Classical.choose (one_hot D γc ρc c Q RF hchar i)

theorem stAt_spec (i : Fin D.N) : OneHotSelector (SB D γc ρc c Q i) (stAt D γc ρc c Q RF hchar i) :=
  Classical.choose_spec (one_hot D γc ρc c Q RF hchar i)

/-- The decoded row label. -/
noncomputable def pubAt (i : Fin D.N) : Pub K := decodePub (BV D γc ρc c Q i) (stAt D γc ρc c Q RF hchar i)

/-- The three hosted child state tags of row `i`. -/
noncomputable def tagsAt (i : Fin D.N) : Fin 3 → K :=
  fun j => (childTagHost curReader (stAt D γc ρc c Q RF hchar i) j).eval (SB D γc ρc c Q i)

theorem hsel_at (i : Fin D.N) :
    ∀ st, (SB D γc ρc c Q i).trace (opCol st) =
      if st = (pubAt D γc ρc c Q RF hchar i).state then 1 else 0 :=
  fun st => stAt_spec D γc ρc c Q RF hchar i st

theorem hsrc_at (i : Fin D.N) :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR curReader (pubAt D γc ρc c Q RF hchar i).state role cc).eval (SB D γc ρc c Q i) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAt D γc ρc c Q RF hchar i) ⟨role, hr⟩) ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_cur,
    OptimizedComputeSameExecution.sourcePubAt_eval_eq_semanticPub _ _ (hsel_at D γc ρc c Q RF hchar i)
      role cc hr hc,
    show pubAt D γc ρc c Q RF hchar i =
      pubOfState (Env.ofSubst computeSubst (SB D γc ρc c Q i)) (stAt D γc ρc c Q RF hchar i) from rfl,
    pubFingerprint_pubOfState, fpCoordinate_fpOf]
  exact (decoded_source_trace (SB D γc ρc c Q i) ⟨role, hr⟩ ⟨cc, hc⟩).symm

include hadj in
theorem hsel_shift (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    ∀ st, (curReader.sel st).eval (shiftNext (SB D γc ρc c Q i)) =
      if st = (pubAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩).state then 1 else 0 := by
  intro st
  show (SB D γc ρc c Q i).traceNext (opCol st) = _
  rw [shift_trace D γc ρc c Q hadj i hi]
  exact hsel_at D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩ st

include hadj in
theorem hsrc_shift (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR curReader (pubAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩).state role cc).eval
          (shiftNext (SB D γc ρc c Q i)) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)
            ⟨role, hr⟩) ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_cur_eval_congr (shift_trace71 D γc ρc c Q hadj i hi) _ role cc hr hc]
  exact hsrc_at D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩ role cc hr hc

include hadj in
theorem htag_shift (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    ∀ j, (childTagHost curReader (pubAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩).state j).eval
        (shiftNext (SB D γc ρc c Q i)) = tagsAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩ j := by
  intro j
  exact childTagHost_cur_eval_congr (shift_trace71 D γc ρc c Q hadj i hi) _ j

omit RF hchar in
theorem hγ_shift (i : Fin D.N) :
    walkGammaChallenge.eval (shiftNext (SB D γc ρc c Q i)) = gamma c.1 := by
  rw [gamma_eval_shift]; exact walkGamma_at D γc ρc c Q i

omit RF hchar in
theorem hα_shift (i : Fin D.N) :
    walkAlphaChallenge.eval (shiftNext (SB D γc ρc c Q i)) = alphaC c.1 := by
  rw [alpha_eval_shift]; exact walkAlpha_at D γc ρc c Q i

include hadj in
theorem nextLabel_eval (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (labelRLC nextReader).eval (SB D γc ρc c Q i) =
      Walk.rlc (gamma c.1) (labelVecOfPub (pubAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)) := by
  rw [labelRLC_next_eval]
  exact labelRLC_eval curReader _ _ _ (hsel_shift D γc ρc c Q hadj RF hchar i hi)
    (hsrc_shift D γc ρc c Q hadj RF hchar i hi) (hγ_shift D γc ρc c Q i)

include hadj in
theorem nextCC_eval (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (childSumCC nextReader).eval (SB D γc ρc c Q i) =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)),
        alphaC c.1 ^ l * Walk.rlc (gamma c.1)
          (childVecN (pubAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)
            (tagsAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩) (l - 1)) := by
  rw [childSumCC_next_eval]
  exact childSumCC_eval curReader _ _ _ _ _ (hsel_shift D γc ρc c Q hadj RF hchar i hi)
    (hsrc_shift D γc ρc c Q hadj RF hchar i hi) (hα_shift D γc ρc c Q i) (hγ_shift D γc ρc c Q i)
    (htag_shift D γc ρc c Q hadj RF hchar i hi)

include hadj in
theorem nextCM_eval (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (selectorCM nextReader).eval (SB D γc ρc c Q i) =
      alphaC c.1 ^ fanoutComp (stAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩) := by
  rw [selectorCM_next_eval]
  exact selectorCM_eval curReader _ _ _ (hsel_shift D γc ρc c Q hadj RF hchar i hi) (hα_shift D γc ρc c Q i)

omit RF hchar in
include hadj in
theorem nextLine_eval (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (finalWalkLine .traceNext).eval (SB D γc ρc c Q i) =
      (finalWalkLine .traceCur).eval (SB D γc ρc c Q ⟨(i : ℕ) + 1, hi⟩) := by
  simp only [finalWalkLine, Expr.eval]
  exact shift_trace D γc ρc c Q hadj i hi _

/-! ## 4. Row 0 and the last row -/

theorem baseTrace11_row0 : (BV D γc ρc c Q (firstRowD D)).baseTrace 11 = 1 := by
  have h := (masks D γc ρc c Q RF (firstRowD D)).1
  simpa using h

theorem initialMask_eq_selector_row0 (st : State) :
    (initialMaskExpr st).eval (SB D γc ρc c Q (firstRowD D)) =
      (SB D γc ρc c Q (firstRowD D)).trace (opCol st) := by
  have hobl := RF.obl (firstRowD D)
  have hlt : opCol st < 11 := by cases st <;> decide
  have hg := hobl.selectorEquality2 (endpointEqualityCheck isFirstVar 20 (opCol st)) (by
    simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨opCol st, hlt, rfl⟩)
  have hfirst : (envP D γc ρc c Q (firstRowD D)).trace 11 = 1 :=
    baseTrace11_row0 D γc ρc c Q RF hchar
  simp only [endpointEqualityCheck, isFirstVar, bv, CoeffExpr.eval, hfirst, one_mul,
    sub_eq_zero] at hg
  have hpub : (SB D γc ρc c Q (firstRowD D)).pub (20 + opCol st) =
      algebraMap F K ((envP D γc ρc c Q (firstRowD D)).pub (20 + opCol st)) := by
    have h1 : ¬ (20 + opCol st < 3) := by omega
    have h2 : 20 ≤ 20 + opCol st ∧ 20 + opCol st < 42 := by omega
    simp only [SB, BV, CorrectedFinalTypedEnv.toSourceEnv, dif_neg h1, dif_pos h2]
    congr 1
    show (envP D γc ρc c Q (firstRowD D)).pub (20 + (20 + opCol st - 20)) = _
    rw [Nat.add_sub_cancel_left]
  have htr : (SB D γc ρc c Q (firstRowD D)).trace (opCol st) =
      algebraMap F K ((envP D γc ρc c Q (firstRowD D)).trace (opCol st)) := by
    rw [SB, source_trace_base _ (opCol st) (by omega)]
    rfl
  simp only [initialMaskExpr, Expr.eval]
  rw [hpub, htr, hg]

theorem hmask_first :
    ∀ st, (firstReader.sel st).eval (SB D γc ρc c Q (firstRowD D)) =
      if st = (pubAt D γc ρc c Q RF hchar (firstRowD D)).state then 1 else 0 := by
  intro st
  show (initialMaskExpr st).eval _ = _
  rw [initialMask_eq_selector_row0 D γc ρc c Q RF hchar st]
  exact hsel_at D γc ρc c Q RF hchar (firstRowD D) st

theorem hsrc_first :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR firstReader (pubAt D γc ρc c Q RF hchar (firstRowD D)).state role cc).eval
          (SB D γc ρc c Q (firstRowD D)) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAt D γc ρc c Q RF hchar (firstRowD D)) ⟨role, hr⟩)
          ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_first]
  exact hsrc_at D γc ρc c Q RF hchar (firstRowD D) role cc hr hc

theorem firstLabel_eval :
    (labelRLC firstReader).eval (SB D γc ρc c Q (firstRowD D)) =
      Walk.rlc (gamma c.1) (labelVecOfPub (pubAt D γc ρc c Q RF hchar (firstRowD D))) :=
  labelRLC_eval firstReader _ _ _ (hmask_first D γc ρc c Q RF hchar) (hsrc_first D γc ρc c Q RF hchar)
    (walkGamma_at D γc ρc c Q (firstRowD D))

theorem firstCC_eval :
    (childSumCC firstReader).eval (SB D γc ρc c Q (firstRowD D)) =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D γc ρc c Q RF hchar (firstRowD D))),
        alphaC c.1 ^ l * Walk.rlc (gamma c.1)
          (childVecN (pubAt D γc ρc c Q RF hchar (firstRowD D)) (tagsAt D γc ρc c Q RF hchar (firstRowD D)) (l - 1)) :=
  childSumCC_eval firstReader _ _ _ _ _ (hmask_first D γc ρc c Q RF hchar)
    (hsrc_first D γc ρc c Q RF hchar)
    (walkAlphaChal_at D γc ρc c Q (firstRowD D)) (walkGamma_at D γc ρc c Q (firstRowD D))
    (fun j => by rw [childTagHost_first]; rfl)

theorem firstCM_eval :
    (selectorCM firstReader).eval (SB D γc ρc c Q (firstRowD D)) =
      alphaC c.1 ^ fanoutComp (stAt D γc ρc c Q RF hchar (firstRowD D)) :=
  selectorCM_eval firstReader _ _ _ (hmask_first D γc ρc c Q RF hchar)
    (walkAlphaChal_at D γc ρc c Q (firstRowD D))

/-! ## 5. The 309 walk sources, evaluated -/

omit RF hchar in
theorem walkCountStep309_eval (env : Env K) :
    walkCountStep309.eval env =
      env.traceNext 303 - env.trace 303 * (selectorCM nextReader).eval env := by
  rw [walkCountStep309, Expr.eval_subst]; rfl

omit RF hchar in
theorem walkAccStep309_eval (env : Env K) :
    walkAccStep309.eval env =
      (finalWalkLine .traceNext).eval env * (labelRLC nextReader).eval env + env.traceNext 306 -
        env.trace 306 - env.trace 303 * (childSumCC nextReader).eval env := by
  rw [walkAccStep309, Expr.eval_subst]; rfl

omit RF hchar in
theorem walkCount1_309_eval (env : Env K) :
    (Trans.walkCount1.subst finalWalkInitialSubst309).eval env =
      env.trace 303 - env.pub 0 * (selectorCM firstReader).eval env := by
  rw [Expr.eval_subst]; rfl

omit RF hchar in
theorem walkAccInit_309_eval (env : Env K) :
    (Trans.walkAccInit.subst finalWalkInitialSubst309).eval env =
      (finalWalkLine .traceCur).eval env * (labelRLC firstReader).eval env + env.trace 306 -
        (env.pub 0 * (childSumCC firstReader).eval env + env.pub 1) := by
  rw [Expr.eval_subst]; rfl

omit RF hchar in
theorem walkOut_309_eval (env : Env K) :
    (Trans.walkOut.subst finalWalkTerminalSubst309).eval env = env.trace 306 := by
  rw [Expr.eval_subst]; rfl

omit RF hchar in
/-- Label / line / coin reads do not touch `W0`/`W1`: they evaluate alike on `SR` and `SB`. -/
theorem SR_eq_SB (i : Fin D.N) (e : Expr) (he : noWalkVars e = true) :
    e.eval (SR D γc ρc c Q i) = e.eval (SB D γc ρc c Q i) :=
  eval_toSourceEnv309_of_noWalkVars (EV D γc ρc c Q i) e he

omit RF hchar in
theorem nw_cmNext : noWalkVars (selectorCM nextReader) = true := by decide
omit RF hchar in
theorem nw_ccNext : noWalkVars (childSumCC nextReader) = true := by decide
omit RF hchar in
theorem nw_lblNext : noWalkVars (labelRLC nextReader) = true := by decide
omit RF hchar in
theorem nw_lineNext : noWalkVars (finalWalkLine .traceNext) = true := by decide
omit RF hchar in
theorem nw_cmFirst : noWalkVars (selectorCM firstReader) = true := by decide
omit RF hchar in
theorem nw_ccFirst : noWalkVars (childSumCC firstReader) = true := by decide
omit RF hchar in
theorem nw_lblFirst : noWalkVars (labelRLC firstReader) = true := by decide
omit RF hchar in
theorem nw_lineCur : noWalkVars (finalWalkLine .traceCur) = true := by decide
omit RF hchar in
theorem nw_walkInv : noWalkVars (walkInv .traceCur) = true := by decide

omit RF hchar in
theorem SR_trace_base (i : Fin D.N) (k : ℕ) (hk : k < 13) :
    (SR D γc ρc c Q i).trace k = algebraMap F K ((BV D γc ρc c Q i).baseTrace ⟨k, hk⟩) := by
  have h3 : k ≠ 303 := by omega
  have h6 : k ≠ 306 := by omega
  simp only [SR, EV, Env309.toSourceEnv, h3, h6, if_false]
  exact source_trace_base _ k hk

omit RF hchar in
theorem lowerW_eval (env : Env309 F K) (e : Expr) (h : (lower309 e).isSome) :
    (lowerW e).eval env = e.eval env.toSourceEnv :=
  (lower309_eval env e _ (lower309_some e h)).symm

/-! ## 6. Row 0 and the last row -/

theorem isFirst_row0 : (BV D γc ρc c Q (firstRowD D)).baseTrace 11 = 1 :=
  baseTrace11_row0 D γc ρc c Q RF hchar

theorem walkLn_row0 :
    (finalWalkLine .traceCur).eval (SB D γc ρc c Q (firstRowD D)) = alphaC c.1 := by
  have hmem : lowerLeaf finalMaskedWalkLn1 ∈ endpoint2_309 := by simp [endpoint2_309]
  have h0 := (RF.obl (firstRowD D)).endpointDegreeTwo _ hmem
  obtain ⟨t, ht⟩ : ∃ t, correctedLowerFinal finalMaskedWalkLn1 = some t :=
    Option.isSome_iff_exists.mp lowerLeaf_total.1
  have h : finalMaskedWalkLn1.eval (SB D γc ρc c Q (firstRowD D)) = 0 := by
    rw [correctedLowerFinal_eval _ _ _ ht]
    simp only [lowerLeaf, ht, Option.getD, WTyped.eval] at h0
    exact h0
  have hm : fixedIsFirst.eval (SB D γc ρc c Q (firstRowD D)) = 1 := by
    simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
      isFirst_row0 D γc ρc c Q RF hchar]
  simp only [finalMaskedWalkLn1, Expr.eval] at h
  rw [hm, one_mul, finalOptimizedWalkLn1] at h
  have heq :
      (Trans.walkLn1.subst finalWalkInitialSubst).eval (SB D γc ρc c Q (firstRowD D)) =
        (finalWalkLine .traceCur).eval (SB D γc ρc c Q (firstRowD D)) -
          (walkChallenge 0).eval (SB D γc ρc c Q (firstRowD D)) := by
    rw [Expr.eval_subst]; rfl
  rw [heq, sub_eq_zero] at h
  rw [h, walkAlpha_at]

theorem isFirst_SR : fixedIsFirst.eval (SR D γc ρc c Q (firstRowD D)) = 1 := by
  simp only [fixedIsFirst, Expr.eval]
  rw [SR_trace_base D γc ρc c Q _ 11 (by norm_num)]
  rw [show (⟨11, by norm_num⟩ : Fin 13) = 11 from rfl, isFirst_row0 D γc ρc c Q RF hchar, map_one]

/-- **`count(1) = initial_count · cm(1)`** on `W0`. -/
theorem walkCount_row0 :
    (SR D γc ρc c Q (firstRowD D)).trace 303 =
      alphaC c.1 * alphaC c.1 ^ fanoutComp (stAt D γc ρc c Q RF hchar (firstRowD D)) := by
  have hmem : lowerW finalMaskedWalkCount1_309 ∈ endpoint2_309 := by simp [endpoint2_309]
  have h0 := (RF.obl (firstRowD D)).endpointDegreeTwo _ hmem
  rw [lowerW_eval _ _ lower309_total.2.2.2.2.1] at h0
  simp only [finalMaskedWalkCount1_309, Expr.eval] at h0
  rw [isFirst_SR D γc ρc c Q RF hchar, one_mul, walkCount1_309_eval, sub_eq_zero,
    SR_eq_SB D γc ρc c Q _ _ nw_cmFirst, firstCM_eval D γc ρc c Q RF hchar] at h0
  rw [h0]
  congr 1
  exact family_initialCount_at D γc ρc c Q _

/-- **The row-0 walk identity on `W1`**. -/
theorem walkAccInit_row0 :
    alphaC c.1 * Walk.rlc (gamma c.1) (labelVecOfPub (pubAt D γc ρc c Q RF hchar (firstRowD D))) +
        (SR D γc ρc c Q (firstRowD D)).trace 306 =
      (∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D γc ρc c Q RF hchar (firstRowD D))),
        alphaC c.1 ^ l * alphaC c.1 * Walk.rlc (gamma c.1)
          (childVecN (pubAt D γc ρc c Q RF hchar (firstRowD D))
            (tagsAt D γc ρc c Q RF hchar (firstRowD D)) (l - 1))) + seedOfClaim D.claim c := by
  have hmem : lowerW finalMaskedWalkAccInit309 ∈ endpoint4_309 := by simp [endpoint4_309]
  have h0 := (RF.obl (firstRowD D)).endpointDegreeFour _ hmem
  rw [lowerW_eval _ _ lower309_total.2.2.2.2.2.2] at h0
  simp only [finalMaskedWalkAccInit309, Expr.eval] at h0
  rw [isFirst_SR D γc ρc c Q RF hchar, one_pow, one_mul, walkAccInit_309_eval, sub_eq_zero,
    SR_eq_SB D γc ρc c Q _ _ nw_lineCur, SR_eq_SB D γc ρc c Q _ _ nw_lblFirst,
    SR_eq_SB D γc ρc c Q _ _ nw_ccFirst, walkLn_row0 D γc ρc c Q RF hchar,
    firstLabel_eval D γc ρc c Q RF hchar, firstCC_eval D γc ρc c Q RF hchar] at h0
  have hp0 : (SR D γc ρc c Q (firstRowD D)).pub 0 = alphaC c.1 :=
    family_initialCount_at D γc ρc c Q _
  have hp1 : (SR D γc ρc c Q (firstRowD D)).pub 1 = seedOfClaim D.claim c :=
    family_seed_at D γc ρc c Q _
  rw [hp0, hp1, Finset.mul_sum] at h0
  rw [h0]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isLast_SR : fixedIsLast.eval (SR D γc ρc c Q (lastRowD D)) = 1 := by
  simp only [fixedIsLast, Expr.eval]
  rw [SR_trace_base D γc ρc c Q _ 12 (by norm_num)]
  have := (masks D γc ρc c Q RF (lastRowD D)).2
  rw [if_pos rfl] at this
  rw [show (⟨12, by norm_num⟩ : Fin 13) = 12 from rfl, this, map_one]

/-- **`out_walk = acc(h) = 0`** on `W1`. -/
theorem walkOut_last : (SR D γc ρc c Q (lastRowD D)).trace 306 = 0 := by
  have hmem : lowerW finalMaskedWalkOut309 ∈ endpoint2_309 := by simp [endpoint2_309]
  have h0 := (RF.obl (lastRowD D)).endpointDegreeTwo _ hmem
  rw [lowerW_eval _ _ lower309_total.2.2.2.2.2.1] at h0
  simp only [finalMaskedWalkOut309, Expr.eval] at h0
  rw [isLast_SR D γc ρc c Q RF hchar, one_mul, walkOut_309_eval] at h0
  exact h0

/-! ## 7. The steps -/

theorem notLast (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) : (BV D γc ρc c Q i).baseTrace 12 = 0 := by
  rw [(masks D γc ρc c Q RF i).2, if_neg]
  intro heq
  have hv : (i : ℕ) = D.N - 1 := congrArg Fin.val heq
  omega

theorem sources (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    DecodedTransitionSourcesVCL (EV D γc ρc c Q i) :=
  conditional_transition_soundness_vcl (RF.obl i) (notLast D γc ρc c Q RF hchar i hi)

include hadj in
theorem walkLn_step (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (finalWalkLine .traceCur).eval (SB D γc ρc c Q ⟨(i : ℕ) + 1, hi⟩) =
      alphaC c.1 * (finalWalkLine .traceCur).eval (SB D γc ρc c Q i) := by
  have hm : Trans.walkLnStep.subst ComputeWalkLabel.finalWalkSubstInGate ∈ paperPackingCoreGates309 := by
    simp [paperPackingCoreGates309, crossRowSingletons309]
  have h := (sources D γc ρc c Q RF hchar i hi).nonIO _ hm
  rw [SR_eq_SB D γc ρc c Q i _ (by decide), SVCompute.walkLnStep_inGate_eval, sub_eq_zero,
    nextLine_eval D γc ρc c Q hadj i hi, walkAlpha_at] at h
  exact h

include hadj in
theorem walkCount_step (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (SR D γc ρc c Q ⟨(i : ℕ) + 1, hi⟩).trace 303 =
      (SR D γc ρc c Q i).trace 303 *
        alphaC c.1 ^ fanoutComp (stAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩) := by
  have hm : walkCountStep309 ∈ paperPackingCoreGates309 := by
    simp [paperPackingCoreGates309, crossRowSingletons309]
  have h := (sources D γc ρc c Q RF hchar i hi).nonIO _ hm
  rw [walkCountStep309_eval, sub_eq_zero, SR_eq_SB D γc ρc c Q i _ nw_cmNext,
    nextCM_eval D γc ρc c Q hadj RF hchar i hi,
    shift_walk D γc ρc c Q hadj i hi 303 (Or.inl rfl)] at h
  exact h

include hadj in
theorem walkAcc_step (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (finalWalkLine .traceCur).eval (SB D γc ρc c Q ⟨(i : ℕ) + 1, hi⟩) *
        Walk.rlc (gamma c.1) (labelVecOfPub (pubAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)) +
        (SR D γc ρc c Q ⟨(i : ℕ) + 1, hi⟩).trace 306 - (SR D γc ρc c Q i).trace 306 =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)),
        alphaC c.1 ^ l * (SR D γc ρc c Q i).trace 303 *
          Walk.rlc (gamma c.1) (childVecN (pubAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩)
            (tagsAt D γc ρc c Q RF hchar ⟨(i : ℕ) + 1, hi⟩) (l - 1)) := by
  have hm : walkAccStep309 ∈ paperPackingCoreGates309 := by
    simp [paperPackingCoreGates309, crossRowSingletons309]
  have h := (sources D γc ρc c Q RF hchar i hi).nonIO _ hm
  rw [walkAccStep309_eval, SR_eq_SB D γc ρc c Q i _ nw_lineNext,
    SR_eq_SB D γc ρc c Q i _ nw_lblNext, SR_eq_SB D γc ρc c Q i _ nw_ccNext,
    nextLine_eval D γc ρc c Q hadj i hi, nextLabel_eval D γc ρc c Q hadj RF hchar i hi,
    nextCC_eval D γc ρc c Q hadj RF hchar i hi,
    shift_walk D γc ρc c Q hadj i hi 306 (Or.inr rfl), Finset.mul_sum] at h
  have h' := sub_eq_zero.mp h
  rw [h']
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ## 8. The `WalkSat` assembly -/

noncomputable def lnW (i : ℕ) : K := (finalWalkLine .traceCur).eval (SB D γc ρc c Q (rowOfD D i))
noncomputable def countW (i : ℕ) : K := (SR D γc ρc c Q (rowOfD D i)).trace 303
noncomputable def accW (i : ℕ) : K := (SR D γc ρc c Q (rowOfD D i)).trace 306
noncomputable def curW (i : ℕ) : K :=
  Walk.rlc (gamma c.1) (labelVecOfPub (pubAt D γc ρc c Q RF hchar (rowOfD D i)))
noncomputable def chldW (i l : ℕ) : K :=
  Walk.rlc (gamma c.1)
    (childVecN (pubAt D γc ρc c Q RF hchar (rowOfD D i)) (tagsAt D γc ρc c Q RF hchar (rowOfD D i)) (l - 1))
noncomputable def foW (i : ℕ) : ℕ := fanoutComp (stAt D γc ρc c Q RF hchar (rowOfD D i))

include hadj in
/-- **`WalkSat` of the VCL compute walk on `W0`/`W1`**: `α = alphaC c.1`,
`seed = seedOfClaim`, `initial_count = alphaC c.1`, over `D.N` rows, at the decoded labels, the
declared child payloads and the decoded fanouts — the twin of `deployed_walkSatD`. -/
theorem vcl_walkSat :
    WalkSat (curW D γc ρc c Q RF hchar) (chldW D γc ρc c Q RF hchar) (foW D γc ρc c Q RF hchar)
      (lnW D γc ρc c Q) (countW D γc ρc c Q) (accW D γc ρc c Q) (alphaC c.1)
      (seedOfClaim D.claim c) (alphaC c.1) D.N := by
  have hpos : 1 ≤ D.N := D.hN
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (finalWalkLine .traceCur).eval (SB D γc ρc c Q (rowOfD D 1)) = alphaC c.1
    rw [rowOf_oneD]
    exact walkLn_row0 D γc ρc c Q RF hchar
  · intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < D.N := by omega
    have hk1 : k + 1 < D.N := by omega
    show (finalWalkLine .traceCur).eval (SB D γc ρc c Q (rowOfD D (k + 1 + 1))) =
      alphaC c.1 * (finalWalkLine .traceCur).eval (SB D γc ρc c Q (rowOfD D (k + 1)))
    rw [rowOf_succD D (k + 1) hk1, rowOf_succD D k hk]
    exact walkLn_step D γc ρc c Q hadj RF hchar ⟨k, hk⟩ hk1
  · show (SR D γc ρc c Q (rowOfD D 1)).trace 303 =
      alphaC c.1 * alphaC c.1 ^ fanoutComp (stAt D γc ρc c Q RF hchar (rowOfD D 1))
    rw [rowOf_oneD]
    exact walkCount_row0 D γc ρc c Q RF hchar
  · intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < D.N := by omega
    have hk1 : k + 1 < D.N := by omega
    show (SR D γc ρc c Q (rowOfD D (k + 1 + 1))).trace 303 =
      (SR D γc ρc c Q (rowOfD D (k + 1))).trace 303 *
        alphaC c.1 ^ fanoutComp (stAt D γc ρc c Q RF hchar (rowOfD D (k + 1 + 1)))
    rw [rowOf_succD D (k + 1) hk1, rowOf_succD D k hk]
    exact walkCount_step D γc ρc c Q hadj RF hchar ⟨k, hk⟩ hk1
  · show (finalWalkLine .traceCur).eval (SB D γc ρc c Q (rowOfD D 1)) *
        Walk.rlc (gamma c.1) (labelVecOfPub (pubAt D γc ρc c Q RF hchar (rowOfD D 1))) +
        (SR D γc ρc c Q (rowOfD D 1)).trace 306 =
      (∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D γc ρc c Q RF hchar (rowOfD D 1))),
        alphaC c.1 ^ l * alphaC c.1 *
          Walk.rlc (gamma c.1)
            (childVecN (pubAt D γc ρc c Q RF hchar (rowOfD D 1))
              (tagsAt D γc ρc c Q RF hchar (rowOfD D 1)) (l - 1)))
        + seedOfClaim D.claim c
    rw [rowOf_oneD, walkLn_row0 D γc ρc c Q RF hchar]
    exact walkAccInit_row0 D γc ρc c Q RF hchar
  · intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < D.N := by omega
    have hk1 : k + 1 < D.N := by omega
    show (finalWalkLine .traceCur).eval (SB D γc ρc c Q (rowOfD D (k + 1 + 1))) *
        Walk.rlc (gamma c.1) (labelVecOfPub (pubAt D γc ρc c Q RF hchar (rowOfD D (k + 1 + 1)))) +
        (SR D γc ρc c Q (rowOfD D (k + 1 + 1))).trace 306 -
        (SR D γc ρc c Q (rowOfD D (k + 1))).trace 306 =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D γc ρc c Q RF hchar (rowOfD D (k + 1 + 1)))),
        alphaC c.1 ^ l * (SR D γc ρc c Q (rowOfD D (k + 1))).trace 303 *
          Walk.rlc (gamma c.1)
            (childVecN (pubAt D γc ρc c Q RF hchar (rowOfD D (k + 1 + 1)))
              (tagsAt D γc ρc c Q RF hchar (rowOfD D (k + 1 + 1))) (l - 1))
    rw [rowOf_succD D (k + 1) hk1, rowOf_succD D k hk]
    exact walkAcc_step D γc ρc c Q hadj RF hchar ⟨k, hk⟩ hk1

/-- **`out_walk = 0`** (`ℕ`-indexed). -/
theorem vcl_walk_out : accW D γc ρc c Q D.N = 0 := by
  show (SR D γc ρc c Q (rowOfD D D.N)).trace 306 = 0
  rw [rowOf_rowsD]
  exact walkOut_last D γc ρc c Q RF hchar

/-! ## 9. The queue witness: `BFSValid` and the tiling -/

theorem queueNonEmpty_SR (i : Fin D.N) : walkQueueNonEmpty309.eval (SR D γc ρc c Q i) = 0 := by
  have h := (queue_sources_vcl (RF.obl i)).1
  rwa [queueNonEmpty309, lowerW_eval _ _ lower309_total.2.2.1] at h

theorem queueTiling_SR (i : Fin D.N) : walkQueueTiling309.eval (SR D γc ρc c Q i) = 0 := by
  have h := (queue_sources_vcl (RF.obl i)).2
  rwa [queueTiling309, lowerW_eval _ _ lower309_total.2.2.2.1] at h

theorem count_ne_ln (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    countW D γc ρc c Q ((i : ℕ) + 1) ≠ lnW D γc ρc c Q ((i : ℕ) + 1) := by
  have hgate := queueNonEmpty_SR D γc ρc c Q RF hchar i
  have h12 : (SR D γc ρc c Q i).trace 12 = 0 := by
    rw [SR_trace_base D γc ρc c Q i 12 (by norm_num)]
    rw [show (⟨12, by norm_num⟩ : Fin 13) = 12 from rfl, notLast D γc ρc c Q RF hchar i hi, map_zero]
  have hrow : rowOfD D ((i : ℕ) + 1) = i := rowOf_succD D (i : ℕ) i.isLt
  rw [countW, lnW, hrow]
  simp only [walkQueueNonEmpty309, Expr.eval, h12] at hgate
  rw [SR_eq_SB D γc ρc c Q i _ nw_walkInv, SR_eq_SB D γc ρc c Q i _ nw_lineCur] at hgate
  intro heq
  simp only [walkCountCol] at hgate
  rw [heq] at hgate
  simp at hgate

theorem count_eq_ln_last : countW D γc ρc c Q D.N = lnW D γc ρc c Q D.N := by
  have hgate := queueTiling_SR D γc ρc c Q RF hchar (lastRowD D)
  have hrow : rowOfD D D.N = lastRowD D := rowOf_rowsD D
  rw [countW, lnW, hrow]
  have hl := isLast_SR D γc ρc c Q RF hchar
  simp only [fixedIsLast, Expr.eval] at hl
  simp only [walkQueueTiling309, Expr.eval, hl, one_mul, walkCountCol] at hgate
  rw [SR_eq_SB D γc ρc c Q _ _ nw_lineCur] at hgate
  exact sub_eq_zero.mp hgate

include hadj in
/-- **Queue validity** (`Batch478.bfsValid_of_ratio_gate`), no condition on `α`. -/
theorem vcl_bfsValid : BFSValid (foW D γc ρc c Q RF hchar) D.N := by
  have hw := vcl_walkSat D γc ρc c Q hadj RF hchar
  refine bfsValid_of_ratio_gate (K := K) (α := alphaC c.1) ?_
  intro i hi1 hih
  have hk : i - 1 < D.N := by omega
  let k : Fin D.N := ⟨i - 1, hk⟩
  have hki : (k : ℕ) + 1 = i := Nat.sub_add_cancel hi1
  have hne := count_ne_ln D γc ρc c Q RF hchar k (by omega)
  have hcnt := Walk.count_closed hw i hi1 (le_of_lt hih)
  have hln := Walk.ln_closed hw i hi1 (le_of_lt hih)
  rw [hki] at hne
  rw [hcnt, hln] at hne
  rw [pow_add, pow_one]
  exact hne

include hadj in
/-- **The tiling outside the priced event** (`computeTilingEvent`). -/
theorem vcl_tiling (hα : c.1 ∉ computeTilingEvent (foW D γc ρc c Q RF hchar) D.N) :
    Sf (foW D γc ρc c Q RF hchar) D.N + 1 = D.N := by
  have hw := vcl_walkSat D γc ρc c Q hadj RF hchar
  have hterm := count_eq_ln_last D γc ρc c Q RF hchar
  have hcnt := Walk.count_closed hw D.N hw.hpos le_rfl
  have hln := Walk.ln_closed hw D.N hw.hpos le_rfl
  have hpow : alphaC c.1 ^ (1 + Sf (foW D γc ρc c Q RF hchar) D.N) = alphaC c.1 ^ D.N := by
    rw [pow_add, pow_one, ← hcnt, ← hln]
    exact hterm
  by_contra hne
  exact hα ((mem_computeTilingEvent_iff (foW D γc ρc c Q RF hchar) D.N c.1).2 ⟨hpow, by omega⟩)

/-- **`V_comp` at every row of the layout, with the `z·z⁻¹` pin discharged** (`nprSeed c.1 ≠ 0`):
`rowFactsP_vcomp` without its `hzZ` premise. -/
theorem vcomp_at (hz : nprSeed c.1 ≠ 0) (i : Fin D.N) : VcompAt (BV D γc ρc c Q i) :=
  rowFactsP_vcomp γc ρc D c Q RF hchar i (zZinv_at D γc ρc c Q i hz)

end

end WalkVCL
end VclL.Compute
end Nock.NockVMROM.Thm54
