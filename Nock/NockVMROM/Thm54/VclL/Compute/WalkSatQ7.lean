import Nock.NockVMROM.Thm54.VclL.Compute.PatchQ7
import Nock.NockVMROM.Thm54.VclL.Compute.RootBindsVCL
import Nock.NockVMROM.Thm54.VclL.Compute.CoordGatherQ7

/-!
# V4T3 step (c) : the compute walk, `root_binds` and `V_comp` at the Q7 chip, coin-map parametric

.

* the walk coins are the slots they occupy (`alphaQ` = slot 6, `gammaQ` = slot 10, `zQ` = slot 1),
  the walk publics the limbs they occupy (`initQ` = public 0, `seedQ` = public 1); nothing assumes a
  coin map, so route (d)'s extension of `chalVQ7` leaves every lemma here unchanged;
* **`lnChain`-free**: the walk steps come from `walk_sources_q7` (core `73` `walkLn`, the `W0`/`W1`
  recurrences through core `74`/`75` + the residual aux sources), never from the deleted `50`, `58`,
  `65`, `72`, `78`; the row-0 identities from `endpoint2Q7` / `endpoint4_309`;
* `RowFactsQ7.of_sat`: acceptance at `computeChipVCLQ7` gives the row facts (`VclSourceObligationsQ7`
  + masks), with injective nodes only;
* **`q7_walkSat`**, `q7_walk_out`, `q7_bfsValid`, `q7_tiling`, **`q7_root_binds`** (given
  `initQ = alphaQ` and `seedQ = RLC^γ(claim label)·α`, the frame's publics), `vcomp_at` (patched row);
* at `frameVCL` coins (`chalVQ7`, `pubVQ7`): `frame_root_binds`, `frame_vcomp_at` — the two
  publics hypotheses discharged by `pubVQ7`'s definition (walk coins `χ0` = `αC`, `χ1` = walk `γ`,
  NPR seed `χ2`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace WalkQ7

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
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Nock.NockVMROM.Thm54.ComputeWalkRootEvents
open Nock.NockVMROM.Thm54.MonolithicRAP

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {h : ℕ}

/-! ## 0. The `lnChain`-free walk sources at the Q7 obligations -/

theorem mem_keptCoreIdsQ7 (i : CorrectedCoreExtGateId) (h79 : i.val ≠ 79) (h80 : i.val ≠ 80)
    (h50 : i.val ≠ 50) (h58 : i.val ≠ 58) (h65 : i.val ≠ 65) (h72 : i.val ≠ 72) (h78 : i.val ≠ 78) :
    i ∈ keptCoreIdsQ7 := by
  simp only [keptCoreIdsQ7, keptCoreIds, List.mem_filter, List.mem_finRange, true_and,
    formRCoreIds, deletedCoreIds]
  simp; omega

/-- Every kept Q7 core position (other than the walk / queue wrappers) vanishes on a nonterminal row. -/
theorem ext_gate_zero_q7 {n : ℕ} {env : Env309 F K} {envF : Env F}
    (hsource : VclSourceObligationsQ7 n env envF) (hnotLast : env.base.baseTrace 12 = 0)
    (i : CorrectedCoreExtGateId) (hi : i ∈ keptCoreIdsQ7)
    (h74 : i ≠ packedWalkCountId) (h75 : i ≠ packedWalkAccId)
    (h76 : i ≠ packedQueueNonEmptyId) (h77 : i ≠ packedQueueTilingId) :
    (correctedFinalExtGate i).eval env.base = 0 := by
  have hc := hsource.extensionCore i hi
  simp only [coreSemValue309, h76, h77, if_false] at hc
  by_cases h20 : i = packedChainId
  · subst i
    have ha := hsource.residualAux 2
    simp only [auxSemValue309, correctedAuxSemanticValue] at ha
    have hchain : env.base.extTrace 60 = env.base.extTraceNext 32 := by
      simpa [correctedCoreSemanticValue, packedWalkCountId, packedWalkAccId, packedChainId,
        packedLnChainId, packedWalkLnId, accAfterChain,
        CorrectedFinalTypedExpr.eval, hnotLast, sub_eq_zero] using hc
    rw [← correctedAccAfterStep_eval_eq_fold env.base hchain]
    exact ha
  by_cases h89 : i = packedLnChainId ∨ i = packedWalkLnId
  · simp only [correctedCoreSemanticValue] at hc
    simp only [h74, h75, h20, h89, ↓reduceIte, notLastScalar, hnotLast, sub_zero, map_one,
      one_mul] at hc
    exact hc
  · simp only [correctedCoreSemanticValue] at hc
    simp only [h74, h75, h20, h89, ↓reduceIte] at hc
    exact hc

/-- **The walk sources the walk needs** (no `lnChain`, no per-state `ln` recurrence). -/
structure WalkSourcesQ7 (env : Env309 F K) : Prop where
  walkLn : (Trans.walkLnStep.subst ComputeWalkLabel.finalWalkSubstInGate).eval env.toSourceEnv = 0
  count : walkCountStep309.eval env.toSourceEnv = 0
  acc : walkAccStep309.eval env.toSourceEnv = 0

theorem walk_sources_q7 {n : ℕ} {env : Env309 F K} {envF : Env F}
    (hsource : VclSourceObligationsQ7 n env envF) (hnotLast : env.base.baseTrace 12 = 0) :
    WalkSourcesQ7 env := by
  have hres : ∀ j : Fin 2, (residualSource309 j).eval env = 0 := by
    intro j
    have hj2 : (⟨j.val, by omega⟩ : CorrectedResidualWitnessId) ≠ 2 := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have ha := hsource.residualAux ⟨j.val, by omega⟩
    have hidx : aux309Idx ⟨j.val, by omega⟩ hj2 = j := Fin.ext rfl
    simp only [auxSemValue309, dif_neg hj2, hidx, sub_eq_zero] at ha
    fin_cases j
    · have hc := hsource.extensionCore packedWalkCountId
        (mem_keptCoreIdsQ7 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
      simp [coreSemValue309, correctedCoreSemanticValue, notLastScalar, hnotLast,
        packedWalkCountId, packedWalkAccId, packedQueueNonEmptyId, packedQueueTilingId] at hc
      rw [← ha]
      simpa [OptimizedComputeCorrectedFinal.residualWitnessRole] using hc
    · have hc := hsource.extensionCore packedWalkAccId
        (mem_keptCoreIdsQ7 _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))
      simp [coreSemValue309, correctedCoreSemanticValue, notLastScalar, hnotLast,
        packedWalkCountId, packedWalkAccId, packedQueueNonEmptyId, packedQueueTilingId] at hc
      rw [← ha]
      simpa [OptimizedComputeCorrectedFinal.residualWitnessRole] using hc
  refine ⟨?_, ?_, ?_⟩
  · have h73 : finalExtTransitionGates.get ⟨73, by decide⟩ =
        Trans.walkLnStep.subst ComputeWalkLabel.finalWalkSubstInGate := by decide
    rw [← h73, eval_toSourceEnv309_of_noWalkVars env _
      (finalExtTransitionGates_noWalkVars _ (List.get_mem _ _))]
    have := correctedFinalExtGate_eval_source env.base ⟨73, by decide⟩
    simp only at this
    rw [this]
    exact ext_gate_zero_q7 hsource hnotLast ⟨73, by decide⟩
      (mem_keptCoreIdsQ7 _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) (by decide) (by decide) (by decide) (by decide)
  · rw [lower309_eval env _ _ (lower309_some _ lower309_total.1)]
    exact hres 0
  · rw [lower309_eval env _ _ (lower309_some _ lower309_total.2.1)]
    exact hres 1

/-- **The queue witness at the Q7 obligations, on every row** (core `76`/`77`, kept). -/
theorem queue_sources_q7 {n : ℕ} {env : Env309 F K} {envF : Env F}
    (hsource : VclSourceObligationsQ7 n env envF) :
    queueNonEmpty309.eval env = 0 ∧ queueTiling309.eval env = 0 := by
  have h1 := hsource.extensionCore packedQueueNonEmptyId
    (mem_keptCoreIdsQ7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
  have h2 := hsource.extensionCore packedQueueTilingId
    (mem_keptCoreIdsQ7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
  simp only [coreSemValue309, ↓reduceIte] at h1
  have hne : packedQueueTilingId ≠ packedQueueNonEmptyId := by decide
  simp only [coreSemValue309, hne, ↓reduceIte] at h2
  exact ⟨h1, h2⟩

/-! ## 1. The row environments, the row facts, the coins as slots -/

variable (D : ChipDataG F K h) (chalV pubVal : ℕ → F) {w : ℕ} (Q : Fin w → F[X])

/-- The walk coin `α` (compute slot `6`). -/
def alphaQ : K := D.G.chalSlot chalV 6
/-- The walk RLC coin `γ` (compute slot `10`). -/
def gammaQ : K := D.G.chalSlot chalV 10
/-- The NPR seed `z` (compute slot `1`). -/
def zQ : K := D.G.chalSlot chalV 1
/-- The walk's `initial_count` public (public `0`). -/
def initQ : K := D.G.pubSlot pubVal 0
/-- The walk seed public (public `1`). -/
def seedQ : K := D.G.pubSlot pubVal 1

/-- The raw row env of row `i`. -/
def envQ (i : Fin D.N) : Env F := envOfTrace Q D.orbit.ω (D.nodes i) chalV pubVal

/-- **The Q7 row facts**: the Q7 obligations at every row's 309-shaped pull-back, and the masks. -/
structure RowFactsQ7 : Prop where
  obl : ∀ i : Fin D.N, VclSourceObligationsQ7 D.N (D.G.env309 (pullEnv (envQ D chalV pubVal Q i)))
    (pullEnv (envQ D chalV pubVal Q i))
  masks : ∀ i : Fin D.N,
    (envQ D chalV pubVal Q i).trace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (envQ D chalV pubVal Q i).trace 12 = (if (i : ℕ) = D.N - 1 then 1 else 0)

/-- **Acceptance at `computeChipVCLQ7` gives the Q7 row facts** (injective nodes only). -/
theorem RowFactsQ7.of_sat (Q : Fin vclWidthE → F[X]) (D0 : ChipData F K h) (γc ρc : ℕ) (hinj : D0.Injective)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipVCLQ7 D0.hN D0.nodes D0.basis γc ρc chalV pubVal D0.orbit) Q) :
    RowFactsQ7 D0.toG chalV pubVal Q := by
  have hs := (computeChipVCLQ7_sat_iff D0.hN D0.nodes D0.basis γc ρc chalV pubVal D0.orbit Q).1 hsat
  have hmem : ∀ i : Fin D0.N, D0.nodes i ∈ rowNodeSet D0.nodes := fun i => by simp [rowNodeSet]
  have h11 : (11 : ℕ) < vclWidthE := by norm_num [vclWidthE]
  have h12 : (12 : ℕ) < vclWidthE := by norm_num [vclWidthE]
  have m0 : Q ⟨11, h11⟩ = firstRowMask D0.nodes := hs.1 ⟨0, by change 0 < 2; norm_num⟩
  have m1 : Q ⟨12, h12⟩ = lastRowMask D0.hN D0.nodes := hs.1 ⟨1, by change 1 < 2; norm_num⟩
  refine ⟨fun i => VclSourceObligationsQ7.of_vclGatesQ7 D0.N D0.basis γc ρc _ (hs.2 _ (hmem i)),
    fun (i : Fin D0.N) => ⟨?_, ?_⟩⟩
  · simp only [envQ, envOfTrace, dif_pos h11, SVCompute.ChipData.toG]
    rw [m0, Nock.Framework.firstRowMask_eval _ hinj]
  · simp only [envQ, envOfTrace, dif_pos h12, SVCompute.ChipData.toG]
    rw [m1, Nock.Framework.lastRowMask_eval _ _ hinj]
    simp only [Fin.ext_iff]
    first | rfl | congr

/-- The pulled-back base row env (309 layout) of row `i`. -/
abbrev envP (i : Fin D.N) : Env F := pullEnv (envQ D chalV pubVal Q i)
abbrev BV (i : Fin D.N) : CorrectedFinalTypedEnv F K := (D.G.env309 (envP D chalV pubVal Q i)).base
abbrev EV (i : Fin D.N) : Env309 F K := D.G.env309 (envP D chalV pubVal Q i)
abbrev SB (i : Fin D.N) : Env K := (BV D chalV pubVal Q i).toSourceEnv
abbrev SR (i : Fin D.N) : Env K := (EV D chalV pubVal Q i).toSourceEnv

/-- Challenge slot `q < 12` of the decoded row is the slot value of `chalV`. -/
theorem SB_chal (i : Fin D.N) (q : ℕ) (hq : q < 12) :
    (SB D chalV pubVal Q i).chal q = D.G.chalSlot chalV q := by
  simp only [SB, BV, CorrectedFinalTypedEnv.toSourceEnv, hq, ↓reduceDIte]
  exact D.G.chal_eq (envP D chalV pubVal Q i) ⟨q, hq⟩

theorem zZinv_at (i : Fin D.N) (hz : zQ D chalV ≠ 0)
    (hzi : D.G.chalSlot chalV 5 = (zQ D chalV)⁻¹) :
    (zZinvExpr.subst computeSubst).eval (SB D chalV pubVal Q i) = 0 := by
  have h1 := SB_chal D chalV pubVal Q i 1 (by norm_num)
  have h5 := SB_chal D chalV pubVal Q i 5 (by norm_num)
  simp [zZinvExpr, Expr.subst, computeSubst, computeTraceSubst, chl, tc, Expr.eval, h1, h5]
  rw [hzi, show D.G.chalSlot chalV 1 = zQ D chalV from rfl, mul_inv_cancel₀ hz, sub_self]

theorem walkGamma_at (i : Fin D.N) : walkGammaChallenge.eval (SB D chalV pubVal Q i) = gammaQ D chalV := by
  have h := SB_chal D chalV pubVal Q i 10 (by norm_num)
  simpa [walkGammaChallenge, walkGammaChallengeIndex, Expr.eval, gammaQ] using h

theorem walkAlpha_at (i : Fin D.N) : (walkChallenge 0).eval (SB D chalV pubVal Q i) = alphaQ D chalV := by
  have h := SB_chal D chalV pubVal Q i 6 (by norm_num)
  simpa [walkChallenge, walkChallengeBase, Expr.eval, alphaQ] using h

theorem walkAlphaChal_at (i : Fin D.N) : walkAlphaChallenge.eval (SB D chalV pubVal Q i) = alphaQ D chalV :=
  walkAlpha_at D chalV pubVal Q i

theorem family_seed_at (i : Fin D.N) : (SB D chalV pubVal Q i).pub 1 = seedQ D pubVal := by
  have h1 : (1 : ℕ) < 3 := by norm_num
  simp only [SB, BV, CorrectedFinalTypedEnv.toSourceEnv, dif_pos h1]
  exact D.G.pub_eq (envP D chalV pubVal Q i) ⟨1, h1⟩

theorem family_initialCount_at (i : Fin D.N) : (SB D chalV pubVal Q i).pub 0 = initQ D pubVal := by
  have h0 : (0 : ℕ) < 3 := by norm_num
  simp only [SB, BV, CorrectedFinalTypedEnv.toSourceEnv, dif_pos h0]
  exact D.G.pub_eq (envP D chalV pubVal Q i) ⟨0, h0⟩


/-! ## 2. The shift (row adjacency) -/

variable (hadj : D.Adjacent)

include hadj in
theorem envF_traceNext_eq (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) (j : ℕ) :
    (envQ D chalV pubVal Q i).traceNext j = (envQ D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩).trace j := by
  have hadj := hadj i hi
  simp only [envQ, envOfTrace]
  split_ifs with h
  · rw [hadj]
  · rfl

include hadj in
theorem envP_traceNext_eq (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) (j : ℕ) :
    (envP D chalV pubVal Q i).traceNext j = (envP D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩).trace j := by
  simp only [envP, pullEnv]
  exact envF_traceNext_eq D chalV pubVal Q hadj i hi _

include hadj in
theorem shift_trace (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) (j : ℕ) (hj : j < 76) :
    (SB D chalV pubVal Q i).traceNext j = (SB D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩).trace j := by
  have hsh := (D.G.shift (envP D chalV pubVal Q i) (envP D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩)
    (fun c => (envP_traceNext_eq D chalV pubVal Q hadj i hi c).symm)).1
  simp only [SB, BV, CorrectedFinalTypedEnv.toSourceEnv]
  by_cases h13 : j < 13
  · simp only [dif_pos h13]
    congr 1
    rw [D.G.baseNext_eq, D.G.base_eq]
    exact envP_traceNext_eq D chalV pubVal Q hadj i hi j
  · simp only [dif_neg h13, dif_pos hj]
    exact (congrFun hsh ⟨j - 13, by omega⟩).symm

include hadj in
theorem shift_trace71 (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    ∀ j, j < 71 → (shiftNext (SB D chalV pubVal Q i)).trace j = (SB D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩).trace j :=
  fun j hj => shift_trace D chalV pubVal Q hadj i hi j (by omega)

include hadj in
/-- The walk columns shift: `W(i).next = W(i+1)`. -/
theorem shift_walk (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) (j : ℕ) (hj : j = 303 ∨ j = 306) :
    (SR D chalV pubVal Q i).traceNext j = (SR D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩).trace j := by
  have hsh := (D.G.shift (envP D chalV pubVal Q i) (envP D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩)
    (fun c => (envP_traceNext_eq D chalV pubVal Q hadj i hi c).symm)).2
  rcases hj with rfl | rfl <;>
  · simp only [SR, EV, Env309.toSourceEnv, if_true, if_false]
    try simp only [show (306 : ℕ) ≠ 303 by norm_num, if_false, if_true]
    first
    | exact (congrFun hsh 0).symm
    | exact (congrFun hsh 1).symm

/-! ## 3. The row facts, the one-hot state and the decoded labels -/

variable (RF : RowFactsQ7 D chalV pubVal Q)
variable (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)

include RF

theorem obl (i : Fin D.N) : VclSourceObligationsQ7 D.N (EV D chalV pubVal Q i) (envP D chalV pubVal Q i) := RF.obl i

omit RF in
theorem baseTrace_eq (i : Fin D.N) (k : ℕ) (hk : k < 13) :
    (BV D chalV pubVal Q i).baseTrace ⟨k, hk⟩ = (envQ D chalV pubVal Q i).trace k := by
  exact (D.G.base_eq (envP D chalV pubVal Q i) ⟨k, hk⟩).trans (pullEnv_trace_lt _ k (by omega))

theorem masks (i : Fin D.N) :
    (BV D chalV pubVal Q i).baseTrace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (BV D chalV pubVal Q i).baseTrace 12 = (if i = lastRowG D then 1 else 0) := by
  refine ⟨(baseTrace_eq D chalV pubVal Q i 11 (by norm_num)).trans (RF.masks i).1, ?_⟩
  rw [show (12 : Fin 13) = ⟨12, by norm_num⟩ from rfl, baseTrace_eq D chalV pubVal Q i 12 (by norm_num),
    (RF.masks i).2]
  simp only [lastRowG, Fin.ext_iff]

include hchar

theorem one_hot (i : Fin D.N) : ∃ st : State, OneHotSelector (SB D chalV pubVal Q i) st :=
  oneHot_of_base15G D.G D.N _ (RF.obl i).base15 hchar

/-- The one-hot state of row `i`. -/
noncomputable def stAt (i : Fin D.N) : State := Classical.choose (one_hot D chalV pubVal Q RF hchar i)

theorem stAt_spec (i : Fin D.N) : OneHotSelector (SB D chalV pubVal Q i) (stAt D chalV pubVal Q RF hchar i) :=
  Classical.choose_spec (one_hot D chalV pubVal Q RF hchar i)

/-- The decoded row label. -/
noncomputable def pubAt (i : Fin D.N) : Pub K := decodePub (BV D chalV pubVal Q i) (stAt D chalV pubVal Q RF hchar i)

/-- The three hosted child state tags of row `i`. -/
noncomputable def tagsAt (i : Fin D.N) : Fin 3 → K :=
  fun j => (childTagHost curReader (stAt D chalV pubVal Q RF hchar i) j).eval (SB D chalV pubVal Q i)

theorem hsel_at (i : Fin D.N) :
    ∀ st, (SB D chalV pubVal Q i).trace (opCol st) =
      if st = (pubAt D chalV pubVal Q RF hchar i).state then 1 else 0 :=
  fun st => stAt_spec D chalV pubVal Q RF hchar i st

theorem hsrc_at (i : Fin D.N) :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR curReader (pubAt D chalV pubVal Q RF hchar i).state role cc).eval (SB D chalV pubVal Q i) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAt D chalV pubVal Q RF hchar i) ⟨role, hr⟩) ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_cur,
    OptimizedComputeSameExecution.sourcePubAt_eval_eq_semanticPub _ _ (hsel_at D chalV pubVal Q RF hchar i)
      role cc hr hc,
    show pubAt D chalV pubVal Q RF hchar i =
      pubOfState (Env.ofSubst computeSubst (SB D chalV pubVal Q i)) (stAt D chalV pubVal Q RF hchar i) from rfl,
    pubFingerprint_pubOfState, fpCoordinate_fpOf]
  exact (decoded_source_trace (SB D chalV pubVal Q i) ⟨role, hr⟩ ⟨cc, hc⟩).symm

include hadj in
theorem hsel_shift (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    ∀ st, (curReader.sel st).eval (shiftNext (SB D chalV pubVal Q i)) =
      if st = (pubAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩).state then 1 else 0 := by
  intro st
  show (SB D chalV pubVal Q i).traceNext (opCol st) = _
  rw [shift_trace D chalV pubVal Q hadj i hi _ (by cases st <;> decide)]
  exact hsel_at D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩ st

include hadj in
theorem hsrc_shift (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR curReader (pubAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩).state role cc).eval
          (shiftNext (SB D chalV pubVal Q i)) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩)
            ⟨role, hr⟩) ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_cur_eval_congr (shift_trace71 D chalV pubVal Q hadj i hi) _ role cc hr hc]
  exact hsrc_at D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩ role cc hr hc

include hadj in
theorem htag_shift (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    ∀ j, (childTagHost curReader (pubAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩).state j).eval
        (shiftNext (SB D chalV pubVal Q i)) = tagsAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩ j := by
  intro j
  exact childTagHost_cur_eval_congr (shift_trace71 D chalV pubVal Q hadj i hi) _ j

omit RF hchar in
theorem hγ_shift (i : Fin D.N) :
    walkGammaChallenge.eval (shiftNext (SB D chalV pubVal Q i)) = gammaQ D chalV := by
  rw [gamma_eval_shift]; exact walkGamma_at D chalV pubVal Q i

omit RF hchar in
theorem hα_shift (i : Fin D.N) :
    walkAlphaChallenge.eval (shiftNext (SB D chalV pubVal Q i)) = alphaQ D chalV := by
  rw [alpha_eval_shift]; exact walkAlpha_at D chalV pubVal Q i

include hadj in
theorem nextLabel_eval (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (labelRLC nextReader).eval (SB D chalV pubVal Q i) =
      Walk.rlc (gammaQ D chalV) (labelVecOfPub (pubAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩)) := by
  rw [labelRLC_next_eval]
  exact labelRLC_eval curReader _ _ _ (hsel_shift D chalV pubVal Q hadj RF hchar i hi)
    (hsrc_shift D chalV pubVal Q hadj RF hchar i hi) (hγ_shift D chalV pubVal Q i)

include hadj in
theorem nextCC_eval (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (childSumCC nextReader).eval (SB D chalV pubVal Q i) =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩)),
        alphaQ D chalV ^ l * Walk.rlc (gammaQ D chalV)
          (childVecN (pubAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩)
            (tagsAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩) (l - 1)) := by
  rw [childSumCC_next_eval]
  exact childSumCC_eval curReader _ _ _ _ _ (hsel_shift D chalV pubVal Q hadj RF hchar i hi)
    (hsrc_shift D chalV pubVal Q hadj RF hchar i hi) (hα_shift D chalV pubVal Q i) (hγ_shift D chalV pubVal Q i)
    (htag_shift D chalV pubVal Q hadj RF hchar i hi)

include hadj in
theorem nextCM_eval (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (selectorCM nextReader).eval (SB D chalV pubVal Q i) =
      alphaQ D chalV ^ fanoutComp (stAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩) := by
  rw [selectorCM_next_eval]
  exact selectorCM_eval curReader _ _ _ (hsel_shift D chalV pubVal Q hadj RF hchar i hi) (hα_shift D chalV pubVal Q i)

omit RF hchar in
include hadj in
theorem nextLine_eval (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (finalWalkLine .traceNext).eval (SB D chalV pubVal Q i) =
      (finalWalkLine .traceCur).eval (SB D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩) := by
  simp only [finalWalkLine, Expr.eval]
  exact shift_trace D chalV pubVal Q hadj i hi _ (by decide)

/-! ## 4. Row 0 and the last row -/

theorem baseTrace11_row0 : (BV D chalV pubVal Q (firstRowG D)).baseTrace 11 = 1 := by
  have h := (masks D chalV pubVal Q RF (firstRowG D)).1
  simpa using h

theorem initialMask_eq_selector_row0 (st : State) :
    (initialMaskExpr st).eval (SB D chalV pubVal Q (firstRowG D)) =
      (SB D chalV pubVal Q (firstRowG D)).trace (opCol st) := by
  have hobl := RF.obl (firstRowG D)
  have hlt : opCol st < 11 := by cases st <;> decide
  have hg := hobl.selectorEquality2 (endpointEqualityCheck isFirstVar 20 (opCol st)) (by
    simp only [finalEndpointEqualityChecks, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨opCol st, hlt, rfl⟩)
  have hfirst : (envP D chalV pubVal Q (firstRowG D)).trace 11 = 1 :=
    (D.G.base_eq (envP D chalV pubVal Q (firstRowG D)) 11).symm.trans
      (baseTrace11_row0 D chalV pubVal Q RF hchar)
  simp only [endpointEqualityCheck, isFirstVar, bv, CoeffExpr.eval, hfirst, one_mul,
    sub_eq_zero] at hg
  have hpub : (SB D chalV pubVal Q (firstRowG D)).pub (20 + opCol st) =
      algebraMap F K ((envP D chalV pubVal Q (firstRowG D)).pub (20 + opCol st)) := by
    have h1 : ¬ (20 + opCol st < 3) := by omega
    have h2 : 20 ≤ 20 + opCol st ∧ 20 + opCol st < 42 := by omega
    simp only [SB, BV, CorrectedFinalTypedEnv.toSourceEnv, dif_neg h1, dif_pos h2]
    congr 1
    rw [D.G.scalarPublic_eq]
    congr 1; show 20 + (20 + opCol st - 20) = _; omega
  have htr : (SB D chalV pubVal Q (firstRowG D)).trace (opCol st) =
      algebraMap F K ((envP D chalV pubVal Q (firstRowG D)).trace (opCol st)) := by
    rw [SB, source_trace_base _ (opCol st) (by omega)]
    exact congrArg _ (D.G.base_eq (envP D chalV pubVal Q (firstRowG D)) ⟨opCol st, by omega⟩)
  simp only [initialMaskExpr, Expr.eval]
  rw [hpub, htr, hg]

theorem hmask_first :
    ∀ st, (firstReader.sel st).eval (SB D chalV pubVal Q (firstRowG D)) =
      if st = (pubAt D chalV pubVal Q RF hchar (firstRowG D)).state then 1 else 0 := by
  intro st
  show (initialMaskExpr st).eval _ = _
  rw [initialMask_eq_selector_row0 D chalV pubVal Q RF hchar st]
  exact hsel_at D chalV pubVal Q RF hchar (firstRowG D) st

theorem hsrc_first :
    ∀ (role cc : ℕ) (hr : role < 12) (hc : cc < 3),
      (sourcePubAtR firstReader (pubAt D chalV pubVal Q RF hchar (firstRowG D)).state role cc).eval
          (SB D chalV pubVal Q (firstRowG D)) =
        OptimizedComputeCodec.fpCoordinate
          (OptimizedComputeCodec.pubFingerprint (pubAt D chalV pubVal Q RF hchar (firstRowG D)) ⟨role, hr⟩)
          ⟨cc, hc⟩ := by
  intro role cc hr hc
  rw [sourcePubAtR_first]
  exact hsrc_at D chalV pubVal Q RF hchar (firstRowG D) role cc hr hc

theorem firstLabel_eval :
    (labelRLC firstReader).eval (SB D chalV pubVal Q (firstRowG D)) =
      Walk.rlc (gammaQ D chalV) (labelVecOfPub (pubAt D chalV pubVal Q RF hchar (firstRowG D))) :=
  labelRLC_eval firstReader _ _ _ (hmask_first D chalV pubVal Q RF hchar) (hsrc_first D chalV pubVal Q RF hchar)
    (walkGamma_at D chalV pubVal Q (firstRowG D))

theorem firstCC_eval :
    (childSumCC firstReader).eval (SB D chalV pubVal Q (firstRowG D)) =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D chalV pubVal Q RF hchar (firstRowG D))),
        alphaQ D chalV ^ l * Walk.rlc (gammaQ D chalV)
          (childVecN (pubAt D chalV pubVal Q RF hchar (firstRowG D)) (tagsAt D chalV pubVal Q RF hchar (firstRowG D)) (l - 1)) :=
  childSumCC_eval firstReader _ _ _ _ _ (hmask_first D chalV pubVal Q RF hchar)
    (hsrc_first D chalV pubVal Q RF hchar)
    (walkAlphaChal_at D chalV pubVal Q (firstRowG D)) (walkGamma_at D chalV pubVal Q (firstRowG D))
    (fun j => by rw [childTagHost_first]; rfl)

theorem firstCM_eval :
    (selectorCM firstReader).eval (SB D chalV pubVal Q (firstRowG D)) =
      alphaQ D chalV ^ fanoutComp (stAt D chalV pubVal Q RF hchar (firstRowG D)) :=
  selectorCM_eval firstReader _ _ _ (hmask_first D chalV pubVal Q RF hchar)
    (walkAlphaChal_at D chalV pubVal Q (firstRowG D))

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
    e.eval (SR D chalV pubVal Q i) = e.eval (SB D chalV pubVal Q i) :=
  eval_toSourceEnv309_of_noWalkVars (EV D chalV pubVal Q i) e he

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
    (SR D chalV pubVal Q i).trace k = algebraMap F K ((BV D chalV pubVal Q i).baseTrace ⟨k, hk⟩) := by
  have h3 : k ≠ 303 := by omega
  have h6 : k ≠ 306 := by omega
  simp only [SR, EV, Env309.toSourceEnv, h3, h6, if_false]
  exact source_trace_base _ k hk

omit RF hchar in
theorem lowerW_eval (env : Env309 F K) (e : Expr) (h : (lower309 e).isSome) :
    (lowerW e).eval env = e.eval env.toSourceEnv :=
  (lower309_eval env e _ (lower309_some e h)).symm

/-! ## 6. Row 0 and the last row -/

theorem isFirst_row0 : (BV D chalV pubVal Q (firstRowG D)).baseTrace 11 = 1 :=
  baseTrace11_row0 D chalV pubVal Q RF hchar

theorem walkLn_row0 :
    (finalWalkLine .traceCur).eval (SB D chalV pubVal Q (firstRowG D)) = alphaQ D chalV := by
  have hmem : lowerLeaf finalMaskedWalkLn1 ∈ endpoint2Q7 := by rw [endpoint2Q7_eq]; simp
  have h0 := (RF.obl (firstRowG D)).endpointDegreeTwo _ hmem
  obtain ⟨t, ht⟩ : ∃ t, correctedLowerFinal finalMaskedWalkLn1 = some t :=
    Option.isSome_iff_exists.mp lowerLeaf_total.1
  have h : finalMaskedWalkLn1.eval (SB D chalV pubVal Q (firstRowG D)) = 0 := by
    rw [correctedLowerFinal_eval _ _ _ ht]
    simp only [lowerLeaf, ht, Option.getD, WTyped.eval] at h0
    exact h0
  have hm : fixedIsFirst.eval (SB D chalV pubVal Q (firstRowG D)) = 1 := by
    simp [fixedIsFirst, Expr.eval, CorrectedFinalTypedEnv.toSourceEnv,
      isFirst_row0 D chalV pubVal Q RF hchar]
  simp only [finalMaskedWalkLn1, Expr.eval] at h
  rw [hm, one_mul, finalOptimizedWalkLn1] at h
  have heq :
      (Trans.walkLn1.subst finalWalkInitialSubst).eval (SB D chalV pubVal Q (firstRowG D)) =
        (finalWalkLine .traceCur).eval (SB D chalV pubVal Q (firstRowG D)) -
          (walkChallenge 0).eval (SB D chalV pubVal Q (firstRowG D)) := by
    rw [Expr.eval_subst]; rfl
  rw [heq, sub_eq_zero] at h
  rw [h, walkAlpha_at]

theorem isFirst_SR : fixedIsFirst.eval (SR D chalV pubVal Q (firstRowG D)) = 1 := by
  simp only [fixedIsFirst, Expr.eval]
  rw [SR_trace_base D chalV pubVal Q _ 11 (by norm_num)]
  rw [show (⟨11, by norm_num⟩ : Fin 13) = 11 from rfl, isFirst_row0 D chalV pubVal Q RF hchar, map_one]

/-- **`count(1) = initial_count · cm(1)`** on `W0`. -/
theorem walkCount_row0 :
    (SR D chalV pubVal Q (firstRowG D)).trace 303 =
      initQ D pubVal * alphaQ D chalV ^ fanoutComp (stAt D chalV pubVal Q RF hchar (firstRowG D)) := by
  have hmem : lowerW finalMaskedWalkCount1_309 ∈ endpoint2Q7 := by rw [endpoint2Q7_eq]; simp
  have h0 := (RF.obl (firstRowG D)).endpointDegreeTwo _ hmem
  rw [lowerW_eval _ _ lower309_total.2.2.2.2.1] at h0
  simp only [finalMaskedWalkCount1_309, Expr.eval] at h0
  rw [isFirst_SR D chalV pubVal Q RF hchar, one_mul, walkCount1_309_eval, sub_eq_zero,
    SR_eq_SB D chalV pubVal Q _ _ nw_cmFirst, firstCM_eval D chalV pubVal Q RF hchar] at h0
  rw [h0]
  congr 1
  exact family_initialCount_at D chalV pubVal Q _

/-- **The row-0 walk identity on `W1`**. -/
theorem walkAccInit_row0 :
    alphaQ D chalV * Walk.rlc (gammaQ D chalV) (labelVecOfPub (pubAt D chalV pubVal Q RF hchar (firstRowG D))) +
        (SR D chalV pubVal Q (firstRowG D)).trace 306 =
      (∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D chalV pubVal Q RF hchar (firstRowG D))),
        alphaQ D chalV ^ l * initQ D pubVal * Walk.rlc (gammaQ D chalV)
          (childVecN (pubAt D chalV pubVal Q RF hchar (firstRowG D))
            (tagsAt D chalV pubVal Q RF hchar (firstRowG D)) (l - 1))) + seedQ D pubVal := by
  have hmem : lowerW finalMaskedWalkAccInit309 ∈ endpoint4_309 := by simp [endpoint4_309]
  have h0 := (RF.obl (firstRowG D)).endpointDegreeFour _ hmem
  rw [lowerW_eval _ _ lower309_total.2.2.2.2.2.2] at h0
  simp only [finalMaskedWalkAccInit309, Expr.eval] at h0
  rw [isFirst_SR D chalV pubVal Q RF hchar, one_pow, one_mul, walkAccInit_309_eval, sub_eq_zero,
    SR_eq_SB D chalV pubVal Q _ _ nw_lineCur, SR_eq_SB D chalV pubVal Q _ _ nw_lblFirst,
    SR_eq_SB D chalV pubVal Q _ _ nw_ccFirst, walkLn_row0 D chalV pubVal Q RF hchar,
    firstLabel_eval D chalV pubVal Q RF hchar, firstCC_eval D chalV pubVal Q RF hchar] at h0
  have hp0 : (SR D chalV pubVal Q (firstRowG D)).pub 0 = initQ D pubVal :=
    family_initialCount_at D chalV pubVal Q _
  have hp1 : (SR D chalV pubVal Q (firstRowG D)).pub 1 = seedQ D pubVal :=
    family_seed_at D chalV pubVal Q _
  rw [hp0, hp1, Finset.mul_sum] at h0
  rw [h0]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isLast_SR : fixedIsLast.eval (SR D chalV pubVal Q (lastRowG D)) = 1 := by
  simp only [fixedIsLast, Expr.eval]
  rw [SR_trace_base D chalV pubVal Q _ 12 (by norm_num)]
  have := (masks D chalV pubVal Q RF (lastRowG D)).2
  rw [if_pos rfl] at this
  rw [show (⟨12, by norm_num⟩ : Fin 13) = 12 from rfl, this, map_one]

/-- **`out_walk = acc(h) = 0`** on `W1`. -/
theorem walkOut_last : (SR D chalV pubVal Q (lastRowG D)).trace 306 = 0 := by
  have hmem : lowerW finalMaskedWalkOut309 ∈ endpoint2Q7 := by rw [endpoint2Q7_eq]; simp
  have h0 := (RF.obl (lastRowG D)).endpointDegreeTwo _ hmem
  rw [lowerW_eval _ _ lower309_total.2.2.2.2.2.1] at h0
  simp only [finalMaskedWalkOut309, Expr.eval] at h0
  rw [isLast_SR D chalV pubVal Q RF hchar, one_mul, walkOut_309_eval] at h0
  exact h0

/-! ## 7. The steps -/

theorem notLast (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) : (BV D chalV pubVal Q i).baseTrace 12 = 0 := by
  rw [(masks D chalV pubVal Q RF i).2, if_neg]
  intro heq
  have hv : (i : ℕ) = D.N - 1 := congrArg Fin.val heq
  omega

theorem sources (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    WalkSourcesQ7 (EV D chalV pubVal Q i) :=
  walk_sources_q7 (RF.obl i) (notLast D chalV pubVal Q RF hchar i hi)

include hadj in
theorem walkLn_step (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (finalWalkLine .traceCur).eval (SB D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩) =
      alphaQ D chalV * (finalWalkLine .traceCur).eval (SB D chalV pubVal Q i) := by
  have h := (sources D chalV pubVal Q RF hchar i hi).walkLn
  rw [SR_eq_SB D chalV pubVal Q i _ (by decide), SVCompute.walkLnStep_inGate_eval, sub_eq_zero,
    nextLine_eval D chalV pubVal Q hadj i hi, walkAlpha_at] at h
  exact h

include hadj in
theorem walkCount_step (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (SR D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩).trace 303 =
      (SR D chalV pubVal Q i).trace 303 *
        alphaQ D chalV ^ fanoutComp (stAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩) := by
  have h := (sources D chalV pubVal Q RF hchar i hi).count
  rw [walkCountStep309_eval, sub_eq_zero, SR_eq_SB D chalV pubVal Q i _ nw_cmNext,
    nextCM_eval D chalV pubVal Q hadj RF hchar i hi,
    shift_walk D chalV pubVal Q hadj i hi 303 (Or.inl rfl)] at h
  exact h

include hadj in
theorem walkAcc_step (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    (finalWalkLine .traceCur).eval (SB D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩) *
        Walk.rlc (gammaQ D chalV) (labelVecOfPub (pubAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩)) +
        (SR D chalV pubVal Q ⟨(i : ℕ) + 1, hi⟩).trace 306 - (SR D chalV pubVal Q i).trace 306 =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩)),
        alphaQ D chalV ^ l * (SR D chalV pubVal Q i).trace 303 *
          Walk.rlc (gammaQ D chalV) (childVecN (pubAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩)
            (tagsAt D chalV pubVal Q RF hchar ⟨(i : ℕ) + 1, hi⟩) (l - 1)) := by
  have h := (sources D chalV pubVal Q RF hchar i hi).acc
  rw [walkAccStep309_eval, SR_eq_SB D chalV pubVal Q i _ nw_lineNext,
    SR_eq_SB D chalV pubVal Q i _ nw_lblNext, SR_eq_SB D chalV pubVal Q i _ nw_ccNext,
    nextLine_eval D chalV pubVal Q hadj i hi, nextLabel_eval D chalV pubVal Q hadj RF hchar i hi,
    nextCC_eval D chalV pubVal Q hadj RF hchar i hi,
    shift_walk D chalV pubVal Q hadj i hi 306 (Or.inr rfl), Finset.mul_sum] at h
  have h' := sub_eq_zero.mp h
  rw [h']
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ## 8. The `WalkSat` assembly -/

noncomputable def lnW (i : ℕ) : K := (finalWalkLine .traceCur).eval (SB D chalV pubVal Q (rowOfG D i))
noncomputable def countW (i : ℕ) : K := (SR D chalV pubVal Q (rowOfG D i)).trace 303
noncomputable def accW (i : ℕ) : K := (SR D chalV pubVal Q (rowOfG D i)).trace 306
noncomputable def curW (i : ℕ) : K :=
  Walk.rlc (gammaQ D chalV) (labelVecOfPub (pubAt D chalV pubVal Q RF hchar (rowOfG D i)))
noncomputable def chldW (i l : ℕ) : K :=
  Walk.rlc (gammaQ D chalV)
    (childVecN (pubAt D chalV pubVal Q RF hchar (rowOfG D i)) (tagsAt D chalV pubVal Q RF hchar (rowOfG D i)) (l - 1))
noncomputable def foW (i : ℕ) : ℕ := fanoutComp (stAt D chalV pubVal Q RF hchar (rowOfG D i))

include hadj in
/-- **`WalkSat` of the VCL compute walk on `W0`/`W1`**: `α = alphaQ D chalV`,
`seed = seedOfClaim`, `initial_count = alphaQ D chalV`, over `D.N` rows, at the decoded labels, the
declared child payloads and the decoded fanouts — the twin of `deployed_walkSatD`. -/
theorem q7_walkSat :
    WalkSat (curW D chalV pubVal Q RF hchar) (chldW D chalV pubVal Q RF hchar) (foW D chalV pubVal Q RF hchar)
      (lnW D chalV pubVal Q) (countW D chalV pubVal Q) (accW D chalV pubVal Q) (alphaQ D chalV)
      (seedQ D pubVal) (initQ D pubVal) D.N := by
  have hpos : 1 ≤ D.N := D.hN
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (finalWalkLine .traceCur).eval (SB D chalV pubVal Q (rowOfG D 1)) = alphaQ D chalV
    rw [rowOf_oneG]
    exact walkLn_row0 D chalV pubVal Q RF hchar
  · intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < D.N := by omega
    have hk1 : k + 1 < D.N := by omega
    show (finalWalkLine .traceCur).eval (SB D chalV pubVal Q (rowOfG D (k + 1 + 1))) =
      alphaQ D chalV * (finalWalkLine .traceCur).eval (SB D chalV pubVal Q (rowOfG D (k + 1)))
    rw [rowOf_succG D (k + 1) hk1, rowOf_succG D k hk]
    exact walkLn_step D chalV pubVal Q hadj RF hchar ⟨k, hk⟩ hk1
  · show (SR D chalV pubVal Q (rowOfG D 1)).trace 303 =
      initQ D pubVal * alphaQ D chalV ^ fanoutComp (stAt D chalV pubVal Q RF hchar (rowOfG D 1))
    rw [rowOf_oneG]
    exact walkCount_row0 D chalV pubVal Q RF hchar
  · intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < D.N := by omega
    have hk1 : k + 1 < D.N := by omega
    show (SR D chalV pubVal Q (rowOfG D (k + 1 + 1))).trace 303 =
      (SR D chalV pubVal Q (rowOfG D (k + 1))).trace 303 *
        alphaQ D chalV ^ fanoutComp (stAt D chalV pubVal Q RF hchar (rowOfG D (k + 1 + 1)))
    rw [rowOf_succG D (k + 1) hk1, rowOf_succG D k hk]
    exact walkCount_step D chalV pubVal Q hadj RF hchar ⟨k, hk⟩ hk1
  · show (finalWalkLine .traceCur).eval (SB D chalV pubVal Q (rowOfG D 1)) *
        Walk.rlc (gammaQ D chalV) (labelVecOfPub (pubAt D chalV pubVal Q RF hchar (rowOfG D 1))) +
        (SR D chalV pubVal Q (rowOfG D 1)).trace 306 =
      (∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D chalV pubVal Q RF hchar (rowOfG D 1))),
        alphaQ D chalV ^ l * initQ D pubVal *
          Walk.rlc (gammaQ D chalV)
            (childVecN (pubAt D chalV pubVal Q RF hchar (rowOfG D 1))
              (tagsAt D chalV pubVal Q RF hchar (rowOfG D 1)) (l - 1)))
        + seedQ D pubVal
    rw [rowOf_oneG, walkLn_row0 D chalV pubVal Q RF hchar]
    exact walkAccInit_row0 D chalV pubVal Q RF hchar
  · intro i hi1 hih
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < D.N := by omega
    have hk1 : k + 1 < D.N := by omega
    show (finalWalkLine .traceCur).eval (SB D chalV pubVal Q (rowOfG D (k + 1 + 1))) *
        Walk.rlc (gammaQ D chalV) (labelVecOfPub (pubAt D chalV pubVal Q RF hchar (rowOfG D (k + 1 + 1)))) +
        (SR D chalV pubVal Q (rowOfG D (k + 1 + 1))).trace 306 -
        (SR D chalV pubVal Q (rowOfG D (k + 1))).trace 306 =
      ∑ l ∈ Finset.Icc 1 (fanoutComp (stAt D chalV pubVal Q RF hchar (rowOfG D (k + 1 + 1)))),
        alphaQ D chalV ^ l * (SR D chalV pubVal Q (rowOfG D (k + 1))).trace 303 *
          Walk.rlc (gammaQ D chalV)
            (childVecN (pubAt D chalV pubVal Q RF hchar (rowOfG D (k + 1 + 1)))
              (tagsAt D chalV pubVal Q RF hchar (rowOfG D (k + 1 + 1))) (l - 1))
    rw [rowOf_succG D (k + 1) hk1, rowOf_succG D k hk]
    exact walkAcc_step D chalV pubVal Q hadj RF hchar ⟨k, hk⟩ hk1

/-- **`out_walk = 0`** (`ℕ`-indexed). -/
theorem q7_walk_out : accW D chalV pubVal Q D.N = 0 := by
  show (SR D chalV pubVal Q (rowOfG D D.N)).trace 306 = 0
  rw [rowOf_rowsG]
  exact walkOut_last D chalV pubVal Q RF hchar

/-! ## 9. The queue witness: `BFSValid` and the tiling -/

theorem queueNonEmpty_SR (i : Fin D.N) : walkQueueNonEmpty309.eval (SR D chalV pubVal Q i) = 0 := by
  have h := (queue_sources_q7 (RF.obl i)).1
  rwa [queueNonEmpty309, lowerW_eval _ _ lower309_total.2.2.1] at h

theorem queueTiling_SR (i : Fin D.N) : walkQueueTiling309.eval (SR D chalV pubVal Q i) = 0 := by
  have h := (queue_sources_q7 (RF.obl i)).2
  rwa [queueTiling309, lowerW_eval _ _ lower309_total.2.2.2.1] at h

theorem count_ne_ln (i : Fin D.N) (hi : (i : ℕ) + 1 < D.N) :
    countW D chalV pubVal Q ((i : ℕ) + 1) ≠ lnW D chalV pubVal Q ((i : ℕ) + 1) := by
  have hgate := queueNonEmpty_SR D chalV pubVal Q RF hchar i
  have h12 : (SR D chalV pubVal Q i).trace 12 = 0 := by
    rw [SR_trace_base D chalV pubVal Q i 12 (by norm_num)]
    rw [show (⟨12, by norm_num⟩ : Fin 13) = 12 from rfl, notLast D chalV pubVal Q RF hchar i hi, map_zero]
  have hrow : rowOfG D ((i : ℕ) + 1) = i := rowOf_succG D (i : ℕ) i.isLt
  rw [countW, lnW, hrow]
  simp only [walkQueueNonEmpty309, Expr.eval, h12] at hgate
  rw [SR_eq_SB D chalV pubVal Q i _ nw_walkInv, SR_eq_SB D chalV pubVal Q i _ nw_lineCur] at hgate
  intro heq
  simp only [walkCountCol] at hgate
  rw [heq] at hgate
  simp at hgate

theorem count_eq_ln_last : countW D chalV pubVal Q D.N = lnW D chalV pubVal Q D.N := by
  have hgate := queueTiling_SR D chalV pubVal Q RF hchar (lastRowG D)
  have hrow : rowOfG D D.N = lastRowG D := rowOf_rowsG D
  rw [countW, lnW, hrow]
  have hl := isLast_SR D chalV pubVal Q RF hchar
  simp only [fixedIsLast, Expr.eval] at hl
  simp only [walkQueueTiling309, Expr.eval, hl, one_mul, walkCountCol] at hgate
  rw [SR_eq_SB D chalV pubVal Q _ _ nw_lineCur] at hgate
  exact sub_eq_zero.mp hgate

include hadj in
/-- **Queue validity** (`Batch478.bfsValid_of_ratio_gate`), no condition on `α`. -/
theorem q7_bfsValid (hinit : initQ D pubVal = alphaQ D chalV) : BFSValid (foW D chalV pubVal Q RF hchar) D.N := by
  have hw := q7_walkSat D chalV pubVal Q hadj RF hchar
  refine bfsValid_of_ratio_gate (K := K) (α := alphaQ D chalV) ?_
  intro i hi1 hih
  have hk : i - 1 < D.N := by omega
  let k : Fin D.N := ⟨i - 1, hk⟩
  have hki : (k : ℕ) + 1 = i := Nat.sub_add_cancel hi1
  have hne := count_ne_ln D chalV pubVal Q RF hchar k (by omega)
  have hcnt := Walk.count_closed hw i hi1 (le_of_lt hih)
  rw [hinit] at hcnt
  have hln := Walk.ln_closed hw i hi1 (le_of_lt hih)
  rw [hki] at hne
  rw [hcnt, hln] at hne
  rw [pow_add, pow_one]
  exact hne

include hadj in
/-- **The tiling outside the `α`-tiling event** (coin-map free form of `computeTilingEvent`). -/
theorem q7_tiling (hinit : initQ D pubVal = alphaQ D chalV) (hα : ¬ (alphaQ D chalV ^ (1 + Sf (foW D chalV pubVal Q RF hchar) D.N) =
      alphaQ D chalV ^ D.N ∧ 1 + Sf (foW D chalV pubVal Q RF hchar) D.N ≠ D.N)) :
    Sf (foW D chalV pubVal Q RF hchar) D.N + 1 = D.N := by
  have hw := q7_walkSat D chalV pubVal Q hadj RF hchar
  have hterm := count_eq_ln_last D chalV pubVal Q RF hchar
  have hcnt := Walk.count_closed hw D.N hw.hpos le_rfl
  rw [hinit] at hcnt
  have hln := Walk.ln_closed hw D.N hw.hpos le_rfl
  have hpow : alphaQ D chalV ^ (1 + Sf (foW D chalV pubVal Q RF hchar) D.N) = alphaQ D chalV ^ D.N := by
    rw [pow_add, pow_one, ← hcnt, ← hln]
    exact hterm
  by_contra hne
  exact hα ⟨hpow, by omega⟩


/-! ## 10. `V_comp` (patched row) and `root_binds` -/

/-- **`V_comp` at every row, at the patched row**, the `z·z⁻¹` pin discharged. -/
theorem vcomp_at (hz : zQ D chalV ≠ 0) (hzi : D.G.chalSlot chalV 5 = (zQ D chalV)⁻¹)
    (i : Fin D.N) : VcompAt (lnPatch (BV D chalV pubVal Q i)) :=
  q7_obligations_vcompG D.G D.N _ (RF.obl i) hchar (zZinv_at D chalV pubVal Q i hz hzi)

include hadj in
/-- **`root_binds` at the Q7 chip**: given the frame's walk publics (`initial_count = α`,
`seed = RLC^γ(claim label at z)·α`), outside the `α`-root and `γ`-root events the first row's
decoded `(s, f, e)` bind the claim at `z`. -/
theorem q7_root_binds {z : K} (hinit : initQ D pubVal = alphaQ D chalV)
    (hseed : seedQ D pubVal = Walk.rlc (gammaQ D chalV) (claimLabelVec z D.claim) * alphaQ D chalV)
    (hα : alphaQ D chalV ∉ alphaBadOf (rootDiffP (curW D chalV pubVal Q RF hchar)
      (chldW D chalV pubVal Q RF hchar) (foW D chalV pubVal Q RF hchar)
      (Walk.rlc (gammaQ D chalV) (claimLabelVec z D.claim)) D.N))
    (hγ : gammaQ D chalV ∉ gammaBadOf (claimLabelVec z D.claim)
      (labelVecOfPub (pubAt D chalV pubVal Q RF hchar (firstRowG D)))) :
    ∃ st0 : State, OneHotSelector (SB D chalV pubVal Q (firstRowG D)) st0 ∧
      SemanticStrategy.bindFP z D.claim.subject (decodePub (BV D chalV pubVal Q (firstRowG D)) st0).s ∧
      SemanticStrategy.bindFP z D.claim.formula (decodePub (BV D chalV pubVal Q (firstRowG D)) st0).f ∧
      SemanticStrategy.bindFP z D.claim.result (decodePub (BV D chalV pubVal Q (firstRowG D)) st0).e := by
  refine ⟨stAt D chalV pubVal Q RF hchar (firstRowG D), stAt_spec D chalV pubVal Q RF hchar (firstRowG D), ?_⟩
  have hw := q7_walkSat D chalV pubVal Q hadj RF hchar
  rw [hinit, hseed] at hw
  exact WalkVCL.root_binds_of_walk (z := z) D.claim (pubAt D chalV pubVal Q RF hchar (firstRowG D))
    hw (q7_walk_out D chalV pubVal Q RF hchar) (by rw [curW, rowOf_oneG]) hα hγ

end

/-! ## 11. At `frameVCL` coins -/

noncomputable section frame
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {h : ℕ}

/-- The walk seed at `frameVCL` coins: `RLC^{χ1}(claim label at χ2) · χ0`. -/
def seedVCL (claim : P8PublicClaim) (χ : SVFrame.Coins SVFrame.frameVCL K) : K :=
  Walk.rlc (χ ⟨1, by decide⟩) (claimLabelVec (χ ⟨2, by decide⟩) claim) * χ ⟨0, by decide⟩

/-- **The compute publics at `frameVCL` coins**: `initial_count = αC` at limbs `0..2`, the walk seed
at `3..5`, the package publics elsewhere. -/
def pubVQ7 (b : Basis (Fin 3) F K) (claim : P8PublicClaim) (pkgPub : ℕ → F)
    (χ : SVFrame.Coins SVFrame.frameVCL K) : ℕ → F :=
  fun j =>
    if h0 : j < 3 then coord b (χ ⟨0, by decide⟩) ⟨j, h0⟩
    else if h : 3 ≤ j ∧ j < 6 then coord b (seedVCL claim χ) ⟨j - 3, by omega⟩
    else pkgPub j

theorem slotK_chalVQ7 (b : Basis (Fin 3) F K) (χ : SVFrame.Coins SVFrame.frameVCL K) (q : ℕ)
    (hq : q < 12) : slotK b (chalVQ7 b χ) q = chalKQ7 χ q := by
  unfold slotK
  have hc : ∀ k : Fin 3, chalVQ7 b χ (3 * q + (k : ℕ)) = coord b (chalKQ7 χ q) k := by
    intro k
    have hk := k.isLt
    simp only [chalVQ7, show 3 * q + (k : ℕ) < 36 by omega, ↓reduceIte]
    have hdiv : (3 * q + (k : ℕ)) / 3 = q := by omega
    have hmod : (3 * q + (k : ℕ)) % 3 = (k : ℕ) := by omega
    rw [hdiv]
    exact congrArg _ (Fin.ext hmod)
  simp_rw [hc]
  exact reconstruct_coord b _

theorem slotK_pubVQ7_zero (b : Basis (Fin 3) F K) (claim : P8PublicClaim) (pkgPub : ℕ → F)
    (χ : SVFrame.Coins SVFrame.frameVCL K) : slotK b (pubVQ7 b claim pkgPub χ) 0 = χ ⟨0, by decide⟩ := by
  unfold slotK
  have hc : ∀ k : Fin 3, pubVQ7 b claim pkgPub χ (3 * 0 + (k : ℕ)) = coord b (χ ⟨0, by decide⟩) k := by
    intro k
    have hk : 3 * 0 + (k : ℕ) < 3 := by have := k.isLt; omega
    simp only [pubVQ7, hk, ↓reduceDIte]
    exact congrArg _ (Fin.ext (by simp))
  simp_rw [hc]
  exact reconstruct_coord b _

theorem slotK_pubVQ7_one (b : Basis (Fin 3) F K) (claim : P8PublicClaim) (pkgPub : ℕ → F)
    (χ : SVFrame.Coins SVFrame.frameVCL K) : slotK b (pubVQ7 b claim pkgPub χ) 1 = seedVCL claim χ := by
  unfold slotK
  have hc : ∀ k : Fin 3, pubVQ7 b claim pkgPub χ (3 * 1 + (k : ℕ)) = coord b (seedVCL claim χ) k := by
    intro k
    have hk := k.isLt
    have h0 : ¬ (3 * 1 + (k : ℕ) < 3) := by omega
    have h1 : 3 ≤ 3 * 1 + (k : ℕ) ∧ 3 * 1 + (k : ℕ) < 6 := by omega
    simp only [pubVQ7, h0, h1, ↓reduceDIte, and_self]
    exact congrArg _ (Fin.ext (by simp))
  simp_rw [hc]
  exact reconstruct_coord b _

variable (D : ChipData F K h) (χ : SVFrame.Coins SVFrame.frameVCL K)
  (Q : Fin vclWidthE → F[X]) (hadj : D.Adjacent)
  (RF : RowFactsQ7 D.toG (chalVQ7 D.basis χ) (pubVQ7 D.basis D.claim D.pub χ) Q)
  (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)

theorem frame_coins :
    alphaQ D.toG (chalVQ7 D.basis χ) = χ ⟨0, by decide⟩ ∧ gammaQ D.toG (chalVQ7 D.basis χ) = χ ⟨1, by decide⟩ ∧
      zQ D.toG (chalVQ7 D.basis χ) = χ ⟨2, by decide⟩ ∧
      slotK D.basis (chalVQ7 D.basis χ) 5 = (χ ⟨2, by decide⟩)⁻¹ ∧
      initQ D.toG (pubVQ7 D.basis D.claim D.pub χ) = χ ⟨0, by decide⟩ ∧
      seedQ D.toG (pubVQ7 D.basis D.claim D.pub χ) = seedVCL D.claim χ :=
  ⟨slotK_chalVQ7 _ _ 6 (by norm_num), slotK_chalVQ7 _ _ 10 (by norm_num),
    slotK_chalVQ7 _ _ 1 (by norm_num), slotK_chalVQ7 _ _ 5 (by norm_num),
    slotK_pubVQ7_zero _ _ _ _, slotK_pubVQ7_one _ _ _ _⟩

/-- **Acceptance at `computeChipQ7` (frameVCL coins) gives the Q7 row facts.** -/
theorem frame_rowFacts (hinj : D.Injective)
    (hsat : RAP.SatisfiesWithPreprocessing
      (computeChipQ7 D.hN D.nodes D.basis χ (pubVQ7 D.basis D.claim D.pub χ) D.orbit) Q) :
    RowFactsQ7 D.toG (chalVQ7 D.basis χ) (pubVQ7 D.basis D.claim D.pub χ) Q :=
  RowFactsQ7.of_sat _ _ Q D 21 24 hinj hsat

include RF hchar in
/-- **`V_comp` (patched row) at `frameVCL` coins** (`χ2 ≠ 0`). -/
theorem frame_vcomp_at (hz : χ ⟨2, by decide⟩ ≠ 0) (i : Fin D.N) :
    VcompAt (lnPatch (BV D.toG (chalVQ7 D.basis χ) (pubVQ7 D.basis D.claim D.pub χ) Q i)) := by
  obtain ⟨-, -, hzq, hzi, -, -⟩ := frame_coins D χ
  exact vcomp_at D.toG _ _ Q RF hchar (by rw [hzq]; exact hz) (by rw [hzq]; exact hzi) i

include hadj in
/-- **`root_binds` at `frameVCL` coins**: walk coins `χ0` (`αC`), `χ1` (walk `γ`), NPR seed `χ2`. -/
theorem frame_root_binds
    (hα : χ ⟨0, by decide⟩ ∉ alphaBadOf (rootDiffP
      (curW D.toG (chalVQ7 D.basis χ) (pubVQ7 D.basis D.claim D.pub χ) Q RF hchar)
      (chldW D.toG (chalVQ7 D.basis χ) (pubVQ7 D.basis D.claim D.pub χ) Q RF hchar)
      (foW D.toG (chalVQ7 D.basis χ) (pubVQ7 D.basis D.claim D.pub χ) Q RF hchar)
      (Walk.rlc (χ ⟨1, by decide⟩) (claimLabelVec (χ ⟨2, by decide⟩) D.claim)) D.N))
    (hγ : χ ⟨1, by decide⟩ ∉ gammaBadOf (claimLabelVec (χ ⟨2, by decide⟩) D.claim)
      (labelVecOfPub (pubAt D.toG (chalVQ7 D.basis χ) (pubVQ7 D.basis D.claim D.pub χ) Q RF hchar
        (firstRowD D)))) :
    ∃ st0 : State, OneHotSelector
        (SB D.toG (chalVQ7 D.basis χ) (pubVQ7 D.basis D.claim D.pub χ) Q (firstRowD D)) st0 ∧
      SemanticStrategy.bindFP (χ ⟨2, by decide⟩) D.claim.subject
        (decodePub (BV D.toG (chalVQ7 D.basis χ) (pubVQ7 D.basis D.claim D.pub χ) Q (firstRowD D)) st0).s ∧
      SemanticStrategy.bindFP (χ ⟨2, by decide⟩) D.claim.formula
        (decodePub (BV D.toG (chalVQ7 D.basis χ) (pubVQ7 D.basis D.claim D.pub χ) Q (firstRowD D)) st0).f ∧
      SemanticStrategy.bindFP (χ ⟨2, by decide⟩) D.claim.result
        (decodePub (BV D.toG (chalVQ7 D.basis χ) (pubVQ7 D.basis D.claim D.pub χ) Q (firstRowD D)) st0).e := by
  obtain ⟨ha, hg, -, -, hi, hs⟩ := frame_coins D χ
  refine q7_root_binds D.toG _ _ Q hadj RF hchar (by rw [ha, hi]) (by rw [hs, hg, ha]; rfl)
    (by rw [ha, hg]; exact hα) (by rw [hg]; exact hγ)

end frame

end WalkQ7
end VclL.Compute
end Nock.NockVMROM.Thm54
