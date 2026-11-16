/-
  Nock/RedTeam/Batch457Thm54RootLabelFromChip.lean

  **The row-0 walk identity, decoded, and the
  three obstructions to `deployed_root_label_eq_claim`.**

  Brief step 1 asked for `deployed_root_label_eq_claim`: for every `c` outside the
  priced walk collision and every trace accepted at `computeChipAt c`, the row-0
  decoded `(s, f, e)` are the claim's fingerprints.  Two of `Batch453`'s four
  `CHIP_SFE_REMAINING` items close here, at the committed family chip and for every `c`:

  * `labelRLC firstReader` at row 0 evaluates to `RLC^γ` of the DECODED row-0 label
    (`root_cur_is_decoded_label`; public initial masks one-hot from
    `finalEndpointEqualityChecks` + the SV gates);
  * `walkAccInit` at row 0, decoded (`walkAccInit_row0_decoded`):
    `αc · RLC^γ(label₀) + acc_walk(0) = initial_count · cc(0) + seedOfClaim c`.

  1. **`initial_count` is not the coin.**  `Thm:Walk_IOP` sets
     `(seed, initial_count) = (α · RLC^γ(rvt_root), α)`.  So the deployed recognizer at tuple `c` has
     `initial_count = P.optimized.family.computeWalkAlpha`, and `Thm:Walk_IOP`'s premise
     holds iff `alphaC c.1 = computeWalkAlpha` — a fixed-value condition on `c`, which the
     brief forbids as a hypothesis.  Negative control at the paper's `WalkSat`:
     `walkSat_ic_ne_alpha_does_not_pin_root` (h = 2).
  2. **The `αc` root event is not in the consumed union.**  Even with `initial_count = α`,
     `cur(1) = RLC^γ(rvt_root)` needs the polynomial identity, i.e. the `h/|𝕂|` root event
     of `:966` on `alphaC`.  `FailureUnion` is an `alphaC`-cylinder
     (`failureUnion_alphaC_cylinder`); abstract witness `walkSat_root_needs_alpha_event`.
  3. **The root/claim `γ`-collision is not a `topologyBadGammas` pair.**  The union's only
     `γ`-event is `specializedTopologyFailureEvent P.strategy.verifier.raw` — at the
     package strategy, trace-free (`p8Summand_trace_free`, `rfl`) — and its pairs are
     `computeSlotBadGammas` (parent-declared vs child-own payload, `Fin 9`).

  No honest-package object stands in for a committed trace: every chip theorem below is at
  `rowEnvAt P c Qc` for a trace `Qc` accepted at `computeChipAt c`.
-/
import Nock.Walk
import Nock.NockVMROM.Thm54.ComputeWalkSeed
import Nock.NockVMROM.Thm54.ComputeWalkLabel
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
import Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
import Nock.NockVMROM.Thm54.ComputeEnvAgreement
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.RawTopologyRAP
import Nock.RedTeam.Batch438Thm54InGateWalkReceipts
import Nock.RedTeam.Batch453Thm54SeedWiring
import Nock.RedTeam.Batch454Thm54ComputeWalkSat
import Nock.NockVMROM.Thm54.P8Core.Batch457Thm54RootLabelFromChip
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch457

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework.Reify
open Nock.RedTeam.Batch438
open Nock.RedTeam.Batch453
open Nock.Framework
open Module
open MonolithicRAP
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])

/-! ## A. Family-chip first/last-row masks (the preprocessing binding at `computeChipAt c`) -/

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
variable (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
variable (hbasis : FormRBasis P.optimized.basis)
variable (hwidth : FormRWidth F)
include hsat
include hax hbasis hwidth

/-- `isFirst = 1` at the first family row, read at the source level. -/
theorem isFirst_source_row0 :
    (rowEnvAt P c Qc (firstRow P)).toSourceEnv.trace 11 = 1 := by
  rw [source_trace_base _ 11 (by norm_num)]
  change algebraMap F K ((rowEnvAt P c Qc (firstRow P)).baseTrace 11) = 1
  rw [baseTrace11_row0 P c Qc hsat hax hbasis hwidth, map_one]

/-! ## B. Public initial masks are one-hot at the row-0 state

`finalEndpointEqualityChecks` (`isFirst · (sel_st − initialMask_st) = 0`, eleven states) is
in the committed list (`DeployedAcceptance.finalEndpointEqualityChecks_mem_allGates`) and
`selectorEquality2` reads them off acceptance.  With the SV one-hot (`deployed_row_one_hot_at`)
the public masks at row 0 are the one-hot of the decoded state. -/

/-- The row-0 state and its one-hot on BOTH readers: trace selectors and public masks. -/
theorem row0_one_hot_both :
    ∃ st0 : State,
      OneHotSelector (rowEnvAt P c Qc (firstRow P)).toSourceEnv st0 ∧
      ∀ st, (firstReader.sel st).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv =
        if st = st0 then 1 else 0 := by
  obtain ⟨st0, hone⟩ := deployed_row_one_hot_at P c Qc hsat (firstRow P)
  refine ⟨st0, hone, fun st => ?_⟩
  show (initialMaskExpr st).eval _ = _
  rw [initialMask_eq_selector_row0 P c Qc hsat hax hbasis hwidth st]
  exact hone st

/-! ## C. `CHIP_SFE_REMAINING[1]` — `labelRLC firstReader` at row 0 is the decoded label -/

/-- **`cur(1)` is `RLC^γ` of the decoded row-0 label**, on the
committed family trace.  Mirror of `Batch438.label_rlc_is_decoded_label` through the
`firstReader` (public masks) instead of `nextReader`. -/
theorem root_cur_is_decoded_label :
    ∃ st0 : State,
      OneHotSelector (rowEnvAt P c Qc (firstRow P)).toSourceEnv st0 ∧
      (labelRLC firstReader).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv =
        Walk.rlc (gamma c.1)
          (labelVecOfPub (decodePub (rowEnvAt P c Qc (firstRow P)) st0)) := by
  obtain ⟨st0, hone, hmask⟩ := row0_one_hot_both P c Qc hsat hax hbasis hwidth
  refine ⟨st0, hone, ?_⟩
  set env0 := (rowEnvAt P c Qc (firstRow P)).toSourceEnv with henv0
  have hsel' : ∀ st', env0.trace (opCol st') =
      if st' = (decodePub (rowEnvAt P c Qc (firstRow P)) st0).state then 1 else 0 :=
    fun st' => hone st'
  have hmask' : ∀ st, (firstReader.sel st).eval env0 =
      if st = (decodePub (rowEnvAt P c Qc (firstRow P)) st0).state then 1 else 0 :=
    fun st => hmask st
  apply labelRLC_eval firstReader env0 _ (gamma c.1) hmask'
  · intro role cc hr hc
    rw [sourcePubAtR_first, sourcePubAtR_cur,
      OptimizedComputeSameExecution.sourcePubAt_eval_eq_semanticPub _ _ hsel' role cc hr hc,
      show decodePub (rowEnvAt P c Qc (firstRow P)) st0 =
        pubOfState (Env.ofSubst computeSubst env0) st0 from rfl,
      pubFingerprint_pubOfState, fpCoordinate_fpOf]
    exact (decoded_source_trace env0 ⟨role, hr⟩ ⟨cc, hc⟩).symm
  · exact walkGamma_at P c Qc (firstRow P)

/-! ## D. `CHIP_SFE_REMAINING[0]` — `walkAccInit` at row 0, decoded -/

omit hsat hax hbasis hwidth in
/-- `walkAccInit` through the first-row subst, operands named (cf.
`Batch438.walkAccStep_inGate_eval`). -/
theorem walkAccInit_first_eval (env : Env K) :
    (Trans.walkAccInit.subst finalWalkInitialSubst).eval env =
      (finalWalkLine .traceCur).eval env * (labelRLC firstReader).eval env +
          (initialOverlayCoord 1).eval env -
        (env.pub 0 * (childSumCC firstReader).eval env + env.pub 1) := by
  rw [Expr.eval_subst]
  rfl

omit hsat hax hbasis hwidth in
theorem walkLn1_first_eval (env : Env K) :
    (Trans.walkLn1.subst finalWalkInitialSubst).eval env =
      (finalWalkLine .traceCur).eval env - (walkChallenge 0).eval env := by
  rw [Expr.eval_subst]
  rfl

omit hsat hax hbasis hwidth in
theorem walkCount1_first_eval (env : Env K) :
    (Trans.walkCount1.subst finalWalkInitialSubst).eval env =
      (initialOverlayCoord 0).eval env - env.pub 0 * (selectorCM firstReader).eval env := by
  rw [Expr.eval_subst]
  rfl

/-! ## E. The family walk's `(seed, initial_count)` -/

/-- **`walkAccInit` at row 0, decoded** (`CHIP_SFE_REMAINING[0]`): for every `c` and every
trace accepted at `computeChipAt c`,
`αc · RLC^γ(label₀) + acc_walk(0) = αc · cc(0) + seedOfClaim c`,
with `label₀` the DECODED row-0 `LT_comp` label — the paper's `:810` at
`(seed, initial_count) = (α · RLC^γ(rvt_root), α)` (`:962`). -/
theorem walkAccInit_row0_decoded :
    ∃ st0 : State,
      OneHotSelector (rowEnvAt P c Qc (firstRow P)).toSourceEnv st0 ∧
      alphaC c.1 * Walk.rlc (gamma c.1)
          (labelVecOfPub (decodePub (rowEnvAt P c Qc (firstRow P)) st0)) +
        (initialOverlayCoord 1).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv =
      alphaC c.1 *
          (childSumCC firstReader).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv +
        seedOfClaim P.optimized.verifier.raw.claim c := by
  obtain ⟨st0, hone, hcur⟩ := root_cur_is_decoded_label P c Qc hsat hax hbasis hwidth
  refine ⟨st0, hone, ?_⟩
  have h := walkAccInit_row0 P c Qc hsat hax hbasis hwidth
  rw [hcur,
    family_seed_at P c Qc (firstRow P),
    family_initialCount_at P c Qc (firstRow P)] at h
  exact h

/-! ## `initial_count` is the coin -/

omit hsat hax hbasis hwidth in
theorem thmWalkIOP_premise_holds (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).toSourceEnv.pub 0 = alphaC c.1 :=
  family_initialCount_at P c Qc i

omit hsat hax hbasis hwidth in
/-- Positive control (kept): at the package's honest tuple the coin is the honest walk coin,
so `computeChipAt_honest_of_chalVal` needs no new hypothesis for slots `0..2`. -/
theorem thmWalkIOP_premise_at_honest :
    alphaC P.honestTuple.1 = P.optimized.family.computeWalkAlpha := rfl

/-- **Negative control at the paper's `WalkSat`:** with
`initial_count ≠ α`, `WalkSat` plus `out_walk = 0` plus `seed = α · root` does NOT force
`cur(1) = root`.  Two rows, root with one child (`fo = (1, 0)`); the cheating trace is
`cur 1 = root + (ic − α) · chld`, `cur 2 = chld`. -/
theorem walkSat_ic_ne_alpha_does_not_pin_root {K : Type} [Field K]
    (α ic root chld : K) (hic : ic ≠ α) (hchld : chld ≠ 0) :
    ∃ (cur : ℕ → K) (chld' : ℕ → ℕ → K) (ln count acc : ℕ → K),
      Walk.WalkSat cur chld' (fun i => if i = 1 then 1 else 0) ln count acc α (α * root) ic 2 ∧
        acc 2 = 0 ∧ cur 1 ≠ root := by
  refine ⟨fun i => if i = 1 then root + (ic - α) * chld else chld,
    fun i l => if i = 1 ∧ l = 1 then chld else 0,
    fun i => α ^ i, fun _ => ic * α, fun i => if i = 1 then α ^ 2 * chld else 0, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro i hi1 hih
      have : i = 1 := by omega
      subst this
      ring
    · simp
    · intro i hi1 hih
      have : i = 1 := by omega
      subst this
      simp
    · simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, and_self, if_pos]
      ring
    · intro i hi1 hih
      have : i = 1 := by omega
      subst this
      simp
  · simp
  · intro h
    have h' : root + (ic - α) * chld = root := by simpa using h
    have : (ic - α) * chld = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hic (sub_eq_zero.mp h1)
    · exact hchld h1

/-! ## The `αc` root event was not in the union. -/

/-- `FailureUnion` is a cylinder along the compute-walk coin `alphaC` (`JointCoins` first
coordinate): membership reads `nprSeed`, `alphaM`, `gamma` only. -/
theorem failureUnion_alphaC_cylinder {Λ : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (a a' g m z lmb : K) :
    ((a, g), (m, z)) ∈ ProductionP8Containment.FailureUnion T C lmb ↔
      ((a', g), (m, z)) ∈ ProductionP8Containment.FailureUnion T C lmb := by
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union,
    mem_zeroSeedFailureEvent_iff, mem_collisionFailureEvent_iff,
    TemplateRawJointSoundness.mem_specializedTopologyFailureEvent_iff,
    mem_guardedAxisFailureEvent_iff, SizeWindowCounting.mem_SizeWindowFailure_iff,
    nprSeed, alphaM, gamma]

/-- **Negative control at `WalkSat` with `initial_count = α`:** for a fixed cheating trace,
one `α₀ ≠ 0` accepts it (`out_walk = 0`) although `cur(1) ≠ root`.  So `cur(1) = root` is
a theorem only outside a root event on `α` — the paper's `h/|𝕂|` — which the union does
not carry (`failureUnion_alphaC_cylinder`). -/
theorem walkSat_root_needs_alpha_event {K : Type} [Field K] (α₀ root : K) (hα : α₀ ≠ 0) :
    ∃ (cur : ℕ → K) (chld' : ℕ → ℕ → K) (ln count acc : ℕ → K),
      Walk.WalkSat cur chld' (fun i => if i = 1 then 1 else 0) ln count acc α₀ (α₀ * root) α₀ 2
        ∧ acc 2 = 0 ∧ cur 1 ≠ root := by
  refine ⟨fun i => if i = 1 then root + α₀ else 0,
    fun i l => if i = 1 ∧ l = 1 then 1 else 0,
    fun i => α₀ ^ i, fun _ => α₀ * α₀, fun _ => 0, ?_, rfl, ?_⟩
  · refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro i hi1 hih
      have : i = 1 := by omega
      subst this
      ring
    · simp
    · intro i hi1 hih
      have : i = 1 := by omega
      subst this
      simp
    · simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, and_self, if_pos]
      ring
    · intro i hi1 hih
      have : i = 1 := by omega
      subst this
      simp
  · intro h
    have h' : root + α₀ = root := by simpa using h
    exact hα (by linear_combination h')

/-! ## The root/claim `γ`-collision
is not a `topologyBadGammas` pair; it is priced as the `γ`-half of `computeWalkRootEvent`
(`ComputeWalkRootEvents.gammaRootEvent`, `9/|𝕂|`). -/

omit hsat hax hbasis hwidth in
theorem optimizedFailureEvent_unfold
    (Qc₀ : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    P.optimizedFailureEvent Qc₀ Qm =
      liftP8Failure (FailureUnion P.strategy P.optimized.census P.objects.cfg.challenges.lam) ∪
        P.famIOEventOf Qc₀ Qm ∪
        liftTimestampFailure
          (OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc₀).length) ∪
        liftInterPoleFailure
          (interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm)
            (P.memoryBaseEnv Qm)) ∪
        liftP8Failure (P.computeWalkRootEvent Qc₀) ∪
        liftP8Failure (P.computeTilingEventOf Qc₀) ∪
        liftP8Failure (P.memoryTilingEventOf Qm) ∪
        liftP8Failure (P.computePrefixGammaEventOf Qc₀) ∪
        liftP8Failure (P.memoryPrefixGammaEventOf Qm) ∪
        liftP8Failure (P.memoryForestAlphaEventOf Qm) ∪
        P.decodedLambdaEventOf Qc₀ Qm ∪
        P.reqPairEventOf Qm :=
  rfl

omit hsat hax hbasis hwidth in
def p8Summand : Finset (OptimizedProductionChallengeTuple K F) :=
  liftP8Failure (FailureUnion P.strategy P.optimized.census P.objects.cfg.challenges.lam)

omit hsat hax hbasis hwidth in
theorem p8Summand_trace_free
    (Qc₀ : Fin P.computeChip.rap.w → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    P.optimizedFailureEvent Qc₀ Qm =
      p8Summand P ∪
        P.famIOEventOf Qc₀ Qm ∪
        liftTimestampFailure
          (OptimizedHostileTimestamps.TimestampCollisionEvent (P.hostileRequests Qc₀).length) ∪
        liftInterPoleFailure
          (interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm)
            (P.memoryBaseEnv Qm)) ∪
        liftP8Failure (P.computeWalkRootEvent Qc₀) ∪
        liftP8Failure (P.computeTilingEventOf Qc₀) ∪
        liftP8Failure (P.memoryTilingEventOf Qm) ∪
        liftP8Failure (P.computePrefixGammaEventOf Qc₀) ∪
        liftP8Failure (P.memoryPrefixGammaEventOf Qm) ∪
        liftP8Failure (P.memoryForestAlphaEventOf Qm) ∪
        P.decodedLambdaEventOf Qc₀ Qm ∪
        P.reqPairEventOf Qm :=
  rfl

/-- The `γ`-set on which `rlc γ u = rlc γ v` for two distinct ten-coordinate labels — the set
`Walk.rlc_collision_card_le` bounds. -/
def rootClaimBadGammas {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (u v : Fin 10 → K) : Finset K :=
  Finset.univ.filter fun γ => Walk.rlc γ u = Walk.rlc γ v

theorem rootClaimBadGammas_card_le {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {u v : Fin 10 → K} (h : u ≠ v) :
    (rootClaimBadGammas u v).card ≤ 9 :=
  Walk.rlc_collision_card_le h

/-- The pair is not degenerate: two distinct labels collide at `γ = 1` (coordinates `0`/`1`
shifted by `±1`).  So the event is a genuine `≤ 9/|𝕂|` event, not `∅`. -/
theorem rootClaimBadGammas_nonempty_example {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (v : Fin 10 → K) :
    let u : Fin 10 → K := fun k => if k = 0 then v 0 + 1 else if k = 1 then v 1 - 1 else v k
    u ≠ v ∧ (1 : K) ∈ rootClaimBadGammas u v := by
  intro u
  constructor
  · intro h
    have := congrFun h 0
    simp [u] at this
  · simp only [rootClaimBadGammas, Finset.mem_filter, Finset.mem_univ, true_and, Walk.rlc,
      one_pow, one_mul]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, u]
    simp
    ring

/-- `computeSlotBadGammas t i` compares the parent's DECLARED slot-`i` payload with the
child's OWN payload (`Fin 9` encode) — a `(row, slot)` pair.  The root label vs the claim's
label is a `Fin 10` pair of a different shape; no `topologyBadGammas` member is built from it.
Receipt: under binding the union's `γ`-event is empty
(`Batch345.topologyBadGammas_empty_of_binding`) while `rootClaimBadGammas` need not be. -/
def rootClaimPairShape : String :=
  "rootClaimBadGammas (claimLabelVec z claim) (labelVecOfPub label₀) : Fin 10 pair; " ++
    "topologyBadGammas = ⋃ (row, slot) computeSlotBadGammas : Fin 9 declared-vs-own pairs"

/-! ## I. Status — what closed, what stops -/

/-- Closed here, at `computeChipAt c` for every `c`. -/
def CHIP_SFE_CLOSED : List String :=
  ["walkAccInit_eval_at_row0", "labelRLC_eval firstReader"]

theorem chip_sfe_closed_length : CHIP_SFE_CLOSED.length = 2 := by decide

theorem chip_sfe_closed_were_remaining :
    ∀ n ∈ CHIP_SFE_CLOSED, n ∈ Batch453.CHIP_SFE_REMAINING := by
  decide

def CHIP_SFE_REMAINING : List String :=
  ["initial_count is the package public, not alphaC (chip: computePublicOfTuple 0..2)",
    "alphaC root event h/|K| (main.tex:966) not in FailureUnion",
    "root/claim gamma collision not a topologyBadGammas pair",
    "strategyOfTraces takes TracesBindsHyps"]

theorem chip_sfe_remaining_length : CHIP_SFE_REMAINING.length = 4 := by decide

/-- Chip-closed publics stay `0`. -/
theorem chip_closed_publics_still_zero :
    Batch403.chipClosedPublics = 0 :=
  rfl

end

end Nock.RedTeam.Batch457

#print axioms Nock.RedTeam.Batch457.masks_at_row_at
#print axioms Nock.RedTeam.Batch457.root_cur_is_decoded_label
#print axioms Nock.RedTeam.Batch457.walkAccInit_row0_decoded
#print axioms Nock.RedTeam.Batch457.family_initialCount_at
#print axioms Nock.RedTeam.Batch457.thmWalkIOP_premise_holds
#print axioms Nock.RedTeam.Batch457.walkSat_ic_ne_alpha_does_not_pin_root
#print axioms Nock.RedTeam.Batch457.failureUnion_alphaC_cylinder
#print axioms Nock.RedTeam.Batch457.walkSat_root_needs_alpha_event
#print axioms Nock.RedTeam.Batch457.p8Summand_trace_free
#print axioms Nock.RedTeam.Batch457.rootClaimBadGammas_card_le
