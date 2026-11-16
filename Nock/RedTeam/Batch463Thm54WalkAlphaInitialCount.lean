/-
  Nock/RedTeam/Batch463Thm54WalkAlphaInitialCount.lean

  **`initial_count = α` on the deployed compute chip.**

  `Thm:Walk_IOP` recognizes `rvt_root` with
  `(seed, initial_count) = (α · RLC^γ(rvt_root), α)` (`:962`, `:966`) and `count(1) =
  initial_count · Σ st · α^fanout` (`:813`).

  Every chip theorem below is at `rowEnvAt P c Qc` for a trace `Qc` accepted at
  `computeChipAt c`; no honest-package object stands in for a committed trace.
-/
import Nock.Walk
import Nock.RedTeam.Batch457Thm54RootLabelFromChip
import Nock.RedTeam.Batch459Thm54ComputeTopologyStop
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch463

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
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
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open Nock.RedTeam.Batch398
open Nock.RedTeam.Batch438
open Nock.RedTeam.Batch455
open Nock.RedTeam.Batch457
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.RedTeam.Batch459
open Module

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])

/-! ## A. The chip reads the coin -/

/-- **Extension public `0` IS the tuple's
compute-walk coin at every `c`, every trace, every row.** -/
theorem initialCount_is_coin (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).toSourceEnv.pub 0 = alphaC c.1 :=
  family_initialCount_at P c Qc i

/-- The family public slots `0..2` are the `𝔽`-coordinates of `alphaC c.1`. -/
theorem family_alpha_slots (k : Fin 3) :
    P.familyComputePublic c (k : ℕ) = coord P.optimized.basis (alphaC c.1) k :=
  computePublicOfTuple_alpha_coord P.optimized.basis P.optimized.verifier.raw.claim
    P.optimized.computePublic c k

/-- **`Thm:Walk_IOP`'s premise `initial_count = α` (`:962`, `:966`) holds unconditionally.** -/
theorem thmWalkIOP_premise_unconditional (i : Fin (rows P)) :
    (rowEnvAt P c Qc i).toSourceEnv.pub 0 = alphaC c.1 :=
  thmWalkIOP_premise_holds P c Qc i

theorem initialCount_varies_with_tuple
    (c' : OptimizedProductionChallengeTuple K F)
    (Qc' : Fin (P.computeChipAt c').rap.w → F[X])
    (hne : alphaC c.1 ≠ alphaC c'.1) (i i' : Fin (rows P)) :
    (rowEnvAt P c Qc i).toSourceEnv.pub 0 ≠ (rowEnvAt P c' Qc' i').toSourceEnv.pub 0 := by
  rw [initialCount_is_coin, initialCount_is_coin]
  exact hne

/-! ## B. The row-0 identity at the coin, and `WalkSat` at the recognizer inputs -/

variable (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsat
include hax hbasis hwidth

/-- **`αc · RLC^γ(label₀) + acc_walk(0) = αc · cc(0) + seedOfClaim c`** — the paper's `:810` at
`(seed, initial_count) = (α · RLC^γ(rvt_root), α)`, for every `c` and every accepted trace, with
`label₀` the decoded row-0 `LT_comp` label. -/
theorem row0_identity_at_coin :
    ∃ st0 : State,
      OneHotSelector (rowEnvAt P c Qc (firstRow P)).toSourceEnv st0 ∧
      alphaC c.1 * Walk.rlc (gamma c.1)
          (labelVecOfPub (decodePub (rowEnvAt P c Qc (firstRow P)) st0)) +
        (initialOverlayCoord 1).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv =
      alphaC c.1 *
          (childSumCC firstReader).eval (rowEnvAt P c Qc (firstRow P)).toSourceEnv +
        seedOfClaim P.optimized.verifier.raw.claim c :=
  walkAccInit_row0_decoded P c Qc hsat hax hbasis hwidth

theorem deployed_walkSat_at_recognizer_inputs :
    WalkSat (curW P c Qc hsat) (chldW P c Qc hsat) (foW P c Qc hsat) (lnW P c Qc)
      (countW P c Qc) (accW P c Qc) (alphaC c.1)
      (Walk.rlc (gamma c.1) (claimLabelVec (nprSeed c.1) P.optimized.verifier.raw.claim) *
        alphaC c.1)
      (alphaC c.1) (rows P) :=
  deployed_walkSat P c Qc hsat hax hbasis hwidth

/-- `count(1) = α · α^{fanout(state₀)}` — the paper's `:813` with `initial_count = α`. -/
theorem count1_at_coin :
    countW P c Qc 1 = alphaC c.1 * alphaC c.1 ^ (foW P c Qc hsat 1) :=
  (deployed_walkSat P c Qc hsat hax hbasis hwidth).count1

/-! ## C. The honest chip needs no new hypothesis -/

omit hsat in
/-- At the package's honest tuple the coin IS the family's `computeWalkAlpha` (`rfl`), so
`OptimizedStrictFullPackage.computeChipAt_honest_of_chalVal` discharges the new slots `0..2`
with `rfl` and its hypothesis list is unchanged. -/
theorem honest_tuple_alpha_is_family_alpha :
    alphaC P.honestTuple.1 = P.optimized.family.computeWalkAlpha :=
  thmWalkIOP_premise_at_honest P

omit hsat in
/-- The generic honest identity, with the coin condition made explicit: any tuple carrying
the family's walk coin and seed reads the package map. -/
theorem family_publics_eq_pkg_of_coin
    (hα : alphaC c.1 = P.optimized.family.computeWalkAlpha)
    (hseed : seedOfClaim P.optimized.verifier.raw.claim c = P.optimized.family.computeWalkSeed) :
    P.familyComputePublic c = P.optimized.computePublic :=
  computePublicOfTuple_eq_pkg_of_seed P.optimized.basis P.optimized.verifier.raw.claim
    P.optimized.family P.optimized.family.problem.cfg.compRows_pos P.optimized.computePublic
    c P.optimized.computePublicPins hα hseed

/-! ## D. Completeness positive control at the paper's `WalkSat` (every `α`) -/

section Completeness
variable {L : Type} [Field L]

/-- The two-row fanout column: root with one child, child a leaf (`Batch461::fo2`). -/
def fo2 : ℕ → ℕ := fun i => if i = 1 then 1 else 0

/-- **The honest two-node tree is accepted at EVERY coin once `initial_count = α`** — the
converse of `Batch461::honest_two_node_walkSat_iff` (accepted iff `ic = α`) in the direction
this move needs: completeness holds at every `α`, not at one coin. -/
theorem honest_two_node_accepted_at_every_alpha (root X α : L) :
    ∃ (ln count acc : ℕ → L),
      WalkSat (fun i => if i = 1 then root else X) (fun i l => if i = 1 ∧ l = 1 then X else 0)
        fo2 ln count acc α (α * root) α 2 ∧ acc 2 = 0 := by
  refine ⟨fun i => α ^ i, fun _ => α * α, fun i => if i = 1 then α * α * X else 0, ?_, rfl⟩
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro i hi1 hih
    ring
  · simp [fo2]
  · intro i hi1 hih
    have : i = 1 := by omega
    subst this
    simp [fo2]
  · simp only [fo2, Finset.Icc_self, Finset.sum_singleton, pow_one, and_self, if_pos]
    ring
  · intro i hi1 hih
    have : i = 1 := by omega
    subst this
    simp only [fo2, show (1 : ℕ) + 1 = 2 from rfl, show ¬ ((2 : ℕ) = 1) by norm_num, if_false,
      if_true, Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), Finset.sum_empty]
    ring

end Completeness

/-! ## E. Record -/

/-- `Batch457.CHIP_SFE_REMAINING[0]` — closed by this batch. -/
def CLOSED_HERE : List String :=
  ["initial_count is the package public, not alphaC (chip: computePublicOfTuple 0..2)"]

theorem closed_here_was_remaining :
    ∀ n ∈ CLOSED_HERE, n ∈ Batch457.CHIP_SFE_REMAINING := by
  decide

/-- The watchlist widening and its negative control, as measured. -/
def WATCHLIST_CONTROL : List String :=
  ["FrozenClosure.watchlist += DeployedChipFamily.computePublicOfTuple",
    "control: else-branch `pkgPub j + 0` -> check-frozen exit 1, fingerprint " ++
      "9841463719093856184 -> 2370672063448031595; reverted, exit 0 (closure 292)"]

theorem watchlist_control_length : WATCHLIST_CONTROL.length = 2 := by decide

end

end Nock.RedTeam.Batch463

#print axioms Nock.RedTeam.Batch463.initialCount_is_coin
#print axioms Nock.RedTeam.Batch463.initialCount_varies_with_tuple
#print axioms Nock.RedTeam.Batch463.row0_identity_at_coin
#print axioms Nock.RedTeam.Batch463.deployed_walkSat_at_recognizer_inputs
#print axioms Nock.RedTeam.Batch463.honest_tuple_alpha_is_family_alpha
#print axioms Nock.RedTeam.Batch463.honest_two_node_accepted_at_every_alpha
