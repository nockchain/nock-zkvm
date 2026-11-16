/-
  Nock/RedTeam/Batch438Thm54InGateWalkReceipts.lean

  A. **`Batch432`'s finding trace is rejected — the gate is `walkAccStep`.**  The deployed
     `walkAccStep` now reads `cur(i+1) = labelRLC nextReader`, whose state-`st` branch reads no
     tag host of `st` (`label_branch_reads_no_own_host`).  `childSumAt nextReader.s1` is
     `Const 0` and reads nothing (fanout 0); only the unused `childTagHost nextReader.s1 0`
     expression reads index `21` (`cc_reads_batch432_host_as_tag`).  Index `21` *is* read on
     the successor row by `walkAccStep` as `e.leaf` in every non-`s1` label branch.  There is
     no column left to scale: `cur` is a function of the row (`label_rlc_is_decoded_label`).

  B. **Hostile evaluation.**  On ANY row whose selectors are one-hot at `st` — a fact the chip's
     booleanity/one-hot gates supply for every accepted trace — `cur(i+1)` is `RLC^γ` of the
     ten-coordinate label of the DECODED row (`Nock.Reified.pubOfState` of the source
     environment), `γ` read at slot `10`.

  C. **Honest positive control.**  The honest chip `P.computeChip` is definitionally
     `P.computeChipAt P.honestTuple` (`computeChipAt_honest_of_chalVal`, `chalValOfTuple_honest`),
     and `chalValOfTuple_honest` now covers slot `10` (`computeKOfTuple_honest` case `10`:
     `gamma honestJointCoins = family.walkGamma`).
-/
import Nock.NockVMROM.Thm54.ComputeWalkLabel
import Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
import Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.ComputeEnvAgreement
import Nock.NockVMROM.Thm54.ComputeWalkSeed
import Nock.RedTeam.Batch432Thm54WalkHostsUnbound
import Nock.NockVMROM.Thm54.P8Core.Batch438Thm54InGateWalkReceipts
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch438

open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open OptimizedComputeSubstitution
open OptimizedComputeGateBasis

/-! ## A. Read-set: the walk's `cur` reads no hosted column -/

/-- Successor-row trace indices an expression reads. -/
def traceNextIdx : Expr → List ℕ
  | .Var .traceNext i => [i]
  | .Var _ _ | .Const _ => []
  | .Add a b | .Sub a b | .Mul a b => traceNextIdx a ++ traceNextIdx b
  | .Neg a | .Pow a _ => traceNextIdx a

/-- The three child-tag hosts of state `st` (Option A): `overlayCoord 2..4`. -/
def tagHostIdxOf (st : State) : List ℕ :=
  [ext0 + 3 * overlayANat st + 2, ext0 + 3 * overlayBNat st + 0, ext0 + 3 * overlayBNat st + 1]

/-- At state `s1` the first tag host is `Batch432`'s former `cur` host (index `21`). -/
theorem s1_tag_host_is_batch432_cur_host :
    (tagHostIdxOf .s1)[0]? = some Batch432.curHostAtS1 := by
  decide

/-- **The label reads no host of its own state.**  In every state branch of the successor-row
label RLC, the columns read are the selectors and the genuine / restored fingerprint sources,
never a tag host of that state. -/
theorem label_branch_reads_no_own_host :
    ∀ st : State, ∀ i ∈ traceNextIdx (labelRLCAt nextReader st), i ∉ tagHostIdxOf st := by
  decide

/-- The former `cur` host at `s1` (index `21`) is not read by the `s1` label branch. -/
theorem batch432_cur_host_not_read_by_label :
    Batch432.curHostAtS1 ∉ traceNextIdx (labelRLCAt nextReader .s1) := by
  decide

/-- Positive control for the unused `childTagHost` expression: it DOES read index `21`
(the declared state-tag host of `s1` slot `0`).  The deployed `childSumAt nextReader.s1`
is `Const 0` and reads nothing; index `21` is not a `cc` input at `s1`. -/
theorem cc_reads_batch432_host_as_tag :
    Batch432.curHostAtS1 ∈ traceNextIdx (childTagHost nextReader .s1 0) := by
  decide

/-! ## B. The in-gate acc step and its hostile evaluation -/

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- **Hostile: `cur(i+1)` is `RLC^γ` of the decoded successor label.**  For any environment
whose successor-row selectors are one-hot at `st`, the in-gate label RLC evaluates to `rlc` at
the slot-`10` coin of the ten-coordinate label of `pubOfState` of the decoded source row. -/
theorem label_rlc_is_decoded_label (env : Env K) (st : State)
    (hsel : ∀ st', env.traceNext (Nock.Reified.opCol st') = if st' = st then 1 else 0) :
    (labelRLC nextReader).eval env =
      Walk.rlc (env.chal 10)
        (labelVecOfPub (pubOfState (Env.ofSubst computeSubst (shiftNext env)) st)) := by
  rw [labelRLC_next_eval]
  have hsel' : ∀ st', (shiftNext env).trace (Nock.Reified.opCol st') =
      if st' = (pubOfState (Env.ofSubst computeSubst (shiftNext env)) st).state then 1 else 0 :=
    fun st' => hsel st'
  apply labelRLC_eval curReader (shiftNext env) _ (env.chal 10) hsel'
  · intro role c hr hc
    rw [sourcePubAtR_cur,
      OptimizedComputeSameExecution.sourcePubAt_eval_eq_semanticPub _ _ hsel' role c hr hc,
      pubFingerprint_pubOfState, fpCoordinate_fpOf]
    exact (decoded_source_trace (shiftNext env) ⟨role, hr⟩ ⟨c, hc⟩).symm
  · rfl

/-! ## C. Honest positive control -/

theorem honest_walk_gamma_slot
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb : ℕ} (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)
    (k : Fin 3) :
    DeployedChipFamily.computeChalValOfTuple P.optimized.basis P.honestTuple (3 * 10 + (k : ℕ)) =
        P.optimized.computeChallenge (3 * 10 + (k : ℕ)) ∧
      DeployedChipFamily.computeKOfTuple P.honestTuple 10 = P.optimized.family.walkGamma :=
  ⟨P.chalValOfTuple_honest 10 k, P.computeKOfTuple_honest 10⟩

/-! ## D. -/

/-- The verifier's seed candidate is a function
of the claim and the coins `(z, αc, γ)` only — constant walk, no trace value. -/
theorem seed_scaffold_is_claim_function
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [Fintype F]
    (claim : P8PublicClaim)
    (c c' : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (hz : nprSeed c.1 = nprSeed c'.1) (hγ : gamma c.1 = gamma c'.1)
    (hα : alphaC c.1 = alphaC c'.1) :
    ComputeWalkSeed.seedOfClaim claim c = ComputeWalkSeed.seedOfClaim claim c' :=
  ComputeWalkSeed.seedOfClaim_congr claim c c' hz hγ hα

end Nock.RedTeam.Batch438

#print axioms Nock.RedTeam.Batch438.label_branch_reads_no_own_host
#print axioms Nock.RedTeam.Batch438.batch432_cur_host_not_read_by_label
#print axioms Nock.RedTeam.Batch438.cc_reads_batch432_host_as_tag
#print axioms Nock.RedTeam.Batch438.walkAccStep_inGate_eval
#print axioms Nock.RedTeam.Batch438.label_rlc_is_decoded_label
