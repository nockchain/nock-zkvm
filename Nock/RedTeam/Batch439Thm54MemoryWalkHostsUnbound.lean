/-
  Nock/RedTeam/Batch439Thm54MemoryWalkHostsUnbound.lean

  The memory twin of `Batch432`.

  * Homogeneity (§B): scaling the hosts `cur`/`cc`, the accumulator `acc` and the seed public by
    any `λ` preserves every hosted walk gate — the hosted chip accepted `λ·cur` with `cur ≠
    RLC^γ(label)`.  `WalkSat` form: `Batch432.walkSat_scale` (generic in the seed, so it is
    the `Corr:forest` seed `Σ RLC(root_i)·α^i` too, `:1006`).
  * `DeployedAcceptanceAt`'s memory conjunct is the chip RAP only (§D).

  * §E — the PACKAGE map's `initial_count` (`P.optimized.memoryPublic`) is
    `memoryWalkAlpha ^ kMem` at every `c` (`family_initialCount_at`, still true).  After
    walk-α the *chip's* `initial_count` is `alphaM c.1 ^ kMem`
    (`Batch475::memory_initialCount_is_coin`).  Memory twin of `Batch457::family_initialCount_at`.
  * Memory twin of `Batch459` §A.  `Batch459::walkSat_without_bfsValid`'s
    `h = 3, fo = (0,2,0)` witness is arity-agnostic and applies to the memory walk verbatim.
-/
import Lean
import Nock.Walk
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.RedTeam.Batch337Thm54HostileGapAudit
import Nock.RedTeam.Batch432Thm54WalkHostsUnbound
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch439

open Lean
open Nock
open Nock.Reified
open Nock.Framework
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.DeployedAcceptance
open scoped Polynomial

/-! ## A. Read-set instrument on `MixedExpr` -/

/-- Does the gate read `𝕂` role `r` on the current or the successor row? -/
def mixedReadsRole {F : Type} (r : ℕ) : MixedExpr F → Bool
  | .Var .traceCur i => i == r
  | .Var .traceNext i => i == r
  | .Var _ _ => false
  | .Lift _ => false
  | .Scale _ u => mixedReadsRole r u
  | .Const _ => false
  | .Add x y => mixedReadsRole r x || mixedReadsRole r y
  | .Sub x y => mixedReadsRole r x || mixedReadsRole r y
  | .Mul x y => mixedReadsRole r x || mixedReadsRole r y
  | .Neg x => mixedReadsRole r x
  | .Pow x _ => mixedReadsRole r x

/-- Reads one of the three hosted walk roles `34` (`cur`), `35` (`cc`), `36` (`cm`). -/
def readsHost {F : Type} (g : MixedExpr F) : Bool :=
  mixedReadsRole 34 g || mixedReadsRole 35 g || mixedReadsRole 36 g

/-- Positions `28`/`29` (hosted `walkCount1`,
`walkAccInit`) and `31`/`32` (hosted `walkCountStep`, `walkAccStep`) read a host; the other 41
gates — every class gate, the aggregator, the chain, the line gates, the terminal, the nine IO
gates and the two endpoints — do not.  So the hosts were bound by the walk gates alone. -/
theorem hosted_host_read_census :
    (MemoryPaperFactorization.hostedPaperKGates (F := ℚ) (K := ℚ)).map readsHost =
      [false, false, false, false, false, false, false, false, false, false,
       false, false, false, false, false, false, false, false, false, false,
       false, false, false, false, false, false, false,
       false, true, true, false, true, true, false,
       false, false, false, false, false, false, false, false, false,
       false, false] := by
  decide

/-- **Closed at the twenty-first move:** no committed memory `𝕂` gate reads a host role. -/
theorem committed_hosts_unread :
    (paperKGates (F := ℚ) (K := ℚ)).map readsHost = List.replicate 49 false := by
  decide

/-! ## B. Homogeneity of the hosted walk gates -/

section Scale

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Scale the hosts `cur` (`34`), `cc` (`35`), the accumulator `acc` (`33`) on both rows, and
the seed public (`1`), by `λ`. -/
def scaleHosts (l : K) (env : Env K) : Env K where
  trace := fun r => if r = 33 ∨ r = 34 ∨ r = 35 then l * env.trace r else env.trace r
  traceNext := fun r => if r = 33 ∨ r = 34 ∨ r = 35 then l * env.traceNext r else env.traceNext r
  chal := env.chal
  pub := fun j => if j = 1 then l * env.pub j else env.pub j

theorem hosted_ln1_scale (l : K) (eK : Env K) (eF : Env F) :
    (MixedExpr.Scale (bcur 4) (MixedExpr.ofExpr (Trans.walkLn1.subst walkBoundarySubst)) : MixedExpr F).eval
        (scaleHosts l eK) eF =
      (MixedExpr.Scale (bcur 4) (MixedExpr.ofExpr (Trans.walkLn1.subst walkBoundarySubst)) : MixedExpr F).eval
        eK eF := by
  simp [MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.eval, Expr.subst, walkBoundarySubst, extVar,
    Trans.walkLn1, Reified.tc, Reified.chl, scaleHosts]

theorem hosted_count1_scale (l : K) (eK : Env K) (eF : Env F) :
    (MixedExpr.Scale (bcur 4) (MixedExpr.ofExpr (Trans.walkCount1.subst walkBoundarySubst)) :
        MixedExpr F).eval (scaleHosts l eK) eF =
      (MixedExpr.Scale (bcur 4) (MixedExpr.ofExpr (Trans.walkCount1.subst walkBoundarySubst)) :
        MixedExpr F).eval eK eF := by
  simp [MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.eval, Expr.subst, walkBoundarySubst, extVar,
    Trans.walkCount1, Trans.pubv, Reified.tc, scaleHosts]

theorem hosted_accInit_scale (l : K) (eK : Env K) (eF : Env F) :
    (MixedExpr.Scale (bcur 4) (MixedExpr.ofExpr (Trans.walkAccInit.subst walkBoundarySubst)) :
        MixedExpr F).eval (scaleHosts l eK) eF =
      l * (MixedExpr.Scale (bcur 4) (MixedExpr.ofExpr (Trans.walkAccInit.subst walkBoundarySubst)) :
        MixedExpr F).eval eK eF := by
  simp [MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.eval, Expr.subst, walkBoundarySubst, extVar,
    Trans.walkAccInit, Trans.pubv, Reified.tc, scaleHosts]
  ring

theorem hosted_lnStep_scale (l : K) (eK : Env K) (eF : Env F) :
    (MixedExpr.Scale (.sub (.const 1) (bcur 5)) (MixedExpr.ofExpr (Trans.walkLnStep.subst walkSubst)) :
        MixedExpr F).eval (scaleHosts l eK) eF =
      (MixedExpr.Scale (.sub (.const 1) (bcur 5)) (MixedExpr.ofExpr (Trans.walkLnStep.subst walkSubst)) :
        MixedExpr F).eval eK eF := by
  simp [MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.eval, Expr.subst, walkSubst, extVar,
    Trans.walkLnStep, Trans.tn, Reified.tc, Reified.chl, scaleHosts]

theorem hosted_countStep_scale (l : K) (eK : Env K) (eF : Env F) :
    (MixedExpr.Scale (.sub (.const 1) (bcur 5)) (MixedExpr.ofExpr (Trans.walkCountStep.subst walkSubst)) :
        MixedExpr F).eval (scaleHosts l eK) eF =
      (MixedExpr.Scale (.sub (.const 1) (bcur 5)) (MixedExpr.ofExpr (Trans.walkCountStep.subst walkSubst)) :
        MixedExpr F).eval eK eF := by
  simp [MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.eval, Expr.subst, walkSubst, extVar,
    Trans.walkCountStep, Trans.tn, Reified.tc, scaleHosts]

theorem hosted_accStep_scale (l : K) (eK : Env K) (eF : Env F) :
    (MixedExpr.Scale (.sub (.const 1) (bcur 5)) (MixedExpr.ofExpr (Trans.walkAccStep.subst walkSubst)) :
        MixedExpr F).eval (scaleHosts l eK) eF =
      l * (MixedExpr.Scale (.sub (.const 1) (bcur 5)) (MixedExpr.ofExpr (Trans.walkAccStep.subst walkSubst)) :
        MixedExpr F).eval eK eF := by
  simp [MixedExpr.eval, MixedExpr.ofExpr_eval, Expr.eval, Expr.subst, walkSubst, extVar,
    Trans.walkAccStep, Trans.tn, Reified.tc, scaleHosts]
  ring

theorem hosted_terminal_scale (l : K) (eK : Env K) (eF : Env F) :
    (walkTerminal (F := F)).eval (scaleHosts l eK) eF = l * (walkTerminal (F := F)).eval eK eF := by
  simp [walkTerminal, MixedExpr.eval, scaleHosts]
  ring

/-- **The hosted walk gates accept the scaled trace.**  Every gate the hosted chip used to bind
`cur`/`cc` is either unchanged or multiplied by `λ`. -/
theorem hostedWalkGates_accept_scaled (l : K) (eK : Env K) (eF : Env F)
    (h : ∀ g ∈ hostedWalkGates (F := F), g.eval eK eF = 0) :
    ∀ g ∈ hostedWalkGates (F := F), g.eval (scaleHosts l eK) eF = 0 := by
  intro g hg
  have h0 := h g hg
  simp only [hostedWalkGates, hostedWalkInitGates, hostedWalkStepGates, List.mem_append,
    List.mem_map, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with (⟨e, (rfl | rfl | rfl), rfl⟩ | ⟨e, (rfl | rfl | rfl), rfl⟩) | rfl
  · rw [hosted_ln1_scale]; exact h0
  · rw [hosted_count1_scale]; exact h0
  · rw [hosted_accInit_scale, h0, mul_zero]
  · rw [hosted_lnStep_scale]; exact h0
  · rw [hosted_countStep_scale]; exact h0
  · rw [hosted_accStep_scale, h0, mul_zero]
  · rw [hosted_terminal_scale, h0, mul_zero]

/-- The scaled host is not the label RLC (`Batch432.scale_cur_ne_rlc`, restated for the memory
label width `6`). -/
theorem scaled_cur_ne_rlc {cur1 scale γ : K} {v : Fin 6 → K}
    (hscale : scale ≠ 1) (hcur : cur1 = Walk.rlc γ v) (hne0 : cur1 ≠ 0) :
    scale * cur1 ≠ Walk.rlc γ v :=
  Batch432.scale_cur_ne_rlc hscale hcur hne0

/-- **`WalkSat` with a free `cur` is homogeneous — forest form** (`Corr:forest`, the paper:
the seed `Σ_i RLC^γ(root_i)·α^i` scales with the hosts). -/
theorem walkSat_scale_forest
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed ic : K} {h : ℕ}
    (scale : K) (hw : Walk.WalkSat cur chld' fo ln count acc α seed ic h) :
    Walk.WalkSat (fun i => scale * cur i) (fun i l => scale * chld' i l) fo ln count
      (fun i => scale * acc i) α (scale * seed) ic h :=
  Batch432.walkSat_scale scale hw

end Scale

/-! ## D. `DeployedAcceptanceAt`'s memory conjunct is the chip RAP only -/

section Deployed

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem deployedAcceptanceAt_memory_is_chip
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X]) (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (h : DeployedAcceptanceAt P c Qc Qm) :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm :=
  h.memory_satisfies

/-! ## E. Coordinator check 1 — the memory walk's publics at `memoryChipAt c` -/

/-- Off the `initial_count` block `6..8`, the memory family map is the package map.
The chip's `initial_count` is now `Batch475::memory_initialCount_is_coin`. -/
theorem memory_publics_are_package_off_block
    (b : Module.Basis (Fin 3) F K) (claim : P8PublicClaim) (kMem : ℕ) (pkgPub : ℕ → F)
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (j : ℕ) (hj : ¬ (6 ≤ j ∧ j < 9)) :
    memoryPublicOfTuple b claim kMem pkgPub c j = pkgPub j :=
  memoryPublicOfTuple_eq_pkg b claim kMem pkgPub c j hj

/-- **`initial_count` of the PACKAGE map** (`P.optimized.memoryPublic`) is the family's
`memoryWalkAlpha ^ kMem` at every `c` — a pin, still true.  The *chip's* `initial_count`
(slots `6..8` of `familyMemoryPublic c`) is `alphaM c.1 ^ kMem`
(`Batch475::memory_initialCount_is_coin`). -/
theorem family_initialCount_at :
    (∑ k : Fin 3, P.optimized.memoryPublic (6 + 3 * 0 + (k : ℕ)) • P.optimized.basis k) =
      P.optimized.family.memoryWalkAlpha ^ P.optimized.family.problem.cfg.kMem :=
  P.optimized.memoryCoordinatePins.walkInitialCount

/-- Buildable
`memoryPublicTargets 1` may still carry the family seed in `pkgPub`;
the deployed subst writes `0`. -/
def family_seed_unpinned : String :=
  "walkSeed pin deleted; walkSubst/walkBoundarySubst pub 1 = Const 0"

theorem family_seed_unpinned_nonempty : family_seed_unpinned ≠ "" := by
  decide

/-- The walk-α the chip reads at `c` is the coin (`memoryKOfTuple c 3 = alphaM c.1`). -/
theorem walkAlpha_at_tuple (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) :
    memoryKOfTuple c 3 = alphaM c.1 := rfl

/-- `Thm:Walk_IOP`'s premise `initial_count = α^k` at `c` is a statement about the coin agreeing
with the family value — it holds at the honest tuple only by construction. -/
theorem thmWalkIOP_premise_iff
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) :
    (∑ k : Fin 3, P.optimized.memoryPublic (6 + 3 * 0 + (k : ℕ)) • P.optimized.basis k) =
        alphaM c.1 ^ P.optimized.family.problem.cfg.kMem ↔
      P.optimized.family.memoryWalkAlpha ^ P.optimized.family.problem.cfg.kMem =
        alphaM c.1 ^ P.optimized.family.problem.cfg.kMem := by
  rw [family_initialCount_at]

end Deployed

/-! ## F. Coordinator check 2 — no queue-length gate on the deployed memory chip -/

/-- Names under `Nock.Walk.QGate` (the structure and its projections). -/
def isQGateName (n : Name) : Bool := (`Nock.Walk.QGate).isPrefixOf n

def CHIP : Name := ``Nock.NockVMROM.Thm54.DeployedChipFamily.memoryChipAt
def WALK_INIT : Name := ``Nock.Reified.Trans.walkLn1
def IN_GATE : Name := ``Nock.NockVMROM.Thm54.MemoryWalkLabel.walkAccStepInGate
def TILING_THM : Name := ``Nock.Walk.Sf_tiling_of_qgate

/-! Negative: no `QGate` name is reached from the deployed memory chip's definition.  Throws on any failed
expectation. -/
run_cmd do
  let env ← getEnv
  let rChip := Batch337.reachSet env CHIP
  let rTiling := Batch337.reachSet env TILING_THM
  let chipQ := rChip.toList.filter isQGateName
  let tilingQ := rTiling.toList.filter isQGateName
  logInfo m!"memoryChipAt reach={rChip.size}; QGate names reached: {chipQ}"
  logInfo m!"Sf_tiling_of_qgate reach={rTiling.size}; QGate names reached: {tilingQ}"
  unless chipQ.isEmpty do
    throwError "deployed memory chip reaches a QGate name: {chipQ}"
  unless rChip.contains WALK_INIT do
    throwError "positive control failed: memoryChipAt does not reach Trans.walkLn1"
  unless rChip.contains IN_GATE do
    throwError "positive control failed: memoryChipAt does not reach walkAccStepInGate"
  unless !tilingQ.isEmpty do
    throwError "positive control failed: Sf_tiling_of_qgate reaches no QGate name"

/-- The gate that would close the tiling on the memory side (recorded, not added). -/
def MISSING_MEMORY_QGATE : String :=
  "Nock.Walk.QGate on the deployed memory chip (queue-length column; Corr:forest q0 = k)"

end Nock.RedTeam.Batch439

#print axioms Nock.RedTeam.Batch439.hosted_host_read_census
#print axioms Nock.RedTeam.Batch439.committed_hosts_unread
#print axioms Nock.RedTeam.Batch439.hostedWalkGates_accept_scaled
#print axioms Nock.RedTeam.Batch439.family_initialCount_at
