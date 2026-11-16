/-
  Nock/RedTeam/Batch706Thm54SplitRetypeReceipts.lean

  * The old `hbinds` was unsatisfiable at
    `3 ≤ |K|` (`Batch573.tracesBindsAll_unsat`).
-/
import Lean
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch332Thm54ZModLiterals
import Nock.RedTeam.Batch531Thm54MemFirstAndReady
import Nock.RedTeam.Batch573Thm54SeedLocal
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch706

open scoped Polynomial
open Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment


section P1

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [charRing : CharP K (ringChar K)]

/-- Every honest strategy binds at every coin, projected from
`BareSemanticSupport.binds`. -/
theorem p1_honest
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (S : BareSemanticSupport F K V) (ω : JointCoins K) (lmb : K) :
    (ProductionStrategy.ofBare S).BindsAtCoin ω lmb :=
  ProductionStrategy.honestBinds S ω lmb

/-- The split forgets only a proof: equal verifier and skeleton ⇒ equal strategies. -/
theorem p1_ext (T U : ProductionStrategy F K)
    (hv : T.verifier = U.verifier) (hs : T.skeleton = U.skeleton) : T = U :=
  ProductionStrategy.ext_of_verifier_skeleton hv hs

end P1

section P1Hostile

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- `strategyOfTraces` takes no binding hypothesis; its `BindsAtCoin` at the
sampled coin is a theorem GIVEN the tree bindings `hc` / `hm`. -/
theorem p1_hostile
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hc : ∀ hz : nprSeed c.1 ≠ 0,
      SemanticStrategy.ComputeTreeBinds (nprSeed c.1)
        (decodedSkeletonOf P Qc Qm).computeTree
        (specializedProblem (timestampOfTraces P Qc Qm c h)
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).exec.computeTree)
    (hm : ∀ hz : nprSeed c.1 ≠ 0,
      List.Forall₂ (SemanticStrategy.MemoryTreeBinds (nprSeed c.1))
        (decodedSkeletonOf P Qc Qm).memoryForest
        (specializedProblem (timestampOfTraces P Qc Qm c h)
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).exec.memoryForest) :
    (strategyOfTraces P Qc Qm c h).BindsAtCoin c.1 c.2.2.2.lambda :=
  strategyOfTraces_bindsAtCoin P Qc Qm c h hc hm

theorem p1_hostile_is_batch531
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    (strategyOfTraces P Qc Qm c h).BindsAtCoin c.1 c.2.2.2.lambda ↔
      Nock.RedTeam.Batch531.TracesBindsAtSeed P Qc Qm c h :=
  Iff.rfl

/-- …and the universal form is still refuted for the traces (no collision event):
`(strategyOfTraces …).BindsAll` is false at `3 ≤ |K|`. -/
theorem p1_hostile_bindsAll_refuted
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) (h3 : 3 ≤ Fintype.card K) :
    ¬ (strategyOfTraces P Qc Qm c h).BindsAll :=
  Nock.RedTeam.Batch573.tracesBindsAll_unsat P Qc Qm c h h3

/-- Every package strategy binds everywhere (it is `ofBare` of the scan support). -/
theorem package_strategy_bindsAtCoin (ω : JointCoins K) (lmb : K) :
    P.strategy.BindsAtCoin ω lmb :=
  P.optimized.strategy_bindsAll.atCoin ω lmb

end P1Hostile


section P2

open Nock.RedTeam.Batch332

local instance charRingDK706 : CharP DK (ringChar DK) := ringChar.charP DK
local instance : Fact (Nat.Prime 769) := ⟨by norm_num⟩
noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _

/-- The concrete coin `((αc, γ), (αm, z)) = ((0, 0), (0, 1))`. -/
noncomputable def ω₀ : JointCoins DK := ((0, 0), (0, 1))

theorem nprSeed_ω₀ : nprSeed ω₀ = 1 := rfl

theorem nprSeed_ω₀_ne_zero : nprSeed ω₀ ≠ 0 := by
  rw [nprSeed_ω₀]
  exact one_ne_zero

theorem p2_tierA_bindsAtCoin :
    ∃ (hOrb : ℕ) (Pk : OptimizedFullStrictNockVMROMPackage (ZMod 769) DK hOrb),
      OptimizedFullStrictThm54Statement Pk ∧
        nprSeed ω₀ ≠ 0 ∧
        Pk.strategy.BindsAtCoin ω₀ MemoryTable.formRDefault := by
  obtain ⟨Pk, hS, _⟩ := b332_tierA_from_zmod
  exact ⟨_, Pk, hS, nprSeed_ω₀_ne_zero,
    Pk.optimized.strategy_bindsAll.atCoin ω₀ MemoryTable.formRDefault⟩

end P2

end Nock.RedTeam.Batch706


open Lean Elab Command Meta

namespace Nock.RedTeam.Batch706

def retired : List Name :=
  [`Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.semantics,
   `Nock.NockVMROM.Thm54.ProductionP8Containment.SemanticSupportAt,
   `Nock.NockVMROM.Thm54.ProductionP8Containment.SemanticSupportAt.ofBare,
   `Nock.NockVMROM.Thm54.ProductionP8Containment.SemanticSupportAt.ofBare_skeleton,
   `Nock.NockVMROM.Thm54.StrategyOfTracesCore.TracesBindsHyps,
   `Nock.RedTeam.Batch531.semanticSupportAt_of_seed,
   `Nock.RedTeam.Batch531.tracesSpecializedExec,
   `Nock.RedTeam.Batch531.tracesSpecializedExec_eq_strategy]

def landed : List Name :=
  [``Nock.NockVMROM.Thm54.ProductionP8Containment.BareSemanticSupport,
   ``Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.BindsAtCoin,
   ``Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.honestBinds,
   ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces_bindsAtCoin,
   ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces,
   ``Nock.RedTeam.Batch531.tracesBindsAtSeed_of_tree]

run_cmd do
  let env ← getEnv
  for n in landed do
    unless (env.find? n).isSome do
      throwError m!"P3 positive control: {n} missing"
  for n in retired do
    if (env.find? n).isSome then
      throwError m!"P3: retired name still present: {n}"
  logInfo m!"P3 retired absent ({retired.length}): {retired}; landed present ({landed.length})"

def binderCounts (n : Name) : MetaM (Nat × Nat) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ => do
    let mut expl := 0
    for x in xs do
      if (← x.fvarId!.getDecl).binderInfo == .default then expl := expl + 1
    return (xs.size, expl)

def kernelWhitelist : List Name := [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let nZ := ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod
  let (t, e) ← liftTermElabM (binderCounts nZ)
  unless t == 27 && e == 14 do
    throwError m!"P4: nockCompiles_zmod {t}/{e}, expected 27/14"
  for n in [nZ, ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package] do
    let axs ← liftCoreM (Lean.collectAxioms n)
    for a in axs do
      unless kernelWhitelist.contains a do
        throwError m!"P4: {n} depends on non-whitelisted axiom {a}"
    logInfo m!"P4 axioms {n}: {axs}"
  logInfo m!"P4 nockCompiles_zmod {t}/{e}"

/-- Content hash of `TraceGen/Gen.lean` in THIS release. This release's `Gen.lean` is a comment-only edit of the
unpublished development `Gen.lean` this receipt was first written against (content hash `219383736119927922`):
comments and whitespace changed, code identical. -/
def genHashScrubbed : UInt64 := 15342590535669274628

run_cmd do
  let s ← IO.FS.readFile "Nock/NockVMROM/Thm54/TraceGen/Gen.lean"
  unless hash s == genHashScrubbed do
    throwError m!"P4: Gen.lean content hash {hash s} ≠ {genHashScrubbed} (this release's Gen.lean; code identical to the development version)"
  logInfo m!"P4 Gen.lean content hash {hash s} = this release's Gen.lean (comment-only edit of the development Gen.lean; code identical)"

end Nock.RedTeam.Batch706

#print axioms Nock.RedTeam.Batch706.p1_honest
#print axioms Nock.RedTeam.Batch706.p1_ext
#print axioms Nock.RedTeam.Batch706.p1_hostile
#print axioms Nock.RedTeam.Batch706.p1_hostile_is_batch531
#print axioms Nock.RedTeam.Batch706.p1_hostile_bindsAll_refuted
#print axioms Nock.RedTeam.Batch706.package_strategy_bindsAtCoin
#print axioms Nock.RedTeam.Batch706.p2_tierA_bindsAtCoin
