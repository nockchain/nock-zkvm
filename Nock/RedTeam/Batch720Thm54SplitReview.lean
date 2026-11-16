/-
  Nock/RedTeam/Batch720Thm54SplitReview.lean

  * **Check 1.**
  * **Check 2 (meaning).**  Every package strategy IS `ProductionStrategy.ofBare` of the scan-derived
    `BareSemanticSupport` (`package_strategy_is_ofBare`, `rfl`) and so binds everywhere
    (`strategy_bindsAll`, a theorem of the package's fields) — so although the TYPE `ProductionStrategy`
    is wider, the class of PACKAGES `of_package` quantifies over is not: `package_strategy_bindsAll_all`
    restates it for every package.  Equal verifier and skeleton ⇒ equal strategies (production
    `ext_of_verifier_skeleton`).
  * `Batch706.p2_tierA_bindsAtCoin` instantiates the sampled-`λ` binder at
    the fixture value `formRDefault = 2`; `p2_tierA_bindsAtCoin_every_lambda` states it at every `λ : DK`
    for the same `nockCompiles_zmod` package and the same concrete coin `ω₀` (`nprSeed ω₀ = 1 ≠ 0`), so the
    fixture value hides no gap.
  * **Check 3.**  `strategyOfTraces_bindsAtCoin`'s type mentions `ComputeTreeBinds` and `MemoryTreeBinds`
    (`hostile_binds_carries_tree_bindings`): the hostile `BindsAtCoin` is never hypothesis-free.
  * **Check 5 (closures).**  (`strategy_bindsAll` itself is a
    convenience theorem outside the closure.)
  * **Check 6.**
-/
import Lean
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.StrategyOfTracesCore
import Nock.NockVMROM.Thm54.ProductionAsymptotic
import Nock.NockVMROM.Thm54.StrictAsymptoticSecurity
import Nock.RedTeam.Batch332Thm54ZModLiterals
import Nock.RedTeam.Batch706Thm54SplitRetypeReceipts
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Lean Elab Command

namespace Nock.RedTeam.Batch720

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

/-! ## Check 2 — the widened type does not widen the packages -/

section Meaning
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
  [FiniteDimensional F K]

/-- Every package's strategy IS the honest strategy `ProductionStrategy.ofBare` of the scan-derived
`BareSemanticSupport` (definitional): the widened TYPE admits other inhabitants, the PACKAGES do not
produce any. -/
theorem package_strategy_is_ofBare {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.strategy = ProductionStrategy.ofBare
      (RawSemanticAssembly.bareSemanticSupport_of_scan P.optimized.verifier P.optimized.commitment
        P.optimized.claim_eq P.optimized.shapeMatch P.optimized.rowFrame P.optimized.scan) :=
  rfl

/-- Every package's strategy binds at every specialization — the content the old field carried is a
theorem of the package. -/
theorem package_strategy_bindsAll_all {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb) :
    P.strategy.BindsAll :=
  P.optimized.strategy_bindsAll

/-- Hence `BindsAtCoin` at every coin and every `λ` for every package strategy. -/
theorem package_strategy_bindsAtCoin_all {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (ω : JointCoins K) (lmb : K) : P.strategy.BindsAtCoin ω lmb :=
  (package_strategy_bindsAll_all P).atCoin ω lmb

end Meaning


section P2EveryLambda

open Nock.RedTeam.Batch332

local instance charRingDK720 : CharP DK (ringChar DK) := ringChar.charP DK
local instance : Fact (Nat.Prime 769) := ⟨by norm_num⟩
noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _

theorem p2_tierA_bindsAtCoin_every_lambda :
    ∃ (hOrb : ℕ) (Pk : OptimizedFullStrictNockVMROMPackage (ZMod 769) DK hOrb),
      OptimizedFullStrictThm54Statement Pk ∧
        nprSeed Nock.RedTeam.Batch706.ω₀ ≠ 0 ∧
        ∀ lmb : DK, Pk.strategy.BindsAtCoin Nock.RedTeam.Batch706.ω₀ lmb := by
  obtain ⟨Pk, hS, _⟩ := b332_tierA_from_zmod
  exact ⟨_, Pk, hS, Nock.RedTeam.Batch706.nprSeed_ω₀_ne_zero,
    fun lmb => Pk.optimized.strategy_bindsAll.atCoin Nock.RedTeam.Batch706.ω₀ lmb⟩

end P2EveryLambda

/-! ## Check 3 / Check 5 -/

run_cmd do
  let env ← getEnv
  -- check 3: the hostile BindsAtCoin theorem carries the tree bindings in its TYPE
  let some ci := env.find? ``Nock.NockVMROM.Thm54.StrategyOfTracesCore.strategyOfTraces_bindsAtCoin
    | throwError "strategyOfTraces_bindsAtCoin missing"
  let used := ci.type.getUsedConstants
  unless used.contains ``Nock.NockVMROM.Thm54.SemanticStrategy.ComputeTreeBinds ∧
      used.contains ``Nock.NockVMROM.Thm54.SemanticStrategy.MemoryTreeBinds do
    throwError "hostile BindsAtCoin is stated without hc/hm"
  logInfo "hostile_binds_carries_tree_bindings: strategyOfTraces_bindsAtCoin's type mentions ComputeTreeBinds and MemoryTreeBinds"

partial def reach (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if !(`Nock).isPrefixOf n then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

run_cmd do
  let env ← getEnv
  let roots := #[``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_zmod,
    ``Nock.NockVMROM.Thm54.TraceGen.GoodSeed.nockCompiles_p76,
    ``Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package]
  let forbidden := #[``Nock.NockVMROM.Thm54.ProductionAsymptotic.FamilyPointwiseHypotheses,
    ``Nock.NockVMROM.Thm54.StrictAsymptoticSecurity.StrategyFamilyData]
  let forbiddenMods : Array Name := #[`Nock.RedTeam.Batch490Thm54TopologyAssembly,
    `Nock.RedTeam.Batch501Thm54MemoryTopology]
  let positive := #[``Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.BindsAtCoin,
    ``Nock.NockVMROM.Thm54.RawSemanticAssembly.productionStrategy_of_scan_bindsAll,
    ``Nock.NockVMROM.Thm54.ProductionP8Containment.ProductionStrategy.BindsAll]
  for r in roots do
    let cl := reach env #[r]
    for f in forbidden do
      if cl.contains f then throwError m!"{f} reached from {r}"
    let hits := cl.toArray.filter fun n => match env.getModuleFor? n with
      | some m => forbiddenMods.contains m | none => false
    unless hits.isEmpty do throwError m!"Batch490/501 reached from {r}"
    for p in positive do
      unless cl.contains p do throwError m!"positive control: {p} not reached from {r}"
    logInfo m!"{r}: closure {cl.size}; no FamilyPointwiseHypotheses/StrategyFamilyData/Batch490/501; BindsAtCoin, BindsAll and productionStrategy_of_scan_bindsAll reached"

end Nock.RedTeam.Batch720

#print axioms Nock.RedTeam.Batch720.package_strategy_is_ofBare
#print axioms Nock.RedTeam.Batch720.package_strategy_bindsAll_all
#print axioms Nock.RedTeam.Batch720.package_strategy_bindsAtCoin_all
#print axioms Nock.RedTeam.Batch720.p2_tierA_bindsAtCoin_every_lambda
