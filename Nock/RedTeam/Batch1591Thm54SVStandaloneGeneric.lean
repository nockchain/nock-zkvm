/-
  Nock/RedTeam/Batch1591Thm54SVStandaloneGeneric.lean

  **Receipts for the generic standalone statement at I0 r2.**
  Production: `P8Core/SVFrame/{MemSoundnessFamily (r2), LeafBoundF, JoinUtil,
  JointSummands, StandaloneGeneric}.lean`.

  §A  `#print axioms` of `standalone_generic`, `standalone_generic_at`, `standalone_fixed`,
      `ctxW_of_accepts`, `holdsF_of_accepts`, `callsWithin_leafBoundF`, the joint-summand lemmas.
  §B  The proof-term walker (`P4_ProofReach` style: types AND values, `value? (allowOpaque := true)`,
      every `Nock.*` constant), ASSERTING: the closures of `standalone_generic` / `_at` /
      `ctxW_of_accepts` / `holdsF_of_accepts` / `jointSummands` contain no constant whose name
      contains a chip, package, `Tuple12`, honest-run or generator marker.
-/
import Lean
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric
import Nock.RedTeam.Batch1590Thm54SVFrameFibre
import Nock.RedTeam.Batch1171Thm54C2InductionPositional
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1591

open Lean Meta Elab Command
open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame

/-! ## §A  Axioms -/

#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_generic
#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_generic_at
#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_fixed
#print axioms Nock.NockVMROM.Thm54.SVFrame.ctxW_of_accepts
#print axioms Nock.NockVMROM.Thm54.SVFrame.holdsF_of_accepts
#print axioms Nock.NockVMROM.Thm54.SVFrame.recOK_row
#print axioms Nock.NockVMROM.Thm54.SVFrame.rec_struct
#print axioms Nock.NockVMROM.Thm54.SVFrame.J_label
#print axioms Nock.NockVMROM.Thm54.SVFrame.callsWithin_leafBoundF
#print axioms Nock.NockVMROM.Thm54.SVFrame.callTreeF_mem_callsAt
#print axioms Nock.NockVMROM.Thm54.SVFrame.seedSummand_mem
#print axioms Nock.NockVMROM.Thm54.SVFrame.censusPairs_length_le
#print axioms Nock.NockVMROM.Thm54.SVFrame.recPairs_length_le
#print axioms Nock.NockVMROM.Thm54.SVFrame.ioEventAt_card_le
#print axioms Nock.NockVMROM.Thm54.SVFrame.join_eq_joinB0
#print axioms Nock.NockVMROM.Thm54.SVFrame.c2JoinFuelF_factor
#print axioms Nock.NockVMROM.Thm54.SVFrame.pr_mem_zipLabels
#check @Nock.NockVMROM.Thm54.SVFrame.standalone_generic
#check @Nock.NockVMROM.Thm54.SVFrame.ExtraPremises
#check @Nock.NockVMROM.Thm54.SVFrame.rowFactsAt
#check @Nock.NockVMROM.Thm54.SVFrame.jointSummands

/-- `Kio := K`, every row of weight `1`): walk-style
IO facts (`SVIO.MemIOFacts`, through `IOFacts.ofMem`) are the frame's `ioFacts` shape at
`internal := []`. -/
example {F K : Type} [Field F] [Field K] [Algebra F K] (coins : FiniteIO.IOCoins K) (ρ : K)
    (M : SVIO.MemIOFacts coins ρ) :
    IOFacts F (FiniteIO.compress (m := 10) coins)
      (ρ + (([] : List (Fin 10 → K)).map fun r => (FiniteIO.compress (m := 10) coins r)⁻¹).sum) :=
  (IOFacts.ofMem F M).withNoInternal

/-- `shapeVCL` carries real widths and round maps (illustrative values). -/
example : (shapeVCL 1 1 197 102 (fun _ => 0) (fun _ => 1)).k = 2 := rfl
#check @Nock.NockVMROM.Thm54.SVFrame.MemSoundnessFamily.internal
#check @Nock.NockVMROM.Thm54.SVFrame.MemSoundnessFamily.response_sound
#check @Nock.NockVMROM.Thm54.SVFrame.CompSoundnessFamily.inline_records
/-- At walk-style instances (`inlineRecords := fun _ => 0`) no record is inline, so
`inline_not_read` / `inline_records` are vacuous and `node_records` covers every record. -/
example (st : Nock.ComputeTable.State) (j : ℕ) : ¬ j < (fun _ : Nock.ComputeTable.State => (0 : ℕ)) st := by
  simp

/-! ## §B  The proof-term walker -/

/-- Every `Nock.*` constant reachable from `root` through types and values (theorems included). -/
partial def walkReach (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut es : Array Expr := #[ci.type]
      if let some v := ci.value? (allowOpaque := true) then es := es.push v
      for e in es do
        for c in e.getUsedConstants do
          if (`Nock).isPrefixOf c && !seen.contains c then todo := todo.push c
  return seen

/-- The forbidden markers: chips, packages, the twelve-coin tuple, honest runs, the generator. -/
def markers : List String :=
  ["memoryChipAt12", "computeChipAt309", "chipWalk", "Tuple12", "Unhosted309", "PartAMemoryChip12",
   "OptimizedFullStrictNockVMROMPackage", "OptimizedStrictNockVMROMPackage", "OptimizedStrictFullPackage",
   "StandaloneVerifier", "currentMemFamily", "HonestCall", "evalGBy", "programLeafBound",
   "genComputeSkeleton", "honest_specialization", "execTemplateEv", "Form R", "formR", "walkAcc",
   "timestamp"]

def hits (s : NameSet) : List Name :=
  s.toList.filter fun n => markers.any fun m => (n.toString.splitOn m).length > 1

elab "#assertClean " id:ident : command => do
  let env ← getEnv
  let root := id.getId
  unless env.contains root do throwError "missing root {root}"
  let s := walkReach env root
  let h := hits s
  unless h.isEmpty do throwError "{root}: forbidden constants reached: {h.take 20}"
  logInfo m!"{root}: proof closure {s.size}; forbidden constants reached: []"

elab "#assertReaches " id:ident : command => do
  let env ← getEnv
  let root := id.getId
  unless env.contains root do throwError "missing root {root}"
  let s := walkReach env root
  let h := hits s
  if h.isEmpty then throwError "{root}: positive control FAILED (nothing reached)"
  logInfo m!"{root}: proof closure {s.size}; positive control reaches {h.length}: {h.take 6}"

#assertClean Nock.NockVMROM.Thm54.SVFrame.standalone_generic
#assertClean Nock.NockVMROM.Thm54.SVFrame.standalone_generic_at
#assertClean Nock.NockVMROM.Thm54.SVFrame.standalone_fixed
#assertClean Nock.NockVMROM.Thm54.SVFrame.ctxW_of_accepts
#assertClean Nock.NockVMROM.Thm54.SVFrame.holdsF_of_accepts
#assertClean Nock.NockVMROM.Thm54.SVFrame.jointSummands
#assertClean Nock.NockVMROM.Thm54.SVFrame.StandaloneThm54Statement
-- positive controls
#assertReaches Nock.NockVMROM.Thm54.SVFrame.chipWalk
#assertReaches Nock.RedTeam.Batch1171.root_good

/-! ## §C  The census reads B0 only -/

section Census

variable {F K Kio Kfp Key : Type} [Field F] [Field K] [Algebra F K]
  [Fintype K] [DecidableEq K] [Fintype F] [Field Kfp] [DecidableEq Key]
  [Fintype Kfp] [DecidableEq Kfp]
  [Field Kio] [Fintype Kio] [DecidableEq Kio] [Algebra F Kio]
  {Φ : CoinFrame} {hC : ℕ} {S : MemShape} {C : TableSpec} {nAcc : ℕ} {m : Fin nAcc → ℕ}
  {R : RecordView F K Kio Kfp Key C S hC m} {Z : SeedSpec Φ K Kfp} {I : IOCoinSpec Φ K Kio}
  (CF : CompSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)
  (MF : MemSoundnessFamily F K Kio Kfp Key Φ hC S C nAcc R Z I)

/-- **The NPR census is a function of `(V, x, y)` and the B0 columns of both sides.** -/
theorem censusSummand_badSet_b0 (V : VerifierData F K hC S) (x : CF.Msg0) (y : MF.Msg0)
    (tr tr' : Traces F C S) (h : b0Tr tr = b0Tr tr') (χ χ' : Coins Φ K) :
    (censusSummand CF MF V x y).badSet tr χ = (censusSummand CF MF V x y).badSet tr' χ' := by
  simp only [censusSummand, seedSummand, h]

/-- **The r2 reading of `s0_census_depends_on_axis`**: the census's axis oracle is `CF.axB0` at
the B0 columns, so B0 data whose `axB0` differ at `S + 2` give different OP0 comparison lists. -/
theorem census_reads_axB0 (V : VerifierData F K hC S) (x : CF.Msg0) (b b' : B0Pair F C S)
    (sv : Nock.MemoryTable.MState → ℕ → Noun) (Sn : ℕ) (subj f : Noun)
    (kids : List SemanticStrategy.ComputeRowSkeleton)
    (h : CF.axB0 V x b.1 b.2 (Sn + 2) ≠ CF.axB0 V x b'.1 b'.2 (Sn + 2)) :
    P8Census.skeletonComparisons (K := Kfp)
        (SVJoinF.c2SkeletonRowF (ringChar Kfp) sv (CF.axB0 V x b.1 b.2) .s0 Sn subj f kids) ≠
      P8Census.skeletonComparisons (K := Kfp)
        (SVJoinF.c2SkeletonRowF (ringChar Kfp) sv (CF.axB0 V x b'.1 b'.2) .s0 Sn subj f kids) :=
  Batch1590.s0_census_depends_on_axis _ _ _ _ _ _ _ _ h

end Census

#print axioms censusSummand_badSet_b0
#print axioms census_reads_axB0

end Nock.RedTeam.Batch1591
