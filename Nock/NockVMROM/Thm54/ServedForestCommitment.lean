import Nock.NockVMROM.Thm54.ServedForestExecution
import Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# `ServedForestCommitment` — the generic honest commitment `Data` layer

The committed compute/memory node trees split cleanly into

* **opcode-invariant** blocks (root `B`, the shared inner root-`A` subtrees, and the served `OP_0`
  compute child), reused verbatim from `MultiRootHonestCommitment`; their node validity, seed
  bindings, and timestamp specializations port unchanged;

* the **parent-touching** root-`A` blocks (the four parent memory rows and the parent compute row),
  whose skeletons carry `P.parentFormula`/`P.parentHead`.  The four memory rows bind head-generically
  (the parent noun appears only as `encS P.parentFormula`, and the record timestamp `= 4` is
  head-independent), so they are proved generically here; and

* the **parent compute row** together with the **six skeleton-only semantic obligations**
  (slot semantics, record equations, census, size window, boundedness, combined boundedness), whose
  content genuinely depends on the abstract parent state `P.parentPub.state` and the parent nouns.
  These are carried as fields of the additive `ServedForestCommit` structure, discharged per-opcode
  when the module is instantiated at `op4Params` / `op3Params` (stages 7/8).

Everything is additive and kernel-clean; the concrete `MultiRootHonestCommitment.dataM`/`statementM`
still stand.
-/

namespace Nock.NockVMROM.Thm54.ServedForestModule

open scoped Classical
open Nock Nock.Noun Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open SemanticStrategy SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.ServedForest
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-! ## A. Generic parent memory record skeleton and the four parent-touching memory skeletons -/

/-- Generic parent memory record skeleton: root the parent formula, child `formulaS`, axis `3`. -/
def parentRecordSkeletonG (P : ServedForestParams) : MemRecSkeleton where
  root := P.parentFormula
  child := formulaS
  axis := 3

def aReadOuterSkelG (P : ServedForestParams) : MemoryRowSkeleton where
  state := .read_root
  parent := P.parentFormula
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => P.parentFormula
  memoryRecord := fun _ => parentRecordSkeletonG P

def aDecomposeOuterSkelG (P : ServedForestParams) : MemoryRowSkeleton where
  state := .decompose
  parent := P.parentFormula
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then P.parentHead else formulaS
  memoryRecord := fun h => nomatch h

def aHeadHaltSkelG (P : ServedForestParams) : MemoryRowSkeleton where
  state := .halt
  parent := P.parentHead
  haltAtom := fun _ => P.headAtom
  haltParent := by intro _; exact P.hhead
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def aVerifyOuterSkelG (P : ServedForestParams) : MemoryRowSkeleton where
  state := .verify_child
  parent := formulaS
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => formulaS
  memoryRecord := fun _ => parentRecordSkeletonG P

/-! ## B. Head-generic seed bindings of the four parent-touching memory rows -/

theorem bind_aReadOuterG (P : ServedForestParams) :
    BindMemoryRowA servedSeed (aReadOuterSkelG P) (aReadOuterLabelGA P) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [aReadOuterSkelG, MemoryTable.fanoutMem, memoryChildCell, memLabelS, aReadOuterPubGA,
        aReadOuterPubG]
  · exact ⟨rfl, rfl, by norm_num [aReadOuterSkelG, parentRecordSkeletonG, memLabelS,
      aReadOuterPubGA, aReadOuterPubG, parentRecordG]⟩

theorem bind_aDecomposeOuterG (P : ServedForestParams) :
    BindMemoryRowA servedSeed (aDecomposeOuterSkelG P) (aDecomposeOuterLabelG P) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_aHeadHaltG (P : ServedForestParams) :
    BindMemoryRowA servedSeed (aHeadHaltSkelG P) (aHeadHaltLabelG P) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem (aHeadHaltSkelG P).state) := by
      simp [aHeadHaltSkelG, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_aVerifyOuterG (P : ServedForestParams) :
    BindMemoryRowA servedSeed (aVerifyOuterSkelG P) (aVerifyOuterLabelGA P) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [aVerifyOuterSkelG, MemoryTable.fanoutMem, memoryChildCell, memLabelS,
        aVerifyOuterPubGA, aVerifyOuterPubG]
  · exact ⟨rfl, rfl, by norm_num [aVerifyOuterSkelG, parentRecordSkeletonG, memLabelS,
      aVerifyOuterPubGA, aVerifyOuterPubG, parentRecordG]⟩

/-! ## C. Head-generic timestamp specializations of the two parent-touching active memory rows -/

theorem stamp_aReadOuterG (P : ServedForestParams) :
    MemoryTimestampSpecializesAt cfgS.challenges.α (memStamp .read_root 1)
      (aReadOuterLabelGA P) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show (aReadOuterPubGA P).mem.ts = _
    rw [if_pos (by rfl)]
    show (parentRecordG P).ts = cfgS.challenges.α ^ 1
    rw [pow_one]; rfl
  · intro h; exact absurd h (by decide)

theorem stamp_aVerifyOuterG (P : ServedForestParams) :
    MemoryTimestampSpecializesAt cfgS.challenges.α (memStamp .verify_child 1)
      (aVerifyOuterLabelGA P) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · show (aVerifyOuterPubGA P).mem.ts = _
    rw [if_pos (by rfl)]
    show (parentRecordG P).ts = cfgS.challenges.α ^ 1
    rw [pow_one]; rfl
  · intro h; exact absurd h (by decide)

/-! ## D. The committed memory node trees (generic root `A`, verbatim root `B`) -/

def aHeadHaltNodeTreeG (P : ServedForestParams) : NTree (MemoryNode K97cubic) :=
  .node (memNode (aHeadHaltSkelG P) 0 (aHeadHaltPubG P)) []
def aVerifyOuterNodeTreeG (P : ServedForestParams) : NTree (MemoryNode K97cubic) :=
  .node (memNode (aVerifyOuterSkelG P) 1 (aVerifyOuterPubGA P)) [aDecomposeInnerNodeTree]
def aReadInnerNodeTreeG (P : ServedForestParams) : NTree (MemoryNode K97cubic) :=
  .node (memNode aReadInnerSkel 2 aReadInnerPubA) [aVerifyOuterNodeTreeG P]
def aDecomposeOuterNodeTreeG (P : ServedForestParams) : NTree (MemoryNode K97cubic) :=
  .node (memNode (aDecomposeOuterSkelG P) 0 (aDecomposeOuterPubG P))
    [aHeadHaltNodeTreeG P, aReadInnerNodeTreeG P]
/-- Committed serviced root `A`, generic over the parent formula/head. -/
def rootANodeTreeG (P : ServedForestParams) : NTree (MemoryNode K97cubic) :=
  .node (memNode (aReadOuterSkelG P) 1 (aReadOuterPubGA P)) [aDecomposeOuterNodeTreeG P]

/-! ## E. Local validity of every committed memory node of the generic root `A` -/

theorem rootANodeTreeG_OK (P : ServedForestParams) :
    MemoryNodesOK cfgS.challenges.z cfgS.challenges.α (rootANodeTreeG P) := by
  refine MemoryNodesOK.mk'
    ⟨rfl, rfl, bind_aReadOuterG P, stamp_aReadOuterG P⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  refine MemoryNodesOK.mk'
    ⟨rfl, rfl, bind_aDecomposeOuterG P,
      stamp_padding (st := .decompose) rfl (aDecomposeOuterPubG P) rfl rfl 0⟩ ?_
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact MemoryNodesOK.mk'
      ⟨rfl, rfl, bind_aHeadHaltG P,
        stamp_padding (st := .halt) rfl (aHeadHaltPubG P) rfl rfl 0⟩ (by simp)
  · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_aReadInner, stamp_aReadInner⟩ ?_
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_aVerifyOuterG P, stamp_aVerifyOuterG P⟩ ?_
    intro f hf
    simp only [List.mem_singleton] at hf
    subst hf
    refine MemoryNodesOK.mk'
      ⟨rfl, rfl, bind_aDecomposeInner,
        stamp_padding (st := .decompose) rfl aDecomposeInnerPub rfl rfl 0⟩ ?_
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact MemoryNodesOK.mk'
        ⟨rfl, rfl, bind_aInnerHeadHalt,
          stamp_padding (st := .halt) rfl aInnerHeadHaltPub rfl rfl 0⟩ (by simp)
    · refine MemoryNodesOK.mk' ⟨rfl, rfl, bind_aVerifyInner, stamp_aVerifyInner⟩ ?_
      intro k hk
      simp only [List.mem_singleton] at hk
      subst hk
      exact MemoryNodesOK.mk'
        ⟨rfl, rfl, bind_aTailHalt,
          stamp_padding (st := .halt) rfl aTailHaltPub rfl rfl 0⟩ (by simp)

/-! ## F. The generic parent compute skeleton, timestamp, and committed compute node tree -/

/-- The nonterminal parent compute skeleton, generic over the parent state/formula/head/result. -/
def parentSkeletonRowG (P : ServedForestExec) : ComputeRowSkeleton where
  state := P.parentPub.state
  subject := subjectS
  formula := P.parentFormula
  evaluation := P.parentResult
  decomposition := fun slot _ =>
    match slot with
    | .f_h => P.parentHead
    | .f_t => formulaS
    | _ => .atom 0
  subformula := fun _ _ slot =>
    match slot with
    | .subject => subjectS
    | .formula => formulaS
    | .result => resultS
  memoryRecord := fun _ _ => parentRecordSkeletonG P.toServedForestParams

/-- The committed parent Nat timestamp exponents (opcode-invariant column shape). -/
def parentStampG (P : ServedForestExec) : ComputeTimestampRow where
  state := P.parentPub.state
  lnPrevExponent := 0
  lnExponent := 1
  recordExponent := fun _ => 1

def parentNodeG (P : ServedForestExec) : ComputeNode K97cubic where
  skel := parentSkeletonRowG P
  stamp := parentStampG P
  row := parentRowG P

/-- The committed compute node tree: the generic parent gate with its single `OP_0` child. -/
def computeNodesMG (P : ServedForestExec) : NTree (ComputeNode K97cubic) :=
  .node (parentNodeG P) [.node servedNode []]

/-- The committed memory node forest: the generic serviced root `A` and the verbatim root `B`. -/
def memoryNodesMG (P : ServedForestExec) : List (NTree (MemoryNode K97cubic)) :=
  [dummyHaltNodeTree, rootANodeTreeG P.toServedForestParams, rootBNodeTree]

/-- The committed semantic skeleton of the generic two-serviced-root fixture. -/
def skelMG (P : ServedForestExec) : SemanticSkeleton :=
  skeletonOfNodes (computeNodesMG P) (memoryNodesMG P)

/-! ## G. The extended interface carrying the parent compute seam + the six skeleton obligations

The parent compute row's seed binding and timestamp specialization, and the six skeleton-only
semantic obligations, all read the abstract parent state `P.parentPub.state` and the parent nouns,
so they cannot be discharged generically; they are carried here and discharged per-opcode. -/

structure ServedForestCommit extends ServedForestExec where
  /-- The parent compute row binds to its committed skeleton at the honest seed. -/
  parentComputeBind :
    BindComputeRow servedSeed (parentSkeletonRowG toServedForestExec) (parentRowG toServedForestExec)
  /-- The committed parent timestamp exponents specialize to the parent row's own columns. -/
  parentComputeStamp :
    ComputeTimestampSpecializesAt cfgS.challenges.α (parentStampG toServedForestExec)
      (parentRowG toServedForestExec)
  /-- Slot semantics on the committed compute skeleton rows. -/
  slotSem : ∀ s ∈ computeSkeletonRows (skelMG toServedForestExec),
    ServedLookupBridge.SkeletonSlotSemantics s
  /-- Record equations on the committed compute skeleton rows. -/
  recordEq : ∀ s ∈ computeSkeletonRows (skelMG toServedForestExec),
    ServedLookupBridge.SkeletonRecordEquations s
  /-- The pre-seed comparison census with leaf window `3`. -/
  censusC : EdgeComparisonCensus.CombinedSkeletonCensus K97cubic (skelMG toServedForestExec) 3
  /-- The size-window nouns are bounded by `3`. -/
  sizeWindowB : SizeWindowCounting.SizeWindowNounsBoundedBy (skelMG toServedForestExec) 3
  /-- Every committed skeleton noun is `q`-bounded. -/
  skelBounded : (skelMG toServedForestExec).BoundedBy 97
  combinedB :
    ProductionP8Containment.CombinedBoundedBy K97cubic 97 (skelMG toServedForestExec)
  pairedRecordLayout : RowLayout.PairedRecordLayout (execSG toServedForestExec)
  honestVer : ∀ row ∈ (execSG toServedForestExec).memoryRows,
    row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)
  generatedC : GeneratedField.ClaimGenerated K97cubic (skelMG toServedForestExec).publicClaim 3

variable (C : ServedForestCommit)

/-! ## H. Local validity of the committed compute node tree -/

theorem computeNodesMG_OK :
    ComputeNodesOK cfgS.challenges.z cfgS.challenges.α (computeNodesMG C.toServedForestExec) := by
  refine ComputeNodesOK.mk'
    ⟨C.parentFanout.symm, rfl, C.parentComputeBind, C.parentComputeStamp⟩ ?_
  intro c hc
  simp only [List.mem_singleton] at hc
  subst hc
  exact ComputeNodesOK.mk' ⟨rfl, rfl, bind_servedRow, stamp_servedRow⟩ (by simp)

/-! ## I. The generic honest commitment `Data` layer -/

/-- **`HonestCommitment.Data` at the generic served-forest execution.**  The committed node trees
are the fourteen memory rows in two serviced roots and the two nonterminal compute rows; the
parent-touching bindings/obligations come from the `ServedForestCommit` fields. -/
def dataMG : HonestCommitment.Data (servedForestModule C.toServedForestExec) where
  computeNodes := computeNodesMG C.toServedForestExec
  memoryNodes := memoryNodesMG C.toServedForestExec
  compute_rows := by
    show mapNTree ComputeNode.row (computeNodesMG C.toServedForestExec)
      = computeTreeSG C.toServedForestExec
    simp [computeNodesMG, parentNodeG, servedNode, mapNTree, computeTreeSG]
  memory_rows := by
    show (memoryNodesMG C.toServedForestExec).map (mapNTree MemoryNode.row)
      = [dummyHaltTreeS, rootATreeGA C.toServedForestParams, rootBTreeA]
    simp [memoryNodesMG, dummyHaltNodeTree, dummyHaltTreeS, dummyHaltPubS, dummyHaltSkel,
      memNode, mapNTree, rootANodeTreeG, aDecomposeOuterNodeTreeG, aHeadHaltNodeTreeG,
      aReadInnerNodeTreeG, aVerifyOuterNodeTreeG, aDecomposeInnerNodeTree,
      aInnerHeadHaltNodeTree, aVerifyInnerNodeTree, aTailHaltNodeTree,
      rootBNodeTree, bDecomposeNodeTree, bVerifyNodeTree, bResultHaltNodeTree,
      bTailHaltNodeTree, rootATreeGA, aDecomposeOuterTreeGA,
      aHeadHaltTreeG, aReadInnerTreeGA, aVerifyOuterTreeGA, aDecomposeInnerTreeA,
      aInnerHeadHaltTree, aVerifyInnerTreeA, aTailHaltTree, rootBTreeA,
      bDecomposeTreeA, bVerifyTreeA, bResultHaltTree, bTailHaltTree]
    exact ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, rfl⟩⟩
  computeOK := computeNodesMG_OK C
  memoryOK := by
    intro t ht
    simp only [memoryNodesMG, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact dummyHaltNodeTree_OK
    · exact rootANodeTreeG_OK C.toServedForestParams
    · exact rootBNodeTree_OK
  root_line_exponent := rfl
  root_line_origin := C.parentLineOrigin
  nounSizeBound := 3
  Λ := 3
  slotSemantics := C.slotSem
  recordEquations := C.recordEq
  census := C.censusC
  sizeWindowBound := C.sizeWindowB
  q_eq_ringChar := ringChar_K97.symm
  skeletonBounded := C.skelBounded
  combinedBounded := C.combinedB

theorem dataMG_skeleton : (dataMG C).skeleton = skelMG C.toServedForestExec := rfl

/-! ## J. The committed residual, the constructed package, and the released statement -/

/-- The committed residual over the generic data (all-zero later-round message). -/
def residualMG : BuildablePackage.CommitmentResidual (servedForestModule C.toServedForestExec) :=
  HonestCommitment.commitmentResidualOfZero (dataMG C)

theorem residualMG_nonvacuous :
    Nonempty (BuildablePackage.CommitmentResidual (servedForestModule C.toServedForestExec)) :=
  ⟨residualMG C⟩

/-- Relaxis remaining join at form R (`kMem = 3` dummy halt). Dummy-wired. -/
def packageMG
    (hmoreMG : BuildableAxisWitness.LaterSeedZeros
      (servedForestModule C.toServedForestExec)) :
    OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 4 :=
  BuildablePackage.buildFullPackage (servedForestModule C.toServedForestExec)
    (inputsMG C.toServedForestExec) (residualMG C) (inputsMG_challenges C.toServedForestExec)
    C.pairedRecordLayout
    hmoreMG
    (hord := fun _ => by
      have hα : (inputsMG C.toServedForestExec).computeWalkAlpha = (2 : K97cubic) := rfl
      have hrows : (servedForestModule C.toServedForestExec).cfg.compRows = 2 := rfl
      rw [hα, omega2_order, hrows]
      norm_num)
    (hordM := fun _ => by
      have hα : (inputsMG C.toServedForestExec).memoryWalkAlpha = (3 : K97cubic) := rfl
      have hrows : (servedForestModule C.toServedForestExec).cfg.memRows = 15 := rfl
      rw [hα, omega3_order, hrows]
      norm_num)
    (hrows := by
      have h1 : (servedForestModule C.toServedForestExec).cfg.compRows = 2 := rfl
      have h2 : (servedForestModule C.toServedForestExec).cfg.memRows = 15 := rfl
      rw [h1, h2, ringChar_K97]
      norm_num)
    (hgenF := C.generatedC) (hF := MultiRootHonestCommitment.f97_primeField)

/-- **The released fourteen-conjunct Theorem-5.4 statement over the generic package.**  The consumed
capstone `optimizedFullStrictNockVMROM_of_package` is unchanged. -/
theorem statementMG
    (hmoreMG : BuildableAxisWitness.LaterSeedZeros
      (servedForestModule C.toServedForestExec))
    (hax : FormRAxisBound (packageMG C hmoreMG).optimized.sampled
      (packageMG C hmoreMG).optimized.basis)
    (hbasis : FormRBasis (packageMG C hmoreMG).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageMG C hmoreMG) :=
  BuildablePackage.universalOptimizedFullStrictThm54 (servedForestModule C.toServedForestExec)
    (inputsMG C.toServedForestExec) (residualMG C) (inputsMG_challenges C.toServedForestExec)
    C.pairedRecordLayout
    hmoreMG
    (hord := fun _ => by
      have hα : (inputsMG C.toServedForestExec).computeWalkAlpha = (2 : K97cubic) := rfl
      have hrows : (servedForestModule C.toServedForestExec).cfg.compRows = 2 := rfl
      rw [hα, omega2_order, hrows]
      norm_num)
    (hordM := fun _ => by
      have hα : (inputsMG C.toServedForestExec).memoryWalkAlpha = (3 : K97cubic) := rfl
      have hrows : (servedForestModule C.toServedForestExec).cfg.memRows = 15 := rfl
      rw [hα, omega3_order, hrows]
      norm_num)
    (hrows := by
      have h1 : (servedForestModule C.toServedForestExec).cfg.compRows = 2 := rfl
      have h2 : (servedForestModule C.toServedForestExec).cfg.memRows = 15 := rfl
      rw [h1, h2, ringChar_K97]
      norm_num)
    (hgenF := C.generatedC) (hF := MultiRootHonestCommitment.f97_primeField)
    hax hbasis hwidth

theorem statementMG_nonvacuous
    (hmoreMG : BuildableAxisWitness.LaterSeedZeros
      (servedForestModule C.toServedForestExec))
    (hax : FormRAxisBound (packageMG C hmoreMG).optimized.sampled
      (packageMG C hmoreMG).optimized.basis)
    (hbasis : FormRBasis (packageMG C hmoreMG).optimized.basis)
    (hwidth : FormRWidth F97) :
    Nonempty (OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageMG C hmoreMG)) :=
  ⟨statementMG C hmoreMG hax hbasis hwidth⟩

end

end Nock.NockVMROM.Thm54.ServedForestModule

#print axioms Nock.NockVMROM.Thm54.ServedForestModule.rootANodeTreeG_OK
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.computeNodesMG_OK
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.dataMG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.residualMG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.packageMG
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.statementMG
