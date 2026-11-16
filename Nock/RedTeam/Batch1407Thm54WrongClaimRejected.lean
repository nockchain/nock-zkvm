import Nock.RedTeam.Batch1406Thm54WrongClaimPackage
import Nock.NockVMROM.Thm54.HostileSemanticSoundness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1407Thm54WrongClaimRejected.lean

  A concrete package of the full type `OptimizedFullStrictNockVMROMPackage F97 K97cubic 5` whose claim
  has a WRONG result, and the theorem that every tuple accepting any fixed trace pair lies in the
  consumed failure event.

  * The package: `WCCommitment.packageD hfirstWC` (`Batch1403`-`1406`): the DistinctCensus fixture
    (`EqualityOperandCensus` / `DistinctCensusExecution` / `DistinctCensusC1` / `DistinctCensusCommitment`)
    copied with the right operand `[8 10] ↦ [15 8]`, which collides with the left operand `[7 9]`
    at the fixture's honest seed `z = 8` (`7 + 9·8 = 15 + 8·8 = 79 mod 97`), and with the OP5 row
    recording `0` ("equal") while Nock returns `1`.  Every honest-data field is proved, `generated`
    and `primeField` included (`buildFullPackage`); the copied fixture's carried premise `hfirstD`
    (memory row 0 has Form R counts / indicator `0`) is DISCHARGED here (`hfirstWC`), and the
    fixture basis is the compiler basis (`compilerBasis_formR`), so `hbasis` is discharged too.
  * `wc_claim`: the claim is `⟨0, [5 [1 [7 9]] [1 [15 8]]], 0⟩`; `wc_claim_wrong`: it does not hold
    (`evalN` gives `1`).
  * `wc_every_accepting_tuple_in_event`: for EVERY tuple `c` and EVERY fixed pair `(Qc, Qm)` accepted at
    the family chips, `c ∈ consumedFailureEvent`.  Only `hax` (`FormRAxisBound`) is discharged by the
    row states (no `s0`/`s9` row), `hwidth` is `formRWidth97`.
  * `wc_honest_seed_bad`: the honest seed lies in the census bad set (the colliding operand pair).

  Fixed-trace shape only
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch1407

open scoped Polynomial
open Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.WCExecution
open Nock.NockVMROM.Thm54.WCOperandCensus
open Nock.NockVMROM.Thm54.WCCommitment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace
open Nock.NockVMROM.Thm54.OptimizedStrictPackage

local instance prime97d : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97d : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

noncomputable section

theorem h3 : MemoryTable.nockAxisOf (3 : K97cubic) = 3 := by
  have := MemoryTable.nockAxisOf_natCast (K := K97cubic) (a := 3) (by rw [ringChar_K97]; norm_num)
  simpa using this
theorem h2 : MemoryTable.nockAxisOf (2 : K97cubic) = 2 := by
  have := MemoryTable.nockAxisOf_natCast (K := K97cubic) (a := 2) (by rw [ringChar_K97]; norm_num)
  simpa using this
theorem pw6 : MemoryTable.pwScaleExp K97cubic = 6 := by
  rw [MemoryTable.pwScaleExp, ringChar_K97]; decide
theorem size3 : Nat.size 3 = 2 := by decide
theorem size2 : Nat.size 2 = 2 := by decide
theorem size97 : Nat.size 97 = 7 := by decide
/-- The copied fixture's carried premise, discharged: row 0's Form R counts and indicator vanish. -/
theorem hfirstWC : (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0 := by
  rw [memoryPubAtD_0]
  simp only [pN1, readPub, cF0, cFd, cH5, cT0, cTv, cTd, cL0, cLv, cR0, cLd, cRd, cA1, cA8, cA10,
    cORd, cOLd, cOL0, cOR0, cA7, cA9]
  simp only [TD, CD, recF, recT, recL, recR, h3, h2, MemoryTable.formRT, MemoryTable.formRC,
    MemoryTable.formRCertShift_three, OptimizedComputeFormRSlots.formRCertShift_two, MemoryTable.formRDefault]
  rw [pw6]
  simp only [scaleD, MemoryTable.pwScaleExp, ringChar_K97, MemoryTable.formRDefault]
  simp (config := {decide := true}) [List.range_succ, MemoryTable.formRCertBit, MemoryTable.formRCertShift, size3, size2, size97]
  constructor <;> ring

/-- **The wrong-claim package.** -/
abbrev PWC : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F97 K97cubic 5 :=
  packageD hfirstWC

def wcFormula : Noun :=
  .cell (.atom 5) (.cell (.cell (.atom 1) (.cell (.atom 7) (.atom 9)))
    (.cell (.atom 1) (.cell (.atom 15) (.atom 8))))

theorem wc_claim :
    PWC.optimized.verifier.raw.claim = ⟨.atom 0, wcFormula, .atom 0⟩ := by
  show (dataD hfirstWC).skeleton.publicClaim = _
  simp [HonestCommitment.Data.skeleton, HonestCommitment.skeletonOfNodes, mapNTree_label,
    SemanticStrategy.SemanticSkeleton.publicClaim]
  all_goals (try refine ⟨?_, ?_, ?_⟩)
  all_goals first | rfl | decide

theorem wc_run : Nock.evalN 8 (.atom 0) wcFormula = some (.atom 1) := by decide

/-- **The claim is WRONG**: Nock evaluates the program to `1`, the claim records `0`. -/
theorem wc_claim_wrong : ¬ PWC.optimized.verifier.raw.claim.Holds := by
  rw [wc_claim]
  rintro ⟨fuel, h⟩
  have h1 := Nock.evalN_mono (Nat.le_max_left fuel 8) h
  have h2 := Nock.evalN_mono (Nat.le_max_right fuel 8) wc_run
  change Nock.evalN _ (.atom 0) wcFormula = some (.atom 0) at h1
  rw [h1] at h2
  simp at h2

theorem wc_guarded : FieldEmbedding.evalGBy (ringChar K97cubic) 2 PWC.optimized.verifier.raw.claim.subject
    PWC.optimized.verifier.raw.claim.formula = some (.atom 1) := by
  rw [wc_claim]
  simp only [wcFormula]
  eval_simp

theorem wc_hbasis : FormRBasis PWC.optimized.basis :=
  TraceGen.compilerBasis_formR (F := F97) (K := K97cubic) (GaloisField.finrank 97 (by norm_num))

/-- No `s0` / `s9` row (`.s5`, `.s1`, `.s1`), so no committed axis leaf. -/
theorem wc_hax : FormRAxisBound PWC.optimized.sampled PWC.optimized.basis := by
  intro i L hL
  have hdec :
      OptimizedComputeCodec.decodeState (encodedRowAt PWC.optimized.sampled i).base =
        (PWC.optimized.family.problem.exec.computePubAt i).state := by
    simp [encodedRowAt, OptimizedComputeOverlay.sampledEncode,
      OptimizedComputeCodec.decodeState_encodeBase]
  have hst : (PWC.optimized.family.problem.exec.computePubAt i).state = .s5 ∨
      (PWC.optimized.family.problem.exec.computePubAt i).state = .s1 := by
    change (execD.computePubAt i).state = .s5 ∨ (execD.computePubAt i).state = .s1
    fin_cases i
    · left
      show (execD.computePubAt ⟨0, by norm_num [cfgD]⟩).state = _
      rw [computePubAtD_zero]; rfl
    · right
      show (execD.computePubAt ⟨1, by norm_num [cfgD]⟩).state = _
      rw [computePubAtD_one]; rfl
    · right
      show (execD.computePubAt ⟨2, by norm_num [cfgD]⟩).state = _
      rw [computePubAtD_two]; rfl
  revert hL
  simp [axisLeafCoord, hdec]
  rcases hst with hst | hst <;> simp [hst]

/-- **NC (a), compiled.**  At the wrong-claim package, every tuple at which ANY fixed trace pair is
accepted by the family chips lies in the consumed failure event. -/
theorem wc_every_accepting_tuple_in_event
    (c : OptimizedProductionChallengeTuple K97cubic F97)
    (Qc : Fin (PWC.computeChipAt c).rap.w → F97[X])
    (Qm : Fin (PWC.memoryChipAt c).rap.w → F97[X])
    (hacc : DeployedAcceptanceAt PWC c Qc Qm) :
    c ∈ PWC.consumedFailureEvent (FamilyComputeRows.honestQc PWC c Qc)
      (FamilyMemoryRows.honestQm PWC c Qm) :=
  HostileSemanticSoundness.wrong_claim_rejected PWC wc_hax wc_hbasis formRWidth97 c Qc Qm hacc
    wc_guarded (by rw [wc_claim]; decide)

/-- No `(Qc, Qm, c)` is
accepted by the parallel package's two chips at a twelve-coin tuple outside the fifteen-summand
event: `HostileSemanticSoundness.hostileSemanticSoundness_pinned` from the statement alone. -/
theorem wc_no_acceptance_outside_event
    (Qc : Fin 309 → F97[X]) (Qm : Fin PWC.memoryChip.rap.w → F97[X])
    (c : PartA12.OptimizedProductionChallengeTuple12 K97cubic F97)
    (hacc : PartAStaged.AcceptanceAt309 PWC Qc Qm c) :
    c ∈ PartAStaged.consumedFailureEvent309 PWC Qc Qm := by
  by_contra hgood
  exact wc_claim_wrong (HostileSemanticSoundness.hostileSemanticSoundness_pinned PWC
    (statementD hfirstWC wc_hax wc_hbasis formRWidth97) Qc Qm c hacc hgood)

/-- The landed 303 orientation, kept as a corollary of `wrong_claim_rejected` (NC (a) at the landed
chips, Form R premises discharged): no `(Qc, Qm, c)` is accepted by the landed chips at an
eleven-coin tuple outside the landed consumed event. -/
theorem wc_no_acceptance_outside_event303
    (Qc : Fin PWC.computeChip.rap.w → F97[X]) (Qm : Fin PWC.memoryChip.rap.w → F97[X])
    (c : OptimizedProductionChallengeTuple K97cubic F97)
    (hacc : PWC.OptimizedProductionAcceptanceAt Qc Qm c) :
    c ∈ PWC.consumedFailureEvent Qc Qm := by
  have h := HostileSemanticSoundness.wrong_claim_rejected PWC wc_hax wc_hbasis formRWidth97 c
    (PWC.familyQc c Qc) (PWC.familyQm c Qm) ⟨hacc.compute_satisfies, hacc.memory_satisfies⟩
    wc_guarded (by rw [wc_claim]; decide)
  rwa [show FamilyComputeRows.honestQc PWC c (PWC.familyQc c Qc) = Qc from
      FamilyEnvCore.honestQc_familyQc PWC.optimized c Qc,
    show FamilyMemoryRows.honestQm PWC c (PWC.familyQm c Qm) = Qm from
      FamilyEnvCore.honestQm_familyQm PWC.optimized c Qm] at h

/-- The package's statement holds (all three Form R hypotheses discharged). -/
theorem wc_statement : OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement PWC :=
  statementD hfirstWC wc_hax wc_hbasis formRWidth97

/-- The honest seed `8` is a collision seed of the two operands (the census summand). -/
theorem wc_honest_seed_bad : ¬ GlobalCarryRecognizer.SepSeed (8 : K97cubic) operandLeft operandRight :=
  (operands_not_sepSeed_iff 8).mpr rfl

end

end Nock.RedTeam.Batch1407

#print axioms Nock.RedTeam.Batch1407.hfirstWC
#print axioms Nock.RedTeam.Batch1407.wc_claim
#print axioms Nock.RedTeam.Batch1407.wc_claim_wrong
#print axioms Nock.RedTeam.Batch1407.wc_hax
#print axioms Nock.RedTeam.Batch1407.wc_statement
#print axioms Nock.RedTeam.Batch1407.wc_every_accepting_tuple_in_event
#print axioms Nock.RedTeam.Batch1407.wc_no_acceptance_outside_event
#print axioms Nock.RedTeam.Batch1407.wc_no_acceptance_outside_event303
#print axioms Nock.RedTeam.Batch1407.wc_honest_seed_bad
