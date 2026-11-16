/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAStatement.lean

  Generated Theorem-5.4 statement on AIR-ordered `DotConfig769`.
-/
import Mathlib.Tactic.IntervalCases
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrder
import Nock.NockVMROM.Thm54.TraceGen.GenChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLayout
import Nock.NockVMROM.Thm54.TraceGen.GenStatement
import Nock.NockVMROM.Thm54.TraceGen.GenTierAInputs
import Nock.NockVMROM.Thm54.BuildableAxisWitness
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

local instance finiteDimK : FiniteDimensional F K := inferInstance

local instance charRingKstmt : CharP K (ringChar K) := ringChar.charP K

noncomputable section

variable (hfirst :
  ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
    ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0)
theorem dotBuildable_honestVer :
    ∀ row ∈ (dotBuildable hfirst).exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) :=
  execThreaded_honestVer seedZ alphaA

theorem dotBuildable_pairedRecordLayout :
    RowLayout.PairedRecordLayout (dotBuildable hfirst).exec := by
  show RowLayout.PairedRecordLayout (execThreaded seedZ alphaA)
  have hA : ∀ row ∈ (execThreadedA seedZ alphaA).memoryRows, ∃ t ∈ bfsForest
      (threadedForest seedZ alphaA), row = t.label.row := by
    intro row hrow
    rw [memoryRowsA_eq_threaded] at hrow
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    exact ⟨t, ht, rfl⟩
  refine pairedRecordLayout_encodeMem _ ?_
    (pairedRecordLayout_of_threadGenForest (execThreadedA seedZ alphaA)
      (encC seedZ) seedZ alphaA (memInputs seedZ) 0
      (bfsAssign (dotTreeAir (K := K))) rfl ?_)
  · intro row hrow
    obtain ⟨t, ht, rfl⟩ := hA row hrow
    exact threaded_bfs_state seedZ alphaA t ht
  · intro row hrow
    obtain ⟨t, ht, rfl⟩ := hA row hrow
    exact threaded_bfs_ver seedZ alphaA t ht

/-- Dummy later-seed parent accums: the section `hmore` is the live witness. -/

theorem goldilocks_two_pow_ne_one :
    ∀ k : ℕ, 0 < k → k < 17 → (2 : F) ^ k ≠ 1 := by
  intro k hk0 hk
  revert hk0
  interval_cases k <;> decide

theorem goldilocks_two_order_ge (n : ℕ) (hn : n ≤ 17) :
    n ≤ orderOf (2 : F) := by
  refine le_of_not_gt fun hlt => ?_
  have hfin : IsOfFinOrder (2 : F) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨768, by norm_num, by decide⟩
  have hpos : 0 < orderOf (2 : F) :=
    Nat.pos_of_ne_zero fun h0 => (orderOf_eq_zero_iff.mp h0) hfin
  exact goldilocks_two_pow_ne_one (orderOf (2 : F)) hpos
    (hlt.trans_le hn) (pow_orderOf_eq_one _)

theorem goldilocks769_two_order : orderOf (2 : F) = 384 := by
  have h384 : (2 : F) ^ 384 = 1 := by decide
  have h192 : (2 : F) ^ 192 ≠ 1 := by decide
  have h128 : (2 : F) ^ 128 ≠ 1 := by decide
  have hdvd : orderOf (2 : F) ∣ 384 := orderOf_dvd_of_pow_eq_one h384
  have hnot192 : ¬ orderOf (2 : F) ∣ 192 := fun h =>
    h192 (orderOf_dvd_iff_pow_eq_one.mp h)
  have hnot128 : ¬ orderOf (2 : F) ∣ 128 := fun h =>
    h128 (orderOf_dvd_iff_pow_eq_one.mp h)
  have hle : orderOf (2 : F) ≤ 384 := Nat.le_of_dvd (by norm_num) hdvd
  have hfin : ∀ n : Fin 385,
      (n : ℕ) ∣ 384 → ¬ (n : ℕ) ∣ 192 → ¬ (n : ℕ) ∣ 128 → (n : ℕ) = 384 := by
    decide
  exact hfin ⟨orderOf (2 : F), Nat.lt_succ_of_le hle⟩ hdvd hnot192 hnot128

theorem goldilocks_two_order_ge_mem (n : ℕ) (hn : n ≤ 384) :
    n ≤ orderOf (2 : F) := by
  rw [goldilocks769_two_order]
  exact hn

theorem dot_walkOrder :
    2 ≤ (dotBuildable hfirst).cfg.compRows →
      (dotBuildable hfirst).cfg.compRows ≤ orderOf (inputs hfirst).computeWalkAlpha := fun _ => by
  have hα : (inputs hfirst).computeWalkAlpha = (2 : K) := rfl
  have hrows : (dotBuildable hfirst).cfg.compRows = 8 := rfl
  rw [hα, hrows]
  have hcast : (2 : K) = (algebraMap F K).toMonoidHom (2 : F) :=
    (map_natCast (algebraMap F K) 2).symm
  rw [hcast, orderOf_injective (algebraMap F K).toMonoidHom
    (RingHom.injective (algebraMap F K)) (2 : F)]
  exact goldilocks_two_order_ge 8 (by norm_num)

theorem dot_memoryWalkOrder :
    2 ≤ (dotBuildable hfirst).cfg.memRows →
      (dotBuildable hfirst).cfg.memRows ≤ orderOf (inputs hfirst).memoryWalkAlpha := fun _ => by
  have hα : (inputs hfirst).memoryWalkAlpha = (2 : K) := rfl
  have hrows : (dotBuildable hfirst).cfg.memRows = 184 := rfl
  rw [hα, hrows]
  have hcast : (2 : K) = (algebraMap F K).toMonoidHom (2 : F) :=
    (map_natCast (algebraMap F K) 2).symm
  rw [hcast, orderOf_injective (algebraMap F K).toMonoidHom
    (RingHom.injective (algebraMap F K)) (2 : F)]
  exact goldilocks_two_order_ge_mem 184 (by norm_num)

theorem dot_rowsBound :
    3 * (dotBuildable hfirst).cfg.compRows < ringChar K ∧
      (dotBuildable hfirst).cfg.memRows < ringChar K := by
  have h1 : (dotBuildable hfirst).cfg.compRows = 8 := rfl
  have h2 : (dotBuildable hfirst).cfg.memRows = 184 := rfl
  rw [h1, h2, ringChar_K]
  norm_num

/-! ### The leaf window is the
row-by-row `TraceConfined 22` of the AIR tree (`Batch164.dot_traceConfined`, restated here), the
guarded run is `Batch192.b192_evalG`'s simp set. -/

theorem dot_air_traceConfined22 : TraceConfined 22 (airReorder (dotTree (K := K))) := by
  rw [airReorder_dotTree]
  intro g hg
  rw [dot_air_bfsRows] at hg
  fin_cases hg <;>
    exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

theorem dot_evalG769 :
    FieldEmbedding.evalGBy 769 8 dotSubject dotFormula = some dotResult := by
  simp [FieldEmbedding.evalGBy, dotSubject, dotFormula, dotParentTail,
    dotBranchPair, dotCondFormula, dotThenFormula, dotElseFormula,
    dotThenTail, dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula,
    dotCore, dotElem0, dotElem1, dotResult, Noun.slot]

theorem dot_program_generated (Λ' : ℕ) (hΛ : 22 ≤ Λ') :
    ∃ (gfuel : ℕ) (G : NTree (GenComputeRow K)) (R : Noun) (fuel : ℕ) (r : Noun),
      genComputeSkeleton (K := K) gfuel dotSubject dotFormula = .ok (G, R) ∧
        FieldEmbedding.evalGBy (ringChar K) fuel dotSubject dotFormula = some r ∧
        programLeafBound (airReorder G) ≤ Λ' :=
  ⟨4, _, _, 8, dotResult, genComputeSkeleton_dot 0, by rw [ringChar_K]; exact dot_evalG769,
    (leafBound_of_traceConfined dot_air_traceConfined22).trans hΛ⟩

theorem dot_claim :
    (data hfirst).skeleton.publicClaim.subject = dotSubject ∧
      (data hfirst).skeleton.publicClaim.formula = dotFormula := by
  show (data hfirst).skeleton.computeTree.label.subject = _ ∧
    (data hfirst).skeleton.computeTree.label.formula = _
  simp only [Data.skeleton, skeletonOfNodes, mapNTree_label]
  show (computeNodes).label.skel.subject = _ ∧ (computeNodes).label.skel.formula = _
  simp only [computeNodes, dotComputeNodesAir, renderRows_eq_mapNTree,
    mapNTree_label, GenComputeRow.node, bfsAssign_label]
  all_goals (try refine ⟨?_, ?_⟩)
  all_goals (rw [renderNode_op1_skel]; simp [bfsLabelAt, bfsRows, bfsForest,
    dotTreeAir, skelNode, NTree.children, NTree.label])
  all_goals first | rfl | decide +kernel

theorem dot_generated :
    GeneratedField.ClaimGenerated K (data hfirst).skeleton.publicClaim (data hfirst).Λ :=
  GeneratedField.claimGenerated_of_eq (dot_claim hfirst).1 (dot_claim hfirst).2
    (dot_program_generated _ (le_of_eq rfl))

theorem dot_primeField : GeneratedField.PrimeFieldElems F := by
  haveI : Fact (Nat.Prime 769) := ⟨by norm_num⟩
  exact GeneratedField.primeFieldElems_zmod 769

noncomputable def package
    (hmore : BuildableAxisWitness.LaterSeedZeros (dotBuildable hfirst)) :
    OptimizedFullStrictNockVMROMPackage F K (inputs hfirst).hOrb :=
  buildFullPackage (dotBuildable hfirst) (inputs hfirst) (commitmentResidualOfZero (data hfirst))
    (inputs_challenges hfirst) (dotBuildable_pairedRecordLayout hfirst)
    hmore (dot_walkOrder hfirst) (dot_memoryWalkOrder hfirst) (dot_rowsBound hfirst)
    (dot_generated hfirst) dot_primeField

theorem statement
    (hmore : BuildableAxisWitness.LaterSeedZeros (dotBuildable hfirst))
    (hax : FormRAxisBound (package hfirst hmore).optimized.sampled
      (package hfirst hmore).optimized.basis)
    (hbasis : FormRBasis (package hfirst hmore).optimized.basis)
    (hwidth : FormRWidth F) :
    OptimizedFullStrictThm54Statement (package hfirst hmore) :=
  Nock.NockVMROM.Thm54.TraceGen.statement_of_generated_residual (data hfirst) (inputs hfirst)
    (inputs_challenges hfirst) (dotBuildable_pairedRecordLayout hfirst)
    hmore (dot_walkOrder hfirst) (dot_memoryWalkOrder hfirst) (dot_rowsBound hfirst)
    (dot_generated hfirst) dot_primeField
    hax hbasis hwidth

end

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.package
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.statement
