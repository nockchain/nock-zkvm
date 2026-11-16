/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierASemanticData.lean

  Per-row `ComputeRowSemanticData` and the assembled
  `ExactExecutionSemanticData 769 22` on AIR-ordered `DotConfig769`.
  Faithfulness is diagonal except OP6's taken-vs-else formula pair,
  which separates because the size coordinates `z^12` and `z^7` differ
  at `seedZ = φ(8)` (`8^5 ≠ 1` in `𝔽_769`).

  `memoryTrace` / `BuildableNockExecution` are not claimed here.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenTierALanguage
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.SemanticTrace

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk Nock.NockVM Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.ExactExecution

noncomputable section

def Λ : ℕ := 22

/-! ## Noun leaf counts and the OP6 off-diagonal pair -/

theorem pairFaithful_self (n : Noun) (h : FieldEmbedding.BoundedBy 769 n) :
    OpcodeSemantics.PairFaithful seedZ 769 n n where
  separates := fun hne => absurd rfl hne
  left_bounded := h
  right_bounded := h

theorem eight_pow_five_ne_one : (8 : F) ^ 5 ≠ 1 := by decide

theorem seedZ_pow_five_ne_one : seedZ ^ 5 ≠ 1 := by
  intro h
  have : (8 : F) ^ 5 = 1 :=
    φ_injective (by simpa [seedZ, map_pow] using h)
  exact eight_pow_five_ne_one this

theorem leaves_dotThenFormula : dotThenFormula.leaves = 12 := by
  simp [Noun.leaves, dotThenFormula, dotThenTail, dotOp2B, dotOp2C,
    dotOp9Formula, dotOp9Tail, dotCoreFormula, dotCore, dotElem0, dotElem1]

theorem leaves_dotElseFormula : dotElseFormula.leaves = 7 := by
  simp [Noun.leaves, dotElseFormula, dotCoreFormula, dotCore, dotElem0, dotElem1]

theorem then_else_fn_ne :
    NPR.fn dotThenFormula seedZ ≠ NPR.fn dotElseFormula seedZ := by
  intro h
  have hsz :
      (GlobalCarryRecognizer.enc seedZ dotThenFormula).size =
        (GlobalCarryRecognizer.enc seedZ dotElseFormula).size := by
    simp only [GlobalCarryRecognizer.enc_eq_fn, h]
  simp only [GlobalCarryRecognizer.enc_size, leaves_dotThenFormula,
    leaves_dotElseFormula] at hsz
  have hpow : seedZ ^ 7 * seedZ ^ 5 = seedZ ^ 7 * 1 := by
    rw [← pow_add]
    simpa [Nat.add_comm] using hsz
  have : seedZ ^ 5 = 1 :=
    mul_left_cancel₀ (pow_ne_zero 7 seedZ_ne_zero) hpow
  exact seedZ_pow_five_ne_one this

theorem then_else_pairFaithful :
    OpcodeSemantics.PairFaithful seedZ 769 dotThenFormula dotElseFormula where
  separates := fun _ => then_else_fn_ne
  left_bounded := b_dotThenFormula
  right_bounded := b_dotElseFormula

/-! ## Row-local comparison faithfulness / leaf bounds -/

theorem op6_comparison_faithful :
    ∀ c ∈ P8Census.skeletonComparisons (K := K) dotOp6Skel,
      OpcodeSemantics.PairFaithful seedZ 769 c.left c.right := by
  intro c hc
  rw [P8Census.skeletonComparisons] at hc
  simp [P8Census.skeletonDec, P8Census.skeletonSubformula, P8Census.skeletonUse,
    dotOp6Skel, genSkelOp6, ComputeTable.fanoutComp, decActive,
    hasTailDecomposition] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h
  · subst h; exact pairFaithful_self _ b_atom6
  · subst h; exact pairFaithful_self _ b_dotFormula
  · subst h; exact pairFaithful_self _ b_dotParentTail
  · subst h; exact pairFaithful_self _ b_dotBranchPair
  · subst h; exact pairFaithful_self _ b_dotSubject
  · subst h; exact pairFaithful_self _ b_dotThenFormula
  · subst h; exact then_else_pairFaithful
  · subst h; exact pairFaithful_self _ b_dotSubject
  · subst h; exact pairFaithful_self _ b_dotCondFormula
  · subst h; exact pairFaithful_self _ b_dotResult

theorem op6_comparison_leaves :
    ∀ c ∈ P8Census.skeletonComparisons (K := K) dotOp6Skel,
      c.LeavesBounded Λ := by
  intro c hc
  rw [P8Census.skeletonComparisons] at hc
  simp [P8Census.skeletonDec, P8Census.skeletonSubformula, P8Census.skeletonUse,
    dotOp6Skel, genSkelOp6, ComputeTable.fanoutComp, decActive,
    hasTailDecomposition] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotFormula, dotParentTail,
      dotCondFormula, dotBranchPair, dotThenFormula, dotElseFormula, dotThenTail,
      dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula, dotCore,
      dotElem0, dotElem1]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotParentTail,
      dotCondFormula, dotBranchPair, dotThenFormula, dotElseFormula, dotThenTail,
      dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula, dotCore,
      dotElem0, dotElem1]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotBranchPair,
      dotThenFormula, dotElseFormula, dotThenTail, dotOp2B, dotOp2C,
      dotOp9Formula, dotOp9Tail, dotCoreFormula, dotCore, dotElem0, dotElem1]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotSubject]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, leaves_dotThenFormula]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, leaves_dotThenFormula,
      leaves_dotElseFormula]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotSubject]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotCondFormula]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotResult]

theorem op2_comparison_faithful :
    ∀ c ∈ P8Census.skeletonComparisons (K := K) dotOp2Skel,
      OpcodeSemantics.PairFaithful seedZ 769 c.left c.right := by
  intro c hc
  rw [P8Census.skeletonComparisons] at hc
  simp [P8Census.skeletonDec, P8Census.skeletonSubformula, P8Census.skeletonUse,
    dotOp2Skel, genSkelOp2, ComputeTable.fanoutComp, decActive,
    hasTailDecomposition] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h
  · subst h; exact pairFaithful_self _ b_atom2
  · subst h; exact pairFaithful_self _ b_dotThenFormula
  · subst h; exact pairFaithful_self _ b_dotThenTail
  · subst h; exact pairFaithful_self _ b_dotSubject
  · subst h; exact pairFaithful_self _ b_dotOp2B
  · subst h; exact pairFaithful_self _ b_dotSubject
  · subst h; exact pairFaithful_self _ b_dotOp2C
  · subst h; exact pairFaithful_self _ b_dotOp2Sf1
  · subst h; exact pairFaithful_self _ b_dotOp2Sf2
  · subst h; exact pairFaithful_self _ b_dotResult

theorem op2_comparison_leaves :
    ∀ c ∈ P8Census.skeletonComparisons (K := K) dotOp2Skel,
      c.LeavesBounded Λ := by
  intro c hc
  rw [P8Census.skeletonComparisons] at hc
  simp [P8Census.skeletonDec, P8Census.skeletonSubformula, P8Census.skeletonUse,
    dotOp2Skel, genSkelOp2, ComputeTable.fanoutComp, decActive,
    hasTailDecomposition] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, leaves_dotThenFormula,
      dotThenTail, dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula,
      dotCore, dotElem0, dotElem1]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotThenTail, dotOp2B,
      dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula, dotCore, dotElem0,
      dotElem1]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotSubject]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotOp2B]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotSubject]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotOp2C, dotOp9Formula,
      dotOp9Tail, dotCoreFormula, dotCore, dotElem0, dotElem1]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotOp2Sf1]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotOp2Sf2, dotOp9Formula,
      dotOp9Tail, dotCoreFormula, dotCore, dotElem0, dotElem1]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotResult]

theorem op1_comparison_faithful (subject formula result head : Noun)
    (h1 : head = .atom 1) (hform : formula = .cell head result)
    (_ : FieldEmbedding.BoundedBy 769 head)
    (hf : FieldEmbedding.BoundedBy 769 formula)
    (hr : FieldEmbedding.BoundedBy 769 result) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp1 subject formula result head),
      OpcodeSemantics.PairFaithful seedZ 769 c.left c.right := by
  intro c hc
  rw [P8Census.skeletonComparisons] at hc
  simp [P8Census.skeletonDec, P8Census.skeletonUse, genSkelOp1, decActive] at hc
  rcases hc with h | h | h
  · subst h; rw [h1]; exact pairFaithful_self _ (by simp [FieldEmbedding.BoundedBy])
  · subst h; rw [hform]; exact pairFaithful_self (.cell head result) (hform ▸ hf)
  · subst h; exact pairFaithful_self _ hr

theorem op1_comparison_leaves (subject formula result head : Noun)
    (h1 : head = .atom 1) (hform : formula = .cell head result)
    (hf : formula.leaves ≤ Λ) (hr : result.leaves ≤ Λ) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp1 subject formula result head),
      c.LeavesBounded Λ := by
  intro c hc
  rw [P8Census.skeletonComparisons] at hc
  simp [P8Census.skeletonDec, P8Census.skeletonUse, genSkelOp1, decActive] at hc
  rcases hc with h | h | h
  · subst h; simp [h1, ComparisonUse.LeavesBounded, Noun.leaves, Λ]
  · subst h
    change formula.leaves ≤ Λ ∧ (Noun.cell head result).leaves ≤ Λ
    rw [← hform]
    exact ⟨hf, hf⟩
  · subst h; exact ⟨hr, hr⟩

theorem op9_comparison_faithful :
    ∀ c ∈ P8Census.skeletonComparisons (K := K) dotOp9Skel,
      OpcodeSemantics.PairFaithful seedZ 769 c.left c.right := by
  intro c hc
  rw [P8Census.skeletonComparisons] at hc
  simp [P8Census.skeletonDec, P8Census.skeletonSubformula, P8Census.skeletonUse,
    P8Census.skeletonMemoryAxis, dotOp9Skel, genSkelOp9, ComputeTable.fanoutComp,
    Nock.Framework.recordCount, decActive, hasTailDecomposition] at hc
  rcases hc with h | h | h | h | h | h | h | h
  · subst h; exact pairFaithful_self _ b_atom9
  · subst h; exact pairFaithful_self _ b_dotOp9Formula
  · subst h; exact pairFaithful_self _ b_dotOp9Tail
  · subst h; exact pairFaithful_self _ b_atom2
  · subst h; exact pairFaithful_self _ b_dotOp2Sf1
  · subst h; exact pairFaithful_self _ b_dotCoreFormula
  · subst h; exact pairFaithful_self _ b_dotCore
  · subst h; exact pairFaithful_self _ b_dotResult

theorem op9_comparison_leaves :
    ∀ c ∈ P8Census.skeletonComparisons (K := K) dotOp9Skel,
      c.LeavesBounded Λ := by
  intro c hc
  rw [P8Census.skeletonComparisons] at hc
  simp [P8Census.skeletonDec, P8Census.skeletonSubformula, P8Census.skeletonUse,
    P8Census.skeletonMemoryAxis, dotOp9Skel, genSkelOp9, ComputeTable.fanoutComp,
    Nock.Framework.recordCount, decActive, hasTailDecomposition] at hc
  rcases hc with h | h | h | h | h | h | h | h
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotOp9Formula, dotOp9Tail,
      dotCoreFormula, dotCore, dotElem0, dotElem1]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotOp9Tail, dotCoreFormula,
      dotCore, dotElem0, dotElem1]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotOp2Sf1]
  · subst h
    simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotCoreFormula, dotCore,
      dotElem0, dotElem1]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotCore, dotElem0, dotElem1]
  · subst h; simp [ComparisonUse.LeavesBounded, Noun.leaves, Λ, dotResult]

theorem row_comparison_faithful
    (s : ComputeRowSkeleton)
    (hs : s ∈ computeSkeletonRows (semanticSkeleton seedZ alphaA)) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      OpcodeSemantics.PairFaithful seedZ 769 c.left c.right := by
  rw [semanticSkeleton_computeRows] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h
  · subst h
    have : (dotTreeAir (K := K)).label.skel = dotOp6Skel := rfl
    rw [this]; exact op6_comparison_faithful
  · subst h
    have : (dotOp2Tree (K := K)).label.skel = dotOp2Skel := rfl
    rw [this]; exact op2_comparison_faithful
  · subst h
    have : (dotCondTree (K := K)).label.skel =
        genSkelOp1 dotSubject dotCondFormula dotCondResult (.atom 1) := rfl
    rw [this]
    exact op1_comparison_faithful _ _ _ _ rfl rfl b_atom1 b_dotCondFormula b_dotCondResult
  · subst h
    have : (dotOp1BTree (K := K)).label.skel =
        genSkelOp1 dotSubject dotOp2B dotOp2Sf1 (.atom 1) := rfl
    rw [this]
    exact op1_comparison_faithful _ _ _ _ rfl rfl b_atom1 b_dotOp2B b_dotOp2Sf1
  · subst h
    have : (dotOp1CTree (K := K)).label.skel =
        genSkelOp1 dotSubject dotOp2C dotOp2Sf2 (.atom 1) := rfl
    rw [this]
    exact op1_comparison_faithful _ _ _ _ rfl rfl b_atom1 b_dotOp2C b_dotOp2Sf2
  · subst h
    have : (dotOp9Tree (K := K)).label.skel = dotOp9Skel := rfl
    rw [this]; exact op9_comparison_faithful
  · subst h
    have : (dotOp9CoreTree (K := K)).label.skel =
        genSkelOp1 dotOp2Sf1 dotCoreFormula dotCore (.atom 1) := rfl
    rw [this]
    exact op1_comparison_faithful _ _ _ _ rfl rfl b_atom1 b_dotCoreFormula b_dotCore
  · subst h
    have : (dotOp9InvokeTree (K := K)).label.skel =
        genSkelOp1 dotCore dotArm dotResult (.atom 1) := rfl
    rw [this]
    exact op1_comparison_faithful _ _ _ _ rfl rfl b_atom1 b_dotArm b_dotResult

theorem row_comparison_leaves
    (s : ComputeRowSkeleton)
    (hs : s ∈ computeSkeletonRows (semanticSkeleton seedZ alphaA)) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K) s,
      c.LeavesBounded Λ := by
  rw [semanticSkeleton_computeRows] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h | h | h
  · subst h
    have : (dotTreeAir (K := K)).label.skel = dotOp6Skel := rfl
    rw [this]; exact op6_comparison_leaves
  · subst h
    have : (dotOp2Tree (K := K)).label.skel = dotOp2Skel := rfl
    rw [this]; exact op2_comparison_leaves
  · subst h
    have : (dotCondTree (K := K)).label.skel =
        genSkelOp1 dotSubject dotCondFormula dotCondResult (.atom 1) := rfl
    rw [this]
    exact op1_comparison_leaves _ _ _ _ rfl rfl
      (by simp [Noun.leaves, Λ, dotCondFormula])
      (by simp [Noun.leaves, Λ, dotCondResult])
  · subst h
    have : (dotOp1BTree (K := K)).label.skel =
        genSkelOp1 dotSubject dotOp2B dotOp2Sf1 (.atom 1) := rfl
    rw [this]
    exact op1_comparison_leaves _ _ _ _ rfl rfl
      (by simp [Noun.leaves, Λ, dotOp2B])
      (by simp [Noun.leaves, Λ, dotOp2Sf1])
  · subst h
    have : (dotOp1CTree (K := K)).label.skel =
        genSkelOp1 dotSubject dotOp2C dotOp2Sf2 (.atom 1) := rfl
    rw [this]
    exact op1_comparison_leaves _ _ _ _ rfl rfl
      (by simp [Noun.leaves, Λ, dotOp2C, dotOp9Formula, dotOp9Tail,
        dotCoreFormula, dotCore, dotElem0, dotElem1])
      (by simp [Noun.leaves, Λ, dotOp2Sf2, dotOp9Formula, dotOp9Tail,
        dotCoreFormula, dotCore, dotElem0, dotElem1])
  · subst h
    have : (dotOp9Tree (K := K)).label.skel = dotOp9Skel := rfl
    rw [this]; exact op9_comparison_leaves
  · subst h
    have : (dotOp9CoreTree (K := K)).label.skel =
        genSkelOp1 dotOp2Sf1 dotCoreFormula dotCore (.atom 1) := rfl
    rw [this]
    exact op1_comparison_leaves _ _ _ _ rfl rfl
      (by simp [Noun.leaves, Λ, dotCoreFormula, dotCore, dotElem0, dotElem1])
      (by simp [Noun.leaves, Λ, dotCore, dotElem0, dotElem1])
  · subst h
    have : (dotOp9InvokeTree (K := K)).label.skel =
        genSkelOp1 dotCore dotArm dotResult (.atom 1) := rfl
    rw [this]
    exact op1_comparison_leaves _ _ _ _ rfl rfl
      (by simp [Noun.leaves, Λ, dotArm, dotElem0])
      (by simp [Noun.leaves, Λ, dotResult])

/-! ## Assembled semantic CORE -/

theorem skelAt_mem (i : Fin (cfg seedZ alphaA).compRows) :
    skeletonRowAt (semanticSkeleton seedZ alphaA)
        (execThreaded seedZ alphaA) bindsAt_seed i ∈
      computeSkeletonRows (semanticSkeleton seedZ alphaA) :=
  List.get_mem _ _

theorem skelAt_bounded (i : Fin (cfg seedZ alphaA).compRows) :
    (skeletonRowAt (semanticSkeleton seedZ alphaA)
      (execThreaded seedZ alphaA) bindsAt_seed i).BoundedBy 769 :=
  List.forall_iff_forall_mem.mp
    (semanticSkeleton_bounded seedZ alphaA).computeRows _ (skelAt_mem i)

noncomputable def rowData (i : Fin (cfg seedZ alphaA).compRows) :
    ComputeRowSemanticData 769 Λ
      ((execThreaded seedZ alphaA).computeRowAt i) :=
  rowSemanticDataOf
    (skelAt_bounded i)
    (semanticSkeleton_operationalPremises _ (skelAt_mem i))
    (skeletonRowAt_binds (semanticSkeleton seedZ alphaA)
      (execThreaded seedZ alphaA) bindsAt_seed i)
    (row_comparison_faithful _ (skelAt_mem i))
    (row_comparison_leaves _ (skelAt_mem i))

noncomputable def semanticData
    (hfirst : ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0) :
    ExactExecutionSemanticData 769 Λ (cfg seedZ alphaA)
      (execThreaded seedZ alphaA) where
  language := language_seed hfirst
  rowAccepted := fun i =>
    computeRowAt_accepted
      (computeRowsAccepted_threaded seedZ alphaA seedZ_ne_zero) i
  rows := rowData

end

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.then_else_pairFaithful
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.semanticData
