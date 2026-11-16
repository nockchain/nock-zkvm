/-
  Nock/NockVMROM/Thm54/TraceGen/GenGenericSeedIrrel.lean

  **Memory-forest counts do not depend on the NPR seed.**  Size of each
  generated tree is a function of the request nouns and axes
  (`recordTreeSize`, `descentContForestSize` in `GenMatmulMemSize.lean`);
  `encC z` only writes fingerprints.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMemSize
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemWeb
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open MemoryTable

variable {K : Type} [Field K]

variable {lmb : K}

theorem totalSize_map_annotated (E : Noun → ComputeTable.FP K)
    (z α : K) : ∀ rs : List MemRecordReq,
    totalSize (rs.map (fun r =>
        genAnnotatedRecordTree E z α lmb r.root r.child r.axis r.recordExp)) =
      (rs.map (fun r => recordTreeSize r.root r.child r.axis)).sum
  | [] => by simp [totalSize]
  | r :: rs => by
      simp [totalSize_cons, genAnnotatedRecordTree_size, totalSize_map_annotated E z α rs]

theorem genRowMemForest_length_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α : K) (reqs : List MemRecordReq) :
    (genRowMemForest E z α lmb reqs).length = (genRowMemForest E' z' α lmb reqs).length := by
  match reqs with
  | [] => simp [genRowMemForest]
  | [r] => simp [genRowMemForest]
  | [r1, r2] =>
    by_cases hc : r1.child = r2.root
    · exact (genRowMemForest_two_chain_size (lmb := lmb) E z α r1 r2 hc).2.trans
        (genRowMemForest_two_chain_size (lmb := lmb) E' z' α r1 r2 hc).2.symm
    · exact (genRowMemForest_two_indep_size (lmb := lmb) E z α r1 r2 hc).2.trans
        (genRowMemForest_two_indep_size (lmb := lmb) E' z' α r1 r2 hc).2.symm
  | [r1, r2, r3] =>
    simp [genRowMemForest_three_eq]
    exact genRowMemForest_length_irrel E E' z z' α [r1, r2]
  | r1 :: r2 :: r3 :: r4 :: rest =>
    simp [genRowMemForest]

theorem genRowMemForest_totalSize_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α : K) (reqs : List MemRecordReq) :
    totalSize (genRowMemForest E z α lmb reqs) =
      totalSize (genRowMemForest E' z' α lmb reqs) := by
  match reqs with
  | [] => simp [genRowMemForest]
  | [r] =>
    rw [genRowMemForest_singleton_size, genRowMemForest_singleton_size]
  | [r1, r2] =>
    by_cases hc : r1.child = r2.root
    · exact (genRowMemForest_two_chain_size (lmb := lmb) E z α r1 r2 hc).1.trans
        (genRowMemForest_two_chain_size (lmb := lmb) E' z' α r1 r2 hc).1.symm
    · exact (genRowMemForest_two_indep_size (lmb := lmb) E z α r1 r2 hc).1.trans
        (genRowMemForest_two_indep_size (lmb := lmb) E' z' α r1 r2 hc).1.symm
  | [r1, r2, r3] =>
    simp [genRowMemForest_three_eq, totalSize_append]
    rw [genRowMemForest_totalSize_irrel E E' z z' α [r1, r2]]
    simp [totalSize_cons, totalSize_nil, genAnnotatedRecordTree_size]
  | r1 :: r2 :: r3 :: r4 :: rest =>
    have hE := totalSize_map_annotated (lmb := lmb) E z α (r1 :: r2 :: r3 :: r4 :: rest)
    have hE' := totalSize_map_annotated (lmb := lmb) E' z' α (r1 :: r2 :: r3 :: r4 :: rest)
    simp [genRowMemForest] at hE hE' ⊢
    rw [hE, hE']

mutual
theorem genMemForestFromTree_totalSize_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α : K) (t : NTree (GenComputeRow K)) :
    totalSize (genMemForestFromTree E z α lmb t) =
      totalSize (genMemForestFromTree E' z' α lmb t) := by
  cases t with
  | node g cs =>
    simp [genMemForestFromTree, totalSize_append]
    rw [genRowMemForest_totalSize_irrel E E' z z' α (extractNodeReqs g),
      genMemForestFromList_totalSize_irrel E E' z z' α cs]

theorem genMemForestFromList_totalSize_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α : K) (ts : List (NTree (GenComputeRow K))) :
    totalSize (genMemForestFromList E z α lmb ts) =
      totalSize (genMemForestFromList E' z' α lmb ts) := by
  cases ts with
  | nil => simp [genMemForestFromList]
  | cons t rest =>
    simp [genMemForestFromList, totalSize_append]
    rw [genMemForestFromTree_totalSize_irrel E E' z z' α t,
      genMemForestFromList_totalSize_irrel E E' z z' α rest]
end

mutual
theorem genMemForestFromTree_length_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α : K) (t : NTree (GenComputeRow K)) :
    (genMemForestFromTree E z α lmb t).length =
      (genMemForestFromTree E' z' α lmb t).length := by
  cases t with
  | node g cs =>
    simp [genMemForestFromTree]
    rw [genRowMemForest_length_irrel (lmb := lmb) E E' z z' α (extractNodeReqs g),
      genMemForestFromList_length_irrel E E' z z' α cs]

theorem genMemForestFromList_length_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α : K) (ts : List (NTree (GenComputeRow K))) :
    (genMemForestFromList E z α lmb ts).length =
      (genMemForestFromList E' z' α lmb ts).length := by
  cases ts with
  | nil => simp [genMemForestFromList]
  | cons t rest =>
    simp [genMemForestFromList]
    rw [genMemForestFromTree_length_irrel E E' z z' α t,
      genMemForestFromList_length_irrel E E' z z' α rest]
end

theorem genMemoryForest_totalSize_irrel (z z' α : K) (inp inp' : Inputs K)
    (t : NTree (GenComputeRow K)) :
    totalSize (genMemoryForest z α lmb inp t) =
      totalSize (genMemoryForest z' α lmb inp' t) := by
  simp [genMemoryForest, threadGenForest_totalSize]
  exact genMemForestFromTree_totalSize_irrel (encC z) (encC z') z z' α
    (bfsAssign (airReorder t))

theorem genMemoryForest_length_irrel (z z' α : K) (inp inp' : Inputs K)
    (t : NTree (GenComputeRow K)) :
    (genMemoryForest z α lmb inp t).length = (genMemoryForest z' α lmb inp' t).length := by
  simp [genMemoryForest, threadGenForest_length]
  exact genMemForestFromTree_length_irrel (lmb := lmb) (encC z) (encC z') z z' α
    (bfsAssign (airReorder t))

theorem genMemoryForest_bfsForest_length_irrel (z z' α : K) (inp inp' : Inputs K)
    (t : NTree (GenComputeRow K)) :
    (bfsForest (genMemoryForest z α lmb inp t)).length =
      (bfsForest (genMemoryForest z' α lmb inp' t)).length := by
  rw [bfsForest_length, bfsForest_length, genMemoryForest_totalSize_irrel]

/-! ## λ-irrelevance of the forest counts

The Form R `λ` is a row label (`MemoryTable.Pub.lambda`), sampled with `α`; it never changes a
tree's shape.  So every count the compiler reads off the memory forest (`programMemRows`,
`programMemRoots`) is the same at every `λ`, and the compiler need not pick one. -/

theorem genRowMemForest_length_lam_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α lmb₁ lmb₂ : K) (reqs : List MemRecordReq) :
    (genRowMemForest E z α lmb₁ reqs).length = (genRowMemForest E' z' α lmb₂ reqs).length := by
  match reqs with
  | [] => simp [genRowMemForest]
  | [r] => simp [genRowMemForest]
  | [r1, r2] =>
    by_cases hc : r1.child = r2.root
    · exact (genRowMemForest_two_chain_size (lmb := lmb₁) E z α r1 r2 hc).2.trans
        (genRowMemForest_two_chain_size (lmb := lmb₂) E' z' α r1 r2 hc).2.symm
    · exact (genRowMemForest_two_indep_size (lmb := lmb₁) E z α r1 r2 hc).2.trans
        (genRowMemForest_two_indep_size (lmb := lmb₂) E' z' α r1 r2 hc).2.symm
  | [r1, r2, r3] =>
    simp [genRowMemForest_three_eq]
    exact genRowMemForest_length_lam_irrel E E' z z' α lmb₁ lmb₂ [r1, r2]
  | r1 :: r2 :: r3 :: r4 :: rest =>
    simp [genRowMemForest]

theorem genRowMemForest_totalSize_lam_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α lmb₁ lmb₂ : K) (reqs : List MemRecordReq) :
    totalSize (genRowMemForest E z α lmb₁ reqs) =
      totalSize (genRowMemForest E' z' α lmb₂ reqs) := by
  match reqs with
  | [] => simp [genRowMemForest]
  | [r] =>
    rw [genRowMemForest_singleton_size, genRowMemForest_singleton_size]
  | [r1, r2] =>
    by_cases hc : r1.child = r2.root
    · exact (genRowMemForest_two_chain_size (lmb := lmb₁) E z α r1 r2 hc).1.trans
        (genRowMemForest_two_chain_size (lmb := lmb₂) E' z' α r1 r2 hc).1.symm
    · exact (genRowMemForest_two_indep_size (lmb := lmb₁) E z α r1 r2 hc).1.trans
        (genRowMemForest_two_indep_size (lmb := lmb₂) E' z' α r1 r2 hc).1.symm
  | [r1, r2, r3] =>
    simp [genRowMemForest_three_eq, totalSize_append]
    rw [genRowMemForest_totalSize_lam_irrel E E' z z' α lmb₁ lmb₂ [r1, r2]]
    simp [totalSize_cons, totalSize_nil, genAnnotatedRecordTree_size]
  | r1 :: r2 :: r3 :: r4 :: rest =>
    have hE := totalSize_map_annotated (lmb := lmb₁) E z α (r1 :: r2 :: r3 :: r4 :: rest)
    have hE' := totalSize_map_annotated (lmb := lmb₂) E' z' α (r1 :: r2 :: r3 :: r4 :: rest)
    simp [genRowMemForest] at hE hE' ⊢
    rw [hE, hE']

mutual
theorem genMemForestFromTree_totalSize_lam_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α lmb₁ lmb₂ : K) (t : NTree (GenComputeRow K)) :
    totalSize (genMemForestFromTree E z α lmb₁ t) =
      totalSize (genMemForestFromTree E' z' α lmb₂ t) := by
  cases t with
  | node g cs =>
    simp [genMemForestFromTree, totalSize_append]
    rw [genRowMemForest_totalSize_lam_irrel E E' z z' α lmb₁ lmb₂ (extractNodeReqs g),
      genMemForestFromList_totalSize_lam_irrel E E' z z' α lmb₁ lmb₂ cs]

theorem genMemForestFromList_totalSize_lam_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α lmb₁ lmb₂ : K) (ts : List (NTree (GenComputeRow K))) :
    totalSize (genMemForestFromList E z α lmb₁ ts) =
      totalSize (genMemForestFromList E' z' α lmb₂ ts) := by
  cases ts with
  | nil => simp [genMemForestFromList]
  | cons t rest =>
    simp [genMemForestFromList, totalSize_append]
    rw [genMemForestFromTree_totalSize_lam_irrel E E' z z' α lmb₁ lmb₂ t,
      genMemForestFromList_totalSize_lam_irrel E E' z z' α lmb₁ lmb₂ rest]
end

mutual
theorem genMemForestFromTree_length_lam_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α lmb₁ lmb₂ : K) (t : NTree (GenComputeRow K)) :
    (genMemForestFromTree E z α lmb₁ t).length =
      (genMemForestFromTree E' z' α lmb₂ t).length := by
  cases t with
  | node g cs =>
    simp [genMemForestFromTree]
    rw [genRowMemForest_length_lam_irrel E E' z z' α lmb₁ lmb₂ (extractNodeReqs g),
      genMemForestFromList_length_lam_irrel E E' z z' α lmb₁ lmb₂ cs]

theorem genMemForestFromList_length_lam_irrel (E E' : Noun → ComputeTable.FP K)
    (z z' α lmb₁ lmb₂ : K) (ts : List (NTree (GenComputeRow K))) :
    (genMemForestFromList E z α lmb₁ ts).length =
      (genMemForestFromList E' z' α lmb₂ ts).length := by
  cases ts with
  | nil => simp [genMemForestFromList]
  | cons t rest =>
    simp [genMemForestFromList]
    rw [genMemForestFromTree_length_lam_irrel E E' z z' α lmb₁ lmb₂ t,
      genMemForestFromList_length_lam_irrel E E' z z' α lmb₁ lmb₂ rest]
end

/-- **Memory-root count at any seed and any `λ`.** -/
theorem genMemoryForest_length_lam_irrel (z z' α lmb₁ lmb₂ : K) (inp inp' : Inputs K)
    (t : NTree (GenComputeRow K)) :
    (genMemoryForest z α lmb₁ inp t).length = (genMemoryForest z' α lmb₂ inp' t).length := by
  simp [genMemoryForest, threadGenForest_length]
  exact genMemForestFromTree_length_lam_irrel (encC z) (encC z') z z' α lmb₁ lmb₂
    (bfsAssign (airReorder t))

/-- **Memory-row count at any seed and any `λ`.** -/
theorem genMemoryForest_bfsForest_length_lam_irrel (z z' α lmb₁ lmb₂ : K) (inp inp' : Inputs K)
    (t : NTree (GenComputeRow K)) :
    (bfsForest (genMemoryForest z α lmb₁ inp t)).length =
      (bfsForest (genMemoryForest z' α lmb₂ inp' t)).length := by
  rw [bfsForest_length, bfsForest_length]
  simp only [genMemoryForest, threadGenForest_totalSize]
  exact genMemForestFromTree_totalSize_lam_irrel (encC z) (encC z') z z' α lmb₁ lmb₂
    (bfsAssign (airReorder t))

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_bfsForest_length_irrel
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_length_irrel
#print axioms Nock.NockVMROM.Thm54.TraceGen.genMemoryForest_bfsForest_length_lam_irrel
