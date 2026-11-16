import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch1258Thm54HonestNonVacuity
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-
  Nock/RedTeam/Batch1259Thm54HonestNonVacuityConcrete.lean

  Program: subject `atom 0`, formula `[1 0]` (OP1), fuel `1`, result `atom 0`.  Field `F = ZMod 73`,
  `K = GaloisField 73 3`, `α = 5` (a primitive root, order `72`).  Measured: 1 compute row,
  `programAcc = 1`, leaf bound `2`, 5 memory rows, 1 root, `Ksz = 2`, `programFit = 6`, orbit height `3`,
  so `hF` needs `24 ∣ p − 1`: `73` is the smallest prime `≥ 25` with `p ≡ 1 mod 24` (Tier A at `769`
  would also do; this one is cheaper).  Every `nockCompiles_zmod` hypothesis is a closed theorem here
  (`hrun0 … hKszChar0`); `concrete_nockCompiles` is the capstone instance and `concrete_nonvacuous`
  the non-vacuity instance (`Batch1258.nonvacuous_zmod`).
-/
open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen

namespace Nock.RedTeam.Batch1259
variable {K : Type} [Field K]

abbrev subj0 : Noun := .atom 0
abbrev form0 : Noun := .cell (.atom 1) (.atom 0)
abbrev T0 : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp1 subj0 form0 (.atom 0) (.atom 1)) [⟨form0, .atom 0, 3, 0⟩]) []

theorem gen0 : genComputeSkeleton (K := K) 1 subj0 form0 = .ok (T0, .atom 0) := by
  simp [genComputeSkeleton]

theorem evalRom0 : evalRom 1 subj0 form0 = some (.atom 0) := by simp [evalRom]

theorem romTree0 (h : evalRom 1 subj0 form0 = some (.atom 0)) : romTree (K := K) h = T0 := by
  have hs := romTree_spec (K := K) h
  rw [gen0] at hs
  injection hs with hs
  exact (Prod.mk.inj hs).1.symm

theorem air0 : airReorder (T0 (K := K)) = T0 := by
  simp [airReorder, skelNode, genSkelOp1, airNeedsSwap]

theorem bfs_leaf {LT : Type} (g : LT) : bfsForest [NTree.node g []] = [NTree.node g []] := by
  rw [bfsForest_cons_eq _ (by simp)]; simp [NTree.children, bfsForest_nil]

theorem bfsRows0 : bfsRows (T0 (K := K)) = [skelNode (genSkelOp1 subj0 form0 (.atom 0) (.atom 1)) [⟨form0, .atom 0, 3, 0⟩]] := by
  simp [bfsRows, bfs_leaf]
theorem acc0 : programAcc (T0 (K := K)) = 1 := by
  rw [programAcc, air0, bfsRows0]; simp [accAt, bfsRows0, skelNode, genSkelOp1, Framework.recordCount]
theorem comp0 : programCompRows (T0 (K := K)) = 1 := by
  rw [programCompRows, air0, bfsRows0]; rfl
theorem leaf0 : programLeafBound (airReorder (T0 (K := K))) = 2 := by
  rw [air0, programLeafBound, bfsRows0]; simp [rowNounsBound, skelNode, genSkelOp1, Noun.leaves]
theorem forest0 (z α lmb : K) :
    genMemForestFromTree (encC z) z α lmb (bfsAssign (T0 (K := K))) =
      [genAnnotatedRecordTree (encC z) z α lmb form0 (.atom 0) 3
        (getRecordExp (stampOfAcc ComputeTable.State.s1 0) 0)] := by
  rw [T0, bfsAssign_node_nil]
  simp [genMemForestFromTree, genMemForestFromList, extractNodeReqs, extractNodeReqsAux,
    genRowMemForest, skelNode, genSkelOp1]

theorem memRows0 (lmb z α : K) : programMemRowsL lmb z α (T0 (K := K)) = 5 := by
  simp only [programMemRowsL, genMemoryForest]
  rw [bfsForest_length, threadGenForest_totalSize, air0, forest0]
  simp [totalSize, genAnnotatedRecordTree_size, recordTreeSize]
  have ht : axisTopBit 3 = true := by decide
  have hr : axisRest 3 = 1 := by decide
  rw [descentForestSize_of_tail _ _ (by omega) ht, hr, descentForestSize_of_lt2 _ _ (by omega)]
  simp [nounWalkSize, formulaHead, formulaTail]

theorem memRoots0 (lmb z α : K) : programMemRootsL lmb z α (T0 (K := K)) = 1 := by
  simp only [programMemRootsL, genMemoryForest]
  rw [threadGenForest_length, air0, forest0]; rfl

/-! ## The configuration `p = 73`, `K = GaloisField 73 3` -/

instance fact73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩
abbrev K0 : Type := GaloisField 73 3
noncomputable instance : Fintype K0 := Fintype.ofFinite K0
noncomputable instance : DecidableEq K0 := Classical.decEq K0
instance : CharP K0 (ringChar K0) := ringChar.charP K0

theorem hK0 : Module.finrank (ZMod 73) K0 = 3 := GaloisField.finrank 73 (by norm_num)

theorem orderOf_five : orderOf (5 : ZMod 73) = 72 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  decide

noncomputable def α0 : K0 := algebraMap (ZMod 73) K0 5

theorem orderOf_α0 : orderOf α0 = 72 := by
  have h := orderOf_injective (algebraMap (ZMod 73) K0).toMonoidHom
    (algebraMap (ZMod 73) K0).injective (5 : ZMod 73)
  rw [orderOf_five] at h
  simpa [α0] using h

theorem ringChar_K0 : ringChar K0 = 73 :=
  CharP.eq K0 (ringChar.charP K0) (charP_of_injective_algebraMap (algebraMap (ZMod 73) K0).injective 73)

theorem hrun0 : Nock.evalN 1 subj0 form0 = some (.atom 0) := by
  simp [Nock.evalN]

theorem hgrom0 : evalGRom 73 1 subj0 form0 = some (.atom 0) := by
  simp [evalGRom]

theorem hbound0 : RunBoundedBy 73 1 subj0 form0 := ⟨_, hgrom0⟩

theorem hs0 : FieldEmbedding.BoundedBy 73 subj0 := by
  simp [FieldEmbedding.BoundedBy]

theorem hf0 : FieldEmbedding.BoundedBy 73 form0 := by
  simp [FieldEmbedding.BoundedBy]

theorem programMemShape0 (α : K) : programMemShape α (T0 (K := K)) = 5 := by
  unfold programMemShape programMemRows; exact memRows0 0 0 α

theorem programFit0 (α : K) : programFit α (T0 (K := K)) = 6 := by
  simp only [programFit, programMemShape0, comp0, acc0]; rfl

theorem orbitHeight6 : orbitHeight 6 = 3 := by
  have hle : orbitHeight 6 ≤ 3 := orbitHeight_le_of_le (by norm_num) (by norm_num)
  have hge : 6 ≤ 2 ^ orbitHeight 6 := le_two_pow_orbitHeight 6
  rcases Nat.lt_or_ge (orbitHeight 6) 3 with h | h
  · interval_cases (orbitHeight 6) <;> simp_all
  · omega

theorem hΛp0 (h : evalRom 1 subj0 form0 = some (.atom 0)) :
    programLeafBound (airReorder (romTree (K := K0) h)) < 73 := by
  rw [romTree0, leaf0]; norm_num

theorem hp0 : 25 ≤ 73 := by norm_num
theorem hp64_0 : 73 < 2 ^ 64 := by norm_num

theorem hF0 (h : evalRom 1 subj0 form0 = some (.atom 0)) :
    3 * 2 ^ orbitHeight (programFit α0 (romTree (K := K0) h)) ∣ 73 - 1 := by
  rw [romTree0, programFit0, orbitHeight6]; norm_num

theorem hwin0 (h : evalRom 1 subj0 form0 = some (.atom 0)) :
    programAcc (romTree (K := K0) h) + 3 < orderOf α0 ∧
      programMemShape α0 (romTree (K := K0) h) ≤ orderOf α0 := by
  rw [romTree0, acc0, programMemShape0, orderOf_α0]; norm_num

theorem hKszChar0 (h : evalRom 1 subj0 form0 = some (.atom 0)) :
    compilerKszOf (0 : K0) α0 (romTree (K := K0) h) < 73 := by
  rw [romTree0]
  simp only [compilerKszOf, compilerKsz, programMemRoots, memRoots0, acc0]
  norm_num

/-- **`nockCompiles_zmod` at one concrete generated program**: subject `0`, formula `[1 0]`
(OP1), `F = ZMod 73`, `K = GaloisField 73 3`, `α = 5` (order `72`), every hypothesis closed. -/
theorem concrete_nockCompiles (lmb0 : K0) :
    ∃ package : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage (ZMod 73) K0
      (orbitHeight (programFit α0
        (romTree (K := K0) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun0 hbound0))))),
      OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subj0, form0, .atom 0⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb0
        ∧ package.optimized.family.memoryWalkAlpha = α0 :=
  GoodSeed.nockCompiles_zmod (p := 73) (K := K0) α0 α0 lmb0 hrun0 hbound0 hs0 hf0
    (hΛp0 _) hp0 hp64_0 hK0 (hF0 _) (hwin0 _) (hKszChar0 _)

/-- **Non-vacuity at one concrete generated program, zero open premises**: the package of
`Batch1258.nonvacuous_zmod` at `[1 0]` over `ZMod 73`: Stmt, the claim, `λ`, and `Batch1173`'s three
conclusions at its honest tuple and honest traces. -/
theorem concrete_nonvacuous (lmb0 : K0) :
    ∃ package : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage (ZMod 73) K0
      (orbitHeight (programFit α0
        (romTree (K := K0) (evalGRom_le_evalRom (evalGRom_of_runBounded hrun0 hbound0))))),
      OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement package
        ∧ package.optimized.verifier.raw.claim = ⟨subj0, form0, .atom 0⟩
        ∧ package.optimized.objects.cfg.challenges.lam = lmb0
        ∧ Nock.RedTeam.Batch1258.NV package :=
  Nock.RedTeam.Batch1258.nonvacuous_zmod (p := 73) (K := K0) α0 lmb0 hrun0 hbound0 hs0 hf0
    (hΛp0 _) hp0 hp64_0 hK0 (hF0 _) (hwin0 _) (hKszChar0 _)

end Nock.RedTeam.Batch1259

#print axioms Nock.RedTeam.Batch1259.concrete_nockCompiles
#print axioms Nock.RedTeam.Batch1259.hF0
#print axioms Nock.RedTeam.Batch1259.hwin0
#print axioms Nock.RedTeam.Batch1259.hKszChar0
#print axioms Nock.RedTeam.Batch1259.hΛp0
#print axioms Nock.RedTeam.Batch1259.ringChar_K0
#print axioms Nock.RedTeam.Batch1259.orderOf_α0
#print axioms Nock.RedTeam.Batch1259.hrun0
#print axioms Nock.RedTeam.Batch1259.hbound0
#print axioms Nock.RedTeam.Batch1259.hs0
#print axioms Nock.RedTeam.Batch1259.hf0
#print axioms Nock.RedTeam.Batch1259.hK0
#print axioms Nock.RedTeam.Batch1259.romTree0
#print axioms Nock.RedTeam.Batch1259.concrete_nonvacuous
