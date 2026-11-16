import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesHostile
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMemSize
import Nock.NockVMROM.Thm54.TraceGen.GenTierASize

/-
  Nock/RedTeam/Batch1571Thm54ZeroBinderShapes.lean

  (a) BFS shape lemmas for compute trees of the shapes a root with one,
  two and three leaf children (`bfsAssign_one_leaf` / `_two_leaves` / `_three_leaves`), copied in
  proof style from `BFSAssign.bfsAssign_eq_assignExponents_two_leaves`; (b) the field kit at
  `K = GaloisField p 3`, `α = algebraMap a`.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Nock.RedTeam.Batch1571

open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen

section
variable {K : Type} [Field K]


theorem bfsForest_one_leaf {α : Type} (g gl : α) :
    bfsForest [NTree.node g [NTree.node gl []]] =
      [NTree.node g [NTree.node gl []], NTree.node gl []] := by
  rw [bfsForest_singleton]
  simp only [NTree.children_node]
  rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, List.flatMap_nil, NTree.children_node,
    List.append_nil, bfsForest_nil, List.cons_append, List.nil_append]

theorem bfsRows_one_leaf (g gl : GenComputeRow K) :
    bfsRows (NTree.node g [NTree.node gl []]) = [g, gl] := by
  simp [bfsRows, bfsForest_one_leaf]

theorem bfsForest_three_leaves {α : Type} (g g1 g2 g3 : α) :
    bfsForest [NTree.node g [NTree.node g1 [], NTree.node g2 [], NTree.node g3 []]] =
      [NTree.node g [NTree.node g1 [], NTree.node g2 [], NTree.node g3 []],
        NTree.node g1 [], NTree.node g2 [], NTree.node g3 []] := by
  rw [bfsForest_singleton]
  simp only [NTree.children_node]
  rw [bfsForest_cons_eq _ (List.cons_ne_nil _ _)]
  simp only [List.flatMap_cons, List.flatMap_nil, NTree.children_node,
    List.append_nil, bfsForest_nil, List.cons_append, List.nil_append]

theorem bfsRows_three_leaves (g g1 g2 g3 : GenComputeRow K) :
    bfsRows (NTree.node g [NTree.node g1 [], NTree.node g2 [], NTree.node g3 []]) = [g, g1, g2, g3] := by
  simp [bfsRows, bfsForest_three_leaves]

/-- One child: BFS stamps. -/
theorem bfsAssign_one_leaf (g gl : GenComputeRow K) :
    bfsAssign (NTree.node g [NTree.node gl []]) =
      NTree.node { g with stamp := stampOfAcc g.skel.state 0 }
        [NTree.node { gl with stamp := stampOfAcc gl.skel.state (Nock.Framework.recordCount g.skel.state) } []] := by
  set t := NTree.node g [NTree.node gl []]
  have hW := bfsForest_one_leaf g gl
  have hlen : (bfsForest [t]).length = 2 := by simp [t, hW]
  have hfo1 : foCol (bfsForest [t]) 1 = 1 := by
    simp [foCol, t, hW, NTree.children_node, List.getElem?_cons_zero]
  have hfo2 : foCol (bfsForest [t]) 2 = 0 := by
    simp [foCol, t, hW, NTree.children_node, List.getElem?_cons_zero,
      List.getElem?_cons_succ]
  have hch1 : childIdxsF 1 (foCol (bfsForest [t])) 2 1 = [2] := by
    unfold childIdxsF firstCF
    simp [Sf_zero, hfo1, List.range'_succ, List.range'_zero, List.filter,
      decide_eq_true_eq]
  have hch2 : childIdxsF 1 (foCol (bfsForest [t])) 2 2 = [] := by
    unfold childIdxsF
    simp [hfo2, List.range'_zero]
  have hlbl1 : bfsLabelAt t 1 =
      { g with stamp := stampOfAcc g.skel.state 0 } := by
    unfold bfsLabelAt
    simp [t, bfsRows_one_leaf, accAt, List.getElem?_cons_zero]
  have hlbl2 : bfsLabelAt t 2 =
      { gl with stamp := stampOfAcc gl.skel.state (Nock.Framework.recordCount g.skel.state) } := by
    unfold bfsLabelAt
    simp [t, bfsRows_one_leaf, accAt, List.getElem?_cons_zero,
      List.getElem?_cons_succ]
  have hlhs :
      buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t) 2 1 =
        NTree.node { g with stamp := stampOfAcc g.skel.state 0 }
          [NTree.node { gl with stamp := stampOfAcc gl.skel.state (Nock.Framework.recordCount g.skel.state) } []] := by
    rw [buildTF_eq_node, hch1, List.map_cons, List.map_nil]
    rw [buildTF_eq_node (i := 2), hch2, List.map_nil]
    rw [hlbl1, hlbl2]
  rw [bfsAssign, hlen, hlhs]

/-- Three leaf children: BFS stamps. -/
theorem bfsAssign_three_leaves (g g1 g2 g3 : GenComputeRow K) :
    bfsAssign (NTree.node g [NTree.node g1 [], NTree.node g2 [], NTree.node g3 []]) =
      NTree.node { g with stamp := stampOfAcc g.skel.state 0 }
        [NTree.node { g1 with stamp := stampOfAcc g1.skel.state (Nock.Framework.recordCount g.skel.state) } [],
         NTree.node { g2 with stamp := stampOfAcc g2.skel.state (Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount g1.skel.state) } [],
         NTree.node { g3 with stamp := stampOfAcc g3.skel.state (Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount g1.skel.state + Nock.Framework.recordCount g2.skel.state) } []] := by
  set t := NTree.node g [NTree.node g1 [], NTree.node g2 [], NTree.node g3 []]
  have hW := bfsForest_three_leaves g g1 g2 g3
  have hlen : (bfsForest [t]).length = 4 := by simp [t, hW]
  have hfo1 : foCol (bfsForest [t]) 1 = 3 := by
    simp [foCol, t, hW, NTree.children_node]
  have hfo2 : foCol (bfsForest [t]) 2 = 0 := by
    simp [foCol, t, hW, NTree.children_node]
  have hfo3 : foCol (bfsForest [t]) 3 = 0 := by
    simp [foCol, t, hW, NTree.children_node]
  have hfo4 : foCol (bfsForest [t]) 4 = 0 := by
    simp [foCol, t, hW, NTree.children_node]
  have hch1 : childIdxsF 1 (foCol (bfsForest [t])) 4 1 = [2, 3, 4] := by
    unfold childIdxsF firstCF
    simp [Sf_zero, hfo1, List.range'_succ, List.range'_zero, List.filter]
  have hch2 : childIdxsF 1 (foCol (bfsForest [t])) 4 2 = [] := by
    unfold childIdxsF
    simp [hfo2, List.range'_zero]
  have hch3 : childIdxsF 1 (foCol (bfsForest [t])) 4 3 = [] := by
    unfold childIdxsF
    simp [hfo3, List.range'_zero]
  have hch4 : childIdxsF 1 (foCol (bfsForest [t])) 4 4 = [] := by
    unfold childIdxsF
    simp [hfo4, List.range'_zero]
  have hrows : bfsRows t = [g, g1, g2, g3] := bfsRows_three_leaves g g1 g2 g3
  have hacc2 : accAt t 1 = Nock.Framework.recordCount g.skel.state := by
    simp [accAt, hrows]
  have hacc3 : accAt t 2 = Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount g1.skel.state := by
    simp [accAt, hrows]
  have hacc4 : accAt t 3 = Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount g1.skel.state + Nock.Framework.recordCount g2.skel.state := by
    simp [accAt, hrows]
  have hlbl1 : bfsLabelAt t 1 = { g with stamp := stampOfAcc g.skel.state 0 } := by
    unfold bfsLabelAt
    simp [hrows, accAt]
  have hlbl2 : bfsLabelAt t 2 =
      { g1 with stamp := stampOfAcc g1.skel.state (Nock.Framework.recordCount g.skel.state) } := by
    unfold bfsLabelAt
    simp [hrows, hacc2]
  have hlbl3 : bfsLabelAt t 3 =
      { g2 with stamp := stampOfAcc g2.skel.state (Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount g1.skel.state) } := by
    unfold bfsLabelAt
    simp [hrows, hacc3]
  have hlbl4 : bfsLabelAt t 4 =
      { g3 with stamp := stampOfAcc g3.skel.state (Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount g1.skel.state + Nock.Framework.recordCount g2.skel.state) } := by
    unfold bfsLabelAt
    simp [hrows, hacc4]
  have hlhs :
      buildTF 1 (foCol (bfsForest [t])) (bfsLabelAt t) 4 1 =
        NTree.node { g with stamp := stampOfAcc g.skel.state 0 }
        [NTree.node { g1 with stamp := stampOfAcc g1.skel.state (Nock.Framework.recordCount g.skel.state) } [],
         NTree.node { g2 with stamp := stampOfAcc g2.skel.state (Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount g1.skel.state) } [],
         NTree.node { g3 with stamp := stampOfAcc g3.skel.state (Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount g1.skel.state + Nock.Framework.recordCount g2.skel.state) } []] := by
    rw [buildTF_eq_node, hch1, List.map_cons, List.map_cons, List.map_cons, List.map_nil]
    rw [buildTF_eq_node (i := 2), hch2, List.map_nil]
    rw [buildTF_eq_node (i := 3), hch3, List.map_nil]
    rw [buildTF_eq_node (i := 4), hch4, List.map_nil]
    rw [hlbl1, hlbl2, hlbl3, hlbl4]
  rw [bfsAssign, hlen, hlhs]

theorem bfsAssign_two_leaves (g g1 g2 : GenComputeRow K) :
    bfsAssign (NTree.node g [NTree.node g1 [], NTree.node g2 []]) =
      NTree.node { g with stamp := stampOfAcc g.skel.state 0 }
        [NTree.node { g1 with stamp := stampOfAcc g1.skel.state (Nock.Framework.recordCount g.skel.state) } [],
         NTree.node { g2 with stamp := stampOfAcc g2.skel.state (Nock.Framework.recordCount g.skel.state + Nock.Framework.recordCount g1.skel.state) } []] := by
  rw [bfsAssign_eq_assignExponents_two_leaves]
  simp only [assignExponents, assignTree, assignList, subtreeRecordCount,
      List.map_nil, List.map_cons, List.sum_nil, List.sum_cons, Nat.zero_add,
      Nat.add_zero]


theorem chain32_length (E : Noun → ComputeTable.FP K) (z α : K) {lmb : K}
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    (genRowMemForest E z α lmb
        [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
         ⟨.cell hd2 tl2, hd2, 2, e2⟩]).length = 1 :=
  genRowMemForest_chain_length E z α _ _ rfl

end

/-! ## Field kit: `K = GaloisField p 3`, `α = algebraMap a` -/

section Kit
variable (p : ℕ) [Fact p.Prime]

noncomputable def αP (a : ZMod p) : GaloisField p 3 := algebraMap (ZMod p) (GaloisField p 3) a

theorem orderOf_αP (a : ZMod p) : orderOf (αP p a) = orderOf a := by
  have h := orderOf_injective (algebraMap (ZMod p) (GaloisField p 3)).toMonoidHom
    (algebraMap (ZMod p) (GaloisField p 3)).injective a
  simpa [αP] using h

theorem hK_P : Module.finrank (ZMod p) (GaloisField p 3) = 3 := GaloisField.finrank p (by norm_num)

theorem dvd_of_fit_le {n H : ℕ} (hH1 : 1 ≤ H) (hle : n ≤ 2 ^ H) (hd : 3 * 2 ^ H ∣ p - 1) :
    3 * 2 ^ orbitHeight n ∣ p - 1 :=
  dvd_trans (mul_dvd_mul_left 3 (pow_dvd_pow 2 (orbitHeight_le_of_le hH1 hle))) hd

end Kit

end Nock.RedTeam.Batch1571
