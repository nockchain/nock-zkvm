/-
  Nock/NockVMROM/Thm54/VclL/Handle/HonestLeafH.lean

  Additive; no handle accumulator, coin or IO summand is touched; no existing module edited.

  The handle nouns of every honest row of the compiler's AIR-reordered tree have `≤ 2 * B` leaves when
  `programLeafBound (airReorder t) ≤ B`:
  * `s f e`: `handleNouns_sfe_leaves` (`HonestSizeH`);
  * `sf1 sf2` (child results) and the OP9 host `m` (a child's formula): each is a child row's own
    evaluation / formula (`childrenMatchSf` at every node of `airReorder t`, `AirLinked`, with the fan-out
    `children.length = fanoutComp`), hence at most `rowNounsBound child ≤ B`;
  * the OP6 host `m` is a head or tail of the formula (`≤ B`), the OP8 host `m = [sf2 s]` has `≤ 2 B`.
  So the honest bound is `2 B` (not `B`): OP8's `m` is a cell of two `B`-bounded nouns.  Then `hrank` for
  `honestVCLW_of_demandH2` follows from `2 * B ≤ 2^110`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestSizeH
import Nock.NockVMROM.Thm54.TraceGen.GenEdgeSelfCensus
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderBinding
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonFanout

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

open Nock Nock.Reified Nock.Framework Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.VclL.Compute

noncomputable section

section Leaf
variable {Kg : Type} [Field Kg]

theorem leaves_hdN_le (n : Noun) : (VclL.hdN n).leaves ≤ n.leaves := by
  cases n with
  | atom _ => simp [VclL.hdN]
  | cell a b => simp only [VclL.hdN, Noun.leaves]; omega

theorem leaves_tlN_le (n : Noun) : (VclL.tlN n).leaves ≤ n.leaves := by
  cases n with
  | atom _ => simp [VclL.tlN]
  | cell a b => simp only [VclL.tlN, Noun.leaves]; omega

theorem leaves_le_rowB_eval (g : GenComputeRow Kg) : g.skel.evaluation.leaves ≤ rowNounsBound g := by
  unfold rowNounsBound; exact le_sup_right

/-- Every node of the AIR-reordered tree of a run has `rowNounsBound ≤ B` when `programLeafBound ≤ B`. -/
theorem rowNounsBound_inTree {t : NTree (GenComputeRow Kg)} {B : ℕ}
    (hB : programLeafBound (airReorder t) ≤ B) :
    ∀ v, InTree (airReorder t) v → rowNounsBound v.label ≤ B :=
  (forall_bfsRows_iff (P := fun g => rowNounsBound g ≤ B) (airReorder t)).mp
    (foldl_sup_le_of_le (bfsRows (airReorder t)) rowNounsBound hB)

/-- **Child results / formulas are bounded by `programLeafBound`**: at every node `u` of the run's
AIR-reordered tree, the result and formula of each subformula slot (`childT`) has `≤ B` leaves. -/
theorem childT_leaves_le {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}
    (h : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result)) {B : ℕ}
    (hB : programLeafBound (airReorder t) ≤ B) (u : NTree (GenComputeRow Kg))
    (hu : InTree (airReorder t) u) (i : Fin 3) :
    (childT u.label.skel i .result).leaves ≤ B ∧ (childT u.label.skel i .formula).leaves ≤ B ∧ 1 ≤ B := by
  have hL : AirLinked (airReorder t) := airLinked_airReorder_of_gen h
  have hm := childrenMatchSf_of_inTree hL hu
  have hfan := airReorder_inTree_fanout (fun v hv => genComputeSkeleton_inTree_fanout h v hv) u hu
  have hrow := rowNounsBound_inTree hB
  have h1 : 1 ≤ B := by
    have := hrow u hu
    have h2 : u.label.skel.subject.leaves ≤ rowNounsBound u.label := leaves_le_rowB_subject _
    have h3 := Noun.one_le_leaves u.label.skel.subject
    omega
  refine ⟨?_, ?_, h1⟩ <;>
  · by_cases hi : (i : ℕ) < ComputeTable.fanoutComp u.label.skel.state
    · have hi' : (i : ℕ) < u.children.length := by rw [hfan]; exact hi
      have hc : InTree (airReorder t) (u.children[(i : ℕ)]'hi') :=
        InTree_trans hu (InTree.sub (List.getElem_mem hi') (InTree.here _))
      have hcb := hrow _ hc
      obtain ⟨-, hf, he⟩ := hm i hi'
      first
        | (have e : childT u.label.skel i .result = P8Census.skeletonSubformula u.label.skel i .result := rfl
           rw [e, ← he]
           exact (leaves_le_rowB_eval _).trans hcb)
        | (have e : childT u.label.skel i .formula = P8Census.skeletonSubformula u.label.skel i .formula := rfl
           rw [e, ← hf]
           exact (leaves_le_rowB_formula _).trans hcb)
    · unfold childT; rw [dif_neg hi]; simpa [Noun.leaves] using h1

/-- The `sf1`, `sf2`, `m` handles of a skeleton row, given the bounds on its pieces. -/
theorem rowOfSkel_sfm_leaves (sk : ComputeRowSkeleton) {B : ℕ} (hf : sk.formula.leaves ≤ B)
    (hs : sk.subject.leaves ≤ B)
    (hc0 : (childT sk 0 .result).leaves ≤ B) (hc1 : (childT sk 1 .result).leaves ≤ B)
    (hc1f : (childT sk 1 .formula).leaves ≤ B) (hB : 1 ≤ B) :
    (rowOfSkel sk).sf1.leaves ≤ B ∧ (rowOfSkel sk).sf2.leaves ≤ B ∧ (rowOfSkel sk).m.leaves ≤ 2 * B := by
  have h1 : (VclL.tlN sk.formula).leaves ≤ B := (leaves_tlN_le _).trans hf
  have h2 : (VclL.tlN (VclL.tlN sk.formula)).leaves ≤ B := (leaves_tlN_le _).trans h1
  have h3 : (VclL.hdN (VclL.tlN (VclL.tlN sk.formula))).leaves ≤ B := (leaves_hdN_le _).trans h2
  have h4 : (VclL.tlN (VclL.tlN (VclL.tlN sk.formula))).leaves ≤ B := (leaves_tlN_le _).trans h2
  have ha : (Noun.atom 0).leaves ≤ B := by simpa [Noun.leaves] using hB
  have hcs : (Noun.cell (childT sk 1 .result) sk.subject).leaves ≤ 2 * B := by
    simp only [Noun.leaves]; omega
  unfold rowOfSkel
  split <;> dsimp only <;> refine ⟨?_, ?_, ?_⟩ <;>
    first | omega | assumption | (split_ifs <;> assumption) | (split_ifs <;> omega)

/-- **All six handle nouns of every honest row have `≤ 2 * B` leaves** (`B ≥ programLeafBound`). -/
theorem handleNouns_leaves_le {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}
    (h : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result)) {B : ℕ}
    (hB : programLeafBound (airReorder t) ≤ B) :
    ∀ g ∈ bfsRows (airReorder t), ∀ n ∈ handleNouns g, n.leaves ≤ 2 * B := by
  refine (forall_bfsRows_iff (P := fun g => ∀ n ∈ handleNouns g, n.leaves ≤ 2 * B) (airReorder t)).mpr ?_
  intro u hu n hn
  have hg : u.label ∈ bfsRows (airReorder t) := by
    unfold bfsRows
    exact List.mem_map.mpr ⟨u, (mem_bfsForest _ u).mpr ⟨airReorder t, List.mem_singleton_self _, hu⟩, rfl⟩
  have hsfe := handleNouns_sfe_leaves t hB hg
  have c0 := childT_leaves_le h hB u hu 0
  have c1 := childT_leaves_le h hB u hu 1
  have hrow := rowNounsBound_inTree hB u hu
  have hsub : u.label.skel.subject.leaves ≤ B := (leaves_le_rowB_subject _).trans hrow
  have hfor : u.label.skel.formula.leaves ≤ B := (leaves_le_rowB_formula _).trans hrow
  have hsm := rowOfSkel_sfm_leaves u.label.skel hfor hsub c0.1 c1.1 c1.2.1 c1.2.2
  simp only [handleNouns, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact hsm.2.2

/-- **`hleafH` from the run.** -/
theorem hleafH_of_run {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}
    (h : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result)) {B : ℕ}
    (hB : programLeafBound (airReorder t) ≤ B) (hB2 : 2 * B ≤ 2 ^ 110) :
    ∀ n ∈ (runRowsH t).flatMap handleNouns, n.leaves ≤ 2 ^ 110 := by
  intro n hn
  obtain ⟨g, hg, hn⟩ := List.mem_flatMap.mp hn
  exact (handleNouns_leaves_le h hB g hg n hn).trans hB2

/-- **`hrank` for `demandH2 (runRowsH t)` from the run.** -/
theorem hrank_of_run {fuel : ℕ} {subject formula result : Noun} {t : NTree (GenComputeRow Kg)}
    (h : genComputeSkeleton (K := Kg) fuel subject formula = .ok (t, result)) {B : ℕ}
    (hB : programLeafBound (airReorder t) ≤ B) (hB2 : 2 * B ≤ 2 ^ 110) :
    ∀ n ∈ (demandH2 (runRowsH t)).cells, rankOf n < 2 ^ 110 :=
  demandH2_rank_lt _ (hleafH_of_run h hB hB2)

end Leaf

end

end Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
