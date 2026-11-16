/-
  Nock/NockVMROM/Thm54/BelowDefs/CensusExtraClosure.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/CensusExtraClosure.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.GenericHonestData

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.CensusExtraClosure

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.HonestCommitment

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **Every edge pair is one execution label against one chosen witness.**  Its left component is
the *child* row's own `subject` / `formula` / `evaluation`; its right component is the *parent*
row's subformula slot, which on the reconstruction is a `Classical.choose` witness.  This is why a
`census` route cannot be split into "labels only": the edge half never is. -/
theorem edgePairs_left_is_a_child_label {tree : NTree EdgeComparisonCensus.Row}
    {pair : Noun × Noun} (hp : pair ∈ EdgeComparisonCensus.edgePairs tree) :
    ∃ node ∈ bfsForest [tree], ∃ i : Fin 3, ∃ child ∈ node.children,
      ((pair.1 = child.label.subject ∧
          pair.2 = P8Census.skeletonSubformula node.label i .subject) ∨
        (pair.1 = child.label.formula ∧
          pair.2 = P8Census.skeletonSubformula node.label i .formula) ∨
        (pair.1 = child.label.evaluation ∧
          pair.2 = P8Census.skeletonSubformula node.label i .result)) := by
  rw [EdgeComparisonCensus.edgePairs, List.mem_flatMap] at hp
  obtain ⟨node, hnode, hrow⟩ := hp
  rw [EdgeComparisonCensus.rowEdgePairs, List.mem_flatMap] at hrow
  obtain ⟨l, hl, hmem⟩ := hrow
  simp only [List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  refine ⟨node, hnode, i, ?_⟩
  revert hmem
  cases hchild : node.childOpt i with
  | none => intro hmem; simp at hmem
  | some child =>
      intro hmem
      have hmemc : child ∈ node.children := by
        have hgo := hchild
        rw [NTree.childOpt] at hgo
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hgo
        rw [← heq]
        exact List.getElem_mem hlt
      refine ⟨child, hmemc, ?_⟩
      simp only [id_eq, EdgeComparisonCensus.edgeTriple, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- **`Def[Nock Program]`'s leaf window at one committed compute row**.

Deliberately *narrow*: it names the row's own public triple and its three subformula triples, and
says nothing at all about the decomposition slots or about any `cons` cell.  Those are derived by
`Lem:decomp` from `RowCellIdentities`, which is what makes the reduction non-circular. -/
def RowLeafWindow (Λ : ℕ) (s : ComputeRowSkeleton) : Prop :=
  s.subject.leaves ≤ Λ ∧
    s.formula.leaves ≤ Λ ∧
      s.evaluation.leaves ≤ Λ ∧
        ∀ (i : Fin 3) (slot : TripleSlot),
          (P8Census.skeletonSubformula s i slot).leaves ≤ Λ

/-- **The five structural `cons` equations Algorithm `NockCompute` states**, at the committed-skeleton
layer and at the total `P8Census` projections the census list actually reads.

`formula_cons`, `tail_cons` and `branchTail_cons` are §A's three restated on `skeletonDec`; `push_cons` is `OP_8`'s
`child_one_input ← (cons(sf_evaluation₂, input_subject), formula_tail_tail)`; and
`cons_result` is the `cons`-state check `evaluation = cons(sf_evaluation₁, sf_evaluation₂)`.

These are the *only* places where the census compares against a cell, so they are exactly the
places `Lem:decomp`'s `λ = λ_L + λ_R` has to be applied.  The structure states no
atom range and no leaf count. -/
structure RowCellIdentities (s : ComputeRowSkeleton) : Prop where
  formula_cons :
    s.formula = .cell (P8Census.skeletonDec s .f_h) (P8Census.skeletonDec s .f_t)
  tail_cons :
    decActive s.state .f_th = true →
      P8Census.skeletonDec s .f_t =
        .cell (P8Census.skeletonDec s .f_th) (P8Census.skeletonDec s .f_tt)
  branchTail_cons :
    decActive s.state .f_tth = true →
      P8Census.skeletonDec s .f_tt =
        .cell (P8Census.skeletonDec s .f_tth) (P8Census.skeletonDec s .f_ttt)
  push_cons :
    s.state = .s8 →
      P8Census.skeletonSubformula s 0 .subject =
        .cell (P8Census.skeletonSubformula s 1 .result) s.subject
  cons_result :
    s.state = .cons →
      s.evaluation =
        .cell (P8Census.skeletonSubformula s 0 .result)
          (P8Census.skeletonSubformula s 1 .result)

theorem wut_leaves (n : Noun) : (Noun.wut n).leaves = 1 := by
  cases n <;> rfl

theorem tis_leaves (a b : Noun) : (Noun.tis a b).leaves = 1 := by
  unfold Noun.tis
  split <;> rfl

theorem incMod_leaves (q : ℕ) (n : Noun) :
    (OpcodeSemantics.incMod q n).leaves = 1 := by
  cases n <;> rfl

theorem skeletonDec_inactive {s : ComputeRowSkeleton} {slot : DecSlot}
    (h : ¬ (decActive s.state slot = true)) :
    P8Census.skeletonDec s slot = .atom 0 := by
  simp [P8Census.skeletonDec, h]

/-- **`Lem:decomp`'s leaf half on the committed skeleton**: the row's
window bound on `formula` propagates to every one of the six total decomposition projections.  The
inactive projections are the literal `.atom 0` and need only `1 ≤ Λ`. -/
theorem skeletonDec_leaves_le {s : ComputeRowSkeleton} {Λ : ℕ}
    (hΛ : 1 ≤ Λ) (hc : RowCellIdentities s) (hf : s.formula.leaves ≤ Λ)
    (slot : DecSlot) :
    (P8Census.skeletonDec s slot).leaves ≤ Λ := by
  have hsplit :
      (P8Census.skeletonDec s .f_h).leaves + (P8Census.skeletonDec s .f_t).leaves ≤ Λ := by
    rw [hc.formula_cons] at hf
    simpa [Noun.leaves] using hf
  have hh : (P8Census.skeletonDec s .f_h).leaves ≤ Λ := by omega
  have ht : (P8Census.skeletonDec s .f_t).leaves ≤ Λ := by omega
  have htail :
      decActive s.state .f_th = true →
        (P8Census.skeletonDec s .f_th).leaves + (P8Census.skeletonDec s .f_tt).leaves ≤ Λ := by
    intro hth
    have h := ht
    rw [hc.tail_cons hth] at h
    simpa [Noun.leaves] using h
  have hbranch :
      decActive s.state .f_tth = true →
        (P8Census.skeletonDec s .f_tth).leaves + (P8Census.skeletonDec s .f_ttt).leaves ≤ Λ := by
    intro htth
    have hactth : decActive s.state .f_th = true := by
      have h6 := (decActive_cases s.state).2.2.2.2.1.mp htth
      exact (decActive_cases s.state).2.2.1.mpr (by simp [h6])
    have h := htail hactth
    have h2 : (P8Census.skeletonDec s .f_tt).leaves ≤ Λ := by omega
    rw [hc.branchTail_cons htth] at h2
    simpa [Noun.leaves] using h2
  cases slot with
  | f_h => exact hh
  | f_t => exact ht
  | f_th =>
      by_cases hact : decActive s.state .f_th = true
      · have := htail hact; omega
      · rw [skeletonDec_inactive hact]; simpa [Noun.leaves] using hΛ
  | f_tt =>
      by_cases hact : decActive s.state .f_th = true
      · have := htail hact; omega
      · have hne : ¬ (decActive s.state .f_tt = true) :=
          fun hh' => hact ((f_tt_active_iff_f_th s.state).mp hh')
        rw [skeletonDec_inactive hne]; simpa [Noun.leaves] using hΛ
  | f_tth =>
      by_cases hact : decActive s.state .f_tth = true
      · have := hbranch hact; omega
      · rw [skeletonDec_inactive hact]; simpa [Noun.leaves] using hΛ
  | f_ttt =>
      by_cases hact : decActive s.state .f_tth = true
      · have := hbranch hact; omega
      · have hne : ¬ (decActive s.state .f_ttt = true) :=
          fun hh' => hact ((f_ttt_active_iff_f_tth s.state).mp hh')
        rw [skeletonDec_inactive hne]; simpa [Noun.leaves] using hΛ

/-- **The per-row core of the reduction.**  Under the paper's leaf window and the paper's five
`cons` equations, every comparison the census reads at that row lies inside the window.  All twelve
row states, no fixture, no seed. -/
theorem skeletonComparisons_leavesBounded_of_window {s : ComputeRowSkeleton} {Λ : ℕ}
    (hΛ : 1 ≤ Λ) (hc : RowCellIdentities s) (hw : RowLeafWindow Λ s) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K) s, c.LeavesBounded Λ := by
  obtain ⟨hsub, hform, heval, hsf⟩ := hw
  have hd : ∀ slot : DecSlot, (P8Census.skeletonDec s slot).leaves ≤ Λ :=
    skeletonDec_leaves_le hΛ hc hform
  have hatom : ∀ k : ℕ, (Noun.atom k).leaves ≤ Λ := by
    intro k; simpa [Noun.leaves] using hΛ
  have hcellF :
      (Noun.cell (P8Census.skeletonDec s .f_h) (P8Census.skeletonDec s .f_t)).leaves ≤ Λ := by
    rw [← hc.formula_cons]; exact hform
  have hcellT :
      decActive s.state .f_th = true →
        (Noun.cell (P8Census.skeletonDec s .f_th) (P8Census.skeletonDec s .f_tt)).leaves ≤ Λ := by
    intro hth; rw [← hc.tail_cons hth]; exact hd .f_t
  have hcellB :
      decActive s.state .f_tth = true →
        (Noun.cell (P8Census.skeletonDec s .f_tth)
          (P8Census.skeletonDec s .f_ttt)).leaves ≤ Λ := by
    intro htth; rw [← hc.branchTail_cons htth]; exact hd .f_tt
  have huse : ∀ (role : ComparisonRole) (l r : Noun),
      l.leaves ≤ Λ → r.leaves ≤ Λ → (P8Census.skeletonUse role l r).LeavesBounded Λ :=
    fun _ _ _ hl hr => ⟨hl, hr⟩
  have hwut : ∀ n : Noun, (Noun.wut n).leaves ≤ Λ := by
    intro n; rw [wut_leaves]; exact hΛ
  have htis : ∀ a b : Noun, (Noun.tis a b).leaves ≤ Λ := by
    intro a b; rw [tis_leaves]; exact hΛ
  have hinc : ∀ n : Noun, (OpcodeSemantics.incMod (ringChar K) n).leaves ≤ Λ := by
    intro n; rw [incMod_leaves]; exact hΛ
  intro c hc'
  cases hst : s.state
  · simp only [P8Census.skeletonComparisons, hst, List.mem_cons, List.not_mem_nil,
      or_false] at hc'
    rcases hc' with rfl | rfl | rfl
    · exact huse _ _ _ (hd _) (hatom _)
    · exact huse _ _ _ hform hcellF
    · exact huse _ _ _ (hd _) (hatom _)
  · simp only [P8Census.skeletonComparisons, hst, List.mem_cons, List.not_mem_nil,
      or_false] at hc'
    rcases hc' with rfl | rfl | rfl
    · exact huse _ _ _ (hd _) (hatom _)
    · exact huse _ _ _ hform hcellF
    · exact huse _ _ _ heval (hd _)
  · have hth : decActive s.state .f_th = true := by simp [decActive, hasTailDecomposition, hst]
    simp only [P8Census.skeletonComparisons, hst, List.mem_cons, List.not_mem_nil,
      or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact huse _ _ _ (hd _) (hatom _)
    · exact huse _ _ _ hform hcellF
    · exact huse _ _ _ (hd _) (hcellT hth)
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ (hsf _ _) (hsf _ _)
    · exact huse _ _ _ (hsf _ _) (hsf _ _)
    · exact huse _ _ _ heval (hsf _ _)
  · simp only [P8Census.skeletonComparisons, hst, List.mem_cons, List.not_mem_nil,
      or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl
    · exact huse _ _ _ (hd _) (hatom _)
    · exact huse _ _ _ hform hcellF
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ heval (hwut _)
  · simp only [P8Census.skeletonComparisons, hst, List.mem_cons, List.not_mem_nil,
      or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl
    · exact huse _ _ _ (hd _) (hatom _)
    · exact huse _ _ _ hform hcellF
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ heval (hinc _)
  · have hth : decActive s.state .f_th = true := by simp [decActive, hasTailDecomposition, hst]
    simp only [P8Census.skeletonComparisons, hst, List.mem_cons, List.not_mem_nil,
      or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact huse _ _ _ (hd _) (hatom _)
    · exact huse _ _ _ hform hcellF
    · exact huse _ _ _ (hd _) (hcellT hth)
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ (hsf _ _) (hsf _ _)
    · exact huse _ _ _ heval (htis _ _)
  · have hth : decActive s.state .f_th = true := by simp [decActive, hasTailDecomposition, hst]
    have htth : decActive s.state .f_tth = true := by simp [decActive, hst]
    simp only [P8Census.skeletonComparisons, hst, List.mem_cons, List.not_mem_nil,
      or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact huse _ _ _ (hd _) (hatom _)
    · exact huse _ _ _ hform hcellF
    · exact huse _ _ _ (hd _) (hcellT hth)
    · exact huse _ _ _ (hd _) (hcellB htth)
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ heval (hsf _ _)
  · have hth : decActive s.state .f_th = true := by simp [decActive, hasTailDecomposition, hst]
    simp only [P8Census.skeletonComparisons, hst, List.mem_cons, List.not_mem_nil,
      or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact huse _ _ _ (hd _) (hatom _)
    · exact huse _ _ _ hform hcellF
    · exact huse _ _ _ (hd _) (hcellT hth)
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ (hsf _ _) (hsf _ _)
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ heval (hsf _ _)
  · have hth : decActive s.state .f_th = true := by simp [decActive, hasTailDecomposition, hst]
    have hpush := hc.push_cons hst
    simp only [P8Census.skeletonComparisons, hst, List.mem_cons, List.not_mem_nil,
      or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact huse _ _ _ (hd _) (hatom _)
    · exact huse _ _ _ hform hcellF
    · exact huse _ _ _ (hd _) (hcellT hth)
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ (hsf _ _) (by rw [← hpush]; exact hsf _ _)
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ heval (hsf _ _)
  · have hth : decActive s.state .f_th = true := by simp [decActive, hasTailDecomposition, hst]
    simp only [P8Census.skeletonComparisons, hst, List.mem_cons, List.not_mem_nil,
      or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact huse _ _ _ (hd _) (hatom _)
    · exact huse _ _ _ hform hcellF
    · exact huse _ _ _ (hd _) (hcellT hth)
    · exact huse _ _ _ (hd _) (hatom _)
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ (hsf _ _) (hsf _ _)
    · exact huse _ _ _ heval (hsf _ _)
  · have hcons := hc.cons_result hst
    simp only [P8Census.skeletonComparisons, hst, List.mem_cons, List.not_mem_nil,
      or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact huse _ _ _ hform hcellF
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ (hsf _ _) hsub
    · exact huse _ _ _ (hsf _ _) (hd _)
    · exact huse _ _ _ heval (by rw [← hcons]; exact heval)

/-- Every node of the committed compute tree contributes its label to the census's row list. -/
theorem mem_computeSkeletonRows_of_inTree {S : SemanticSkeleton}
    {node : NTree ComputeRowSkeleton} (h : InTree S.computeTree node) :
    node.label ∈ computeSkeletonRows S := by
  unfold computeSkeletonRows
  exact List.mem_map.mpr
    ⟨node, (mem_bfsForest [S.computeTree] node).2 ⟨S.computeTree, by simp, h⟩, rfl⟩

/-- **THE REDUCTION.**  The paper's `NockProgram^Λ` leaf window at every committed compute row, plus Algorithm `NockCompute`'s five structural `cons`
equations, plus `1 ≤ Λ`, give `census` outright — for every `K`, every skeleton, no seed, no
fixture, no carrier field.

The three obligations `census_of_identified_skeleton_pairs` names are discharged as follows: the
per-row comparisons by `Lem:decomp`'s leaf half through
`skeletonComparisons_leavesBounded_of_window`; the public-claim triple by the window at the root
row; and the parent/child edge pairs by the window at the *child* row (left component, an execution
label on the reconstruction) and at the *parent* row's subformula triple (right component, a chosen
witness on the reconstruction). -/
theorem census_of_leafWindow (S : SemanticSkeleton) (Λ : ℕ) (hΛ : 1 ≤ Λ)
    (hc : ∀ s ∈ computeSkeletonRows S, RowCellIdentities s)
    (hw : ∀ s ∈ computeSkeletonRows S, RowLeafWindow Λ s) :
    EdgeComparisonCensus.CombinedSkeletonCensus K S Λ := by
  have hroot : S.computeTree.label ∈ computeSkeletonRows S :=
    mem_computeSkeletonRows_of_inTree (InTree.here _)
  refine GenericHonestData.census_of_identified_skeleton_pairs (K := K) ?_ ?_ ?_
  · intro s hs c hcm
    exact skeletonComparisons_leavesBounded_of_window hΛ (hc s hs) (hw s hs) c hcm
  · obtain ⟨h1, h2, h3, _⟩ := hw _ hroot
    exact ⟨h1, h2, h3⟩
  · intro pair hp
    obtain ⟨node, hnode, i, child, hmemc, hcase⟩ := edgePairs_left_is_a_child_label hp
    have hIn : InTree S.computeTree node := by
      obtain ⟨t, ht, hin⟩ := (mem_bfsForest [S.computeTree] node).1 hnode
      simp only [List.mem_singleton] at ht
      subst ht
      exact hin
    have hchildIn : InTree S.computeTree child :=
      InTree_trans hIn (.sub hmemc (.here _))
    have hwn := hw _ (mem_computeSkeletonRows_of_inTree hIn)
    have hwc := hw _ (mem_computeSkeletonRows_of_inTree hchildIn)
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact ⟨hwc.1, hwn.2.2.2 _ _⟩
    · exact ⟨hwc.2.1, hwn.2.2.2 _ _⟩
    · exact ⟨hwc.2.2.1, hwn.2.2.2 _ _⟩

/-- **`sizeWindowBound` from the leaf window**, for every `K`, every skeleton, no seed, no fixture. -/
theorem sizeWindowBound_of_leafWindow (S : SemanticSkeleton) (Λ : ℕ)
    (hw : ∀ s ∈ computeSkeletonRows S, RowLeafWindow Λ s) :
    SizeWindowCounting.SizeWindowNounsBoundedBy S Λ := by
  intro n hn
  obtain ⟨s, hs, hns⟩ := List.mem_flatMap.mp hn
  have hws := hw s hs
  cases hst : s.state <;>
    simp only [SizeWindowCounting.requiredSizeWindowNouns, hst, List.mem_cons,
      List.not_mem_nil, or_false] at hns <;>
    first
      | exact absurd hns not_false
      | (subst hns; exact hws.2.2.2 _ _)

end

end Nock.NockVMROM.Thm54.CensusExtraClosure
