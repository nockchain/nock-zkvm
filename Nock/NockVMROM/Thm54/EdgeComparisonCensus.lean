import Nock.NockVMROM.Thm54.BoundSemanticTrace

/-!
# Fixed pre-seed edge-comparison census

For each structural child slot in the seed-independent semantic compute tree, this module records
the three noun pairs needed to identify the child root with the parent's recursive-call slot.
-/

namespace Nock.NockVMROM.Thm54.EdgeComparisonCensus

open scoped Classical
open Nock Nock.Walk

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

abbrev Row := SemanticStrategy.ComputeRowSkeleton

/-- Three fixed comparisons for one present parent-to-child edge. -/
def edgeTriple (parent child : Row) (i : Fin 3) : List (Noun × Noun) :=
  [ (child.subject, P8Census.skeletonSubformula parent i .subject),
    (child.formula, P8Census.skeletonSubformula parent i .formula),
    (child.evaluation, P8Census.skeletonSubformula parent i .result) ]

/-- At most the three arity slots are inspected; absent slots emit no comparison. -/
def rowEdgePairs (node : NTree Row) : List (Noun × Noun) :=
  (List.ofFn fun i : Fin 3 =>
    match node.childOpt i with
    | none => []
    | some child => edgeTriple node.label child.label i).flatMap id

/-- All fixed edge occurrences in canonical skeleton BFS order. -/
def edgePairs (tree : NTree Row) : List (Noun × Noun) :=
  (bfsForest [tree]).flatMap rowEdgePairs

@[simp]
theorem edgeTriple_length (parent child : Row) (i : Fin 3) :
    (edgeTriple parent child i).length = 3 := rfl

private theorem flatMap_length_le
    {α β : Type*} (bound : ℕ) (xs : List α) (f : α → List β)
    (h : ∀ x ∈ xs, (f x).length ≤ bound) :
    (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, (f y).length ≤ bound :=
        fun y hy => h y (by simp [hy])
      have hi := ih hxs
      calc
        (f x).length + (xs.flatMap f).length ≤ bound + xs.length * bound :=
          Nat.add_le_add hx hi
        _ = (xs.length + 1) * bound := by simp [Nat.add_mul, Nat.add_comm]

theorem rowEdgePairs_length_le (node : NTree Row) :
    (rowEdgePairs node).length ≤ 9 := by
  unfold rowEdgePairs
  have h := flatMap_length_le 3
    (List.ofFn fun i : Fin 3 =>
      match node.childOpt i with
      | none => []
      | some child => edgeTriple node.label child.label i) id (by
        intro xs hxs
        simp only [List.mem_ofFn] at hxs
        obtain ⟨i, rfl⟩ := hxs
        split <;> simp [edgeTriple])
  simpa using h

/-- At most nine edge comparisons per compute node. -/
theorem edgePairs_length_le (tree : NTree Row) :
    (edgePairs tree).length ≤ 9 * (bfsForest [tree]).length := by
  unfold edgePairs
  have h := flatMap_length_le 9 (bfsForest [tree]) rowEdgePairs
    (fun node _ => rowEdgePairs_length_le node)
  simpa [Nat.mul_comm] using h

theorem pair_mem_edgeTriple
    (parent child : Row) (i : Fin 3) (slot : SemanticStrategy.TripleSlot) :
    (match slot with
      | .subject => (child.subject, P8Census.skeletonSubformula parent i .subject)
      | .formula => (child.formula, P8Census.skeletonSubformula parent i .formula)
      | .result => (child.evaluation, P8Census.skeletonSubformula parent i .result)) ∈
      edgeTriple parent child i := by
  cases slot <;> simp [edgeTriple]

/-- Exact lookup for every one of the three occurrences on an actual skeleton edge. -/
theorem edge_pair_mem
    {tree node child : NTree Row}
    (hnode : InTree tree node) (i : Fin 3)
    (hchild : node.childOpt i = some child)
    (slot : SemanticStrategy.TripleSlot) :
    (match slot with
      | .subject =>
          (child.label.subject,
            P8Census.skeletonSubformula node.label i .subject)
      | .formula =>
          (child.label.formula,
            P8Census.skeletonSubformula node.label i .formula)
      | .result =>
          (child.label.evaluation,
            P8Census.skeletonSubformula node.label i .result)) ∈
      edgePairs tree := by
  rw [edgePairs, List.mem_flatMap]
  refine ⟨node, ?_, ?_⟩
  · exact (mem_bfsForest [tree] node).2 ⟨tree, by simp, hnode⟩
  · rw [rowEdgePairs, List.mem_flatMap]
    refine ⟨edgeTriple node.label child.label i, ?_,
      pair_mem_edgeTriple _ _ i slot⟩
    simp only [List.mem_ofFn]
    exact ⟨i, by simp [hchild]⟩

/-- Leaf bounds for the entirely pre-seed edge list. -/
structure BoundEdgeCensus (tree : NTree Row) (Λ : ℕ) : Prop where
  leaves_bounded :
    ∀ pair ∈ edgePairs tree,
      pair.1.leaves ≤ Λ ∧ pair.2.leaves ≤ Λ

namespace BoundEdgeCensus

def census {tree : NTree Row} {Λ : ℕ}
    (C : BoundEdgeCensus tree Λ) : ComparisonCensus Λ :=
  ComparisonCensus.ofPairList (edgePairs tree) C.leaves_bounded

@[simp]
theorem census_count {tree : NTree Row} {Λ : ℕ}
    (C : BoundEdgeCensus tree Λ) :
    C.census.count = (edgePairs tree).length := rfl

theorem count_le {tree : NTree Row} {Λ : ℕ}
    (C : BoundEdgeCensus tree Λ) :
    C.census.count ≤ 9 * (bfsForest [tree]).length := by
  rw [census_count]
  exact edgePairs_length_le tree

theorem pair_lookup {tree : NTree Row} {Λ : ℕ}
    (C : BoundEdgeCensus tree Λ)
    {pair : Noun × Noun} (hpair : pair ∈ edgePairs tree) :
    ∃ i : Fin C.census.count, C.census.pair i = pair :=
  ComparisonCensus.exists_pair_of_mem _ _ hpair

section Finite
variable [Fintype K] [DecidableEq K]

theorem badSeeds_card_le {tree : NTree Row} {Λ : ℕ}
    (C : BoundEdgeCensus tree Λ) :
    (C.census.badSeeds (K := K)).card ≤
      (9 * (bfsForest [tree]).length) * (2 * Λ - 1) :=
  C.census.badSeeds_card_le.trans
    (Nat.mul_le_mul_right (2 * Λ - 1) C.count_le)

end Finite
end BoundEdgeCensus

/-- One genuinely pre-seed occurrence list, determined by a bare semantic skeleton alone. -/
def combinedSkeletonPairs (K : Type) [Field K]
    (S : SemanticStrategy.SemanticSkeleton) :
    List (Noun × Noun) :=
  BoundSemanticTrace.skeletonPairs K S ++ edgePairs S.computeTree

/-- Leaf bounds for the combined local/edge census of a bare semantic skeleton. -/
structure CombinedSkeletonCensus
    (K : Type) [Field K] (S : SemanticStrategy.SemanticSkeleton) (Λ : ℕ) : Prop where
  p8 : BoundSemanticTrace.SkeletonP8Census K S Λ
  edges : BoundEdgeCensus S.computeTree Λ

namespace CombinedSkeletonCensus

def census {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : CombinedSkeletonCensus K S Λ) : ComparisonCensus Λ :=
  ComparisonCensus.ofPairList (combinedSkeletonPairs K S) (by
    intro pair hp
    rw [combinedSkeletonPairs, List.mem_append] at hp
    exact hp.elim (C.p8.leaves_bounded pair) (C.edges.leaves_bounded pair))

@[simp] theorem census_count
    {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : CombinedSkeletonCensus K S Λ) :
    C.census.count =
      (BoundSemanticTrace.skeletonPairs K S).length +
        (edgePairs S.computeTree).length := by
  simp [census, combinedSkeletonPairs]

theorem count_le
    {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : CombinedSkeletonCensus K S Λ) :
    C.census.count ≤
      3 + 19 * (SemanticStrategy.computeSkeletonRows S).length := by
  rw [census_count]
  have hp :
      (BoundSemanticTrace.skeletonPairs K S).length ≤
        3 + 10 * (SemanticStrategy.computeSkeletonRows S).length := by
    simpa only [BoundSemanticTrace.SkeletonP8Census.census_count] using C.p8.count_le
  have he := edgePairs_length_le S.computeTree
  have hrows :
      (SemanticStrategy.computeSkeletonRows S).length =
        (bfsForest [S.computeTree]).length := by
    simp [SemanticStrategy.computeSkeletonRows]
  rw [hrows] at hp ⊢
  omega

theorem p8_pair_lookup
    {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : CombinedSkeletonCensus K S Λ)
    {pair : Noun × Noun} (hp : pair ∈ BoundSemanticTrace.skeletonPairs K S) :
    ∃ i : Fin C.census.count, C.census.pair i = pair :=
  ComparisonCensus.exists_pair_of_mem _ _ (by
    rw [combinedSkeletonPairs, List.mem_append]
    exact Or.inl hp)

theorem edge_pair_lookup
    {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : CombinedSkeletonCensus K S Λ)
    {pair : Noun × Noun} (hp : pair ∈ edgePairs S.computeTree) :
    ∃ i : Fin C.census.count, C.census.pair i = pair :=
  ComparisonCensus.exists_pair_of_mem _ _ (by
    rw [combinedSkeletonPairs, List.mem_append]
    exact Or.inr hp)

section Finite
variable [Fintype K] [DecidableEq K]

theorem badSeeds_card_le
    {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : CombinedSkeletonCensus K S Λ) :
    (C.census.badSeeds (K := K)).card ≤
      (3 + 19 * (SemanticStrategy.computeSkeletonRows S).length) *
        (2 * Λ - 1) :=
  C.census.badSeeds_card_le.trans
    (Nat.mul_le_mul_right (2 * Λ - 1) C.count_le)

end Finite
end CombinedSkeletonCensus

def combinedPairs (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)) :
    List (Noun × Noun) :=
  P8Census.boundPairs T ++ edgePairs T.skeleton.computeTree

structure CombinedBoundCensus
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)) (Λ : ℕ) : Prop where
  p8 : P8Census.BoundP8Census T Λ
  edges : BoundEdgeCensus T.skeleton.computeTree Λ

namespace CombinedBoundCensus

def census {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : CombinedBoundCensus T Λ) : ComparisonCensus Λ :=
  ComparisonCensus.ofPairList (combinedPairs T) (by
    intro pair hp
    rw [combinedPairs, List.mem_append] at hp
    exact hp.elim (C.p8.leaves_bounded pair) (C.edges.leaves_bounded pair))

@[simp]
theorem census_count
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : CombinedBoundCensus T Λ) :
    C.census.count =
      (P8Census.boundPairs T).length + (edgePairs T.skeleton.computeTree).length := by
  simp [census, combinedPairs]

/-- Updated total pre-seed workload: at most `3 + 19·rows`. -/
theorem count_le
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : CombinedBoundCensus T Λ) :
    C.census.count ≤
      3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length := by
  rw [census_count]
  have hp :
      (P8Census.boundPairs T).length ≤
        3 + 10 * (SemanticStrategy.computeSkeletonRows T.skeleton).length := by
    simpa only [P8Census.BoundP8Census.census_count] using C.p8.count_le
  have he := edgePairs_length_le T.skeleton.computeTree
  have hrows :
      (SemanticStrategy.computeSkeletonRows T.skeleton).length =
        (bfsForest [T.skeleton.computeTree]).length := by
    simp [SemanticStrategy.computeSkeletonRows]
  rw [hrows] at hp ⊢
  omega

theorem p8_pair_lookup
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : CombinedBoundCensus T Λ)
    {pair : Noun × Noun} (hp : pair ∈ P8Census.boundPairs T) :
    ∃ i : Fin C.census.count, C.census.pair i = pair :=
  ComparisonCensus.exists_pair_of_mem _ _ (by
    rw [combinedPairs, List.mem_append]
    exact Or.inl hp)

theorem edge_pair_lookup
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : CombinedBoundCensus T Λ)
    {pair : Noun × Noun} (hp : pair ∈ edgePairs T.skeleton.computeTree) :
    ∃ i : Fin C.census.count, C.census.pair i = pair :=
  ComparisonCensus.exists_pair_of_mem _ _ (by
    rw [combinedPairs, List.mem_append]
    exact Or.inr hp)

section Finite
variable [Fintype K] [DecidableEq K]

theorem badSeeds_card_le
    {T : SemanticStrategy.BoundP8Strategy (F := F) (K := K)} {Λ : ℕ}
    (C : CombinedBoundCensus T Λ) :
    (C.census.badSeeds (K := K)).card ≤
      (3 + 19 * (SemanticStrategy.computeSkeletonRows T.skeleton).length) *
        (2 * Λ - 1) :=
  C.census.badSeeds_card_le.trans
    (Nat.mul_le_mul_right (2 * Λ - 1) C.count_le)

end Finite
end CombinedBoundCensus

/-- Literal noun agreement at every ordered skeleton call edge. -/
def ChildSkeletonCoherence (tree : NTree Row) : Prop :=
  ∀ node, InTree tree node →
    ∀ (i : Fin 3) (hi : (i : ℕ) < ComputeTable.fanoutComp node.label.state)
      child, node.childOpt i = some child →
      child.label.subject = node.label.subformula i hi .subject ∧
      child.label.formula = node.label.subformula i hi .formula ∧
      child.label.evaluation = node.label.subformula i hi .result

private theorem forall₂_exists_right_of_mem_left
    {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp at hx
  | cons hab htail ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨_, by simp, hab⟩
      · obtain ⟨y, hy, hxy⟩ := ih hx
        exact ⟨y, by simp [hy], hxy⟩

private theorem paired_subtree
    {z : K} {sroot : NTree Row}
    {troot : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (hbind : SemanticStrategy.ComputeTreeBinds z sroot troot)
    {snode : NTree Row} (hsnode : InTree sroot snode) :
    ∃ tnode, InTree troot tnode ∧
      SemanticStrategy.ComputeTreeBinds z snode tnode := by
  induction hsnode generalizing troot with
  | here => exact ⟨troot, .here _, hbind⟩
  | @sub _ schild snode hs hsub ih =>
      obtain ⟨tchild, htchild, hchildBind⟩ :=
        forall₂_exists_right_of_mem_left hbind.children hs
      obtain ⟨tnode, htnode, hnodeBind⟩ := ih hchildBind
      exact ⟨tnode, .sub htchild htnode, hnodeBind⟩

private theorem bounded_of_inTree
    {q : ℕ} {S : SemanticStrategy.SemanticSkeleton}
    (hb : S.BoundedBy q) {node : NTree Row}
    (hnode : InTree S.computeTree node) :
    node.label.BoundedBy q := by
  apply (List.forall_iff_forall_mem.mp hb.computeRows) node.label
  unfold SemanticStrategy.computeSkeletonRows
  rw [List.mem_map]
  exact ⟨node,
    (mem_bfsForest [S.computeTree] node).2 ⟨S.computeTree, by simp, hnode⟩, rfl⟩

private theorem separated_combined_skeleton_edge
    [Fintype K] [DecidableEq K]
    {S : SemanticStrategy.SemanticSkeleton} {Λ : ℕ}
    (C : CombinedSkeletonCensus K S Λ) (z : K)
    (hgood : z ∉ C.census.badSeeds (K := K))
    {pair : Noun × Noun} (hp : pair ∈ edgePairs S.computeTree) :
    GlobalCarryRecognizer.SepSeed z pair.1 pair.2 := by
  obtain ⟨j, hj⟩ := C.edge_pair_lookup hp
  have hsep := P8Census.sepSeed_of_not_mem_badSeeds C.census z hgood j
  simpa [hj] using hsep

/-- The fixed edge collision class closes all child/root noun equalities.

No noun in this theorem depends on `z`: `combinedPairs T` is computed entirely from `T.skeleton`.
The sampled execution is used only to show that both pre-seed nouns bind to the same actual
`Fcomp` fingerprint. -/
theorem childSkeletonCoherence_of_skeletonCensus
    [Fintype K] [DecidableEq K]
    (S : SemanticStrategy.SemanticSkeleton)
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) (z : K)
    (binds : SemanticStrategy.BindsAt z S cfg exec)
    (C : CombinedSkeletonCensus K S Λ)
    {q : ℕ} (hb : S.BoundedBy q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htopology : RVTWithArity (ComputeTable.Fcomp (K := K))
      exec.computeTree)
    (hgood : z ∉ C.census.badSeeds (K := K)) :
    ChildSkeletonCoherence S.computeTree := by
  intro snode hsnode i hi schild hschild
  let troot := exec.computeTree
  have hglobalBind := binds.computeTree
  obtain ⟨tnode, htnode, hnodeBind⟩ :=
    paired_subtree hglobalBind hsnode
  cases hnodeBind with
  | @node srow sc tlabel tc shape hparentBind hchildren =>
      have hil : (i : ℕ) < sc.length := by simpa [shape] using hi
      obtain ⟨his, hsget⟩ :=
        (List.getElem?_eq_some_iff.mp hschild)
      have hsEq : schild = sc[i] := hsget.symm
      subst schild
      have hit : (i : ℕ) < tc.length := by
        simpa [hchildren.length_eq] using hil
      let tchild := tc[i]
      have hchildBind :
          SemanticStrategy.ComputeTreeBinds z sc[i] tchild :=
        hchildren.get hil hit
      have htchildMem : tchild ∈ tc := List.get_mem tc ⟨i, hit⟩
      have htchildIn : InTree troot tchild :=
        InTree_trans htnode (.sub htchildMem (.here _))
      have hF :=
        ((RVT_iff_forall_InTree (ComputeTable.Fcomp (K := K)) troot).mp
          htopology.rvt (.node tlabel tc) htnode).1
      have hlink := hF.2.2.2 i (by
        have hstate := hparentBind.1
        simpa [hstate] using hi)
      have htopt : (NTree.childLabel (.node tlabel tc) i) = some tchild.label := by
        simp [NTree.childLabel, NTree.childOpt, List.getElem?_eq_getElem hit, tchild]
      change Option.map
        (fun c => (c.2.2.1.s, c.2.2.1.f, c.2.2.1.e))
        ((NTree.node tlabel tc).childLabel i) =
          some (ComputeTable.sfTriple tlabel.2.2.1 i) at hlink
      rw [htopt] at hlink
      simp only [Option.map_some, Option.some.injEq] at hlink
      rcases hparentBind with
        ⟨hstate, _hseed, _hpubstate, _hps, _hpf, _hpe, _hpdec, hpsf, _hpmem⟩
      rcases hchildBind.root with
        ⟨_hcstate, _hcseed, _hcpubstate, hcs, hcf, hce, _hcdec, _hcsf, _hcmem⟩
      have hpSlots := hpsf i
      have hi' : (i : ℕ) < ComputeTable.fanoutComp srow.state := hi
      simp only [hi', dite_true] at hpSlots
      have hbParent := bounded_of_inTree hb hsnode
      have hbChild := bounded_of_inTree hb
        (InTree_trans hsnode (.sub (List.get_mem sc ⟨i, hil⟩) (.here _)))
      have hmemSubject := edge_pair_mem hsnode i hschild
        SemanticStrategy.TripleSlot.subject
      have hmemFormula := edge_pair_mem hsnode i hschild
        SemanticStrategy.TripleSlot.formula
      have hmemResult := edge_pair_mem hsnode i hschild
        SemanticStrategy.TripleSlot.result
      have hsepSubject := separated_combined_skeleton_edge C z hgood hmemSubject
      have hsepFormula := separated_combined_skeleton_edge C z hgood hmemFormula
      have hsepResult := separated_combined_skeleton_edge C z hgood hmemResult
      have hsf :
          P8Census.skeletonSubformula srow i .subject =
            srow.subformula i hi' .subject := by
        simp [P8Census.skeletonSubformula, hi']
      have hff :
          P8Census.skeletonSubformula srow i .formula =
            srow.subformula i hi' .formula := by
        simp [P8Census.skeletonSubformula, hi']
      have hef :
          P8Census.skeletonSubformula srow i .result =
            srow.subformula i hi' .result := by
        simp [P8Census.skeletonSubformula, hi']
      change GlobalCarryRecognizer.SepSeed z sc[i].label.subject
        (P8Census.skeletonSubformula srow i .subject) at hsepSubject
      change GlobalCarryRecognizer.SepSeed z sc[i].label.formula
        (P8Census.skeletonSubformula srow i .formula) at hsepFormula
      change GlobalCarryRecognizer.SepSeed z sc[i].label.evaluation
        (P8Census.skeletonSubformula srow i .result) at hsepResult
      rw [hsf] at hsepSubject
      rw [hff] at hsepFormula
      rw [hef] at hsepResult
      change sc[i].label.subject = srow.subformula i hi' .subject ∧
        sc[i].label.formula = srow.subformula i hi' .formula ∧
        sc[i].label.evaluation = srow.subformula i hi' .result
      have hfpSubject :
          tchild.label.2.2.1.s =
            SemanticStrategy.tripleFP
              (computeSubformulaFPs tlabel.2.2.1 i) .subject := by
        simpa [computeSubformulaFPs, SemanticStrategy.tripleFP] using
          congrArg Prod.fst hlink
      have hfpFormula :
          tchild.label.2.2.1.f =
            SemanticStrategy.tripleFP
              (computeSubformulaFPs tlabel.2.2.1 i) .formula := by
        simpa [computeSubformulaFPs, SemanticStrategy.tripleFP] using
          congrArg (fun x => x.2.1) hlink
      have hfpResult :
          tchild.label.2.2.1.e =
            SemanticStrategy.tripleFP
              (computeSubformulaFPs tlabel.2.2.1 i) .result := by
        simpa [computeSubformulaFPs, SemanticStrategy.tripleFP] using
          congrArg (fun x => x.2.2) hlink
      constructor
      · apply GlobalCarryRecognizer.noun_eq_of_enc_eq z _ _
          hsepSubject hcast hbChild.1 (hbParent.2.2.2.2.1 i hi .subject)
        exact hcs.symm.trans (hfpSubject.trans (hpSlots .subject))
      · constructor
        · apply GlobalCarryRecognizer.noun_eq_of_enc_eq z _ _
            hsepFormula hcast hbChild.2.1
              (hbParent.2.2.2.2.1 i hi .formula)
          exact hcf.symm.trans (hfpFormula.trans (hpSlots .formula))
        · apply GlobalCarryRecognizer.noun_eq_of_enc_eq z _ _
            hsepResult hcast hbChild.2.2.1
              (hbParent.2.2.2.2.1 i hi .result)
          exact hce.symm.trans (hfpResult.trans (hpSlots .result))

theorem childSkeletonCoherence_of_combinedCensus
    [Fintype K] [DecidableEq K]
    (T : SemanticStrategy.BoundP8Strategy (F := F) (K := K))
    (C : CombinedBoundCensus T Λ) (z : K) (hz : z ≠ 0)
    {q : ℕ} (hb : T.skeleton.BoundedBy q)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htopology : RVTWithArity (ComputeTable.Fcomp (K := K))
      (P8Census.boundSampledExec T z hz).computeTree)
    (hgood : z ∉ C.census.badSeeds (K := K)) :
    ChildSkeletonCoherence T.skeleton.computeTree := by
  let C' : CombinedSkeletonCensus K T.skeleton Λ :=
    { p8 :=
        { leaves_bounded := by
            intro pair hp
            exact C.p8.leaves_bounded pair (by
              simpa [BoundSemanticTrace.skeletonPairs, P8Census.boundPairs] using hp) }
      edges := C.edges }
  have hcensus : C'.census = C.census := by
    rfl
  apply childSkeletonCoherence_of_skeletonCensus T.skeleton
    (P8Census.boundSampledExec T z hz) z (T.afterSeed z hz).binds C'
    hb hcast htopology
  simpa [hcensus] using hgood

end
end Nock.NockVMROM.Thm54.EdgeComparisonCensus

#print axioms Nock.NockVMROM.Thm54.EdgeComparisonCensus.edge_pair_mem
#print axioms Nock.NockVMROM.Thm54.EdgeComparisonCensus.BoundEdgeCensus.badSeeds_card_le
#print axioms Nock.NockVMROM.Thm54.EdgeComparisonCensus.CombinedSkeletonCensus.count_le
#print axioms Nock.NockVMROM.Thm54.EdgeComparisonCensus.CombinedSkeletonCensus.badSeeds_card_le
#print axioms Nock.NockVMROM.Thm54.EdgeComparisonCensus.childSkeletonCoherence_of_skeletonCensus
#print axioms Nock.NockVMROM.Thm54.EdgeComparisonCensus.CombinedBoundCensus.count_le
#print axioms Nock.NockVMROM.Thm54.EdgeComparisonCensus.CombinedBoundCensus.badSeeds_card_le
#print axioms Nock.NockVMROM.Thm54.EdgeComparisonCensus.childSkeletonCoherence_of_combinedCensus
