/-
  Nock/NockVMROM/Thm54/TraceGen/GenAirOrderChildLink.lean

  `childLinkComp` on every node of a rendered AIR-ordered generated tree.
  `Checker.NTree.All` is label-only, so the tree-wide statement is the
  node-level `ChildLinkAll` / `InTree` form.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderAirLinked
import Nock.NockVMROM.Thm54.TraceGen.GenTierAComputeLink
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonBind

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! ## Tree plumbing -/

theorem mem_airReorder_children {g : GenComputeRow K}
    {cs : List (NTree (GenComputeRow K))} {c : NTree (GenComputeRow K)}
    (hc : c ∈ (airReorder (.node g cs)).children) :
    ∃ c0 ∈ cs, c = airReorder c0 := by
  simp [airReorder] at hc
  split_ifs at hc
  · obtain ⟨c0, hmem, rfl⟩ := List.mem_map.mp (mem_swapPair hc)
    exact ⟨c0, hmem, rfl⟩
  · obtain ⟨c0, hmem, rfl⟩ := List.mem_map.mp hc
    exact ⟨c0, hmem, rfl⟩

theorem inTree_airReorder_label (t : NTree (GenComputeRow K)) :
    ∀ u, InTree (airReorder t) u →
      ∃ u0, InTree t u0 ∧ u.label = u0.label := by
  let P := fun t : NTree (GenComputeRow K) =>
    ∀ u, InTree (airReorder t) u → ∃ u0, InTree t u0 ∧ u.label = u0.label
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro g cs ih u h
    cases h with
    | here =>
      exact ⟨.node g cs, InTree.here _, airReorder_label _⟩
    | sub hs hu =>
      obtain ⟨c0, hc0, rfl⟩ := mem_airReorder_children hs
      obtain ⟨u0, hu0, hl⟩ := ih c0 hc0 u hu
      exact ⟨u0, InTree.sub hc0 hu0, hl⟩
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

theorem airReorder_inTree_fanout
    {t : NTree (GenComputeRow K)}
    (hfan : ∀ u, InTree t u →
      u.children.length = fanoutComp u.label.skel.state)
    (u : NTree (GenComputeRow K)) (hu : InTree (airReorder t) u) :
    u.children.length = fanoutComp u.label.skel.state := by
  let P := fun t : NTree (GenComputeRow K) =>
    (∀ u, InTree t u → u.children.length = fanoutComp u.label.skel.state) →
      ∀ u, InTree (airReorder t) u →
        u.children.length = fanoutComp u.label.skel.state
  have hP : P t := by
    apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
    · intro g cs ih hfan' u hu
      cases hu with
      | here =>
        have hroot := hfan' _ (InTree.here _)
        simpa [airReorder_children_length, airReorder_label] using hroot
      | sub hs hu' =>
        obtain ⟨c0, hc0, rfl⟩ := mem_airReorder_children hs
        exact ih c0 hc0 (fun v hv => hfan' v (InTree.sub hc0 hv)) u hu'
    · intro c hc; simp at hc
    · intro head tail ihHead ihTail c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ihHead
      · exact ihTail c hc
  exact hP hfan u hu

omit [Field K] in
theorem inTree_mapNTree {α β : Type*} (f : α → β) :
    ∀ t u, InTree (mapNTree f t) u →
      ∃ u0, InTree t u0 ∧ u = mapNTree f u0 := by
  intro t
  let P := fun t : NTree α =>
    ∀ u, InTree (mapNTree f t) u → ∃ u0, InTree t u0 ∧ u = mapNTree f u0
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro g cs ih u h
    cases h with
    | here =>
      exact ⟨.node g cs, InTree.here _, rfl⟩
    | sub hs hu =>
      simp [mapNTree, NTree.children] at hs
      obtain ⟨c0, hc0, rfl⟩ := hs
      obtain ⟨u0, hu0, rfl⟩ := ih c0 hc0 u hu
      exact ⟨u0, InTree.sub hc0 hu0, rfl⟩
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

theorem AirLinked_children_of {t : NTree (GenComputeRow K)}
    (h : AirLinked t) : ∀ c ∈ t.children, AirLinked c := by
  cases t with
  | node g cs =>
    have h' : childrenMatchSf (.node g cs) ∧ ∀ c ∈ cs, AirLinked c := by
      simpa [AirLinked] using h
    simpa [NTree.children] using h'.2

theorem AirLinked_of_inTree {t u : NTree (GenComputeRow K)}
    (h : AirLinked t) (hu : InTree t u) : AirLinked u := by
  induction hu with
  | here => exact h
  | sub hs _ ih =>
    exact ih (AirLinked_children_of h _ hs)

/-! ## `sfTriple` from `BindComputeRow` -/

theorem sfTriple_eq_encC_of_bind {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K} (hbind : BindComputeRow z s row)
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state) :
    sfTriple row.2.2.1 i =
      (encC z (s.subformula i hi TripleSlot.subject),
        encC z (s.subformula i hi TripleSlot.formula),
        encC z (s.subformula i hi TripleSlot.result)) := by
  unfold BindComputeRow at hbind
  have hsf := hbind.2.2.2.2.2.2.2.1 i
  rw [dif_pos hi] at hsf
  have hs := hsf TripleSlot.subject
  have hf := hsf TripleSlot.formula
  have he := hsf TripleSlot.result
  simp [bindFP, tripleFP, computeSubformulaFPs] at hs hf he
  apply Prod.ext
  · rw [hs, ← encC_eq]
  · apply Prod.ext
    · rw [hf, ← encC_eq]
    · rw [he, ← encC_eq]

theorem sfTriple_eq_skeleton_of_bind {z : K} {s : ComputeRowSkeleton}
    {row : State × DTcomp K} (hbind : BindComputeRow z s row)
    (i : Fin 3) (hi : (i : ℕ) < fanoutComp s.state) :
    sfTriple row.2.2.1 i =
      (encC z (P8Census.skeletonSubformula s i TripleSlot.subject),
        encC z (P8Census.skeletonSubformula s i TripleSlot.formula),
        encC z (P8Census.skeletonSubformula s i TripleSlot.result)) := by
  have htrip := sfTriple_eq_encC_of_bind hbind i hi
  simp [P8Census.skeletonSubformula, hi] at htrip ⊢
  exact htrip

/-! ## One-node `childLinkComp` -/

theorem childLinkComp_of_match (z α : K) (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K)))
    (hfan : cs.length = fanoutComp g.skel.state)
    (hmatch : childrenMatchSf (.node g cs))
    (hbind : BindComputeRow z g.skel (renderNode z α g).row) :
    childLinkComp
      (mapNTree (GenComputeRow.row ∘ renderNode z α) (.node g cs)).label
      (fun j =>
        (mapNTree (GenComputeRow.row ∘ renderNode z α) (.node g cs)).childLabel j) := by
  intro i hi
  have hfanI : (i : ℕ) < fanoutComp g.skel.state := by
    have := hi
    simp [mapNTree_label, Function.comp, renderNode_state] at this
    exact this
  have hi' : (i : ℕ) < cs.length := by
    simpa [hfan] using hfanI
  have hget : cs[(i : ℕ)]? = some (cs[(i : ℕ)]'hi') :=
    List.getElem?_eq_getElem hi'
  have hsfe := renderNode_sfe z α (cs[(i : ℕ)]'hi').label
  have hsfP := hmatch i hi'
  have htrip := sfTriple_eq_skeleton_of_bind hbind i hfanI
  dsimp
  rw [mapNTree_childLabel]
  simp [NTree.childLabel, NTree.childOpt, NTree.children_node, hget, mapNTree_label,
    Function.comp]
  rw [htrip]
  apply Prod.ext
  · exact hsfe.1.trans (congrArg (encC z) hsfP.1)
  · apply Prod.ext
    · exact hsfe.2.1.trans (congrArg (encC z) hsfP.2.1)
    · exact hsfe.2.2.trans (congrArg (encC z) hsfP.2.2)

theorem childLinkComp_of_airLinked_node (z α : K)
    (t : NTree (GenComputeRow K))
    (hL : AirLinked t)
    (hfan : t.children.length = fanoutComp t.label.skel.state)
    (hbind : BindComputeRow z t.label.skel (renderNode z α t.label).row) :
    childLinkComp
      (mapNTree (GenComputeRow.row ∘ renderNode z α) t).label
      (fun j => (mapNTree (GenComputeRow.row ∘ renderNode z α) t).childLabel j) := by
  cases t with
  | node g cs =>
    exact childLinkComp_of_match z α g cs hfan
      (childrenMatchSf_of_AirLinked hL) hbind

/-! ## Tree-wide child link -/

/-- Rendered `childLinkComp` at one generated node. -/
def ChildLinkHolds (z α : K) (t : NTree (GenComputeRow K)) : Prop :=
  childLinkComp
    (mapNTree (GenComputeRow.row ∘ renderNode z α) t).label
    (fun j => (mapNTree (GenComputeRow.row ∘ renderNode z α) t).childLabel j)

/-- Every node of an AIR-ordered tree satisfies `childLinkComp` after render. -/
def ChildLinkAll (z α : K) : NTree (GenComputeRow K) → Prop
  | .node g cs =>
    ChildLinkHolds z α (.node g cs) ∧ ∀ c ∈ cs, ChildLinkAll z α c

theorem ChildLinkAll_here {z α : K} {t : NTree (GenComputeRow K)}
    (h : ChildLinkAll z α t) : ChildLinkHolds z α t := by
  cases t with
  | node g cs =>
    have h' : ChildLinkHolds z α (.node g cs) ∧ ∀ c ∈ cs, ChildLinkAll z α c := by
      simpa [ChildLinkAll] using h
    exact h'.1

theorem ChildLinkAll_children_of {z α : K} {t : NTree (GenComputeRow K)}
    (h : ChildLinkAll z α t) : ∀ c ∈ t.children, ChildLinkAll z α c := by
  cases t with
  | node g cs =>
    have h' : ChildLinkHolds z α (.node g cs) ∧ ∀ c ∈ cs, ChildLinkAll z α c := by
      simpa [ChildLinkAll] using h
    simpa [NTree.children] using h'.2

theorem ChildLinkAll_of_inTree {z α : K} {t u : NTree (GenComputeRow K)}
    (h : ChildLinkAll z α t) (hu : InTree t u) : ChildLinkHolds z α u := by
  induction hu with
  | here => exact ChildLinkAll_here h
  | sub hs _ ih =>
    exact ih (ChildLinkAll_children_of h _ hs)

theorem childLinkAll_of_airLinked (z α : K)
    {t : NTree (GenComputeRow K)}
    (hL : AirLinked t)
    (hfan : ∀ u, InTree t u →
      u.children.length = fanoutComp u.label.skel.state)
    (hbind : ∀ u, InTree t u →
      BindComputeRow z u.label.skel (renderNode z α u.label).row) :
    ChildLinkAll z α t := by
  let P := fun t : NTree (GenComputeRow K) =>
    AirLinked t →
      (∀ u, InTree t u → u.children.length = fanoutComp u.label.skel.state) →
        (∀ u, InTree t u →
          BindComputeRow z u.label.skel (renderNode z α u.label).row) →
          ChildLinkAll z α t
  have hP : P t := by
    apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
    · intro g cs ih hL' hfan' hbind'
      simp only [ChildLinkAll]
      constructor
      · exact childLinkComp_of_airLinked_node z α _ hL'
          (hfan' _ (InTree.here _)) (hbind' _ (InTree.here _))
      · intro c hc
        exact ih c hc (AirLinked_of_inTree hL' (InTree.sub hc (InTree.here _)))
          (fun u hu => hfan' u (InTree.sub hc hu))
          (fun u hu => hbind' u (InTree.sub hc hu))
    · intro c hc; simp at hc
    · intro head tail ihHead ihTail c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ihHead
      · exact ihTail c hc
  exact hP hL hfan hbind

/-- Generated trees are child-linked after `airReorder` and `renderNode`. -/
theorem childLinkAll_airReorder_of_gen (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok p) :
    ChildLinkAll z α (airReorder p.1) := by
  have h' : genComputeSkeleton (K := K) fuel subject formula = .ok (p.1, p.2) := by
    simpa [Prod.mk.eta] using h
  refine childLinkAll_of_airLinked z α (airLinked_airReorder_of_gen h) ?_ ?_
  · intro u hu
    exact airReorder_inTree_fanout (fun v hv =>
      genComputeSkeleton_inTree_fanout h' v hv) u hu
  · intro u hu
    obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label p.1 u hu
    simpa [hl] using genComputeSkeleton_inTree_bind_own z α h' u0 hu0

theorem childLinkHolds_airReorder_of_gen (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok p)
    (u : NTree (GenComputeRow K)) (hu : InTree (airReorder p.1) u) :
    ChildLinkHolds z α u :=
  ChildLinkAll_of_inTree (childLinkAll_airReorder_of_gen z α h) hu

theorem childLinkComp_render_airReorder_of_gen (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok p)
    (u : NTree (State × DTcomp K))
    (hu : InTree (mapNTree (GenComputeRow.row ∘ renderNode z α) (airReorder p.1)) u) :
    childLinkComp u.label (fun j => u.childLabel j) := by
  obtain ⟨u0, hu0, rfl⟩ := inTree_mapNTree _ _ _ hu
  exact childLinkHolds_airReorder_of_gen z α h u0 hu0

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.childLinkAll_airReorder_of_gen
#print axioms Nock.NockVMROM.Thm54.TraceGen.childLinkComp_render_airReorder_of_gen
