/-
  Nock/NockVMROM/Thm54/TraceGen/GenRequestAxisBound.lean

  **Every memory-record request axis of an accepted guarded ROM run is `< q`.**

  `genComputeSkeleton` (`Gen.lean::genComputeSkeleton`) issues requests at exactly three kinds of
  axes: the formula-open record `@3`, the formula-tail record `@2`, and the two served lookups —
  the `OP_0` slot read `*[a 0 b] = /[b a]` at axis `b` and the `OP_9` arm fetch at the formula-tail-head axis atom.  In both served cases the axis is an atom of
  the formula being executed.  So it is `< q` as soon as every formula the generator meets is
  `BoundedBy q`, and that holds along a successful guarded run `evalGRom q` from `BoundedBy q`
  subject/formula: formulas built from intermediate results (`OP_2`'s `*[sf1 sf2]`, `OP_9`'s arm)
  are results (or slots of results) of guarded sub-runs, which are `BoundedBy q` by
  `evalGRom_boundedBy` — the no-wraparound condition the paper.

  The skeleton's intermediate results are identified with the guarded run's through the reference
  interpreter (`genComputeSkeleton_evalN`, `evalGRom_evalN`).

  * `genComputeSkeleton_request_axes_lt` — fuel induction over every arm (template:
    `GenMatmulMem.lean::genComputeSkeleton_tree_requests_wf`);
  * `treeRequestAxesLt_airReorder`, `bfsAssign_extract_requests_axis_lt` — transport through the
    AIR reorder and the BFS stamp assignment (templates `treeRequestsWF_airReorder`,
    `bfsAssign_extract_requests_slot`);
  * `romTree_assigned_request_axes_lt`, `skeleton_assigned_request_axes_lt` — packaged consumer
    forms.

  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGuardedRom
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMem

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open MemoryTable

variable {K : Type} [Field K]

/-- Every request emitted anywhere in `t` has axis `< q`. -/
def treeRequestAxesLt (q : ℕ) (t : NTree (GenComputeRow K)) : Prop :=
  ∀ n, InTree t n → ∀ req ∈ n.label.requests, req.axis < q

theorem treeRequestAxesLt_node {q : ℕ} (g : GenComputeRow K)
    (cs : List (NTree (GenComputeRow K)))
    (hg : ∀ req ∈ g.requests, req.axis < q)
    (hcs : ∀ c ∈ cs, treeRequestAxesLt q c) :
    treeRequestAxesLt q (.node g cs) := by
  intro n hn
  cases hn with
  | here => exact hg
  | sub hs hst => exact hcs _ hs n hst

/-- The skeleton's result and a successful guarded ROM run's result coincide (both are the
reference interpreter's). -/
theorem skel_result_eq_evalGRom {q fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {r r' : Noun}
    (hg : genComputeSkeleton (K := K) fuel subject formula = .ok (t, r))
    (hr : evalGRom q fuel subject formula = some r') : r = r' :=
  Option.some.inj ((genComputeSkeleton_evalN hg).symm.trans (evalGRom_evalN hr))

set_option maxHeartbeats 1600000 in
/-- **Core induction.**  On a successful guarded ROM run over `BoundedBy q` subject and formula,
every request axis in the accepted compute tree is `< q`.  Axes `3`/`2` are below `q` by `hq`;
the `OP_0` / `OP_9` axes are atoms of a `BoundedBy q` formula. -/
theorem genComputeSkeleton_request_axes_lt {q : ℕ} (hq : 3 < q) :
    ∀ {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {r r' : Noun},
      genComputeSkeleton (K := K) fuel subject formula = .ok (t, r) →
      evalGRom q fuel subject formula = some r' →
      FieldEmbedding.BoundedBy q subject → FieldEmbedding.BoundedBy q formula →
      treeRequestAxesLt q t := by
  have h3 : (3 : ℕ) < q := hq
  have h2 : (2 : ℕ) < q := by omega
  intro fuel
  induction fuel with
  | zero =>
    intro subject formula t r r' h _ _ _
    simp [genComputeSkeleton] at h
  | succ n ih =>
    intro subject formula t r r' h hgrom hs hf
    cases formula with
    | atom _ =>
      simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        obtain ⟨hfl, hft⟩ := hf
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error e => simp [genComputeSkeleton, hL] at h
        | ok pr =>
          obtain ⟨lTree, lRes⟩ := pr
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hL, hR] at h
          | ok pr =>
            obtain ⟨rTree, rRes⟩ := pr
            simp only [evalGRom] at hgrom
            cases gL : evalGRom q n subject (.cell lh lt) with
            | none => rw [gL] at hgrom; simp at hgrom
            | some l =>
              cases gR : evalGRom q n subject tl with
              | none => rw [gL, gR] at hgrom; simp at hgrom
              | some rr =>
                simp [genComputeSkeleton, hL, hR] at h
                obtain ⟨ht, _⟩ := h
                subst t
                refine treeRequestAxesLt_node _ _ ?_ ?_
                · intro req hreq
                  simp [skelNode] at hreq
                  subst req
                  exact h3
                · intro c hc
                  simp at hc
                  rcases hc with rfl | rfl
                  · exact ih hL gL hs hfl
                  · exact ih hR gR hs hft
      | atom op =>
        obtain ⟨_, hft⟩ := hf
        match op with
        | 0 =>
          cases tl with
          | atom ax =>
            cases hsl : Noun.slot ax subject with
            | none => simp [genComputeSkeleton, hsl] at h
            | some result =>
              simp [genComputeSkeleton, hsl] at h
              obtain ⟨ht, _⟩ := h
              subst t
              refine treeRequestAxesLt_node _ _ ?_ (by intro c hc; simp at hc)
              intro req hreq
              simp [skelNode] at hreq
              rcases hreq with hreq | hreq
              · subst req; exact h3
              · subst req; exact hft
          | cell _ _ => simp [genComputeSkeleton] at h
        | 1 =>
          simp [genComputeSkeleton] at h
          obtain ⟨ht, _⟩ := h
          subst t
          refine treeRequestAxesLt_node _ _ ?_ (by intro c hc; simp at hc)
          intro req hreq
          simp [skelNode] at hreq
          subst req
          exact h3
        | 2 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            obtain ⟨hfb, hfc⟩ := hft
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sf1⟩ := pr
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, sf2⟩ := pr
                cases hM : genComputeSkeleton (K := K) n sf1 sf2 with
                | error e => simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pr =>
                  obtain ⟨mTree, result⟩ := pr
                  simp only [evalGRom] at hgrom
                  cases gB : evalGRom q n subject b with
                  | none => rw [gB] at hgrom; simp at hgrom
                  | some sb =>
                    cases gC : evalGRom q n subject c with
                    | none => rw [gB, gC] at hgrom; simp at hgrom
                    | some sc =>
                      rw [gB, gC] at hgrom
                      have e1 := skel_result_eq_evalGRom hB gB
                      have e2 := skel_result_eq_evalGRom hC gC
                      subst e1 e2
                      have hb1 := evalGRom_boundedBy n subject b sf1 hs hfb gB
                      have hb2 := evalGRom_boundedBy n subject c sf2 hs hfc gC
                      simp [genComputeSkeleton, hB, hC, hM] at h
                      obtain ⟨ht, _⟩ := h
                      subst t
                      refine treeRequestAxesLt_node _ _ ?_ ?_
                      · intro req hreq
                        simp [skelNode] at hreq
                        rcases hreq with hreq | hreq
                        · subst req; exact h3
                        · subst req; exact h2
                      · intro ch hc
                        simp at hc
                        rcases hc with rfl | rfl | rfl
                        · exact ih hB gB hs hfb
                        · exact ih hC gC hs hfc
                        · exact ih hM hgrom hb1 hb2
        | 3 =>
          cases hC : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hC] at h
          | ok pr =>
            obtain ⟨callTree, callResult⟩ := pr
            simp only [evalGRom] at hgrom
            cases gT : evalGRom q n subject tl with
            | none => rw [gT] at hgrom; simp at hgrom
            | some v =>
              simp [genComputeSkeleton, hC] at h
              obtain ⟨ht, _⟩ := h
              subst t
              refine treeRequestAxesLt_node _ _ ?_ ?_
              · intro req hreq
                simp [skelNode] at hreq
                subst req
                exact h3
              · intro ch hc
                simp at hc
                subst ch
                exact ih hC gT hs hft
        | 4 =>
          cases hC : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hC] at h
          | ok pr =>
            obtain ⟨callTree, callResult⟩ := pr
            cases hinc : Noun.lus callResult with
            | none => simp [genComputeSkeleton, hC, hinc] at h
            | some result =>
              simp only [evalGRom] at hgrom
              cases gT : evalGRom q n subject tl with
              | none => rw [gT] at hgrom; simp at hgrom
              | some v =>
                simp [genComputeSkeleton, hC, hinc] at h
                obtain ⟨ht, _⟩ := h
                subst t
                refine treeRequestAxesLt_node _ _ ?_ ?_
                · intro req hreq
                  simp [skelNode] at hreq
                  subst req
                  exact h3
                · intro ch hc
                  simp at hc
                  subst ch
                  exact ih hC gT hs hft
        | 5 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            obtain ⟨hfb, hfc⟩ := hft
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sf1⟩ := pr
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, sf2⟩ := pr
                simp only [evalGRom] at hgrom
                cases gB : evalGRom q n subject b with
                | none => rw [gB] at hgrom; simp at hgrom
                | some sb =>
                  cases gC : evalGRom q n subject c with
                  | none => rw [gB, gC] at hgrom; simp at hgrom
                  | some sc =>
                    simp [genComputeSkeleton, hB, hC] at h
                    obtain ⟨ht, _⟩ := h
                    subst t
                    refine treeRequestAxesLt_node _ _ ?_ ?_
                    · intro req hreq
                      simp [skelNode] at hreq
                      rcases hreq with hreq | hreq
                      · subst req; exact h3
                      · subst req; exact h2
                    · intro ch hc
                      simp at hc
                      rcases hc with rfl | rfl
                      · exact ih hB gB hs hfb
                      · exact ih hC gC hs hfc
        | 6 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b cd =>
            cases cd with
            | atom _ => simp [genComputeSkeleton] at h
            | cell c d =>
              obtain ⟨hfb, hfc, hfd⟩ := hft
              cases hB : genComputeSkeleton (K := K) n subject b with
              | error e => simp [genComputeSkeleton, hB] at h
              | ok pr =>
                obtain ⟨condTree, cond⟩ := pr
                simp only [evalGRom] at hgrom
                cases gB : evalGRom q n subject b with
                | none => rw [gB] at hgrom; simp at hgrom
                | some vb =>
                  rw [gB] at hgrom
                  have e1 := skel_result_eq_evalGRom hB gB
                  subst e1
                  cases cond with
                  | cell _ _ => simp [genComputeSkeleton, hB] at h
                  | atom cv =>
                    match cv with
                    | 0 =>
                      cases hC : genComputeSkeleton (K := K) n subject c with
                      | error e => simp [genComputeSkeleton, hB, hC] at h
                      | ok pr =>
                        obtain ⟨takenTree, result⟩ := pr
                        simp [genComputeSkeleton, hB, hC] at h
                        obtain ⟨ht, _⟩ := h
                        subst t
                        refine treeRequestAxesLt_node _ _ ?_ ?_
                        · intro req hreq
                          simp [skelNode] at hreq
                          rcases hreq with hreq | hreq | hreq
                          · subst req; exact h3
                          · subst req; exact h2
                          · subst req; exact h2
                        · intro ch hc
                          simp at hc
                          rcases hc with rfl | rfl
                          · exact ih hB gB hs hfb
                          · exact ih hC hgrom hs hfc
                    | 1 =>
                      cases hD : genComputeSkeleton (K := K) n subject d with
                      | error e => simp [genComputeSkeleton, hB, hD] at h
                      | ok pr =>
                        obtain ⟨takenTree, result⟩ := pr
                        simp [genComputeSkeleton, hB, hD] at h
                        obtain ⟨ht, _⟩ := h
                        subst t
                        refine treeRequestAxesLt_node _ _ ?_ ?_
                        · intro req hreq
                          simp [skelNode] at hreq
                          rcases hreq with hreq | hreq | hreq
                          · subst req; exact h3
                          · subst req; exact h2
                          · subst req; exact h2
                        · intro ch hc
                          simp at hc
                          rcases hc with rfl | rfl
                          · exact ih hB gB hs hfb
                          · exact ih hD hgrom hs hfd
                    | _ + 2 => simp [genComputeSkeleton, hB] at h
        | 7 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            obtain ⟨hfb, hfc⟩ := hft
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sb⟩ := pr
              cases hC : genComputeSkeleton (K := K) n sb c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, result⟩ := pr
                simp only [evalGRom] at hgrom
                cases gB : evalGRom q n subject b with
                | none => rw [gB] at hgrom; simp at hgrom
                | some vb =>
                  rw [gB] at hgrom
                  have e1 := skel_result_eq_evalGRom hB gB
                  subst e1
                  have hbb := evalGRom_boundedBy n subject b sb hs hfb gB
                  simp [genComputeSkeleton, hB, hC] at h
                  obtain ⟨ht, _⟩ := h
                  subst t
                  refine treeRequestAxesLt_node _ _ ?_ ?_
                  · intro req hreq
                    simp [skelNode] at hreq
                    rcases hreq with hreq | hreq
                    · subst req; exact h3
                    · subst req; exact h2
                  · intro ch hc
                    simp at hc
                    rcases hc with rfl | rfl
                    · exact ih hB gB hs hfb
                    · exact ih hC hgrom hbb hfc
        | 8 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            obtain ⟨hfb, hfc⟩ := hft
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sb⟩ := pr
              cases hC : genComputeSkeleton (K := K) n (.cell sb subject) c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, result⟩ := pr
                simp only [evalGRom] at hgrom
                cases gB : evalGRom q n subject b with
                | none => rw [gB] at hgrom; simp at hgrom
                | some vb =>
                  rw [gB] at hgrom
                  have e1 := skel_result_eq_evalGRom hB gB
                  subst e1
                  have hbb := evalGRom_boundedBy n subject b sb hs hfb gB
                  simp [genComputeSkeleton, hB, hC] at h
                  obtain ⟨ht, _⟩ := h
                  subst t
                  refine treeRequestAxesLt_node _ _ ?_ ?_
                  · intro req hreq
                    simp [skelNode] at hreq
                    rcases hreq with hreq | hreq
                    · subst req; exact h3
                    · subst req; exact h2
                  · intro ch hc
                    simp at hc
                    rcases hc with rfl | rfl
                    · exact ih hB gB hs hfb
                    · exact ih hC hgrom ⟨hbb, hs⟩ hfc
        | 9 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom ax =>
              obtain ⟨hax, hfc⟩ := hft
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error e => simp [genComputeSkeleton, hC] at h
              | ok pr =>
                obtain ⟨coreTree, core⟩ := pr
                cases hslot : Noun.slot ax core with
                | none => simp [genComputeSkeleton, hC, hslot] at h
                | some arm =>
                  cases hI : genComputeSkeleton (K := K) n core arm with
                  | error e => simp [genComputeSkeleton, hC, hslot, hI] at h
                  | ok pr =>
                    obtain ⟨invokeTree, result⟩ := pr
                    simp only [evalGRom] at hgrom
                    cases gC : evalGRom q n subject c with
                    | none => rw [gC] at hgrom; simp at hgrom
                    | some vc =>
                      rw [gC] at hgrom
                      have e1 := skel_result_eq_evalGRom hC gC
                      subst e1
                      dsimp only at hgrom
                      rw [hslot] at hgrom
                      have hbc := evalGRom_boundedBy n subject c core hs hfc gC
                      have hba := FieldEmbedding.slot_boundedBy q ax core hbc hslot
                      simp [genComputeSkeleton, hC, hslot, hI] at h
                      obtain ⟨ht, _⟩ := h
                      subst t
                      refine treeRequestAxesLt_node _ _ ?_ ?_
                      · intro req hreq
                        simp [skelNode] at hreq
                        rcases hreq with hreq | hreq | hreq
                        · subst req; exact h3
                        · subst req; exact h2
                        · subst req; exact hax
                      · intro ch hc
                        simp at hc
                        rcases hc with rfl | rfl
                        · exact ih hC gC hs hfc
                        · exact ih hI hgrom hbc hba
        | 10 => simp [genComputeSkeleton] at h
        | 11 => simp [genComputeSkeleton] at h
        | _ + 12 => simp [genComputeSkeleton] at h

/-- The AIR reorder permutes children only; request lists are untouched. -/
theorem treeRequestAxesLt_airReorder {q : ℕ} {t : NTree (GenComputeRow K)}
    (h : treeRequestAxesLt q t) : treeRequestAxesLt q (airReorder t) := by
  intro u hu req hreq
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t u hu
  exact h u0 hu0 req (by simpa [hl] using hreq)

/-- BFS stamp assignment does not change root/child/axis, so every extracted memory-record request
of an assigned node keeps its axis `< q`. -/
theorem bfsAssign_extract_requests_axis_lt {q : ℕ} (t : NTree (GenComputeRow K))
    (ht : treeRequestAxesLt q t) (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign t) n) :
    ∀ r ∈ extractNodeReqs n.label, r.axis < q := by
  have hnF : n ∈ bfsForest [bfsAssign t] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab := bfsAssign_bfsForest_labels t
  have hmem : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [hlab] at hmem
  simp only [List.mem_map] at hmem
  rcases hmem with ⟨i, hi, hieq⟩
  have hi' := lt_bfsRows_of_mem_range' (t := t) hi
  intro r hr
  rw [← hieq, extractNodeReqs, bfsLabelAt_requests t i hi'] at hr
  obtain ⟨req, hreq, _, _, hr3⟩ := extractNodeReqsAux_mem _ 0 _ r hr
  have hlen : i - 1 < (bfsForest [t]).length := by
    rwa [← bfsRows_length]
  have hnode : (bfsForest [t])[i - 1] ∈ bfsForest [t] := List.getElem_mem _
  have hin : InTree t (bfsForest [t])[i - 1] := by
    have := (mem_bfsForest [t] _).mp hnode
    rcases this with ⟨c, hc, hIn⟩
    simp only [List.mem_singleton] at hc
    subst c
    exact hIn
  have hreq' : req ∈ (bfsForest [t])[i - 1].label.requests := by
    have : (bfsRows t)[i - 1] = (bfsForest [t])[i - 1].label := by
      simp [bfsRows]
    simpa [this] using hreq
  rw [hr3]
  exact ht _ hin req hreq'

/-- **Packaged form, any accepted skeleton.**  Every memory-record request extracted from the
assigned, AIR-reordered tree of an accepted skeleton has axis `< q`, given a successful guarded ROM
run on `BoundedBy q` subject and formula. -/
theorem skeleton_assigned_request_axes_lt {q fuel : ℕ} {subject formula result r' : Noun}
    {t : NTree (GenComputeRow K)} (hq : 3 < q)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hgrom : evalGRom q fuel subject formula = some r')
    (hs : FieldEmbedding.BoundedBy q subject) (hf : FieldEmbedding.BoundedBy q formula) :
    ∀ n, InTree (bfsAssign (airReorder t)) n → ∀ r ∈ extractNodeReqs n.label, r.axis < q :=
  bfsAssign_extract_requests_axis_lt _
    (treeRequestAxesLt_airReorder (genComputeSkeleton_request_axes_lt hq h hgrom hs hf))

/-- **Packaged form, the ROM tree.**  The consumer shape: from `hgrom` alone (plus `hq`, `hs`,
`hf`), every extracted request of `bfsAssign (airReorder (romTree _))` has axis `< q`. -/
theorem romTree_assigned_request_axes_lt {q fuel : ℕ} {subject formula result : Noun}
    (hq : 3 < q) (hgrom : evalGRom q fuel subject formula = some result)
    (hs : FieldEmbedding.BoundedBy q subject) (hf : FieldEmbedding.BoundedBy q formula) :
    ∀ n, InTree (bfsAssign (airReorder (romTree (K := K) (evalGRom_le_evalRom hgrom)))) n →
      ∀ r ∈ extractNodeReqs n.label, r.axis < q :=
  skeleton_assigned_request_axes_lt hq (romTree_spec (K := K) (evalGRom_le_evalRom hgrom))
    hgrom hs hf

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.skel_result_eq_evalGRom
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_request_axes_lt
#print axioms Nock.NockVMROM.Thm54.TraceGen.treeRequestAxesLt_airReorder
#print axioms Nock.NockVMROM.Thm54.TraceGen.bfsAssign_extract_requests_axis_lt
#print axioms Nock.NockVMROM.Thm54.TraceGen.skeleton_assigned_request_axes_lt
#print axioms Nock.NockVMROM.Thm54.TraceGen.romTree_assigned_request_axes_lt
