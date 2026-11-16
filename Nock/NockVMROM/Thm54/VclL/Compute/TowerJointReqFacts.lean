import Nock.NockVMROM.Thm54.VclL.Compute.Hax63
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMem
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenTraceConfined

/-!
# Request facts of an accepted generator run

For every accepted `genComputeSkeleton` run:

* `ReqOK t`: every request of every row has axis `≤ 3` or exactly the row's `honestAx`, and its root has at
  most `rowNounsBound v.label` leaves for SOME row `v` of the tree (the row's own formula / subject, a
  subterm of its formula, or, for the `OP_9` arm fetch, the SUBJECT of the invoke child, which is the core).

Used by `TowerJointSizes` to derive `hrank` (from `programLeafBound ≤ 2^110`) and `h62` (from
`programAxisBound < 2^63`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Noun Nock.Walk Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.SemanticStrategy

set_option autoImplicit false
set_option maxHeartbeats 1600000

section reqfacts
variable {K : Type} [Field K]

/-- Request facts at every node: axis small or the row's `honestAx`; root bounded by some row's nouns. -/
def ReqOK (t : NTree (GenComputeRow K)) : Prop :=
  ∀ u, InTree t u → ∀ req ∈ u.label.requests,
    (req.axis ≤ 3 ∨ req.axis = honestAx u.label.skel) ∧
      ∃ v, InTree t v ∧ req.root.leaves ≤ rowNounsBound v.label

theorem ReqOK.node (g : GenComputeRow K) (cs : List (NTree (GenComputeRow K)))
    (hg : ∀ req ∈ g.requests, (req.axis ≤ 3 ∨ req.axis = honestAx g.skel) ∧
      ∃ v, InTree (.node g cs) v ∧ req.root.leaves ≤ rowNounsBound v.label)
    (hcs : ∀ c ∈ cs, ReqOK c) : ReqOK (.node g cs) := by
  intro u hu req hreq
  cases hu with
  | here => exact hg req hreq
  | sub hs hst =>
    obtain ⟨h1, v, hv, h3⟩ := hcs _ hs u hst req hreq
    exact ⟨h1, v, InTree.sub hs hv, h3⟩

theorem leaves_le_rowB_subject (g : GenComputeRow K) : g.skel.subject.leaves ≤ rowNounsBound g :=
  le_sup_of_le_left le_sup_left

theorem leaves_le_rowB_formula (g : GenComputeRow K) : g.skel.formula.leaves ≤ rowNounsBound g :=
  le_sup_of_le_left le_sup_right

theorem own_formula (g : GenComputeRow K) (cs : List (NTree (GenComputeRow K))) (n : Noun)
    (h : n.leaves ≤ g.skel.formula.leaves) :
    ∃ v, InTree (.node g cs) v ∧ n.leaves ≤ rowNounsBound v.label :=
  ⟨_, InTree.here _, h.trans (leaves_le_rowB_formula g)⟩

theorem own_subject (g : GenComputeRow K) (cs : List (NTree (GenComputeRow K))) (n : Noun)
    (h : n.leaves ≤ g.skel.subject.leaves) :
    ∃ v, InTree (.node g cs) v ∧ n.leaves ≤ rowNounsBound v.label :=
  ⟨_, InTree.here _, h.trans (leaves_le_rowB_subject g)⟩

set_option maxHeartbeats 3200000 in
theorem gen_reqFacts :
    ∀ {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {r : Noun},
      genComputeSkeleton (K := K) fuel subject formula = .ok (t, r) →
      (t.label.skel.subject = subject ∧ t.label.skel.formula = formula) ∧ ReqOK t := by
  intro fuel
  induction fuel with
  | zero =>
    intro subject formula t r h
    simp [genComputeSkeleton] at h
  | succ n ih =>
    intro subject formula t r h
    cases formula with
    | atom _ =>
      simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error e => simp [genComputeSkeleton, hL] at h
        | ok pr =>
          obtain ⟨lTree, lRes⟩ := pr
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hL, hR] at h
          | ok pr =>
            obtain ⟨rTree, rRes⟩ := pr
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨ht, _⟩ := h
            subst t
            refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ ?_⟩
            · intro req hreq
              simp [skelNode] at hreq
              subst req
              exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelCons, Noun.leaves])⟩
            · intro c hc
              simp at hc
              rcases hc with rfl | rfl
              · exact (ih hL).2
              · exact (ih hR).2
      | atom op =>
        match op with
        | 0 =>
          cases tl with
          | atom ax =>
            cases hs : Noun.slot ax subject with
            | none => simp [genComputeSkeleton, hs] at h
            | some result =>
              simp [genComputeSkeleton, hs] at h
              obtain ⟨ht, _⟩ := h
              subst t
              refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ (by intro c hc; simp at hc)⟩
              intro req hreq
              simp [skelNode] at hreq
              rcases hreq with hreq | hreq
              · subst req
                exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelOp0])⟩
              · subst req
                exact ⟨Or.inr (by simp [skelNode, genSkelOp0, honestAx]),
                  own_subject _ _ _ (by simp [skelNode, genSkelOp0])⟩
          | cell _ _ => simp [genComputeSkeleton] at h
        | 1 =>
          simp [genComputeSkeleton] at h
          obtain ⟨ht, _⟩ := h
          subst t
          refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ (by intro c hc; simp at hc)⟩
          intro req hreq
          simp [skelNode] at hreq
          subst req
          exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelOp1])⟩
        | 2 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
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
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  obtain ⟨ht, _⟩ := h
                  subst t
                  refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ ?_⟩
                  · intro req hreq
                    simp [skelNode] at hreq
                    rcases hreq with hreq | hreq
                    · subst req
                      exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelOp2])⟩
                    · subst req
                      exact ⟨Or.inl (by simp), own_formula _ _ _
                        (by simp [skelNode, genSkelOp2, Noun.leaves])⟩
                  · intro ch hc
                    simp at hc
                    rcases hc with rfl | rfl | rfl
                    · exact (ih hB).2
                    · exact (ih hC).2
                    · exact (ih hM).2
        | 3 =>
          cases hC : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hC] at h
          | ok pr =>
            obtain ⟨callTree, callResult⟩ := pr
            simp [genComputeSkeleton, hC] at h
            obtain ⟨ht, _⟩ := h
            subst t
            refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ ?_⟩
            · intro req hreq
              simp [skelNode] at hreq
              subst req
              exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelOp3])⟩
            · intro ch hc
              simp at hc
              subst ch
              exact (ih hC).2
        | 4 =>
          cases hC : genComputeSkeleton (K := K) n subject tl with
          | error e => simp [genComputeSkeleton, hC] at h
          | ok pr =>
            obtain ⟨callTree, callResult⟩ := pr
            cases hinc : Noun.lus callResult with
            | none => simp [genComputeSkeleton, hC, hinc] at h
            | some result =>
              simp [genComputeSkeleton, hC, hinc] at h
              obtain ⟨ht, _⟩ := h
              subst t
              refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ ?_⟩
              · intro req hreq
                simp [skelNode] at hreq
                subst req
                exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelOp4])⟩
              · intro ch hc
                simp at hc
                subst ch
                exact (ih hC).2
        | 5 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sf1⟩ := pr
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, sf2⟩ := pr
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨ht, _⟩ := h
                subst t
                refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ ?_⟩
                · intro req hreq
                  simp [skelNode] at hreq
                  rcases hreq with hreq | hreq
                  · subst req
                    exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelOp5])⟩
                  · subst req
                    exact ⟨Or.inl (by simp), own_formula _ _ _
                      (by simp [skelNode, genSkelOp5, Noun.leaves])⟩
                · intro ch hc
                  simp at hc
                  rcases hc with rfl | rfl
                  · exact (ih hB).2
                  · exact (ih hC).2
        | 6 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b cd =>
            cases cd with
            | atom _ => simp [genComputeSkeleton] at h
            | cell c d =>
              cases hB : genComputeSkeleton (K := K) n subject b with
              | error e => simp [genComputeSkeleton, hB] at h
              | ok pr =>
                obtain ⟨condTree, cond⟩ := pr
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
                      refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ ?_⟩
                      · intro req hreq
                        simp [skelNode] at hreq
                        rcases hreq with hreq | hreq | hreq
                        · subst req
                          exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelOp6])⟩
                        · subst req
                          exact ⟨Or.inl (by simp), own_formula _ _ _
                            (by simp [skelNode, genSkelOp6, Noun.leaves])⟩
                        · subst req
                          exact ⟨Or.inl (by simp), own_formula _ _ _
                            (by simp [skelNode, genSkelOp6, Noun.leaves]; omega)⟩
                      · intro ch hc
                        simp at hc
                        rcases hc with rfl | rfl
                        · exact (ih hB).2
                        · exact (ih hC).2
                  | 1 =>
                    cases hD : genComputeSkeleton (K := K) n subject d with
                    | error e => simp [genComputeSkeleton, hB, hD] at h
                    | ok pr =>
                      obtain ⟨takenTree, result⟩ := pr
                      simp [genComputeSkeleton, hB, hD] at h
                      obtain ⟨ht, _⟩ := h
                      subst t
                      refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ ?_⟩
                      · intro req hreq
                        simp [skelNode] at hreq
                        rcases hreq with hreq | hreq | hreq
                        · subst req
                          exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelOp6])⟩
                        · subst req
                          exact ⟨Or.inl (by simp), own_formula _ _ _
                            (by simp [skelNode, genSkelOp6, Noun.leaves])⟩
                        · subst req
                          exact ⟨Or.inl (by simp), own_formula _ _ _
                            (by simp [skelNode, genSkelOp6, Noun.leaves]; omega)⟩
                      · intro ch hc
                        simp at hc
                        rcases hc with rfl | rfl
                        · exact (ih hB).2
                        · exact (ih hD).2
                  | _ + 2 => simp [genComputeSkeleton, hB] at h
        | 7 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sb⟩ := pr
              cases hC : genComputeSkeleton (K := K) n sb c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, result⟩ := pr
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨ht, _⟩ := h
                subst t
                refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ ?_⟩
                · intro req hreq
                  simp [skelNode] at hreq
                  rcases hreq with hreq | hreq
                  · subst req
                    exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelOp7])⟩
                  · subst req
                    exact ⟨Or.inl (by simp), own_formula _ _ _
                      (by simp [skelNode, genSkelOp7, Noun.leaves])⟩
                · intro ch hc
                  simp at hc
                  rcases hc with rfl | rfl
                  · exact (ih hB).2
                  · exact (ih hC).2
        | 8 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error e => simp [genComputeSkeleton, hB] at h
            | ok pr =>
              obtain ⟨bTree, sb⟩ := pr
              cases hC : genComputeSkeleton (K := K) n (.cell sb subject) c with
              | error e => simp [genComputeSkeleton, hB, hC] at h
              | ok pr =>
                obtain ⟨cTree, result⟩ := pr
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨ht, _⟩ := h
                subst t
                refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ ?_⟩
                · intro req hreq
                  simp [skelNode] at hreq
                  rcases hreq with hreq | hreq
                  · subst req
                    exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelOp8])⟩
                  · subst req
                    exact ⟨Or.inl (by simp), own_formula _ _ _
                      (by simp [skelNode, genSkelOp8, Noun.leaves])⟩
                · intro ch hc
                  simp at hc
                  rcases hc with rfl | rfl
                  · exact (ih hB).2
                  · exact (ih hC).2
        | 9 =>
          cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom ax =>
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
                    simp [genComputeSkeleton, hC, hslot, hI] at h
                    obtain ⟨ht, _⟩ := h
                    subst t
                    refine ⟨⟨rfl, rfl⟩, ReqOK.node _ _ ?_ ?_⟩
                    · intro req hreq
                      simp [skelNode] at hreq
                      rcases hreq with hreq | hreq | hreq
                      · subst req
                        exact ⟨Or.inl (by simp), own_formula _ _ _ (by simp [skelNode, genSkelOp9])⟩
                      · subst req
                        exact ⟨Or.inl (by simp), own_formula _ _ _
                          (by simp [skelNode, genSkelOp9, Noun.leaves])⟩
                      · subst req
                        refine ⟨Or.inr (by simp [skelNode, genSkelOp9, honestAx]),
                          invokeTree, InTree.sub (by simp) (InTree.here _), ?_⟩
                        have hs := (ih hI).1.1
                        show core.leaves ≤ rowNounsBound invokeTree.label
                        rw [← hs]
                        exact leaves_le_rowB_subject _
                    · intro ch hc
                      simp at hc
                      rcases hc with rfl | rfl
                      · exact (ih hC).2
                      · exact (ih hI).2
        | 10 => simp [genComputeSkeleton] at h
        | 11 => simp [genComputeSkeleton] at h
        | _ + 12 => simp [genComputeSkeleton] at h

end reqfacts

end VclL.Compute
end Nock.NockVMROM.Thm54
