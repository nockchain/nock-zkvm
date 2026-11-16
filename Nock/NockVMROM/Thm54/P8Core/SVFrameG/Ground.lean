/-
  The grounding layer.  `Grounded` is as strong
  as `HoldsF` (organizational; it cannot weaken soundness).  Root uniqueness is stated about the
  constructed tree's own root `T.label` (DESIGN's fix), not for all `sk` with `G root sk`.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.SVFrameG

open Nock Nock.Walk Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SVGenuineF (HoldsF GenuineSkelF RowOutputF holdsF_of_genuineF)
open Nock.NockVMROM.Thm54.ComputedWindow (FormulaShape KidInputs)

/-- Node-local semantics at a denotation. -/
def LocalOK {L : Type} (q : ℕ) (den : L → ComputeRowSkeleton) (u : NTree L) : Prop :=
  FormulaShape (den u.label).state (den u.label).formula ∧
  KidInputs (den u.label).state (den u.label).subject (den u.label).formula
    (u.children.map (fun c => den c.label)) ∧
  RowOutputF q (den u.label).state (den u.label).subject (den u.label).formula
    (u.children.map (fun c => den c.label)) (den u.label).evaluation

theorem genuine_of_local {L : Type} (q : ℕ) (den : L → ComputeRowSkeleton) :
    ∀ t : NTree L, (∀ u, InTree t u → LocalOK q den u) → GenuineSkelF q (mapNTree den t)
  | .node l cs, h => by
    obtain ⟨h1, h2, h3⟩ := h _ (InTree.here _)
    have hl : (cs.map (mapNTree den)).map NTree.label = cs.map (fun c => den c.label) := by
      rw [List.map_map]; congr 1; funext c; exact mapNTree_label den c
    simp only [mapNTree]
    refine GenuineSkelF.node ?_ ?_ ?_ ?_
    · simpa [NTree.label] using h1
    · rw [hl]; exact h2
    · rw [hl]; exact h3
    · intro k hk
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
      exact genuine_of_local q den c
        (fun u hu => h u (InTree.sub (by simpa [NTree.children] using hc) hu))

theorem holdsF_of_local {L : Type} (q : ℕ) (den : L → ComputeRowSkeleton) (t : NTree L)
    (h : ∀ u, InTree t u → LocalOK q den u) (x : P8PublicClaim)
    (hs : (den t.label).subject = x.subject) (hf : (den t.label).formula = x.formula)
    (he : (den t.label).evaluation = x.result) : HoldsF q x :=
  holdsF_of_genuineF (genuine_of_local q den t h)
    (by simpa using hs) (by simpa using hf) (by simpa using he)

/-- Same-shape relation between a label tree and a skeleton tree. -/
inductive TreeRel {L : Type} (G : L → ComputeRowSkeleton → Prop) :
    NTree L → NTree ComputeRowSkeleton → Prop
  | node {l sk cs ks} (h : G l sk) (kids : List.Forall₂ (TreeRel G) cs ks) :
      TreeRel G (.node l cs) (.node sk ks)

theorem TreeRel.root {L : Type} {G : L → ComputeRowSkeleton → Prop} {t T}
    (h : TreeRel G t T) : G t.label T.label := by
  cases h with | node h _ => exact h

/-- Layer-2 output at one accepted coin. -/
structure Grounded {L : Type} (q : ℕ) (G : L → ComputeRowSkeleton → Prop)
    (ClaimBinds : L → P8PublicClaim → Prop) (t : NTree L) (x : P8PublicClaim) : Prop where
  root_binds : ClaimBinds t.label x
  tree : ∃ T, TreeRel G t T ∧ GenuineSkelF q T ∧ T.label.subject = x.subject ∧
    T.label.formula = x.formula ∧ (ClaimBinds t.label x → T.label.evaluation = x.result)

theorem holdsF_of_grounded {L : Type} {q : ℕ} {G : L → ComputeRowSkeleton → Prop}
    {CB : L → P8PublicClaim → Prop} {t : NTree L} {x : P8PublicClaim}
    (h : Grounded q G CB t x) : HoldsF q x := by
  obtain ⟨T, -, hg, hs, hf, he⟩ := h.tree
  exact holdsF_of_genuineF hg hs hf (he h.root_binds)

end Nock.NockVMROM.Thm54.SVFrameG
