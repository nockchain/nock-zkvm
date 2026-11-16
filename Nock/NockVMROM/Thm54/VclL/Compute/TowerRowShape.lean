import Nock.NockVMROM.Thm54.VclL.Compute.TowerJointReqFacts
import Nock.NockVMROM.Thm54.TraceGen.GenSlotKeys

/-!
# The per-state request shapes of the generator rows

`RowShape g`: the request keys of a generator row are
the closed forms the compute chip's slot records read: at `s1` the evaluation is the formula tail; at the
`slotAcc` export slots `1`, `2` the keys are the (cell) formula tail / tail-tail at axis `2`; at `s0` the
path key is `(subject, honestAx)` with `slot honestAx subject = evaluation`; at `s9` it is
`(core, honestAx)` with `slot honestAx core = arm`.  Proved for every node of an accepted run by the same
fuel induction as `genComputeSkeleton_slot0` / `gen_reqFacts`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Noun Nock.Walk Nock.NockVMROM.Thm54.TraceGen Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.VclL

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

section shape
variable {K : Type} [Field K]

/-- **The request shapes of a generator row.** -/
def RowShape (g : GenComputeRow K) : Prop :=
  (g.skel.state = .s1 → g.skel.evaluation = formulaTail g.skel.formula) ∧
  ((g.skel.state = .s2 ∨ g.skel.state = .s5 ∨ g.skel.state = .s6 ∨ g.skel.state = .s7 ∨
      g.skel.state = .s8 ∨ g.skel.state = .s9) →
    (rowSlotKeys g)[1]? = some (formulaTail g.skel.formula, 2) ∧
      (formulaTail g.skel.formula).isCell = true) ∧
  (g.skel.state = .s6 →
    (rowSlotKeys g)[2]? = some (formulaTail (formulaTail g.skel.formula), 2) ∧
      (formulaTail (formulaTail g.skel.formula)).isCell = true) ∧
  (g.skel.state = .s0 →
    (rowSlotKeys g)[1]? = some (g.skel.subject, honestAx g.skel) ∧
      Noun.slot (honestAx g.skel) g.skel.subject = some g.skel.evaluation) ∧
  (g.skel.state = .s9 →
    (rowSlotKeys g)[2]? = some (P8Census.skeletonSubformula g.skel 0 .result, honestAx g.skel) ∧
      Noun.slot (honestAx g.skel) (P8Census.skeletonSubformula g.skel 0 .result) =
        some (P8Census.skeletonSubformula g.skel 1 .formula))

theorem gen_rowShape (fuel : ℕ) :
    ∀ (s f : Noun) (ct : NTree (GenComputeRow K)) (res : Noun),
      genComputeSkeleton fuel s f = .ok (ct, res) →
      ∀ t, InTree ct t → RowShape t.label := by
  induction fuel with
  | zero => intro s f ct res h; simp [genComputeSkeleton] at h
  | succ n ih =>
    intro s f ct res h t ht
    unfold genComputeSkeleton at h
    repeat' (split at h)
    all_goals first
      | (exfalso; simp at h; done)
      | skip
    all_goals
      (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       cases ht with
       | here =>
         simp [RowShape, rowSlotKeys, skelNode, formulaTail, Noun.isCell, honestAx,
           P8Census.skeletonSubformula, genSkelOp0, genSkelOp1, genSkelOp2, genSkelOp3,
           genSkelOp4, genSkelOp5, genSkelOp6, genSkelOp7, genSkelOp8, genSkelOp9, genSkelCons,
           ComputeTable.fanoutComp, *]
       | sub hs hst =>
         simp only [NTree.children_node, List.mem_cons, List.not_mem_nil, or_false] at hs <;>
         first
           | exact hs.elim
           | (subst hs; exact ih _ _ _ _ (by assumption) _ hst)
           | (rcases hs with rfl | rfl <;> exact ih _ _ _ _ (by assumption) _ hst)
           | (rcases hs with rfl | rfl | rfl <;> exact ih _ _ _ _ (by assumption) _ hst))

end shape

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.gen_rowShape
end VclL.Compute
end Nock.NockVMROM.Thm54
