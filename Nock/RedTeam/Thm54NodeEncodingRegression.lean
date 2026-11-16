import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.RedTeam.Thm54P7PlusIORegression

/-!
# Concrete node-encoding regression

IO endpoints remain explicit values and the already-proved request/response capacities
are replayed unchanged.
-/

open scoped Classical

namespace Nock.RedTeam.Thm54NodeEncodingRegression

open Nock Nock.NockVMROM.Thm54
open Nock.RedTeam.Thm54P3Nonvacuity

noncomputable section

abbrev K17 := Nock.RedTeam.Thm54P2Nonvacuity.K17

/-- The exact witness field has characteristic `17 > 11`. -/
theorem production_stateTagChar : NodeEncoding.StateTagChar K17 :=
  NodeEncoding.zmod17_stateTagChar

def productionFamily : PlusIOSegmentedFamily K17 K17 :=
  PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncodersScopedP7
    Nock.RedTeam.Thm54P7PlusIORegression.problem
    production_stateTagChar
    0 0 0
    (by
      change exec.derivedRequestIO.length + 1 ≤ 2 ^ cfg.orbit.h
      rw [derived_request_singleton]
      norm_num [cfg, orbit8])
    (by
      change exec.derivedResponseIO.length + 1 ≤ 2 ^ cfg.orbit.h
      rw [derived_response_singleton]
      norm_num [cfg, orbit8])

/-- The compute walk label is the paper's ten-coordinate `LT_comp`; was `93` (`87` before Option A). -/
theorem productionFamily_widths :
    productionFamily.compNodeWidth = 10 ∧ productionFamily.memNodeWidth = 6 :=
  ⟨rfl, rfl⟩

theorem productionFamily_uses_concrete_encoders :
    productionFamily.compNodeEncode =
        NodeEncoding.computeNodeEncode production_stateTagChar ∧
      productionFamily.memNodeEncode =
        NodeEncoding.memoryNodeEncode production_stateTagChar :=
  ⟨rfl, rfl⟩

theorem productionFamily_scoped_walk_challenges :
    productionFamily.computeWalkAlpha = productionFamily.problem.cfg.challenges.α ∧
      productionFamily.memoryWalkAlpha = productionFamily.problem.cfg.challenges.α ∧
      productionFamily.walkGamma = productionFamily.problem.cfg.challenges.γ :=
  ⟨rfl, rfl, rfl⟩

/-- Concrete regression for the former `State.toNat` collision. -/
theorem production_s0_cons_encodings_differ :
    productionFamily.compNodeEncode
        (ComputeTable.State.s0,
          (Nock.RedTeam.Thm54P2Nonvacuity.cLabel.2.1,
            ({ Nock.RedTeam.Thm54P2Nonvacuity.cLabel.2.2.1 with state := .s0 },
              Nock.RedTeam.Thm54P2Nonvacuity.cLabel.2.2.2))) ≠
      productionFamily.compNodeEncode
        (ComputeTable.State.cons,
          (Nock.RedTeam.Thm54P2Nonvacuity.cLabel.2.1,
            ({ Nock.RedTeam.Thm54P2Nonvacuity.cLabel.2.2.1 with state := .cons },
              Nock.RedTeam.Thm54P2Nonvacuity.cLabel.2.2.2))) := by
  exact NodeEncoding.computeNodeEncode_s0_ne_cons production_stateTagChar _ _ _

end

end Nock.RedTeam.Thm54NodeEncodingRegression

#print axioms Nock.RedTeam.Thm54NodeEncodingRegression.production_stateTagChar
#print axioms Nock.RedTeam.Thm54NodeEncodingRegression.productionFamily
#print axioms Nock.RedTeam.Thm54NodeEncodingRegression.productionFamily_scoped_walk_challenges
#print axioms Nock.RedTeam.Thm54NodeEncodingRegression.production_s0_cons_encodings_differ
