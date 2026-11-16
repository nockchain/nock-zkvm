import Nock.NockVMROM.Thm54.JointVerification
import Nock.RedTeam.Thm54NodeEncodingRegression

/-!
This remains the segmented `102/44`, `1-1*` algebraic scope.
-/

open scoped Classical

namespace Nock.RedTeam.Thm54P7JointRegression

open Nock Nock.NockVMROM.Thm54
open Nock.RedTeam.Thm54P3Nonvacuity
open Nock.RedTeam.Thm54P7PlusIORegression
open Nock.RedTeam.Thm54NodeEncodingRegression

noncomputable section

abbrev K17 := Nock.RedTeam.Thm54P2Nonvacuity.K17

/-- Concrete S6 nonvacuity: one endpoint choice and one joint assignment simultaneously contain
all six accepting families on the committed chained execution.  The final conjuncts pin the
actual segmented widths and `1-1*` translator degree. -/
theorem balanced_jointVerification_nonempty :
    ∃ requests responses outMem : IOField K17,
      ∃ A : JointAssignment
          (productionFamily.withIOEndpoints requests responses outMem) 17,
        A.sameExecution.Satisfies ∧
          requests = responses ∧
          outMem = 0 ∧
          ChainedSemanticExactLanguage
            (productionFamily.withIOEndpoints requests responses outMem).problem.cfg
            (productionFamily.withIOEndpoints requests responses outMem).problem.exec ∧
          Fintype.card ComputePlusIOColumn = 102 ∧
          Fintype.card MemoryPlusIOColumn = 45 ∧
          (productionFamily.withIOEndpoints
            requests responses outMem).problem.cfg.eDeg = 1 := by
  obtain ⟨requests, responses, outMem, ⟨A⟩⟩ :=
    jointVerification_complete productionFamily
      production_chained semanticWitness
      (by
        change cfg.Ksz < 17
        norm_num [cfg])
  have hendpoints : requests = responses ∧ outMem = 0 := by
    simpa [PlusIOSegmentedFamily.withIOEndpoints] using A.public_endpoints
  refine ⟨requests, responses, outMem, A, A.sixFamilies,
    hendpoints.1, hendpoints.2, ?_, compute_disjoint_width,
    memory_disjoint_width, ?_⟩
  · change ChainedSemanticExactLanguage cfg exec
    exact production_chained
  · exact
      (productionFamily.withIOEndpoints
        requests responses outMem).problem.cfg.eDeg_eq_one

end

end Nock.RedTeam.Thm54P7JointRegression

#print axioms Nock.RedTeam.Thm54P7JointRegression.balanced_jointVerification_nonempty

