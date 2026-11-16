/-
  Nock/RedTeam/Batch363Thm54AcceptedContent.lean

  **`AcceptedContent`.**  The production spine consumes
  row predicates, lists and equalities from `Accepts`, not
  `SixRAPSatisfy`.  Restated spine
  `` `ProductionP8AcceptedContent.lean::accepted_outside_failureUnion_content` ``;
  converse `` `::accepted_outside_failureUnion_at_of_content` `` via
  `` `::acceptedContent_of_accepts` ``.

  Paper: the paper (`V_comp`), `:960-966`
  (`Thm:Walk_IOP`), `:1413`.  Lean:
  `` `ProductionP8AcceptedContent.lean::AcceptedContent` ``.
-/
import Nock.NockVMROM.Thm54.ProductionP8AcceptedContent
import Nock.RedTeam.Batch558Thm54FormRJoin

namespace Nock.RedTeam.Batch363

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ProductionP8Containment

set_option autoImplicit false

/-! ## Extraction and converse -/

/-- `Accepts` plus the topology event (already in `FailureUnion`) yields
`AcceptedContent`. -/
def of_accepts :=
  @acceptedContent_of_accepts

/-- The restated spine. -/
def content_spine :=
  @accepted_outside_failureUnion_content

/-- Converse: original `Accepts` spine via the extraction. -/
def original_via_content :=
  @accepted_outside_failureUnion_at_of_content

/-- Relaxis from `AcceptedContent` plus the guarded event does **not**
follow; remaining join is `Batch558.cancellingTree_is_remaining_join`. -/
def axis_validity_remaining_join :=
  @Nock.RedTeam.Batch558.cancellingTree_is_remaining_join

end Nock.RedTeam.Batch363

#print axioms Nock.RedTeam.Batch363.of_accepts
#print axioms Nock.RedTeam.Batch363.content_spine
#print axioms Nock.RedTeam.Batch363.original_via_content
#print axioms Nock.RedTeam.Batch363.axis_validity_remaining_join
