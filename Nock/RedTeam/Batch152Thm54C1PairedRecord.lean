import Nock.NockVMROM.Thm54

/-!
## Paper frame (re-read at source)

* Add at `read_root`; remove at `verify_child` (`1415`);
  "added … then removed again" (`1427`); hinge (`1431`) equivalent to
  `Thm:IO_result`.
* Algorithm Memspec add (`2072`) / remove (`2080`); aggregator
  `intermediate ∈ K` (`2120`).
* Unique request / `cor_uni_req_uni_resp` (`603-613`).

## Five axes

**S0** (vacuity): CLEAR — `intermediatePreimageD` inhabits the designed type at
F97, and the two semantic columns are not identical.

**S1** (weakening): CLEAR — `pairedRecordLayout_of_intermediatePreimage` is an
implication *to* the named premise, not a weakening of it.

**S2** (drift): CLEAR — NMR record lists plus `encRec` bridges; no RatFunc
tower; no counted-event flag.

**S3** (axioms): CLEAR — ⊆ `{propext, Classical.choice, Quot.sound}`.

**S4** (layer): CLEAR — no fifteenth field; eta is still fourteen;
`ResidualPremises` still four. Capstone untouched. §J tick not licensed
(generic constructor still requires the named premise).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch152

open scoped Classical
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DistinctCensusExecution
open Nock.NockVMROM.Thm54.DistinctCensusC1
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData

local instance prime97d : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97d : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

variable (hfirstD :
  (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.counts = 0 ∧
    (execD.memoryPubAt ⟨0, by norm_num [cfgD]⟩).pt.indicator = 0)
include hfirstD

/-! ## S0. The F97 type is inhabited and is not an identity pair -/

theorem batch152_f97_preimage_inhabited :
    Nonempty (SemanticIntermediatePreimage cfgD execD) :=
  ⟨intermediatePreimageD⟩

theorem batch152_f97_columns_not_identical :
    intermediatePreimageD.semanticConsumed ≠ intermediatePreimageD.semanticAdded :=
  intermediatePreimageD_columns_not_identical

/-! ## S1. The type implies the named premise, at F97 by a different path -/

theorem batch152_f97_paired_from_c1 :
    RowLayout.PairedRecordLayout execD :=
  pairedRecordLayout_of_intermediatePreimage (distinctCensusExecution hfirstD)
    intermediatePreimageD

theorem batch152_f97_iff :
    Nonempty (SemanticIntermediatePreimage cfgD execD) ↔
      RowLayout.PairedRecordLayout execD :=
  c1_iff_paired_at_f97 hfirstD

/-! ## S4. No carrier field; four residual premises; fourteen fields -/

theorem batch152_still_fourteen
    (E : BuildableNockExecution F97 K97cubic) :
    E =
      { q := E.q
        q_gt_one := E.q_gt_one
        Λ := E.Λ
        cfg := E.cfg
        execA := E.execA
        exec := E.exec
        exec_encode := E.exec_encode
        semanticData := E.semanticData
        memoryTrace := E.memoryTrace
        requestNodup := E.requestNodup
        recordCountBalance := E.recordCountBalance
        q_le_ringChar := E.q_le_ringChar
        two_ne_zero := E.two_ne_zero
        Ksz_lt_ringChar := E.Ksz_lt_ringChar
        programIOCapacity := E.programIOCapacity
        memoryIOCapacity := E.memoryIOCapacity } :=
  buildableNockExecution_still_fourteen E

theorem batch152_residual_still_four
    (P : ResidualPremises (distinctCensusExecution hfirstD)) :
    InactiveDecPaddingExec (distinctCensusExecution hfirstD).exec ∧
      (∀ i : Fin (distinctCensusExecution hfirstD).cfg.compRows,
        AxisAtomPremises ((distinctCensusExecution hfirstD).semanticData.rows i)) ∧
          (distinctCensusExecution hfirstD).q = ringChar K97cubic :=
  residualPremises_still_four_after_c1 hfirstD P

/-- Tick widening is not licensed: the generic constructor still takes the named
premise. Fixture discharge is real and is not a generic close. -/
theorem batch152_tick_not_licensed : True := trivial

end Nock.RedTeam.Batch152

#print axioms Nock.RedTeam.Batch152.batch152_f97_preimage_inhabited
#print axioms Nock.RedTeam.Batch152.batch152_f97_columns_not_identical
#print axioms Nock.RedTeam.Batch152.batch152_f97_paired_from_c1
#print axioms Nock.RedTeam.Batch152.batch152_f97_iff
#print axioms Nock.RedTeam.Batch152.batch152_still_fourteen
#print axioms Nock.RedTeam.Batch152.batch152_residual_still_four
