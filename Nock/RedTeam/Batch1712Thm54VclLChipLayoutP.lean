/-
  Nock/RedTeam/Batch1712Thm54VclLChipLayoutP.lean

  **The obligations-parametric compute layout.**

  Contract choice (V4c item 1): option (a), an additive `ChipLayoutP` whose obligations predicate is a
  FIELD (`Obl : ChipData → CorrectedFinalTypedEnv → Env → Prop`), with R2's layout embedded by
  `ChipLayout.toP` (`Obl := CorrectedComputeSourceObligations`), `layout309P := layout309.toP`
  (`layout309P_Obl`: `rfl`) and the one-line bridge `rowFacts_iff_toP : RowFacts D L c Q ↔
  RowFactsP D L.toP c Q`.
-/
import Nock.NockVMROM.Thm54.P8Core.SVCompute.ChipLayoutP
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch1712

open Nock.NockVMROM.Thm54.SVCompute

#print axioms ChipLayout.toP
#print axioms chipOfP_toP
#print axioms layout309P_Obl
#print axioms layout309P_gatesOK
#print axioms RowFactsP.of_sat
#print axioms rowFacts_iff_toP
#print axioms rowFacts_of_satP
#print axioms gatesOK_toP

end Nock.RedTeam.Batch1712
