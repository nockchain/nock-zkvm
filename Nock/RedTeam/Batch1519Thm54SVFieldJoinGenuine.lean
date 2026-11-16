/-
  Nock/RedTeam/Batch1519Thm54SVFieldJoinGenuine.lean

  **Receipts for the field C2 join and
  field genuineness.**

  Production modules (all below the statement file, under `P8Core/`):
  * `Batch1510Thm54SVJoinF` — `c2EvaluationF q` / `c2SkeletonRowF q` / `c2JoinFuelF q`: the C2 join
    with the OP4 arm mod `q` (`incMod q`), every other arm verbatim.
  * `Batch1511Thm54SVGenuineF` — `RowOutputF q`, `GenuineSkelF q`, `genuineF_evalFBy`,
    `HoldsF`, `holdsF_of_genuineF`, the field call tree `CallTreeF q S0 F0 d s f`,
    `callTreeF_kid` (calls propagate down the evaluation order, no honest tree), `callTreeF_rows`.
  * `Batch1512Thm54SVJoinAssemblyF` — `Batch1021`'s stack (`J_*`, `computeTreeBinds_join_*`,
    `J_succ_eq`, `J_eq_of_le`) at the field join; OP4 via `computeTreeBinds_op4F` (`[CharP K q]`).
  * `Batch1513Thm54SVReadyFuelF` — `Batch1090`'s stack (`C2JoinReadyF`, `C2ChipReady`,
    `computeTreeBinds_of_chipReady`, …) at the field join.
  * `Batch1514Thm54SVAlignmentF` — `C2Aligned q`, **`genuineF_of_ready`** (aligned + chip-ready ⇒
    field-genuine join, NO run), `evalFBy_of_ready`, `holdsF_of_ready`; the census corollaries
    `c2Row_pairs_le`, `J_isJ`, `J_nodes`, `sf_le`, `c2_tree_census` over `GenuineSkelF`.
  * `Batch1515Thm54SVInductionGenericF` — `evalFBy_boundedBy`, `evalFBy_det`, `evalN_of_holdsF`
    (the corollary to real Nock under a successful guarded run), `Batch1171`'s record facts
    `J_label_eq` / `memoryRecord_eq` / `J_rec` at the field join (record function `Batch1171.c2Rec`),
    `kid_e_bind`, `kid_evalF`, `kid_eval_boundedF`, and the skeleton-generic oracles
    `censusOK_of_not_mem` / `windowOK_of_not_mem`.

  This artifact:
  1. **The R1b control, at the twin** (`op4_overflow_twin`): on the tree of
     `Batch1091.op4_overflow_unbounded` (`q = 31`, a served `atom 30` under OP4), the FIELD join's
     root is `atom 0`, `BoundedBy 31`, and equals `evalFBy 31`'s result; the Nat join's root on the
     same tree is `atom 31` (`op4_overflow_unbounded`, re-cited).  The twin removes exactly the
     discrepancy the receipt exhibits.
  2. A one-row positive control for `holdsF_of_genuineF` (`[1 5]` on any subject) and the root of
     the call tree.
  3. `#print axioms` for the API.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1515Thm54SVInductionGenericF
import Nock.RedTeam.Batch1091Thm54C2Alignment

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1519

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.SVJoinF
open Nock.NockVMROM.Thm54.SVGenuineF
open Nock.FieldEmbedding

/-- **R1b at the twin.**  The tree of `Batch1091.op4_overflow_unbounded`: the field join's root is
`atom 0` (bounded, and `evalFBy 31`'s result), where the Nat join's is `atom 31`. -/
theorem op4_overflow_twin (row4 row0 : (State × DTcomp (ZMod 31)) × ℕ)
    (svq : MState → ℕ → Noun) (axq : ℕ → ℕ)
    (h4 : row4.1.1 = .s4) (h0 : row0.1.1 = .s0)
    (hserve : svq .verify_child (row0.2 + 2) = .atom 30) :
    (c2JoinFuelF 31 (fun l : (State × DTcomp (ZMod 31)) × ℕ => l.1.1) (fun l => l.2) svq axq 2
        (.node row4 [.node row0 []]) (.atom 30)
        (.cell (.atom 4) (.cell (.atom 0) (.atom 1)))).label.evaluation = .atom 0 ∧
      BoundedBy 31 (.atom 0) ∧
      evalFBy 31 2 (.atom 30) (.cell (.atom 4) (.cell (.atom 0) (.atom 1))) = some (.atom 0) ∧
      (StrategyOfTracesR0AC2.c2JoinFuel (fun l : (State × DTcomp (ZMod 31)) × ℕ => l.1.1)
        (fun l => l.2) svq axq 2 (.node row4 [.node row0 []]) (.atom 30)
        (.cell (.atom 4) (.cell (.atom 0) (.atom 1)))).label.evaluation = .atom 31 := by
  -- OP0's field result is `op0ResF` (the subject at axis 1); both branches give `atom 30`
  have hres : op0ResF svq axq row0.2 (.atom 30) = .atom 30 := by
    unfold op0ResF; split <;> simp [hserve]
  refine ⟨?_, by simp, ?_, (Batch1091.op4_overflow_unbounded row4 row0 svq axq h4 h0 hserve).1⟩
  · simp [c2JoinFuelF, c2SkeletonRowF, c2EvaluationF, h4, h0, kidSkel, hres, nounTail,
      OpcodeSemantics.incMod]
  · simp [evalFBy, lusFBy, Noun.slot]

/-- The one-row skeleton of `[1 5]` at subject `s`. -/
def quoteRow (s : Noun) : ComputeRowSkeleton where
  state := .s1
  subject := s
  formula := .cell (.atom 1) (.atom 5)
  evaluation := .atom 5
  decomposition := fun _ _ => .atom 0
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 0, 0⟩

/-- **Positive control**: a one-row field-genuine tree proves its claim under `HoldsF`. -/
theorem quote_genuine (q : ℕ) (s : Noun) : GenuineSkelF q (.node (quoteRow s) []) :=
  GenuineSkelF.node ⟨.atom 5, rfl⟩ (by simp [quoteRow, ComputedWindow.KidInputs])
    (by simp [quoteRow, RowOutputF, ComputedWindow.tl, StrategyOfTraces.nounTail]) (by simp)

theorem quote_holdsF (q : ℕ) (s : Noun) :
    HoldsF q ⟨s, .cell (.atom 1) (.atom 5), .atom 5⟩ :=
  holdsF_of_genuineF (quote_genuine q s) rfl rfl rfl

/-- The claim is the root of its own call tree. -/
theorem callTree_root (q : ℕ) (s f : Noun) : CallTreeF q s f 0 s f := .root

end Nock.RedTeam.Batch1519

#print axioms Nock.RedTeam.Batch1519.op4_overflow_twin
#print axioms Nock.RedTeam.Batch1519.quote_holdsF
#print axioms Nock.NockVMROM.Thm54.SVGenuineF.genuineF_evalFBy
#print axioms Nock.NockVMROM.Thm54.SVGenuineF.holdsF_of_genuineF
#print axioms Nock.NockVMROM.Thm54.SVGenuineF.callTreeF_kid
#print axioms Nock.NockVMROM.Thm54.SVGenuineF.callTreeF_rows
#print axioms Nock.NockVMROM.Thm54.SVJoinAssemblyF.computeTreeBinds_op4F
#print axioms Nock.NockVMROM.Thm54.SVJoinAssemblyF.J_eq_of_le
#print axioms Nock.NockVMROM.Thm54.SVReadyFuelF.computeTreeBinds_of_chipReady
#print axioms Nock.NockVMROM.Thm54.SVReadyFuelF.c2JoinReadyF_of_chipReady
#print axioms Nock.NockVMROM.Thm54.SVAlignmentF.genuineF_of_ready
#print axioms Nock.NockVMROM.Thm54.SVAlignmentF.evalFBy_of_ready
#print axioms Nock.NockVMROM.Thm54.SVAlignmentF.holdsF_of_ready
#print axioms Nock.NockVMROM.Thm54.SVAlignmentF.c2_tree_census
#print axioms Nock.NockVMROM.Thm54.SVInductionGenericF.evalFBy_boundedBy
#print axioms Nock.NockVMROM.Thm54.SVInductionGenericF.evalN_of_holdsF
#print axioms Nock.NockVMROM.Thm54.SVInductionGenericF.J_rec
#print axioms Nock.NockVMROM.Thm54.SVInductionGenericF.kid_e_bind
#print axioms Nock.NockVMROM.Thm54.SVInductionGenericF.kid_evalF
#print axioms Nock.NockVMROM.Thm54.SVInductionGenericF.kid_eval_boundedF
#print axioms Nock.NockVMROM.Thm54.SVInductionGenericF.censusOK_of_not_mem
#print axioms Nock.NockVMROM.Thm54.SVInductionGenericF.windowOK_of_not_mem
