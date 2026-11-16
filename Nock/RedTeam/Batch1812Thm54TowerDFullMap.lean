/-
  Nock/RedTeam/Batch1812Thm54TowerDFullMap.lean

  **The full Im map.**

  * `fullImMap_ext_cols` / `fullImMap_walk` / `fullImMap_pub`: the Im columns are the 50 fingerprint
    triples `232.. 381` then `382` (role 56), `385` (57), `388` (59), `391` (`W1`): 54 triples,
    `+162` columns, all appended after the width `232`, pairwise disjoint (an explicit arithmetic
    progression); one Im public triple at `48`.
  * `kept_core_kreads_full`: every KEPT (Q7) core gate carrying an Im half reads, among its `𝕂`-only
    leaves, only `𝕂` coins and the walk line / count — coefficient positions, honest `𝕂` values
    (`a, b, c` = slots 2–4, `αC` = 6, walk `γ` = 10, `ln` = role 61, `walk_inv` = 62; the pre-309
    forms of 74–77, which the chip replaces by `notLast·w58/w59` and the 309 queue gates).
  * `walk309_full`: the width-309 walk sources (ep2, ep4, aux0, aux1, queue) — which carry an Im
    half, that all are `qLinearW` (no `qmul` needed), and their `𝕂`-only reads (coefficients
    `ln`, `W0`, `αC`, walk `γ`, walk `α` = public 0, `requests` = public 2 in a non-Im gate).
-/
import Nock.RedTeam.Batch1811Thm54TowerDInvGenHonest

set_option autoImplicit false
set_option maxRecDepth 300000

namespace Nock.RedTeam.Batch1812

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.VclL.Compute
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD
open Nock.RedTeam.Batch1810

/-- The full map's Im trace columns, in role order. -/
theorem fullImMap_ext_cols :
    (List.finRange 63).filterMap fullImMap.ext =
      (List.range 50).map (fun j => vclWidthE + 3 * j) ++
        [vclWidthE + 150, vclWidthE + 153, vclWidthE + 156] := by
  decide +kernel

theorem fullImMap_walk : fullImMap.walk 0 = none ∧ fullImMap.walk 1 = some (vclWidthE + 159) := by
  decide

theorem fullImMap_pub :
    fullImMap.extPub 0 = none ∧ fullImMap.extPub 1 = some 48 ∧ fullImMap.extPub 2 = none := by
  decide

theorem fullImMap_chal : fullImMap.chal = towerChal := rfl

/-- `+162` Im columns (`54` triples), ending at `394 = 232 + 162`. -/
theorem fullImMap_column_count :
    3 * (((List.finRange 63).filterMap fullImMap.ext).length +
      ((List.finRange 2).filterMap fullImMap.walk).length) = 162 ∧
    vclWidthE + 162 = 394 := by
  decide +kernel

/-- Core gates needing `qmul` (Re body replaced) under the full map. -/
theorem nonLinear_core_full :
    (List.range 82).filter (fun i => !qLinear fullImMap (core i)) =
      [0, 1, 2, 3, 4, 5, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 42, 59, 60, 61, 62, 63, 64,
        67, 69, 70, 71, 75, 78, 79, 80] := by
  decide +kernel

/-- `𝕂`-only leaves of a typed gate under a map (non-base). -/
def kReads (M : ImMap) : CorrectedFinalTypedExpr → List String
  | .extCur i => if (M.ext i).isSome then [] else [s!"e{i.val}"]
  | .extNext i => if (M.ext i).isSome then [] else [s!"e{i.val}"]
  | .challenge i => if (M.chal i).isSome then [] else [s!"c{i.val}"]
  | .extensionPublic i => if (M.extPub i).isSome then [] else [s!"E{i.val}"]
  | .add x y => kReads M x ++ kReads M y
  | .sub x y => kReads M x ++ kReads M y
  | .mul x y => kReads M x ++ kReads M y
  | .neg x => kReads M x
  | .pow x _ => kReads M x
  | _ => []

def kReadsW (M : ImMap) : WTyped → List String
  | .leaf t => kReads M t
  | .wCur j => if (M.walk j).isSome then [] else [s!"W{j.val}"]
  | .wNext j => if (M.walk j).isSome then [] else [s!"W{j.val}"]
  | .add x y => kReadsW M x ++ kReadsW M y
  | .sub x y => kReadsW M x ++ kReadsW M y
  | .mul x y => kReadsW M x ++ kReadsW M y
  | .neg x => kReadsW M x
  | .pow x _ => kReadsW M x

/-- **The kept Q7 core gates with an Im half read only coefficient `𝕂` leaves.** -/
theorem kept_core_kreads_full :
    (keptCoreIdsQ7.map (·.val)).filterMap (fun i =>
        if hasIm fullImMap (core i) && !(kReads fullImMap (core i)).isEmpty then
          some (i, (kReads fullImMap (core i)).eraseDups) else none) =
      [(42, ["c2", "c3", "c4"]), (74, ["c6"]), (75, ["e61", "c10", "c6"]), (76, ["e62", "e61"]),
        (77, ["e61"])] := by
  decide +kernel

/-- **The width-309 walk sources** (ep2 ×6, ep4, aux0, aux1, queue ×2): (carries Im, `qLinearW`,
`𝕂`-only reads) under the full map. -/
theorem walk309_full :
    (endpoint2_309 ++ endpoint4_309 ++
        [residualSource309 0, residualSource309 1, queueNonEmpty309, queueTiling309]).map
      (fun g => (hasImW fullImMap g, qLinearW fullImMap g, (kReadsW fullImMap g).eraseDups)) =
      [(false, true, ["e61", "c6"]), (false, true, ["W0", "E0", "c6"]), (true, true, []),
        (false, true, ["e32"]), (false, true, ["e60", "E2"]), (false, true, ["e54"]),
        (true, true, ["e61", "c10", "E0", "c6"]), (false, true, ["W0", "c6"]),
        (true, true, ["e61", "c10", "W0", "c6"]), (false, true, ["e62", "W0", "e61"]),
        (false, true, ["W0", "e61"])] := by
  decide +kernel

end Nock.RedTeam.Batch1812

#print axioms Nock.RedTeam.Batch1812.fullImMap_ext_cols
#print axioms Nock.RedTeam.Batch1812.fullImMap_column_count
#print axioms Nock.RedTeam.Batch1812.nonLinear_core_full
#print axioms Nock.RedTeam.Batch1812.kept_core_kreads_full
#print axioms Nock.RedTeam.Batch1812.walk309_full
