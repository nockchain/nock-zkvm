/-
  Nock/RedTeam/Batch1711Thm54VclLComputeChip.lean

  **`computeChipVCL` — the reindex-and-filter of `allGates309`
  (part (b)).**

  Production: `Thm54/VclL/Compute/Support.lean` (column support: generic in `F`, `K` and the basis,
  `typedCompile_colsIn` / `compile309_colsIn` by induction through `mulVec` / `powVec`; the typed
  sources `tNoCert` / `wNoCert` by `decide +kernel`) and `Thm54/VclL/Compute/ChipVCL.lean`
  (`vclCol`, `reindexE`, `eval_reindexE`, `keptGates309`, `vclGates`, `vclRAP`, `computeChipVCL`,
  `computeChipVCL_sat_iff`, `colRoundVCL`).

  **Measured** (over `𝕂`, no tower, `e = 3`): `(e, w, s, d, k) = (3, 221, 309, 4, 2)` against the
  309 chip's `(3, 309, 418, 4, 2)`; `wRAP = ![208, 13]`.  Gates: `418 − 97` (`formRCertificateGates`)
  `− 6` (`formRLamPins`) `− 6` (core ids `79`, `80`, the record-1/2 sampled denominator pins — the
  ONLY other readers of Form R, positive control `formR_core_reads_cert`) `− 2` (`computeExpGates`
  ↦ the arity-1 `serialGates`, `+ 2`) `= 309`; kept groups `307` = `15 + 240 + 9 + 18 + 3 + 22`.
  Width `309 − 100` (columns `202..301`) `+ 12` (`vIdx ×2`, root `idx/μ ×4`, inverse triples `×6`) = 221.
  Layout: base/ext `0..201`, `vIdx` `202,203`, root `204..207`, walk `208..213`, inverses `214..219`,
  serial `220` (tail, round `0`).  ln / `ln_prev` gates RETAINED (their columns are inside `0..201`).
  Over the tower (`Quad K`) the 309 → 471 doubling applies to the `𝕂`-valued roles; not measured here.

  NOT claimed: the columns `202..207`, `214..219` are unconstrained until the part-(c) gates pin them
  to the reshaped records; and `ChipLayout.sat_iff` as typed at `CorrectedComputeSourceObligations`
  (which contains `formR99`, `formRLam`, all 82 core ids and the arity-form `expGates`) does NOT hold
  for this chip: `computeChipVCL_sat_iff` is its gate-level replacement.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.ChipVCL
import Mathlib.Data.Rat.Defs
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackageDefs
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch1711

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Compute
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal

/-- The 309 chip's fingerprint, for the side-by-side (untouched). -/
theorem chip309_fingerprint_vs_vcl :
    vclWidth = 309 - 100 + 12 ∧ vclRound0 + 13 = vclWidth := by decide

theorem layout_columns :
    vIdxCol 0 = 202 ∧ rootCol 0 = 204 ∧ walkColVCL 0 0 = 208 ∧ lookupInvBase 0 = 214 ∧
      serialCol = 220 ∧ serialCol = vclWidth - 1 := by decide

theorem serial_round0 : colRoundVCL serialCol = 0 := colRoundVCL_serial

theorem kept_core_80_of_82 : keptCoreIds.length = 80 := keptCoreIds_length

/-- Positive control: the two dropped ids DO read Form R. -/
theorem dropped_ids_read_formR :
    tNoCert (correctedFinalExtGate ⟨79, by omega⟩) = false ∧
      tNoCert (correctedFinalExtGate ⟨80, by omega⟩) = false := formR_core_reads_cert

#print axioms vclRAP_fingerprint
#print axioms vclGates_degree
#print axioms vclGates_length
#print axioms keptGates309_colsIn
#print axioms keptGates309_length
#print axioms correctedCoreVCL_colsIn
#print axioms formR_core_reads_cert
#print axioms eval_reindexE
#print axioms degree_reindexE
#print axioms computeChipVCL_sat_iff
#print axioms colRoundVCL_walk

end Nock.RedTeam.Batch1711
