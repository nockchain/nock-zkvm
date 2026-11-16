/-
  Nock/RedTeam/Batch1903Thm54TowerGenTable.lean

  **The 94 table columns of an honest un-hosted row, A-free.**

  * `sampledRestore309_of_vcomp`: the deployed restore inverts the 309 (un-hosted) encoding on `V_comp` rows.
  * `Row309Reads.table`: any source env reading one un-hosted row (selectors, 58 core roles, `α`, `z⁻¹`)
    decodes through `computeSubst` to `computeEnvFull` on all 94 table columns (A-free copy of
    `exactFinalTransitionEnv_table_current`).
  * Negative control `hosted_differs`: the DEPLOYED (hosted) encoding puts the walk count in role-A
    coordinate 0, where the 309 encoding keeps the genuine fingerprint coordinate, so the two encodings
    are not interchangeable at the tower env.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerGenTable

set_option autoImplicit false

namespace Nock.RedTeam.Batch1903

open Nock Nock.ComputeTable Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeOverlay Nock.NockVMROM.Thm54.Unhosted309

/-- An `s1` row with all fingerprints zero. -/
def pub0 : Pub ℚ :=
  { state := .s1, s := 0, f := 0, e := 0, sf1_s := 0, sf1_f := 0, sf1_e := 0, sf2_s := 0, sf2_f := 0,
    sf2_e := 0, sf3_s := 0, sf3_f := 0, sf3_e := 0, ln_prev := 0, ln := 0,
    mr1 := MemRec.zero, mr2 := MemRec.zero, mr3 := MemRec.zero }

def dec0 : Dec ℚ := ⟨0, 0, 0, 0, 0, 0⟩

/-- Overlay with walk count `1`. -/
def ov1 : SampledOverlayValues ℚ :=
  { walkCount := 1, walkAcc := 0, sf1_st := 0, sf2_st := 0, sf3_st := 0, ioAcc := 0,
    denom0 := 0, denom1 := 0, denom2 := 0 }

/-- **NC**: hosted vs un-hosted differ at role-A (`2` for `s1`) coordinate `0`. -/
theorem hosted_differs :
    sampledEncodeExtension pub0 dec0 ⟨0, 0⟩ ov1 (.inl (2, 0)) = 1 ∧
      sampledEncodeExtension309 pub0 dec0 ⟨0, 0⟩ ov1 (.inl (2, 0)) = 0 := by
  constructor <;>
    simp [sampledEncodeExtension, sampledEncodeExtension309, pub0, ov1, overlayRoleA,
      sampledOverlayA, OptimizedComputeCodec.fpCoordinate, OptimizedComputeCodec.encodeExtension,
      OptimizedComputeCodec.pubFingerprint] <;> rfl

end Nock.RedTeam.Batch1903

#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.sampledRestore309_of_vcomp
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.Row309Reads.semPub_value
#print axioms Nock.NockVMROM.Thm54.VclL.Compute.TowerD.Row309Reads.table
#print axioms Nock.RedTeam.Batch1903.hosted_differs
