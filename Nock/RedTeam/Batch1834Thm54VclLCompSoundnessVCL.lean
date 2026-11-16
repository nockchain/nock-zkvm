/-
  Nock/RedTeam/Batch1834Thm54VclLCompSoundnessVCL.lean

  **`CompSoundnessVCL` assembled.**
  Production `Thm54/VclL/Compute/CompSoundnessVCL.lean`:
  `seedSpecCF`, `compSoundnessVCL F K hC S : CompSoundnessFamily F K K K RV.KeyVCL frameVCL hC S
  (tableVCLE hC) 3 (recordViewVCL …) (seedSpecCF K) (ioCF K)`.  Soundness fields proved; the honest
  fields are a PLACEHOLDER (`Honest := PEmpty`, LD2p's).  Instance level: `Kio = Kfp = K`.
  The test instance at a concrete field pair is the `example` below (instantiation receipt).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL
import Mathlib.FieldTheory.Finite.GaloisField

set_option autoImplicit false

namespace Nock.RedTeam.Batch1834

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL

#check @compSoundnessVCL
#print axioms compSoundnessVCL
#print axioms seedSpecCF

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable instance : Fintype (GaloisField 97 3) := Fintype.ofFinite _
instance : CharP (GaloisField 97 3) (ringChar (GaloisField 97 3)) := ringChar.charP _
attribute [local instance] Classical.propDecidable

/-- **The test instance**: `F = ZMod 97`, `K = GF(97³)`, any memory shape and compute height. -/
noncomputable example (hC : ℕ) (S : MemShape) :
    CompSoundnessFamily (ZMod 97) (GaloisField 97 3) (GaloisField 97 3) (GaloisField 97 3)
      Nock.NockVMROM.Thm54.VclL.RV.KeyVCL frameVCL hC S
      (Nock.NockVMROM.Thm54.VclL.Compute.tableVCLE hC) 3
      (Nock.NockVMROM.Thm54.VclL.RV.recordViewVCL (ZMod 97) (GaloisField 97 3) (GaloisField 97 3)
        (Nock.NockVMROM.Thm54.VclL.Compute.tableVCLE hC) S hC)
      (seedSpecCF (GaloisField 97 3)) (Nock.NockVMROM.Thm54.VclL.Compute.CompChipVCL.ioCF (GaloisField 97 3)) :=
  compSoundnessVCL (ZMod 97) (GaloisField 97 3) hC S

end Nock.RedTeam.Batch1834
