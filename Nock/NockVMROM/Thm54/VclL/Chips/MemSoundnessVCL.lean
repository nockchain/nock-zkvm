/-
  Nock/NockVMROM/Thm54/VclL/Chips/MemSoundnessVCL.lean

  **`MemSoundnessVCL` — the memory soundness family at VCL.**

  `memSoundnessVCL δF hT hP` is a `MemSoundnessFamily` at the VCL-L coordinates (`Φ := frameVCL`,
  `Kio = Kfp = Quad δ`, `R := RV.recordViewVCL`, `Z := seedSpecVCL δ`, `I := ioSpecVCLQuad δ`,
  `S := shapeV hT hP`, `Msg0 := Unit`, `Msg2 := Quad δ`) with EVERY SOUNDNESS field proved:
  `chip` (the `ok`-gated cell / path chips), `ioFacts` (`cellValidityFacts` / `cellExportFacts` /
  `pathProviderFacts`) and its length / record / round fields, `internal*`, `servedKeys` / `servedRoot`
  / `served` / `window*`, `summands` (zero seed, census, dyck-root), `reqCond := reqCondVCL`,
  `serves` (`vcl_serves`), `response_sound` (`vcl_response_sound`).

  **Instance level (labelled).**
-/
import Nock.NockVMROM.Thm54.VclL.Chips.MemResponseVCL
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemHonest

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Chips.PathModel
open Module
open scoped Polynomial

noncomputable section

section Family
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  [DecidableEq (Quad (algebraMap F K δF))] (hT hP : ℕ) {hC : ℕ} {C : TableSpec}

/-- **`MemSoundnessVCL`**: the memory soundness family at VCL-L (soundness fields proved; honest
honest fields `HonestVCL`; see the module doc). -/
def memSoundnessVCL :
    MemSoundnessFamily F K (Quad (algebraMap F K δF)) (Quad (algebraMap F K δF)) RV.KeyVCL frameVCL hC
      (shapeV hT hP) C 3 (m := RV.mVCL) (RV.recordViewVCL F K (Quad (algebraMap F K δF)) C (shapeV hT hP) hC)
      (seedSpecVCL (algebraMap F K δF)) (ioSpecVCLQuad (algebraMap F K δF)) where
  Msg0 := Unit
  Msg2 := Quad (algebraMap F K δF)
  chip := fun V t _ ρ y χ => vclChip δF hT hP ρ y V χ t
  chip_width := fun V t _ ρ y χ => vclChip_width δF hT hP ρ y V χ t
  respBound := vclRespBound hT hP
  internal := fun V _ Q _ a => vclInternal δF hT hP V Q a
  internalBound := vclInternalBound hT hP
  ioFacts := fun V _ ρ y χ Q h a => vclIoFacts h a
  ioFacts_length := fun V _ ρ y χ Q h a => vclIoFacts_length h a
  internal_length := fun V _ ρ y χ Q _ a => vclInternal_length δF hT hP V Q a
  internal_ne_zero := fun V _ ρ y χ Q h a => vclInternal_ne_zero h a
  respRecords := fun V _ Q _ a => vclResp δF hT hP V Q a
  respRound := 1
  respRound_le_io := fun i hi => (ioSpecVCLQuad_round (algebraMap F K δF) i hi).ge
  respRecords_round := fun V _ Q Q' _ _ hQ _ => by
    funext a
    exact congrFun (vclResp_round δF hT hP V Q Q' hQ) a
  ioFacts_records := fun V _ ρ y χ Q h a => vclIoFacts_records h a
  internal_round := fun V _ Q Q' _ _ hQ _ => by
    funext a
    exact congrFun (vclInternal_round δF hT hP V Q Q' hQ) a
  servedKeys := fun V _ b => vclServedKeys δF hT hP V b
  servedRoot := fun V _ b => vclServedRoot hT hP V b
  served := fun V _ b => vclServed hT hP V b
  servedKeys_length := fun V _ b => vclServedKeys_length δF hT hP V b
  window := fun _ _ _ => vclWindow
  served_leaves_le := fun V _ b κ _ => vclServed_leaves_le hT hP V b κ
  windowBound := fun _ _ => vclWindow
  window_le := fun _ _ _ => le_refl _
  summands := fun V x => vclSummands δF hT hP V x
  reqCond := fun _ reqs χ => reqCondVCL reqs χ
  serves := fun V _ ρ y χ Q h Qc reqs _ hsum hne hio hcount _ => vcl_serves h reqs hsum hne hio hcount
  response_sound := fun V _ ρ y χ Q h Qc reqs _ hsum hne hio hcount hsumm =>
    vcl_response_sound δF hT hP V ρ y χ Q h Qc reqs hsum hne hio hcount hsumm
  Honest := HonestVCL (K := K) δF hT hP hC
  honestV := fun H => H.V
  honestMsg0 := fun _ => ()
  honestReq := fun H χ => H.req χ
  honestMsg2 := fun H χ => H.msg2 χ
  honestQ := fun H χ t => H.trace χ t
  honest_staged := fun H t => trace_staged H t
  honestBad := fun H => H.bad
  honest_accepted := fun H χ Qc hbad t => accepted H χ Qc hbad t

end Family

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
