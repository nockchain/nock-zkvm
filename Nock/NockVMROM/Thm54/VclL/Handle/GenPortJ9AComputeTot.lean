/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AComputeTot.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AOfComp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.V1J9A.GenCompX9
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (W9 N9 N9_def idOfA accTA ρA ρSA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll

section Rho
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- The honest accumulator total `m` at any public is `accTA` (`accV9` reads no public). -/
theorem accV9_eq_accTA (χ : Coins frameJ8 KC) (χe : CoinsE)
    (hχ : chalVJ8 powerBasis3 χ = Example.chalE χe) (pub : ℕ → ZMod P) {m c : ℕ} (hm : m < 6)
    (hc : c = 3 * m) :
    K3.toK (Nock.V1J8.CompX.readK
        (fun c => (totals9 (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
          (idOfA (p := P) Rt hgen) (W9 t) pub χe).getD c 0) c) =
      accTA deltaF powerBasis3 Rt hgen χ m := by
  subst hc
  rw [totals9_readK _ _ _ _ _ _ hm]
  unfold accTA
  rw [hχ, N9_def]
  exact Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOfComp.accV9_pub powerBasis3 deltaF _ _ _ _ _ pub (fun _ => 0) _ _

/-- **`compGenX9_rho`**: `ρ` from the executable totals is the honest `ρA`. -/
theorem compGenX9_rho (χ : Coins frameJ8 KC) (χe : CoinsE)
    (hχ : chalVJ8 powerBasis3 χ = Example.chalE χe) (pub : ℕ → ZMod P) (i : Fin 5) :
    K6.toQ ((rhoOfTot (totals9 (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
        (idOfA (p := P) Rt hgen) (W9 t) pub χe)).1 i) = ρA deltaF powerBasis3 Rt hgen χ i := by
  unfold rhoOfTot ρA
  by_cases h3 : (i : ℕ) = 3
  · simp only [if_pos h3, K6.toQ]
    rw [accV9_eq_accTA Rt hgen χ χe hχ pub (m := 0) (c := 0) (by norm_num) rfl,
      accV9_eq_accTA Rt hgen χ χe hχ pub (m := 1) (c := 3) (by norm_num) rfl]
  · by_cases h4 : (i : ℕ) = 4
    · simp only [if_neg h3, if_pos h4, K6.toQ]
      rw [accV9_eq_accTA Rt hgen χ χe hχ pub (m := 2) (c := 6) (by norm_num) rfl,
        accV9_eq_accTA Rt hgen χ χe hχ pub (m := 3) (c := 9) (by norm_num) rfl]
    · simp only [if_neg h3, if_neg h4]
      exact K6.toQ_zero

/-- **`compGenX9_rho`, `ρS`.** -/
theorem compGenX9_rhoS (χ : Coins frameJ8 KC) (χe : CoinsE)
    (hχ : chalVJ8 powerBasis3 χ = Example.chalE χe) (pub : ℕ → ZMod P) :
    K6.toQ (rhoOfTot (totals9 (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd
        (idOfA (p := P) Rt hgen) (W9 t) pub χe)).2 = ρSA deltaF powerBasis3 Rt hgen χ := by
  unfold rhoOfTot ρSA
  simp only [K6.toQ]
  rw [accV9_eq_accTA Rt hgen χ χe hχ pub (m := 4) (c := 12) (by norm_num) rfl,
    accV9_eq_accTA Rt hgen χ χe hχ pub (m := 5) (c := 15) (by norm_num) rfl]

end Rho

/-- **`compGenX9_eq_closed`**: `compGenX9_eq` with the node value `nodeV9E` itself; no binder beyond the run data. -/
theorem compGenX9_eq_closed
    [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
    (c : P8PublicClaim) (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ)
    (W : List (NTree LX9)) (χe : CoinsE)
    {j : ℕ} (hj : j < W.length) {d : ℕ} (hd : d < 137) :
    (((compGenX9 c H pd idOf W χe).rows).getD j #[]).getD d 0 =
      Nock.NockVMROM.Thm54.VclL.HonestTraceX9.trX9 powerBasis3 deltaF H pd idOf W (Example.chalE χe)
        (pubFinal9 c H pd idOf W χe)
        (Nock.NockVMROM.Thm54.VclL.Compute.TowerD.lnClosed (K3.toK (χe ⟨13, by decide⟩)))
        (Nock.NockVMROM.Thm54.VclL.Compute.TowerD.cntClosed (Walk.foCol W) (K3.toK (χe ⟨13, by decide⟩))
          (K3.toK (χe ⟨13, by decide⟩)))
        (Nock.NockVMROM.Thm54.VclL.HonestSatX9.accW9
          (fun u => K3.toK (nodeV9E H pd idOf (χe ⟨14, by decide⟩) u)) W (K3.toK (χe ⟨13, by decide⟩))) j
        (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow.invPermX9 d) :=
  compGenX9_eq c H pd idOf W χe _ (fun _ => rfl) hj hd

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll.totals9_readK
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot.compGenX9_rho
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot.compGenX9_rhoS
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot.compGenX9_eq_closed
