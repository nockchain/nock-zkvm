/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHCoin.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (W9 idOfA ρA ρSA pubCA mA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeAll
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AComputeTot

/-- **`hchi_toχ`**: the compute challenge vector of `toχ χe` is `chalE χe`. -/
theorem hchi_toχ (χe : CoinsE) :
    VerJ8.chalVJ8 powerBasis3 (toχ χe) = Example.chalE χe :=
  (Nock.V1J8.Check.chalVJ8_eq χe).trans rfl

/-- The compute coin limbs: `chalE (3q + k)` is limb `k` of the `q`-th compute coin. -/
theorem chalE_limb (χe : CoinsE) (q : ℕ) (hq : q < 6) (k : Fin 3) :
    Example.chalE χe (3 * q + (k : ℕ)) = limbZ (coinHQE χe q) k := by
  have hk := k.2
  have h1 : 3 * q + (k : ℕ) < 18 := by omega
  have h2 : (3 * q + (k : ℕ)) / 3 = q := by omega
  have h3 : (3 * q + (k : ℕ)) % 3 = k := by omega
  unfold Example.chalE chalVJ8E
  rw [if_pos h1, h2, h3]
  fin_cases k <;> rfl

theorem αC0_toχ (χe : CoinsE) :
    InhabJ8Comp.αC0 powerBasis3 (toχ χe) = K3.toK (χe ⟨13, by decide⟩) := by
  unfold InhabJ8Comp.αC0
  rw [hchi_toχ]
  apply Nock.NockVMROM.Thm54.VclL.Compute.LogUp.limbVal_eq_of_coords
  intro k
  rw [coord_K _ _ k.2]
  have := chalE_limb χe 2 (by norm_num) k
  show _ = Example.chalE χe (Nock.NockVMROM.Thm54.VclL.Handle.ChipH.chalAlphaW + (k : ℕ))
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ChipH.chalAlphaW
  rw [show 6 + (k : ℕ) = 3 * 2 + (k : ℕ) by norm_num, this]
  rfl

theorem γC0_toχ (χe : CoinsE) :
    InhabJ8Comp.γC0 powerBasis3 (toχ χe) = K3.toK (χe ⟨14, by decide⟩) := by
  unfold InhabJ8Comp.γC0
  rw [hchi_toχ]
  apply Nock.NockVMROM.Thm54.VclL.Compute.LogUp.limbVal_eq_of_coords
  intro k
  rw [coord_K _ _ k.2]
  have := chalE_limb χe 3 (by norm_num) k
  show _ = Example.chalE χe (Nock.NockVMROM.Thm54.VclL.Handle.ChipH.chalGammaW + (k : ℕ))
  unfold Nock.NockVMROM.Thm54.VclL.Handle.ChipH.chalGammaW
  rw [show 9 + (k : ℕ) = 3 * 3 + (k : ℕ) by norm_num, this]
  rfl

/-- The executable claim message is the honest `mA`'s underlying `mCOf`. -/
theorem mOf_eq_mCOf (c : P8PublicClaim) (H : Noun → ℕ × ℕ) :
    Nock.V1J8.Gen.mOf c H = Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp.mCOf H c := rfl

section Pub
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **`pubFinal9_eq_pubCA`**: the generator's final publics at `χe` are the honest twin compute publics at `toχ χe`. -/
theorem pubFinal9_eq_pubCA (χe : CoinsE) :
    pubFinal9 (cJ s f r) (j9aDataOf P Rg Rt hgen).H (j9aDataOf P Rg Rt hgen).pd (idOfA (p := P) Rt hgen)
        (W9 t) χe =
      pubCA deltaF powerBasis3 Rt hgen (toχ χe) := by
  unfold pubFinal9 pubCA
  rw [mOf_eq_mCOf]
  rw [← Nock.V1J9.Check9.pubVJ9_eq]
  congr 1
  · funext i
    exact compGenX9_rho Rt hgen (toχ χe) χe (hchi_toχ χe) _ i
  · exact compGenX9_rhoS Rt hgen (toχ χe) χe (hchi_toχ χe) _

end Pub

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin.hchi_toχ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin.αC0_toχ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin.γC0_toχ
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin.mOf_eq_mCOf
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin.pubFinal9_eq_pubCA

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCoin
