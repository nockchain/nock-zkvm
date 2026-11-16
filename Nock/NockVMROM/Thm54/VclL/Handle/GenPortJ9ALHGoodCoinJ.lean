/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9ALHGoodCoinJ.lean

  **A good executable coin exists for the J-9 AL honest record** (twin of `GenPortJ9AHGoodCoinJ`).

  The J-9 AL capstone `ComplJ9ALClosed.complJ9AL_closed` is finished in another tree and is NOT imported here.
  Its conclusion enters as two NAMED HYPOTHESES on an abstract honest record `B : HonestJ9AL ..`:
  * `hfrac` = the second conjunct of `complJ9AL_closed` (bad fraction `≤ B.epsC`);
  * `hlt`   = the `B.epsC < 1 / 2 ^ 120` half of its fifth conjunct (valid at `Fintype.card K = cK`, which
    `card_KC` supplies at `KC`).
  Everything else is the J9A twin's argument: transfer along `toχ : CoinsE ≃ Coins frameJ8 KC`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALObl

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHGoodCoinJ

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALObl (HonestJ9AL)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin (toχEquiv)

noncomputable section

open Classical in
/-- **`exists_good_coinEJL`**: from the capstone's bad-fraction bound and `epsC < 2⁻¹²⁰`, an executable coin
`χe : CoinsE` whose `toχ` is good for the honest record `B`. -/
theorem exists_good_coinEJL {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
    (B : HonestJ9AL P KC deltaF Rg fuel s f r)
    (hfrac : (((Finset.univ.filter fun χ : Coins frameJ8 KC => ¬ B.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 KC) ≤ B.epsC))
    (hlt : B.epsC < 1 / 2 ^ 120) : ∃ χe : CoinsE, B.Good (toχ χe) := by
  have h1 : (((Finset.univ.filter fun χe : CoinsE => ¬ B.Good (toχ χe)).card : ℚ) /
      Fintype.card CoinsE ≤ B.epsC) := by
    rw [GenPortJ9AHGoodCoin.bad_card_eq B.Good, GenPortJ9AHGoodCoin.card_coinsE]; exact hfrac
  by_contra hno
  push_neg at hno
  have hall : (Finset.univ.filter fun χe : CoinsE => ¬ B.Good (toχ χe)) = Finset.univ := by
    ext χe; simp [hno χe]
  have hc : Fintype.card CoinsE ≠ 0 := Fintype.card_ne_zero
  rw [hall, Finset.card_univ, div_self (by exact_mod_cast hc)] at h1
  have hge : (1 : ℚ) / 2 ^ 120 < 1 := by norm_num
  linarith

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHGoodCoinJ

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9ALHGoodCoinJ
#print axioms exists_good_coinEJL
end Axioms
