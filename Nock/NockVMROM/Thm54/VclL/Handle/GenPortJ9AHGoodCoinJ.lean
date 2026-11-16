/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoinJ.lean

  **G1E-P7: a good executable coin exists at any checked registry (no `hcid`, no `RtG`).**
  Same proofs as `GenPortJ9AHGoodCoin`, through `ComplClosedChecked.complJ9A_closed_of`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin
import Nock.NockVMROM.Thm54.VclL.Handle.ComplClosedChecked
import Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff

noncomputable section

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin (toχEquiv)

section Final
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
  (hgen : genX Rg.R fuel s f = some (t, r))

open Classical in
/-- The three facts, from `complJ9A_closed`, at the global instance. -/
theorem goodCoin_coreJ (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Rt hgen))
    (hC : CheckedRegistry.CompiledBy P Rg Rt) :
    let B := ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A
    (((Finset.univ.filter fun χe : CoinsE => ¬ B.Good (toχ χe)).card : ℚ) /
        Fintype.card CoinsE ≤ B.epsC) ∧
      B.epsC < 1 / 2 ^ 120 ∧ ∃ χe : CoinsE, B.Good (toχ χe) := by
  intro B
  have hcl := ComplClosedChecked.complJ9A_closed_of deltaF powerBasis3 Rt hgen hpG hax9 hop5 hleaf hwalk9
    hwalkA hC h31A
  obtain ⟨-, h2, -, -, h5⟩ := hcl
  obtain ⟨hlt, -⟩ := h5 GenPortJ9AHGoodCoin.card_KC
  have h1 : (((Finset.univ.filter fun χe : CoinsE => ¬ B.Good (toχ χe)).card : ℚ) /
        Fintype.card CoinsE ≤ B.epsC) := by
    rw [GenPortJ9AHGoodCoin.bad_card_eq B.Good, GenPortJ9AHGoodCoin.card_coinsE]; exact h2
  refine ⟨h1, hlt, ?_⟩
  by_contra hno
  push_neg at hno
  have hall : (Finset.univ.filter fun χe : CoinsE => ¬ B.Good (toχ χe)) = Finset.univ := by
    ext χe; simp [hno χe]
  have hc : Fintype.card CoinsE ≠ 0 := Fintype.card_ne_zero
  rw [hall, Finset.card_univ, div_self (by exact_mod_cast hc)] at h1
  have hge : (1 : ℚ) / 2 ^ 120 < 1 := by norm_num
  linarith

section Inst
variable [iA : Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod P) KC deltaF))]

open Classical in
theorem badE_leJ (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Rt hgen))
    (hC : CheckedRegistry.CompiledBy P Rg Rt) :
    let B := ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A
    ((Finset.univ.filter fun χe : CoinsE => ¬ B.Good (toχ χe)).card : ℚ) / Fintype.card CoinsE ≤ B.epsC := by
  obtain rfl : iA = GenPortJ9AHonest.algG := Subsingleton.elim _ _
  exact (goodCoin_coreJ Rt hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hC).1

theorem epsC_ltJ (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Rt hgen))
    (hC : CheckedRegistry.CompiledBy P Rg Rt) :
    (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).epsC < 1 / 2 ^ 120 := by
  obtain rfl : iA = GenPortJ9AHonest.algG := Subsingleton.elim _ _
  exact (goodCoin_coreJ Rt hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hC).2.1

theorem exists_good_coinEJ (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Rt hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Rt hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Rt hgen))
    (hC : CheckedRegistry.CompiledBy P Rg Rt) :
    ∃ χe : CoinsE, (ComplJ9ARun.BRun9A deltaF powerBasis3 Rt hgen hpG h31A).Good (toχ χe) := by
  obtain rfl : iA = GenPortJ9AHonest.algG := Subsingleton.elim _ _
  exact (goodCoin_coreJ Rt hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hC).2.2

end Inst
end Final
end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ
#print axioms goodCoin_coreJ
#print axioms badE_leJ
#print axioms epsC_ltJ
#print axioms exists_good_coinEJ
end Axioms
