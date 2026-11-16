/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHGoodCoin.lean

-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff

noncomputable section

/-- `K3.toK` as an equivalence. -/
def toKEquiv : K3 ≃ KC := Equiv.ofBijective K3.toK ⟨K3.toK_injective, K3.toK_surjective⟩

/-- `K3` is finite, through `toK`. -/
instance instFintypeK3 : Fintype K3 := Fintype.ofEquiv KC toKEquiv.symm

/-- `KC` has `VclL.Events.cK` elements. -/
theorem card_KC : Fintype.card KC = VclL.Events.cK := by
  rw [Nock.TraceGenExe.KC_card, Nock.NockVMROM.Thm54.VclL.Events.cK_eq]

/-- `toχ` is a bijection onto `Coins frameJ8 KC`. -/
def toχEquiv : CoinsE ≃ Coins frameJ8 KC := Equiv.piCongrRight fun _ => toKEquiv

/-- `toχEquiv` acts as `toχ`. -/
theorem toχEquiv_apply (χe : CoinsE) : toχEquiv χe = toχ χe := rfl

/-- `CoinsE` and `Coins frameJ8 KC` have the same cardinality. -/
theorem card_coinsE : Fintype.card CoinsE = Fintype.card (Coins frameJ8 KC) :=
  Fintype.card_congr toχEquiv

open Classical in
/-- Transfer of a predicate's bad count along `toχ`. -/
theorem bad_card_eq (G : Coins frameJ8 KC → Prop) :
    (Finset.univ.filter fun χe : CoinsE => ¬ G (toχ χe)).card =
      (Finset.univ.filter fun χ : Coins frameJ8 KC => ¬ G χ).card := by
  refine Finset.card_bij (fun χe _ => toχ χe) ?_ ?_ ?_
  · intro a ha; simpa using ha
  · intro a _ b _ h; exact toχEquiv.injective h
  · intro χ hχ
    refine ⟨toχEquiv.symm χ, ?_, ?_⟩
    · have e : toχ (toχEquiv.symm χ) = χ := toχEquiv.apply_symm_apply χ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [e]; simpa using hχ
    · exact toχEquiv.apply_symm_apply χ

section Final
variable [Fact (ringChar (ZMod P)).Prime] [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
  (hgen : genX Rg.R fuel s f = some (t, r))

open Classical in
/-- The three facts, from `complJ9A_closed`, at the global instance. -/
theorem goodCoin_core (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Example.RtG hgen))
    (hcid : ComplJ8Jet.CalledIds t = ∅) :
    let B := ComplJ9ARun.BRun9A deltaF powerBasis3 Example.RtG hgen hpG h31A
    (((Finset.univ.filter fun χe : CoinsE => ¬ B.Good (toχ χe)).card : ℚ) /
        Fintype.card CoinsE ≤ B.epsC) ∧
      B.epsC < 1 / 2 ^ 120 ∧ ∃ χe : CoinsE, B.Good (toχ χe) := by
  intro B
  have hcl := ComplJ9AClosed.complJ9A_closed deltaF powerBasis3 Example.RtG hgen hpG hax9 hop5 hleaf hwalk9
    hwalkA (fun id hid => by rw [hcid] at hid; simp at hid) (fun id hid => by rw [hcid] at hid; simp at hid) h31A
  obtain ⟨-, h2, -, -, h5⟩ := hcl
  obtain ⟨hlt, -⟩ := h5 card_KC
  have h1 : (((Finset.univ.filter fun χe : CoinsE => ¬ B.Good (toχ χe)).card : ℚ) /
        Fintype.card CoinsE ≤ B.epsC) := by
    rw [bad_card_eq B.Good, card_coinsE]; exact h2
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
theorem badE_le (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Example.RtG hgen))
    (hcid : ComplJ8Jet.CalledIds t = ∅) :
    let B := ComplJ9ARun.BRun9A deltaF powerBasis3 Example.RtG hgen hpG h31A
    ((Finset.univ.filter fun χe : CoinsE => ¬ B.Good (toχ χe)).card : ℚ) / Fintype.card CoinsE ≤ B.epsC := by
  obtain rfl : iA = GenPortJ9AHonest.algG := Subsingleton.elim _ _
  exact (goodCoin_core hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hcid).1

theorem epsC_lt (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Example.RtG hgen))
    (hcid : ComplJ8Jet.CalledIds t = ∅) :
    (ComplJ9ARun.BRun9A deltaF powerBasis3 Example.RtG hgen hpG h31A).epsC < 1 / 2 ^ 120 := by
  obtain rfl : iA = GenPortJ9AHonest.algG := Subsingleton.elim _ _
  exact (goodCoin_core hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hcid).2.1

theorem exists_good_coinE (hpG : P = Nock.Atoms.p)
    (hax9 : ComplJ9ABinders.ProgAxOK9A P t) (hop5 : ComplJ8.ProgOp5OK P t)
    (hleaf : ComplJ8Walk.RootsLeafOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).roots)
    (hwalk9 : ComplJ9ABinders.WalkDepthOK9A (ComplJ8Data.rowsOfT t))
    (hwalkA : ComplJ8Walk.WalkDepthOK (ComplJ8Data.j8DataOf P Rg Example.RtG hgen).preads)
    (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf P Rg Example.RtG hgen))
    (hcid : ComplJ8Jet.CalledIds t = ∅) :
    ∃ χe : CoinsE, (ComplJ9ARun.BRun9A deltaF powerBasis3 Example.RtG hgen hpG h31A).Good (toχ χe) := by
  obtain rfl : iA = GenPortJ9AHonest.algG := Subsingleton.elim _ _
  exact (goodCoin_core hgen hpG hax9 hop5 hleaf hwalk9 hwalkA h31A hcid).2.2

end Inst
end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoin
#print axioms badE_le
#print axioms epsC_lt
#print axioms exists_good_coinE
end Axioms
