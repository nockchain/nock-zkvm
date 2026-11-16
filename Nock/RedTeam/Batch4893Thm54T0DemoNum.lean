import Nock.RedTeam.Batch4892Thm54T0Demo
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHGoodCoinJ
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ProbJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8

set_option autoImplicit false

namespace Nock.RedTeam.Batch4893

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.V1J8.Exe (toχ)
open Nock.Jet.Autogen (Tpl HasTy compile Ex Ty)
open Nock.TraceGenExe (KC deltaF powerBasis3)
open Nock.RedTeam.Batch4892
open Nock.NockVMROM.Thm54.VclL (fuelChip)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)

noncomputable section

/-! ## 7. `exists_good_coinEJ` -/

theorem BN_faithful : RgN.R.Faithful := RgN.faithful

theorem hC_N : Nock.NockVMROM.Thm54.VclL.Handle.CheckedRegistry.CompiledBy pG RgN RtN := CN.compiledBy

/-- **`good_coin_N`: the natural-number-typed jet run has a good coin.**  For the run `complJ9A_closed_of_N` is about
(the compiled template `TN` on the subject `[3 (p+5)]`), there is a coin vector `χe` at which the run's honest
record is good (`Good`). -/
theorem good_coin_N : ∃ χe,
    BN.Good (toχ χe) :=
  GenPortJ9AHGoodCoinJ.exists_good_coinEJ RtN genN rfl hax9N hop5N hleafN hwalk9N hwalkAN h31N hC_N

/-! ## 9. Non-vacuity of `probJ9A_final_clean`'s numeric binders at the run -/

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHStaticJ (jCount_le ents0T_one ents1T_one ents2T_one ents3_one
  entsX_one)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (jCount)
open Nock.Jet.ChipJ8 (ents0T ents1T ents2T ents3 entsX)

/-- The rows of the run with the census readout's free fields (`Λ`, `leaves`, `maxlen`); `BudJ9A` does not read them. -/
abbrev rN' : RealIOJ9A.RowsJ9A :=
  { BN.rows with
    Λ := fuelChip
    leaves := 2 * fuelChip
    maxlen := 2 ^ 31 }

theorem regsN : DD.regs = [7] := by
  show (List.map Prod.fst DD.calls).dedup = _
  rw [callsN]; rfl

theorem nVN1 : nVOf DA = 1 := by
  unfold nVOf; rw [preadsN9]; simp

/-- **`numerics_N`: the numeric hypotheses of the J-9 A soundness bound are satisfied at the natural-number-typed
jet run.**  For the run of `complJ9A_closed_of_N`, there is a coin `χ` at which `AcceptsJ9A` accepts, and at the same
time: the registry is faithful, `p` is the Goldilocks prime, `|K| = cK`, the row counts are within the corner
bounds and the axis and split tables within `2^31`, the length, leaf and census bounds hold, `g ≤ 2^31`, and
every public size is within the row budget; so `probJ9A_final_clean`'s bound applies to this run non-vacuously. -/
theorem numerics_N : ∃ χ : Coins frameJ8 KC,
    AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 BN.Pb RgN.R (ComplJ8.cJ sN fJ rN) χ (BN.M χ) (BN.tr χ) rN' BN.g ∧
    RgN.R.Faithful ∧ pG = Nock.Atoms.p ∧ Fintype.card KC = VclL.Events.cK ∧
    RowsLe rN'.toRowsJ8 EncInjJ8.cornerC ∧ rN'.AX ≤ 2 ^ 31 ∧ rN'.SP ≤ 2 ^ 31 ∧
    (∀ x < ringChar (ZMod pG), Nock.Atoms.lenL x ≤ rN'.maxlen) ∧
    2 * fuelChip ≤ rN'.leaves ∧
    BN.Pb.nA + 2 ≤ rN'.maxlen ∧ BN.g ≤ 2 ^ 31 ∧
    BN.Pb.n ≤ rN'.N ∧ BN.Pb.nC ≤ rN'.D ∧ BN.Pb.nW ≤ rN'.W ∧ BN.Pb.nA ≤ rN'.A ∧ BN.Pb.nV ≤ rN'.AW ∧
    BN.Pb.nC ≤ 2 ^ 31 ∧
    (AcceptsJ8P.censusG BN.Pb.toPubJ8 (ComplJ8.cJ sN fJ rN)).length + 6 ≤ 2 ^ 31 := by
  obtain ⟨-, χ, hacc⟩ := complJ9A_N_figure
  have h31 := ComplJ9AClosed.rowsLe31A_runA deltaF powerBasis3 RtN genN rfl h31N
  obtain ⟨⟨hn, hC, hW, hJ, hA, hV⟩, hX, hS⟩ := h31
  have fJ' : BN.Pb.nJ ≤ 2 ^ 20 := jrowsN_len
  have fn : BN.Pb.n = 2 := N9N
  have fnX : BN.Pb.nX = 1 := nXN
  have fnV : BN.Pb.nV = 1 := nVN1
  have fnA : BN.Pb.nA ≤ 3 := acsN_len
  have freg : BN.Pb.regs.length = 1 := by
    show DD.regs.length = 1
    rw [regsN]; rfl
  have j0 := jCount_le ents0T ents0T_one BN.Pb.lay
  have j1 := jCount_le ents1T ents1T_one BN.Pb.lay
  have j2 := jCount_le ents2T ents2T_one BN.Pb.lay
  have j3 := jCount_le ents3 ents3_one BN.Pb.lay
  have jX := jCount_le entsX entsX_one BN.Pb.lay
  have hg : BN.g ≤ 2 ^ 31 := by
    show ComplJ8Comp.canonG BN.Pb.toPubJ8 ≤ 2 ^ 31
    unfold ComplJ8Comp.canonG
    have : (BN.Pb.toPubJ8).n = 2 := fn
    have : (BN.Pb.toPubJ8).regs.length = 1 := freg
    have : (BN.Pb.toPubJ8).nJ ≤ 2 ^ 20 := fJ'
    omega
  refine ⟨χ, ?_, BN_faithful, rfl, card_KC, ?_, ?_, ?_, ?_, ?_, ?_, hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hb := hacc.hbud
    exact { hacc with
      hbud := { x1 := hb.x1, x2 := hb.x2, p1 := hb.p1, p2 := hb.p2, s1 := hb.s1, s2 := hb.s2 }
      hbudV := hacc.hbudV }
  · refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl, le_rfl⟩
    · show BN.Pb.n + BN.Pb.nX ≤ 2 ^ 31; omega
    · exact hC
    · exact hW
    · exact hA
    · exact hV
    · exact hJ
    · show BN.Pb.nA ≤ 2 ^ 31; omega
    · show 0 ≤ 2 ^ 31; omega
    · show jCount ents2T BN.Pb.lay + jCount ents3 BN.Pb.lay ≤ 2 ^ 31; omega
    · show BN.Pb.nA ≤ 2 ^ 31; omega
    · show 2 * BN.Pb.nV ≤ 2 ^ 31; omega
    · show jCount entsX BN.Pb.lay ≤ 2 ^ 31; omega
  · show BN.Pb.nX ≤ 2 ^ 31; omega
  · show BN.Pb.nS ≤ 2 ^ 31; omega
  · intro x hx
    rw [ZMod.ringChar_zmod_n] at hx
    show Nock.Atoms.lenL x ≤ 2 ^ 31
    unfold Nock.Atoms.lenL
    rw [if_pos (by simpa [Nock.Atoms.p, pG, Nock.Field.p] using hx)]
    omega
  · exact le_rfl
  · show BN.Pb.nA + 2 ≤ 2 ^ 31; omega
  · show BN.Pb.n ≤ BN.Pb.n + BN.Pb.nX; omega
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact hC
  · have h3 : (AcceptsJ8P.claimCells (ComplJ8.cJ sN fJ rN)).length ≤ 3 := by
      unfold AcceptsJ8P.claimCells
      refine (List.length_filter_le _ _).trans ?_
      simp
    have : (AcceptsJ8P.censusG BN.Pb.toPubJ8 (ComplJ8.cJ sN fJ rN)).length =
        BN.Pb.regs.length + (AcceptsJ8P.claimCells (ComplJ8.cJ sN fJ rN)).length := by
      simp [AcceptsJ8P.censusG]
    omega

end
end Nock.RedTeam.Batch4893

#print axioms Nock.RedTeam.Batch4893.good_coin_N
#print axioms Nock.RedTeam.Batch4893.numerics_N
