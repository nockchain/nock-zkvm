/-
the JOINT datum witness `∃ d, DatumOK d ∧ StmtP d` at nock's single-orbit
toy datum `BT := ComplJ8Closed.BRunA … ` of `Nock.RedTeam.Batch4842.complJ8_closed_toy` (`*[[0 0] [0 1]]`, empty registry).
`d.Pb = BT.Pb` (one orbit); `d.r = cornerC` (BT's own `rows` has the free fields `Λ, leaves, maxlen = 0`, which
`DatumOK` rules out, so the rows are widened by `acceptsJ8V_mono_rows`, which is the honest fact: `AcceptsJ8V` reads `r, g` only
through upper-bound budget fields).
-/
import NockvmE2E.J8.InstJ8
import Nock.RedTeam.Batch4842Thm54J8ComplClose
import Nock.RedTeam.Batch4775Thm54NVJetRegime

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.J8.WitJ8

open NockvmE2E.J8.InstJ8
open Nock.RedTeam.Batch4842
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (jCount)
open Nock.Jet.ChipJ8 (PRow)
open NockvmE2E.Rap NockvmE2E.Succ
open Nock.TraceGenExe
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (corner31)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of

noncomputable section

/-- an empty layout has no keys -/
theorem jCount_zero (es : List (Nock.Jet.ChipJ8.Kd × List Nock.Jet.ChipJ8.KE)) {n : ℕ} (lay : Fin n → PRow) (h : n = 0) :
    jCount es lay = 0 := by
  subst h; simp [jCount]

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of (PbOf nVOf)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (cornerC)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ)

/-! ## 1. the table sizes of the toy datum -/

theorem sz_n : BT.Pb.n = 1 := by
  show (Nock.Walk.bfsForest [DT.t]).length = 1
  show (Nock.Walk.bfsForest [InhabJ8Base.t0]).length = 1
  rw [InhabJ8Comp.bfs0]; rfl

theorem sz_nC : BT.Pb.nC = 2 := by
  show DT.cells.length = 2
  rw [(ComplJ8Data.toy_cells_H RtT).1]; rfl

theorem sz_nW : BT.Pb.nW ≤ 1 := by
  show (Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows DT.cells DT.reads).length ≤ 1
  have := Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows_length_le DT.cells []
  rw [reads_T]
  simp [Nock.NockVMROM.Thm54.VclL.pathReads] at this
  omega

theorem sz_nJ : BT.Pb.nJ = 0 := by
  show DT.jrows.length = 0
  rw [jrows_T]; rfl

theorem sz_nA : BT.Pb.nA ≤ 2 := by
  show DT.acs.length ≤ 2
  exact acs_T

theorem sz_nV : BT.Pb.nV = 1 := by
  show nVOf DT = 1
  simp [nVOf, preads_T]

theorem regs_nil : BT.Pb.regs = [] := by
  show DT.regs = []
  show (DT.calls.map Prod.fst).dedup = []
  rw [calls_T]; rfl

/-! ## 2. the datum -/

/-- the datum: BT's `Pb` (one orbit), the empty registry, the toy claim, the census-corner rows, `g = 2^31`, the union domain
`{ω^i : i < 2}` of the common orbit's generator -/
def dW : Datum :=
  ⟨BT.Pb, Nock.Jet.VerifiedRegistry.empty.R, cJ InhabJ8Base.s0 InhabJ8Base.f0 InhabJ8Base.s0, cornerC, 2 ^ 31, 2, BT.Pb.orbit.ω⟩

/-- BT's acceptance widened from `BT.rows`/`BT.g` to the census corner `cornerC`/`2^31` -/
theorem acc_dW : ∃ (χ : Coins Φ0 KC) (M : MsgJ8' P KC deltaF) (tr : TrJ8 (ZMod P)),
    AcceptsJ8V deltaF powerBasis3 dW.Pb dW.Rg dW.c χ M tr dW.r dW.g := by
  obtain ⟨-, χ, hχ⟩ := complJ8_closed_toy.2.2.2.2 card_KC
  have h0 := jCount_zero Nock.Jet.ChipJ8.ents2T BT.Pb.lay sz_nJ
  have h1 := jCount_zero Nock.Jet.ChipJ8.ents3 BT.Pb.lay sz_nJ
  have h2 := jCount_zero Nock.Jet.ChipJ8.entsX BT.Pb.lay sz_nJ
  have h3 := jCount_zero Nock.Jet.ChipJ8.ents0T BT.Pb.lay sz_nJ
  have h4 := jCount_zero Nock.Jet.ChipJ8.ents1T BT.Pb.lay sz_nJ
  have hn := sz_n; have hC := sz_nC; have hW := sz_nW; have hA := sz_nA; have hV := sz_nV; have hJ := sz_nJ; have hr : BT.Pb.regs.length = 0 := by rw [regs_nil]; rfl
  refine ⟨χ, BT.M χ, BT.tr χ, Nock.RedTeam.Batch4775.acceptsJ8V_mono_rows deltaF powerBasis3 hχ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  all_goals
    simp only [BT, ComplJ8Closed.BRunA, ComplJ8Of.BOf, ComplJ8Of.honestJ8Of, ComplJ8Comp.canonRows, ComplJ8Comp.canonG,
      cornerC, corner31, dW] at *
  all_goals omega

/-! ## 3. `DatumOK` -/

/-- every table's nodes are `ω^i`, `i < n_t ≤ 2`: inside `{ω^i : i < 2}` -/
theorem rowNodeSet_sub2 {n : ℕ} (hn : n ≤ 2) (ω : ZMod P) (nodes : Fin n → ZMod P) (h : ∀ i, nodes i = ω ^ (i : ℕ)) :
    Nock.Framework.rowNodeSet nodes ⊆ (Finset.range 2).image (fun i => ω ^ i) := by
  classical
  intro x hx
  unfold Nock.Framework.rowNodeSet at hx
  obtain ⟨i, -, rfl⟩ := (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) nodes Finset.univ x).mp hx
  rw [h i]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by have := i.isLt; omega), rfl⟩

theorem datumOK_dW : DatumOK dW := by
  have hn := sz_n; have hC := sz_nC; have hW := sz_nW; have hA := sz_nA; have hV := sz_nV; have hJ := sz_nJ
  have hrl : BT.Pb.regs.length = 0 := by rw [regs_nil]; rfl
  refine ⟨Nock.Jet.VerifiedRegistry.empty.faithful, card_KC, by (show WeightsJ8.RowsLe cornerC cornerC; simp [WeightsJ8.RowsLe]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hrc : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n _
    rw [hrc] at hx
    unfold Nock.Atoms.lenL
    rw [if_pos hx]
    show 1 ≤ 2 ^ 31
    norm_num
  · exact le_refl _
  · show BT.Pb.nA + 2 ≤ 2 ^ 31; omega
  · show 2 ^ 31 ≤ 2 ^ 31; exact le_rfl
  · show BT.Pb.n ≤ 2 ^ 31; omega
  · show BT.Pb.nC ≤ 2 ^ 31; omega
  · show BT.Pb.nW ≤ 2 ^ 31; omega
  · show BT.Pb.nA ≤ 2 ^ 31; omega
  · show BT.Pb.nV ≤ 2 ^ 31; omega
  · show BT.Pb.nC ≤ 2 ^ 31; omega
  · show (censusG BT.Pb (cJ InhabJ8Base.s0 InhabJ8Base.f0 InhabJ8Base.s0)).length ≤ 2 ^ 31
    simp only [censusG, regs_nil, List.map_nil, List.nil_append, List.length_map]
    have : (Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P.claimCells (cJ InhabJ8Base.s0 InhabJ8Base.f0 InhabJ8Base.s0)).length ≤ 3 := by
      unfold Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P.claimCells
      exact (List.length_filter_le _ _).trans (by simp)
    omega
  · intro t
    fin_cases t
    · exact rowNodeSet_sub2 (by show BT.Pb.n ≤ 2; omega) _ _ (fun i => rfl)
    · exact rowNodeSet_sub2 (by show BT.Pb.nC ≤ 2; omega) _ _ (fun i => rfl)
    · exact rowNodeSet_sub2 (by show BT.Pb.nW ≤ 2; omega) _ _ (fun i => rfl)
    · exact rowNodeSet_sub2 (by show BT.Pb.nJ ≤ 2; omega) _ _ (fun i => rfl)
    · exact rowNodeSet_sub2 (by show BT.Pb.nA ≤ 2; omega) _ _ (fun i => rfl)
    · exact rowNodeSet_sub2 (by show BT.Pb.nV ≤ 2; omega) _ _ (fun i => rfl)
  · show 2 ≤ 2 ^ 26; norm_num

/-! ## 4. the joint witness -/

theorem stmt_pub_dW : StmtP dW := by
  obtain ⟨χ, M, tr, hacc⟩ := acc_dW
  exact (stmt_pub_of_acc dW χ M tr hacc).1

/-- **`∃ d, DatumOK d ∧ StmtP d`**, at nock's single-orbit toy datum (`d.Pb = BT.Pb`) -/
theorem jointWitness : ∃ d : Datum, DatumOK d ∧ StmtP d := ⟨dW, datumOK_dW, stmt_pub_dW⟩

/-- the same datum with `PubP` at an accepting coin -/
theorem jointWitnessPub : ∃ (d : Datum) (χ : Coins Φ0 KC) (M : Msg), DatumOK d ∧ StmtP d ∧ PubP d χ M := by
  obtain ⟨χ, M, tr, hacc⟩ := acc_dW
  exact ⟨dW, χ, _, datumOK_dW, (stmt_pub_of_acc dW χ M tr hacc).1, (stmt_pub_of_acc dW χ M tr hacc).2⟩

end

end NockvmE2E.J8.WitJ8

#print axioms NockvmE2E.J8.WitJ8.jointWitness
#print axioms NockvmE2E.J8.WitJ8.jointWitnessPub
