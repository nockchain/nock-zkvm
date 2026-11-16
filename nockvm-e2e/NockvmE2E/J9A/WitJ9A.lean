/-
`DatumOK9A` (and `AccJ9A`) at the chips-ABSENT record of nock's `Batch4882.complJ9A_absent_toy`
(`*[(p+5) [0 1]]`, empty registry, `axOn = spOn = false`): the J-9 A twin of `J8/InstJ8D.datumOK_witness`.
The datum is `dT` with rows widened to `RealIOJ9A.cornerC9` (`acceptsJ9A_mono_rows`), `g = 2^31`, and the union domain
`{ω^i : i < 2^26}` with `ω` the common orbit generator (every table of `PbOf` has nodes `ω^i`, `i < n`, and `n ≤ 2^26`).
-/
import NockvmE2E.J9A.InstJ9AWit

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.J9A.WitJ9A

open NockvmE2E.J9A.InstJ9A
open NockvmE2E.J9A.InstJ9AWit (dT)
open NockvmE2E.J8.InstJ8 (P Φ0)
open Nock.Walk (bfsForest)
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL (fuelChip)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.SVFrame (Coins)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (censusG claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (jCount)
open Nock.RedTeam.Batch4856
open Nock.RedTeam.Batch4882
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAbsent (pubA msgA trA rowsA)
open Nock.TraceGenExe
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8

noncomputable section

/-- the toy's table sizes are `≤ 2^26` (`h31_9`'s proof, at the tighter bound) -/
theorem sizes26 : ∀ x ∈ sizesJ8 D9T, x ≤ 2 ^ 26 := by
  intro x hx
  simp only [sizesJ8, nVOf, preads9, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hW : (Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows D9T.cells D9T.reads).length ≤ 2 ^ 26 := by
    rw [reads9]
    have := Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows_length_le D9T.cells []
    simp [Nock.NockVMROM.Thm54.VclL.pathReads] at this
    rw [cells9] at this ⊢
    omega
  have hB : (bfsForest [D9T.t]).length = 1 := by
    show (bfsForest [t9]).length = 1
    rw [bfs9]; rfl
  have hC : D9T.cells.length = 1 := by rw [cells9]; rfl
  have hA := acs9_len
  have hJ : D9T.jrows.length = 0 := by rw [jrows9]; rfl
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- the datum of the witness: `dT` (chips absent) with the rows widened to `RealIOJ9A.cornerC9`, `g = 2^31`, and the union domain
`{ω^i : i < 2^26}`, `ω` the common orbit generator -/
def dW : Datum9A := { dT with r := RealIOJ9A.cornerC9, g := 2 ^ 31, hN := 2 ^ 26, ω := B9T.Pb.orbit.ω }

theorem nodes_sub {n : ℕ} (nodes : Fin n → ZMod P) (ω : ZMod P) (h : ∀ i, nodes i = ω ^ (i : ℕ)) (hn : n ≤ 2 ^ 26) :
    Nock.Framework.rowNodeSet nodes ⊆ (Finset.range (2 ^ 26)).image (fun i => ω ^ i) := by
  intro x hx
  unfold Nock.Framework.rowNodeSet at hx
  obtain ⟨i, -, rfl⟩ := (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) nodes Finset.univ x).mp hx
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le i.isLt hn), (h i).symm⟩

theorem n26 : B9T.Pb.n ≤ 2 ^ 26 :=
  (sizes26 ((bfsForest [D9T.t]).length) (by simp [sizesJ8]) : ((bfsForest [D9T.t]).length) ≤ 2 ^ 26)
theorem nC26 : B9T.Pb.nC ≤ 2 ^ 26 :=
  (sizes26 (D9T.cells.length) (by simp [sizesJ8]) : (D9T.cells.length) ≤ 2 ^ 26)
theorem nW26 : B9T.Pb.nW ≤ 2 ^ 26 :=
  (sizes26 ((Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows D9T.cells D9T.reads).length) (by simp [sizesJ8]) : ((Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows D9T.cells D9T.reads).length) ≤ 2 ^ 26)
theorem nJ26 : B9T.Pb.nJ ≤ 2 ^ 26 :=
  (sizes26 (D9T.jrows.length) (by simp [sizesJ8]) : (D9T.jrows.length) ≤ 2 ^ 26)
theorem nA26 : B9T.Pb.nA ≤ 2 ^ 26 :=
  (sizes26 (D9T.acs.length) (by simp [sizesJ8]) : (D9T.acs.length) ≤ 2 ^ 26)
theorem nV26 : B9T.Pb.nV ≤ 2 ^ 26 :=
  (sizes26 (nVOf D9T) (by simp [sizesJ8]) : (nVOf D9T) ≤ 2 ^ 26)

theorem hHt_W : ∀ t, HtOf9 dW t ⊆ HdomOf9 dW := by
  intro t
  fin_cases t
  · exact nodes_sub _ _ (fun i => rfl) n26
  · exact nodes_sub _ _ (fun i => rfl) nC26
  · exact nodes_sub _ _ (fun i => rfl) nW26
  · exact nodes_sub _ _ (fun i => rfl) nJ26
  · exact nodes_sub _ _ (fun i => rfl) nA26
  · exact nodes_sub _ _ (fun i => rfl) nV26
  · exact nodes_sub (n := 1) _ _ (fun i => by
      have : i = 0 := Subsingleton.elim _ _
      subst this; rfl) (by decide)
  · exact nodes_sub (n := 1) _ _ (fun i => by
      have : i = 0 := Subsingleton.elim _ _
      subst this; rfl) (by decide)

theorem regs9 : D9T.regs = [] := by
  show (List.map Prod.fst D9T.calls).dedup = []
  rw [calls9]; rfl

theorem nJ0 : B9T.Pb.nJ = 0 := by
  show D9T.jrows.length = 0
  rw [jrows9]; rfl

theorem jCount0 {n : ℕ} (h : n = 0) (es : List (Nock.Jet.ChipJ8.Kd × List Nock.Jet.ChipJ8.KE))
    (lay : Fin n → Nock.Jet.ChipJ8.PRow) : jCount es lay = 0 := by
  subst h; simp [jCount]

theorem hreg_W : (censusG dW.Pb.toPubJ8 dW.c).length + 6 ≤ 2 ^ 31 := by
  have h1 : dW.Pb.toPubJ8.regs.length = 0 := by
    show D9T.regs.length = 0
    rw [regs9]; rfl
  have h2 : (claimCells dW.c).length ≤ 3 := (List.length_filter_le _ _).trans (by simp)
  unfold censusG
  simp only [List.length_append, List.length_map, h1]
  omega

/-- the numeric fields of `DatumOK9A` at `dW` -/
theorem datumOK_witness9 : DatumOK9A dW := by
  have hrc : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n _
  refine ⟨Nock.Jet.VerifiedRegistry.empty.faithful, ?_, ?_, le_rfl, le_rfl, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    hreg_W, hHt_W, by norm_num [dW]⟩
  · rw [Nock.TraceGenExe.KC_card, Nock.NockVMROM.Thm54.VclL.Events.cK_eq]
  · show RowsLe EncInjJ8.cornerC EncInjJ8.cornerC
    simp [RowsLe]
  · intro x hx
    rw [hrc] at hx
    unfold lenL
    rw [if_pos hx]
    show 1 ≤ 2 ^ 31
    norm_num
  · show 2 * fuelChip ≤ EncInjJ8.cornerC.leaves
    simp [EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]
  · show B9T.Pb.nA + 2 ≤ EncInjJ8.cornerC.maxlen
    have := nA26
    show _ ≤ 2 ^ 31
    omega
  · exact (n26.trans (by norm_num [dW, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))
  · exact (nC26.trans (by norm_num [dW, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))
  · exact (nW26.trans (by norm_num [dW, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))
  · exact (nA26.trans (by norm_num [dW, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))
  · exact (nV26.trans (by norm_num [dW, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))
  · exact (nC26.trans (by norm_num [dW, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))

theorem rows_eq : B9T.rows = Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp.canonRows B9T.Pb
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.extraRows := rfl

theorem acc_W : ∃ (χ : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC) (M : MsgJ9A' P KC deltaF) (tr : TrJ9A (ZMod P)), AccJ9A dW χ M tr := by
  obtain ⟨-, χ, h⟩ := complJ9A_absent_toy_figure
  have hj := nJ0
  have n1 := n26; have n2 := nC26; have n3 := nW26; have n4 := nJ26; have n5 := nA26; have n6 := nV26
  have hg : B9T.g ≤ 2 ^ 31 := by
    show Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp.canonG B9T.Pb ≤ 2 ^ 31
    unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp.canonG
    have h1 : B9T.Pb.regs.length = 0 := by show D9T.regs.length = 0; rw [regs9]; rfl
    rw [h1, jCount0 hj, jCount0 hj]
    have : (2 : ℕ) ^ 26 ≤ 2 ^ 31 := by norm_num
    omega
  refine ⟨χ, _, _, acceptsJ9A_mono_rows h ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hg⟩ <;>
    simp only [rows_eq, rowsA, dW, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31,
      Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp.canonRows, Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.extraRows,
      jCount0 hj] <;>
    omega

/-- **`j9a_absent_witness`**: `DatumOK9A`, `StmtP9A`, `PubP9A` and `AccJ9A` hold together at the chips-absent toy record
(`axOn = spOn = false`), widened to `cornerC9`: the J-9 A twin of `InstJ8D.datumOK_witness`. -/
theorem j9a_absent_witness :
    ∃ (χ : Nock.NockVMROM.Thm54.SVFrame.Coins Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8.frameJ8 KC)
      (M : MsgJ9A' P KC deltaF) (tr : TrJ9A (ZMod P)),
      DatumOK9A dW ∧ StmtP9A dW ∧ AccJ9A dW χ M tr ∧
      PubP9A dW χ (M, fun j => ClaimJ9.pubVJ9 deltaF powerBasis3 dW.c M.m M.ρ M.ρS χ j) := by
  obtain ⟨χ, M, tr, h⟩ := acc_W
  exact ⟨χ, M, tr, datumOK_witness9, (stmt_pub_of_acc9 dW χ M tr h).1, h, (stmt_pub_of_acc9 dW χ M tr h).2⟩

end

end NockvmE2E.J9A.WitJ9A

#print axioms NockvmE2E.J9A.WitJ9A.datumOK_witness9
#print axioms NockvmE2E.J9A.WitJ9A.acc_W
#print axioms NockvmE2E.J9A.WitJ9A.j9a_absent_witness
