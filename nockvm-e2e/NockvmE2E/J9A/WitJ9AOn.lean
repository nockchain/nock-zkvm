/-
the chips-ON non-vacuity witness, the twin of `WitJ9A.j9a_absent_witness` at nock's
`Batch4883.BA = BRun9A deltaF powerBasis3 RtT genA rfl h31A`, the honest record of `*[sA [[0 AB] [0 AF]]]` (big axis `AB = 2^64-1`
served by the axis chip, field axis `AF = 2^63-1` served by the split chip; `axOn = spOn = true`), widened to `cornerC9`, `g = 2^31`.

* `j9a_on_witness`: `DatumOK9A dOn ∧ StmtP9A dOn ∧ AccJ9A dOn χ M tr ∧ PubP9A dOn … ∧ axOn ∧ spOn`.
* The union domain is `{ω^i : i < 2^26}`, `ω = oA.ω`; the J-8 memory tables use `orbJ8 DA`, whose generator is `oA.ω` because
  `htJ8 DA = htA DA` (the J-8 tables already contain a 3-row table, and the three new tables have ≤ 4 rows).
-/
import NockvmE2E.J9A.InstJ9A
import Nock.RedTeam.Batch4883Thm54J9AComplToy

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.J9A.WitJ9AOn

open NockvmE2E.J9A.InstJ9A
open NockvmE2E.J8.InstJ8 (P Φ0)
open Nock.Walk (bfsForest)
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL (fuelChip)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.SVFrame (Coins)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (censusG claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (sizesA htA orbA oA N9 nXOf nSOf Rows31A)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.TraceGenExe
open Nock.RedTeam.Batch4883 (BA DA DD tA sA fA rA h31A genA acsA_len cellsA_len readsA_lt readsA_len nVA N9A nXA nSA
  walk_bound callsA)

noncomputable section

/-- every table of the run has `≤ 2^26` rows (`h31A`'s proof at the tighter bound; the bounds are the toy's, not exact sizes) -/
theorem sizes26 : ∀ x ∈ sizesA DA, x ≤ 2 ^ 26 := by
  intro x hx
  simp only [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.sizesA, sizesJ8, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  have hB : (bfsForest [DA.t]).length = 3 := by
    show (bfsForest [tA]).length = 3
    rw [Nock.RedTeam.Batch4883.bfsA]; rfl
  have hC : DA.cells.length ≤ 2 ^ 26 := by
    rw [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec.j9aDataOf_cells, Nock.RedTeam.Batch4883.cellsDD]
    have h := Nock.RedTeam.Batch4883.foldl_addCells_len DD.roots []
    have h2 : (DD.roots.map Nock.RedTeam.Batch4883.ncell).sum ≤ 2 ^ 26 := by
      rw [Nock.RedTeam.Batch4883.rootsA]; decide
    simp only [List.length_nil, zero_add] at h
    exact le_trans h h2
  have hW : (Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows DA.cells DA.reads).length ≤ 2 ^ 26 := by
    have := walk_bound DA.cells DA.reads readsA_lt
    have := readsA_len
    omega
  have hJ : DA.jrows.length = 0 := by
    show DD.jrows.length = 0
    rw [Nock.RedTeam.Batch4883.jrowsA]; rfl
  have hA := acsA_len
  have hV : nVOf DA ≤ 2 ^ 26 := by
    unfold nVOf
    split_ifs
    · norm_num
    · refine le_trans (walk_bound _ _ ?_) ?_
      · intro x hx
        rw [Nock.RedTeam.Batch4883.preadsDA] at hx
        simp only [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData.limbReads, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData.limbAxes_lt
          (by rw [Nock.RedTeam.Batch4883.limbsB]; simp) y hy
      · rw [Nock.RedTeam.Batch4883.preadsDA]
        simp [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData.limbReads,
          Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData.limbAxes, Nock.RedTeam.Batch4883.limbsB]
  have hN : N9 DA.t = 3 := N9A
  have hX : nXOf Nock.Field.p DA.acs.length DA.H DA.t = 4 := nXA
  have hS : nSOf Nock.Field.p DA.t = 1 := nSA
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;> omega

/-- the J-8 memory tables' orbit height equals the new chips' (`3 ≤ ` the first J-8 table, the new tables have `≤ 4` rows) -/
theorem ht_eq : htJ8 DA = htA DA := by
  refine le_antisymm (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.htJ8_le_htA DA) ?_
  have h3 : 3 ≤ szJ8 DA := by
    have hB : (bfsForest [DA.t]).length = 3 := by
      show (bfsForest [tA]).length = 3
      rw [Nock.RedTeam.Batch4883.bfsA]; rfl
    have := le_szJ8 DA _ (by simp [sizesJ8] : (bfsForest [DA.t]).length ∈ sizesJ8 DA)
    omega
  have h2 : 2 ≤ htJ8 DA := by
    unfold htJ8
    refine le_trans ?_ (le_max_right _ _)
    exact le_trans (by decide : Nat.clog 2 3 = 2).ge (Nat.clog_mono_right _ h3)
  rw [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.htA_def]
  refine max_le (le_trans (by norm_num) h2) (Nat.clog_le_of_le_pow
    (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.foldr_max_le _ _ ?_))
  intro x hx
  simp only [Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.sizesA, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with hx | rfl | rfl | rfl
  · exact le_two_pow_ht DA hx
  · have : N9 DA.t = 3 := N9A
    rw [this]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ htJ8 DA := Nat.pow_le_pow_right (by norm_num) h2
  · have : nXOf Nock.Field.p DA.acs.length DA.H DA.t = 4 := nXA
    rw [this]
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ htJ8 DA := Nat.pow_le_pow_right (by norm_num) h2
  · have : nSOf Nock.Field.p DA.t = 1 := nSA
    rw [this]
    exact Nat.one_le_two_pow

theorem orbitOf_ω_congr {q : ℕ} [Fact q.Prime] {h h' : ℕ} (e : h = h') (h1 : 1 ≤ h) (h1' : 1 ≤ h')
    (hd : 3 * 2 ^ h ∣ Fintype.card (ZMod q) - 1) (hd' : 3 * 2 ^ h' ∣ Fintype.card (ZMod q) - 1) :
    (orbitOf (F := ZMod q) h h1 hd).ω = (orbitOf (F := ZMod q) h' h1' hd').ω := by
  subst e; rfl

/-- the J-8 memory tables' orbit generator is the new chips' -/
theorem orb_ω (hF : DvdOK DA) (hA : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.DvdA DA) :
    (orbJ8 DA hF).ω = (orbA DA hA).ω :=
  orbitOf_ω_congr ht_eq _ _ _ _

theorem orb_run : (orbJ8 DA (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.hF_run Nock.RedTeam.Batch4842.RtT
    Nock.RedTeam.Batch4883.genA rfl h31A)).ω =
    (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.oA Nock.RedTeam.Batch4842.RtT Nock.RedTeam.Batch4883.genA rfl h31A).ω :=
  orb_ω _ _

/-- **the datum**: `BA.Pb` (axis and split chips present), the empty registry, the toy claim, rows widened to `cornerC9`, `g = 2^31`,
union domain `{ω^i : i < 2^26}`, `ω = oA.ω` -/
def dOn : Datum9A :=
  { Pb := BA.Pb, Rg := Nock.Jet.VerifiedRegistry.empty.R, c := ComplJ8.cJ sA fA rA, r := RealIOJ9A.cornerC9, g := 2 ^ 31,
    hN := 2 ^ 26,
    ω := (Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.oA Nock.RedTeam.Batch4842.RtT Nock.RedTeam.Batch4883.genA rfl h31A).ω }

theorem nodes_sub {n : ℕ} (nodes : Fin n → ZMod P) (ω : ZMod P) (h : ∀ i, nodes i = ω ^ (i : ℕ)) (hn : n ≤ 2 ^ 26) :
    Nock.Framework.rowNodeSet nodes ⊆ (Finset.range (2 ^ 26)).image (fun i => ω ^ i) := by
  intro x hx
  unfold Nock.Framework.rowNodeSet at hx
  obtain ⟨i, -, rfl⟩ := (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) nodes Finset.univ x).mp hx
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le i.isLt hn), (h i).symm⟩

theorem n26 : BA.Pb.n ≤ 2 ^ 26 := sizes26 (N9 DA.t) (by simp [sizesA])
theorem nC26 : BA.Pb.nC ≤ 2 ^ 26 := sizes26 DA.cells.length (by simp [sizesA, sizesJ8])
theorem nW26 : BA.Pb.nW ≤ 2 ^ 26 :=
  sizes26 (Nock.NockVMROM.Thm54.VclL.GenWalk.walkRows DA.cells DA.reads).length (by simp [sizesA, sizesJ8])
theorem nJ26 : BA.Pb.nJ ≤ 2 ^ 26 := sizes26 DA.jrows.length (by simp [sizesA, sizesJ8])
theorem nA26 : BA.Pb.nA ≤ 2 ^ 26 := sizes26 DA.acs.length (by simp [sizesA, sizesJ8])
theorem nV26 : BA.Pb.nV ≤ 2 ^ 26 := sizes26 (nVOf DA) (by simp [sizesA, sizesJ8])
theorem nX26 : BA.Pb.nX ≤ 2 ^ 26 := sizes26 (nXOf Nock.Field.p DA.acs.length DA.H DA.t) (by simp [sizesA])
theorem nS26 : BA.Pb.nS ≤ 2 ^ 26 := sizes26 (nSOf Nock.Field.p DA.t) (by simp [sizesA])

theorem hHt_On : ∀ t, HtOf9 dOn t ⊆ HdomOf9 dOn := by
  intro t
  fin_cases t
  · exact nodes_sub _ _ (fun i => rfl) n26
  · exact nodes_sub _ _ (fun i => congrArg (· ^ (i : ℕ)) orb_run) nC26
  · exact nodes_sub _ _ (fun i => congrArg (· ^ (i : ℕ)) orb_run) nW26
  · exact nodes_sub _ _ (fun i => congrArg (· ^ (i : ℕ)) orb_run) nJ26
  · exact nodes_sub _ _ (fun i => congrArg (· ^ (i : ℕ)) orb_run) nA26
  · exact nodes_sub _ _ (fun i => congrArg (· ^ (i : ℕ)) orb_run) nV26
  · exact nodes_sub _ _ (fun i => rfl) nX26
  · exact nodes_sub _ _ (fun i => rfl) nS26

theorem regsOn : DA.regs = [] := by
  show (List.map Prod.fst DD.calls).dedup = []
  rw [callsA]; rfl

theorem hreg_On : (censusG dOn.Pb.toPubJ8 dOn.c).length + 6 ≤ 2 ^ 31 := by
  have h1 : dOn.Pb.toPubJ8.regs.length = 0 := by
    show DA.regs.length = 0
    rw [regsOn]; rfl
  have h2 : (claimCells dOn.c).length ≤ 3 := (List.length_filter_le _ _).trans (by simp)
  unfold censusG
  simp only [List.length_append, List.length_map, h1]
  omega

theorem nJ0 : BA.Pb.nJ = 0 := by
  show DA.jrows.length = 0
  show DD.jrows.length = 0
  rw [Nock.RedTeam.Batch4883.jrowsA]; rfl

theorem jCount0 {n : ℕ} (h : n = 0) (es : List (Nock.Jet.ChipJ8.Kd × List Nock.Jet.ChipJ8.KE))
    (lay : Fin n → Nock.Jet.ChipJ8.PRow) :
    Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount es lay = 0 := by
  subst h; simp [Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount]

/-- the numeric fields of `DatumOK9A` at `dOn` -/
theorem datumOK_on : DatumOK9A dOn := by
  have hrc : ringChar (ZMod P) = P := ZMod.ringChar_zmod_n _
  have c31 : ∀ x : ℕ, x ≤ 2 ^ 26 → x ≤ 2 ^ 31 := fun x h => h.trans (by norm_num)
  refine ⟨Nock.Jet.VerifiedRegistry.empty.faithful, ?_, ?_, le_rfl, le_rfl, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    hreg_On, hHt_On, by norm_num [dOn]⟩
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
  · show BA.Pb.nA + 2 ≤ EncInjJ8.cornerC.maxlen
    have := nA26
    show _ ≤ 2 ^ 31
    omega
  · exact (n26.trans (by norm_num [dOn, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))
  · exact (nC26.trans (by norm_num [dOn, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))
  · exact (nW26.trans (by norm_num [dOn, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))
  · exact (nA26.trans (by norm_num [dOn, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))
  · exact (nV26.trans (by norm_num [dOn, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))
  · exact (nC26.trans (by norm_num [dOn, RealIOJ9A.cornerC9, EncInjJ8.cornerC, Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31]))

theorem rows_eq : BA.rows = Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.rowsA9 BA.Pb := rfl

theorem acc_on : ∃ (χ : Coins frameJ8 KC) (M : MsgJ9A' P KC deltaF) (tr : TrJ9A (ZMod P)), AccJ9A dOn χ M tr := by
  obtain ⟨-, -, -, χ, h⟩ := Nock.RedTeam.Batch4883.complJ9A_toy_figure
  have hj := nJ0
  have n1 := n26; have n2 := nC26; have n3 := nW26; have n4 := nJ26; have n5 := nA26; have n6 := nV26
  have n7 := nX26; have n8 := nS26
  have hg : BA.g ≤ 2 ^ 31 := by
    show Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp.canonG BA.Pb.toPubJ8 ≤ 2 ^ 31
    unfold Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp.canonG
    have h1 : BA.Pb.toPubJ8.regs.length = 0 := by show DA.regs.length = 0; rw [regsOn]; rfl
    rw [h1, jCount0 hj, jCount0 hj]
    have : (2 : ℕ) ^ 26 ≤ 2 ^ 31 := by norm_num
    show BA.Pb.n + 0 + (0 + 0) ≤ _
    omega
  refine ⟨χ, _, _, acceptsJ9A_mono_rows h ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hg⟩ <;>
    simp only [rows_eq, Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.rowsA9, dOn, RealIOJ9A.cornerC9, EncInjJ8.cornerC,
      Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8.corner31,
      Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Comp.canonRows, Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of.extraRows,
      jCount0 hj] <;>
    omega

/-- **`j9a_on_witness`**: `DatumOK9A`, `StmtP9A`, `AccJ9A` and `PubP9A` hold together at nock's chips-ON toy record (axis chip and
split chip present), widened to `cornerC9` -/
theorem j9a_on_witness :
    ∃ (χ : Coins frameJ8 KC) (M : MsgJ9A' P KC deltaF) (tr : TrJ9A (ZMod P)),
      DatumOK9A dOn ∧ StmtP9A dOn ∧ AccJ9A dOn χ M tr ∧
      PubP9A dOn χ (M, fun j => ClaimJ9.pubVJ9 deltaF powerBasis3 dOn.c M.m M.ρ M.ρS χ j) ∧
      dOn.Pb.axOn = true ∧ dOn.Pb.spOn = true := by
  obtain ⟨χ, M, tr, h⟩ := acc_on
  exact ⟨χ, M, tr, datumOK_on, (stmt_pub_of_acc9 dOn χ M tr h).1, h, (stmt_pub_of_acc9 dOn χ M tr h).2,
    Nock.RedTeam.Batch4883.axOnA_tA, Nock.RedTeam.Batch4883.spOnA_tA⟩

end

end NockvmE2E.J9A.WitJ9AOn

#print axioms NockvmE2E.J9A.WitJ9AOn.datumOK_on
#print axioms NockvmE2E.J9A.WitJ9AOn.acc_on
#print axioms NockvmE2E.J9A.WitJ9AOn.j9a_on_witness
