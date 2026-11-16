/-
J9A-LINK ' (absent program): side conditions of nockvm F1 `genJ9AX_honest_at` at `kAbs` (RtG, fuel 1000).
-/
import NockvmE2E.J9A.LinkJ9AF1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.J9A.LinkJ9AF1Abs

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open NockvmE2E.J9A.LinkJ9AToy (sB fB kAbs rowsAbs R9a W9a R9a_eq W9a_eq genX_abs)
open Nock.RedTeam.Batch4842 (RtT factRC charPKC algRC card_KC)

noncomputable section

theorem genTa : genX Nock.Jet.VerifiedRegistry.empty.R 1000 sB fB = some (kAbs, .atom (Nock.Field.p + 5)) := genX_abs
abbrev DD := j8DataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty Example.RtG genTa
abbrev DA := ComplJ9ADataRec.j9aDataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty Example.RtG genTa

theorem rowsAb : rowsOfT kAbs = rowsAbs := by
  simp only [rowsOfT, NockvmE2E.J9A.LinkJ9AToy.bfs_abs]; rfl

theorem callsAb : DD.calls = [] := by
  show Nock.V1J8.Gen.callsOf (rowsOfT kAbs) = []
  rw [rowsAb]; decide +kernel

theorem rootsAb : DD.roots = Nock.V1J8.Gen.rootsOf ⟨sB, fB, .atom (Nock.Field.p + 5)⟩ rowsAbs := by
  show Nock.V1J8.Gen.rootsOf _ (rowsOfT kAbs) ++ _ = _
  rw [rowsAb]
  simp only [jNounsP, callsAb']
  simp
where callsAb' : Nock.V1J8.Gen.callsOf rowsAbs = [] := by decide +kernel

theorem hleafAb : ComplJ8Walk.RootsLeafOK DD.roots := by
  rw [rootsAb]
  show ∀ x ∈ Nock.V1J8.Gen.rootsOf ⟨sB, fB, .atom (Nock.Field.p + 5)⟩ rowsAbs, x.leaves ≤ 2 ^ 109
  decide +kernel

theorem walkReads9Ab : ComplJ9ABinders.walkReads9 rowsAbs = [(sB, 2)] := by decide +kernel

theorem hwalk9Ab : ComplJ9ABinders.WalkDepthOK9A (rowsOfT kAbs) := by
  show ComplJ8Walk.WalkDepthOK (ComplJ9ABinders.walkReads9 _)
  rw [rowsAb, walkReads9Ab]; intro r hr
  have hsub : r ∈ [(sB, 2)] := by
    simp only [VclL.pathReads, List.mem_dedup, List.mem_filter] at hr; exact hr.1
  simp at hsub; subst hsub; decide

theorem preadsAb : DD.preads = [] := by
  show pairReadsP _ _ (rowsOfT kAbs) = []
  rw [rowsAb]
  simp [pairReadsP, Nock.V1J8.FillX.isPairB, rowsAbs, rowOfSkelX, kAbs, mkX]

theorem hwalkAAb : ComplJ8Walk.WalkDepthOK DD.preads := by
  rw [preadsAb]; intro r hr; simp [VclL.pathReads] at hr

theorem jrowsAb : DD.jrows = [] := by
  show mvFixP _ (Nock.Jet.ChipJ8.honestJ8G _ _ (List.map Prod.fst DD.calls).dedup DD.calls) _ = []
  rw [callsAb]; rfl

theorem inTree_kAbs (u : NTree SkelX) (h : InTree kAbs u) : u = kAbs := by
  have : u ∈ bfsForest [kAbs] := (mem_bfsForest [kAbs] u).2 ⟨kAbs, by simp, h⟩
  rw [NockvmE2E.J9A.LinkJ9AToy.bfs_abs] at this; simpa using this

theorem pAbs : (2 : ℕ) < Nock.Field.p := by simp [Nock.Field.p]

theorem hax9Ab : ComplJ9ABinders.ProgAxOK9A Nock.Field.p kAbs := by
  intro u hu
  rw [inTree_kAbs u hu]
  simp only [ComplJ9ABinders.AxRowX9A, rowOfSkelX, kAbs, mkX]
  intro ax h
  simp [VclL.tlN, fB] at h; subst h; exact Or.inl pAbs

theorem hop5Ab : ComplJ8.ProgOp5OK Nock.Field.p kAbs := by
  intro u hu
  rw [inTree_kAbs u hu]; intro h; simp [rowOfSkelX, kAbs, mkX] at h

theorem calledAb : ∀ id, id ∉ ComplJ8Jet.CalledIds kAbs := by
  rintro id ⟨u, hu, hst, -⟩
  rw [inTree_kAbs u hu] at hst; simp [rowOfSkelX, kAbs, mkX] at hst

theorem rows9Ab : ComplJ9AGen.rowsOfT9 kAbs = R9a := R9a_eq

theorem keys9Ab : ComplJ9AChainsRun.axKeys9 (ComplJ9AGen.rowsOfT9 kAbs) = [] := by
  rw [rows9Ab]; decide +kernel

theorem fieldAx9Ab : ComplJ9AData.fieldAx9 Nock.Field.p (ComplJ9AGen.rowsOfT9 kAbs) = [] := by
  rw [rows9Ab]; decide +kernel

theorem axOffAb : ComplJ9ARun.axOnA kAbs = false := by
  simp [ComplJ9ARun.axOnA, keys9Ab]
theorem spOffAb : ComplJ9ARun.spOnA Nock.Field.p kAbs = false := by
  simp [ComplJ9ARun.spOnA, fieldAx9Ab]

theorem walkReadsX9Ab : ComplJ9AReads.walkReadsX9 (ComplJ9AGen.rowsOfT9 kAbs) = [(sB, 2)] := by
  rw [rows9Ab]; decide +kernel

theorem readsAb : DA.reads = [(sB, 2)] := by
  change ComplJ9AReads.walkReadsX9 _ ++ ComplJ9AChainsRun.axChainReadsK9 _ = _
  rw [walkReadsX9Ab]
  simp [ComplJ9AChainsRun.axChainReadsK9, keys9Ab]

theorem filterRowsAb : ((ComplJ9AGen.rowsOfT9 kAbs).toList.filter
    fun l => decide (l.chip = .s10B ∧ Nock.Field.p ≤ l.n)) = [] := by
  rw [rows9Ab]; decide +kernel

theorem preadsDAb : DA.preads = [] := by
  rw [ComplJ9ADataRec.j9aDataOf_preads, preadsAb, List.nil_append]
  unfold ComplJ9AChainsRun.axReadsK9
  rw [filterRowsAb]; simp [keys9Ab]

theorem nVAb : nVOf DA ≤ 2 ^ 31 := by
  unfold nVOf; rw [preadsDAb]; simp

theorem limbsAb : Nock.Atoms.limbs (Nock.Field.p + 5) = [6, 2 ^ 32 - 1] := by
  unfold Nock.Atoms.limbs Nock.Atoms.B Nock.Field.p
  rw [Nat.digits_def' (by norm_num) (by norm_num), Nat.digits_def' (by norm_num) (by norm_num)]
  norm_num

theorem bigsAb : DD.bigs = [Nock.Field.p + 5] := by
  show bigsP _ DD.roots (rowsOfT kAbs) = _
  rw [rootsAb, rowsAb]
  unfold bigsP
  rw [show (List.filter _ _).dedup = [Nock.Field.p + 5] by decide +kernel]
  simp

theorem acsAb_len : DA.acs.length ≤ 3 := by
  show (acsP _ DD.bigs _).length ≤ 3
  rw [bigsAb]
  unfold acsP
  simp only [List.foldl_cons, List.foldl_nil, limbsAb]
  have hsp : Nock.V1J8.Gen.spineOf [6, 2 ^ 32 - 1] = [Nock.V1J8.Gen.combOf [6, 2 ^ 32 - 1]] := rfl
  rw [hsp]
  have hL : Nock.V1J8.Gen.addNew [] [Nock.V1J8.Gen.combOf [6, 2 ^ 32 - 1]] =
      [Nock.V1J8.Gen.combOf [6, 2 ^ 32 - 1]] := by simp [Nock.V1J8.Gen.addNew]
  rw [hL]
  have hcell : ∀ x ∈ [Nock.V1J8.Gen.combOf [6, 2 ^ 32 - 1]], x.isCell = true := by
    intro x hx; simp at hx; subst hx; rfl
  have hlo := ComplJ8Atom.len_le_of_sub (ComplJ8Atom.linkOrder_spec _ hcell).1
    (fun x hx => ((ComplJ8Atom.linkOrder_spec _ hcell).2.1 x).mp hx)
  simp only [List.length_append, List.length_singleton]
  split_ifs <;> simp at hlo ⊢ <;> omega

theorem cellsDDb : DD.cells = Nock.V1J8.Gen.cellsOfRoots DD.roots := NockvmE2E.J9A.LinkJ9AF1.cells_gen_pub genTa

theorem cellsAb_len : DA.cells.length ≤ 2 ^ 31 := by
  rw [ComplJ9ADataRec.j9aDataOf_cells, cellsDDb]
  have h := Nock.RedTeam.Batch4883.foldl_addCells_len DD.roots []
  have h2 : (DD.roots.map Nock.RedTeam.Batch4883.ncell).sum ≤ 2 ^ 31 := by
    rw [rootsAb]; decide +kernel
  simp only [List.length_nil, zero_add] at h
  exact le_trans h h2

theorem N9Ab : ComplJ9ARun.N9 kAbs = 1 := by
  rw [ComplJ9ARun.N9_def, ComplJ9ARun.W9, NockvmE2E.J9A.LinkJ9AToy.genX9T_abs]; simp [bfsForest]

theorem nXAb : ComplJ9ARun.nXOf Nock.Field.p DA.acs.length DA.H kAbs = 1 := by
  simp [ComplJ9ARun.nXOf, axOffAb]

theorem nSAb : ComplJ9ARun.nSOf Nock.Field.p kAbs = 1 := by
  simp [ComplJ9ARun.nSOf, spOffAb]

theorem h31Ab : ComplJ9ARun.Rows31A DA := by
  intro x hx
  simp only [ComplJ9ARun.sizesA, sizesJ8, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hB : (bfsForest [DA.t]).length = 1 := by
    show (bfsForest [kAbs]).length = 1
    rw [NockvmE2E.J9A.LinkJ9AToy.bfs_abs]; rfl
  have hC := cellsAb_len
  have hW : (VclL.GenWalk.walkRows DA.cells DA.reads).length ≤ 2 ^ 31 := by
    have := Nock.RedTeam.Batch4883.walk_bound DA.cells [(sB, 2)] (by intro x hx; simp at hx; subst hx; norm_num)
    rw [readsAb]
    simp only [List.length_cons, List.length_nil] at this ⊢
    omega
  have hJ : DA.jrows.length = 0 := by
    show DD.jrows.length = 0
    rw [jrowsAb]; rfl
  have hA := acsAb_len
  have hV := nVAb
  have hN : ComplJ9ARun.N9 DA.t = 1 := N9Ab
  have hX : ComplJ9ARun.nXOf Nock.Field.p DA.acs.length DA.H DA.t = 1 := nXAb
  have hS : ComplJ9ARun.nSOf Nock.Field.p DA.t = 1 := nSAb
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;> omega

open NockvmE2E.J9A.LinkJ9AToy (XA orbAbs orbAbs_ok abs_sizes_gen HF1abs recSp genJ9AX_abs abs9_air)
open NockvmE2E.Exec.ShapeF (shapeOkF)
open NockvmE2E.Exec.J9AChips (famJ9A)
open NockvmE2E.J9A.DatX9Ok (DX9)
open NockvmE2E.J9A.E2EJ9AToyR (hJ_abs cAbs)
open NockvmE2E.J9A.InstJ9A (AccJ9A PubP9A)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm OrbFits)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AClosed (obligations_of_runA rowsLe31A_runA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (BRun9A)
open Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff

theorem good_exists_abs :
    ∃ χe : CoinsE, (BRun9A deltaF powerBasis3 Example.RtG genTa rfl h31Ab).Good (toχ χe) := by
  have O := obligations_of_runA deltaF powerBasis3 Example.RtG genTa rfl hax9Ab hop5Ab hleafAb hwalk9Ab hwalkAAb
    (fun id h => absurd h (calledAb id)) (fun id h => absurd h (calledAb id)) h31Ab
  have hrows := rowsLe31A_runA deltaF powerBasis3 Example.RtG genTa rfl h31Ab
  have hfig := O.fig rfl card_KC hrows
  obtain ⟨χ, hχ⟩ := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl.exists_good9A deltaF powerBasis3 _ O
    (lt_trans hfig (by norm_num))
  refine ⟨fun i => Function.surjInv K3.toK_surjective (χ i), ?_⟩
  have : toχ (fun i => Function.surjInv K3.toK_surjective (χ i)) = χ := by
    funext i; exact Function.surjInv_eq K3.toK_surjective (χ i)
  rw [this]; exact hχ

def orbAbsN : OrbJ9A :=
  let O : Orb := ⟨XA.k + 1, Nock.TraceGenExe.Gold.ofU64 XA.hGen⟩
  ⟨O, O, O, O, O, O, O, O⟩

theorem abs_orbAdm (hsh : shapeOkF famJ9A XA = true) (χe : CoinsE) :
    OrbAdm (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe) orbAbsN := by
  obtain ⟨hX, hC, hW, hA, hV, hAX, hSP, hJ, -⟩ := abs_sizes_gen χe
  have ho := orbAbs_ok hsh
  have hk : XA.k + 1 = 1 := by have : XA.k = 0 := rfl; omega
  have key : ∀ (q : ChipIn) (hn : q.n ≤ 6), OrbFits q ⟨XA.k + 1, Nock.TraceGenExe.Gold.ofU64 XA.hGen⟩ := by
    intro q hn
    refine ⟨⟨(ho 0).1, (ho 0).2⟩, ?_⟩
    show q.n ≤ 3 * 2 ^ (XA.k + 1)
    rw [hk]; omega
  exact ⟨key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega),
    key _ (by omega), key _ (by omega)⟩

theorem hF1_abs (hsh : shapeOkF famJ9A XA = true) : HF1abs := by
  obtain ⟨χe, hχ⟩ := good_exists_abs
  refine ⟨χe, _, genJ9AX_abs χe, ?_⟩
  obtain ⟨hv, h⟩ := Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.genJ9AX_honest_at genTa rfl hax9Ab hop5Ab hleafAb
    hwalk9Ab hwalkAAb h31Ab (genJ9AX_abs χe) hχ orbAbsN (abs_orbAdm hsh χe)
  exact ⟨hv, h⟩

open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9) in
theorem abs9_air_closed (hsh : shapeOkF famJ9A XA = true) :
    ∃ χ M tr,
      AccJ9A (DX9 XA hsh hJ_abs 1 0 cAbs) χ M tr ∧
      PubP9A (DX9 XA hsh hJ_abs 1 0 cAbs) χ (M, fun j => pubVJ9 deltaF powerBasis3 cAbs M.m M.ρ M.ρS χ j) :=
  abs9_air hsh (hF1_abs hsh)

end
end NockvmE2E.J9A.LinkJ9AF1Abs

#print axioms NockvmE2E.J9A.LinkJ9AF1Abs.h31Ab
#print axioms NockvmE2E.J9A.LinkJ9AF1Abs.good_exists_abs
#print axioms NockvmE2E.J9A.LinkJ9AF1Abs.hF1_abs
#print axioms NockvmE2E.J9A.LinkJ9AF1Abs.abs9_air_closed
