/-
J9A-LINK ': discharge nockvm F1 `genJ9AX_honest_at` at the toy program; HF1 then closed.
-/
import NockvmE2E.J9A.LinkJ9AToy
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.J9A.LinkJ9AF1

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.Edit Nock.Edit.GenX Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.V1J9A Nock.V1J9A.GenJ9AX Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.RedTeam.Batch4883 hiding callsA rootsA hleafA preadsA hwalkAA jrowsA cellsDD cellsA_len readsA_lt readsA_len preadsDA nVA bigsA acsA_len nXA h31A DD DA
open Nock.RedTeam.Batch4842 (RtT factRC charPKC algRC card_KC)

noncomputable section

theorem genT : genX Nock.Jet.VerifiedRegistry.empty.R 1000 sA fA = some (tA, rA) := LinkJ9AToy.genX_toy
abbrev DD := ComplJ8Data.j8DataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty Example.RtG genT
abbrev DA := ComplJ9ADataRec.j9aDataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty Example.RtG genT

theorem callsA : DD.calls = [] := by
  show Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT tA) = []
  rw [rowsA]; exact hcallsA

theorem rootsA : DD.roots = Nock.V1J8.Gen.rootsOf ⟨sA, fA, rA⟩ rowsL := by
  show Nock.V1J8.Gen.rootsOf _ (ComplJ8Data.rowsOfT tA) ++ _ = _
  rw [rowsA]
  simp only [ComplJ8Data.jNounsP, hcallsA]
  simp

theorem hleafA : ComplJ8Walk.RootsLeafOK DD.roots := by
  rw [rootsA]
  show ∀ x ∈ Nock.V1J8.Gen.rootsOf ⟨sA, fA, rA⟩ rowsL, x.leaves ≤ 2 ^ 109
  decide

theorem preadsA : DD.preads = [] := by
  show ComplJ8Data.pairReadsP _ _ (ComplJ8Data.rowsOfT tA) = []
  rw [rowsA]
  simp [ComplJ8Data.pairReadsP, Nock.V1J8.FillX.isPairB, rowOfSkelX, tA, kB, kF, mkX]

theorem hwalkAA : ComplJ8Walk.WalkDepthOK DD.preads := by
  rw [preadsA]; intro r hr; simp [VclL.pathReads] at hr

theorem jrowsA : DD.jrows = [] := by
  show ComplJ8Data.mvFixP _ (Nock.Jet.ChipJ8.honestJ8G _ _ (List.map Prod.fst DD.calls).dedup DD.calls) _ = []
  rw [callsA]; rfl

theorem cellsDD : DD.cells = Nock.V1J8.Gen.cellsOfRoots DD.roots := cells_gen genT

theorem cellsA_len : DA.cells.length ≤ 2 ^ 31 := by
  rw [ComplJ9ADataRec.j9aDataOf_cells, cellsDD]
  have h := foldl_addCells_len DD.roots []
  have h2 : (DD.roots.map ncell).sum ≤ 2 ^ 31 := by
    rw [rootsA]; decide
  simp only [List.length_nil, zero_add] at h
  exact le_trans h h2

theorem readsA_lt : ∀ x ∈ DA.reads, x.2 < 2 ^ 62 := by
  intro x hx
  change x ∈ ComplJ9AReads.walkReadsX9 _ ++ ComplJ9AChainsRun.axChainReadsK9 _ at hx
  rw [walkReadsX9A, List.nil_append] at hx
  simp only [ComplJ9AChainsRun.axChainReadsK9, List.mem_filter, List.mem_flatMap] at hx
  obtain ⟨⟨k, -, hl⟩, -⟩ := hx
  have h33 : (2 : ℕ) ^ 33 < 2 ^ 62 := by norm_num
  exact lt_trans (ComplJ9AData.segReads_lt _ _ _ x hl) h33

theorem readsA_len : DA.reads.length ≤ 4 := by
  change (ComplJ9AReads.walkReadsX9 _ ++ ComplJ9AChainsRun.axChainReadsK9 _).length ≤ 4
  rw [walkReadsX9A, List.nil_append]
  unfold ComplJ9AChainsRun.axChainReadsK9
  refine le_trans (List.length_filter_le _ _) ?_
  rw [keys9A]
  simp [segReads_length, topB, topF]

theorem preadsDA : DA.preads = ComplJ9AData.limbReads AB := by
  rw [ComplJ9ADataRec.j9aDataOf_preads, preadsA, List.nil_append]
  unfold ComplJ9AChainsRun.axReadsK9
  rw [filterKeysA, filterRowsA]
  simp

theorem nVA : nVOf DA ≤ 2 ^ 31 := by
  unfold nVOf
  split_ifs
  · norm_num
  · refine le_trans (walk_bound _ _ ?_) ?_
    · intro x hx
      rw [preadsDA] at hx
      simp only [ComplJ9AData.limbReads, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ComplJ9AData.limbAxes_lt (by rw [limbsB]; simp) y hy
    · rw [preadsDA]; simp [ComplJ9AData.limbReads, ComplJ9AData.limbAxes, limbsB]

theorem bigsA : DD.bigs = [AB] := by
  show ComplJ8Data.bigsP _ DD.roots (ComplJ8Data.rowsOfT tA) = _
  rw [rootsA, rowsA]
  unfold ComplJ8Data.bigsP
  rw [show (List.filter _ _).dedup = [AB] by decide]
  simp

theorem acsA_len : DA.acs.length ≤ 3 := by
  show (ComplJ8Data.acsP _ DD.bigs _).length ≤ 3
  rw [bigsA]
  unfold ComplJ8Data.acsP
  simp only [List.foldl_cons, List.foldl_nil, limbsB]
  have hsp : Nock.V1J8.Gen.spineOf [2 ^ 32 - 1, 2 ^ 32 - 1] = [Nock.V1J8.Gen.combOf [2 ^ 32 - 1, 2 ^ 32 - 1]] := rfl
  rw [hsp]
  have hL : Nock.V1J8.Gen.addNew [] [Nock.V1J8.Gen.combOf [2 ^ 32 - 1, 2 ^ 32 - 1]] =
      [Nock.V1J8.Gen.combOf [2 ^ 32 - 1, 2 ^ 32 - 1]] := by simp [Nock.V1J8.Gen.addNew]
  rw [hL]
  have hcell : ∀ x ∈ [Nock.V1J8.Gen.combOf [2 ^ 32 - 1, 2 ^ 32 - 1]], x.isCell = true := by
    intro x hx; simp at hx; subst hx; rfl
  have hlo := ComplJ8Atom.len_le_of_sub (ComplJ8Atom.linkOrder_spec _ hcell).1
    (fun x hx => ((ComplJ8Atom.linkOrder_spec _ hcell).2.1 x).mp hx)
  simp only [List.length_append, List.length_singleton]
  split_ifs <;> simp at hlo ⊢ <;> omega

theorem nXA : ComplJ9ARun.nXOf Nock.Field.p DA.acs.length DA.H tA = 4 := by
  rw [ComplJ9ARun.nXOf_eq axOnA_tA, ComplJ9AChainsRun.axChains9_table_length, keys9A]
  simp [limbsB, limbsF]

theorem h31A : ComplJ9ARun.Rows31A DA := by
  intro x hx
  simp only [ComplJ9ARun.sizesA, sizesJ8, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hB : (bfsForest [DA.t]).length = 3 := by
    show (bfsForest [tA]).length = 3
    rw [bfsA]; rfl
  have hC := cellsA_len
  have hW : (VclL.GenWalk.walkRows DA.cells DA.reads).length ≤ 2 ^ 31 := by
    have := walk_bound DA.cells DA.reads readsA_lt
    have := readsA_len
    omega
  have hJ : DA.jrows.length = 0 := by
    show DD.jrows.length = 0
    rw [jrowsA]; rfl
  have hA := acsA_len
  have hV := nVA
  have hN : ComplJ9ARun.N9 DA.t = 3 := N9A
  have hX : ComplJ9ARun.nXOf Nock.Field.p DA.acs.length DA.H DA.t = 4 := nXA
  have hS : ComplJ9ARun.nSOf Nock.Field.p DA.t = 1 := nSA
  rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;> omega

theorem cells_gen_pub {fuel : ℕ} {s f r : Noun} {t : NTree SkelX} (hgen : genX Nock.Jet.VerifiedRegistry.empty.R fuel s f = some (t, r)) :
    (j8DataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty Example.RtG hgen).cells =
      Nock.V1J8.Gen.cellsOfRoots (j8DataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty Example.RtG hgen).roots := rfl

/-! ## Step 4: a good coin exists (recipe) -/

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AClosed (obligations_of_runA rowsLe31A_runA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (BRun9A)

theorem good_exists_toy :
    ∃ χe : CoinsE, (BRun9A deltaF powerBasis3 Example.RtG genT rfl h31A).Good (toχ χe) := by
  have O := obligations_of_runA deltaF powerBasis3 Example.RtG genT rfl hax9A hop5A hleafA hwalk9A hwalkAA
    (fun id h => absurd h (calledA id)) (fun id h => absurd h (calledA id)) h31A
  have hrows := rowsLe31A_runA deltaF powerBasis3 Example.RtG genT rfl h31A
  have hfig := O.fig rfl card_KC hrows
  obtain ⟨χ, hχ⟩ := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl.exists_good9A deltaF powerBasis3 _ O
    (lt_trans hfig (by norm_num))
  refine ⟨fun i => Function.surjInv K3.toK_surjective (χ i), ?_⟩
  have : toχ (fun i => Function.surjInv K3.toK_surjective (χ i)) = χ := by
    funext i; exact Function.surjInv_eq K3.toK_surjective (χ i)
  rw [this]; exact hχ

/-! ## Steps 1-3 and 5 -/

open Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open NockvmE2E.Exec.V (ExecInst)
open NockvmE2E.Exec.ShapeF (shapeOkF)
open NockvmE2E.Exec.J9AChips (famJ9A)
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.Exec.Toy9R (toy9R)
open NockvmE2E.J9A.DatX9Ok (DX9)
open NockvmE2E.J9A.E2EJ9AToyR (hJ_toy cToy toyS toyF)
open NockvmE2E.J9A.InstJ9A (AccJ9A PubP9A)
open NockvmE2E.J9A.LinkJ9AToy (R9 W9T)
open NockvmE2E.J9A.LinkJ9AToy (XT orbToy orbToy_ok toy_sizes_gen toy_valid mkPbA_withOrb_toy HF1 recSp)
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA (Orb OrbJ9A OrbAdm OrbFits reorb)

def orbToyN : OrbJ9A :=
  let O : Orb := ⟨XT.k + 1, Nock.TraceGenExe.Gold.ofU64 XT.hGen⟩
  ⟨O, O, O, O, O, O, O, O⟩

theorem toy_k : XT.k + 1 = 7 := by
  have : XT.k = 6 := rfl
  omega

theorem withOrb_eq (I : InJ9A) :
    Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHOrbA.withOrb I orbToyN = LinkJ9AToy.withOrb I orbToy := rfl

theorem toy_orbAdm (hsh : shapeOkF famJ9A XT = true) (χe : CoinsE) :
    OrbAdm (recSp sA fA rA rowsL R9 W9T χe) orbToyN := by
  obtain ⟨hX, hC, hW, hA, hV, hAX, hSP, hJ, -⟩ := LinkJ9AToy.toy_sizes_gen χe
  have ho := orbToy_ok hsh
  have hk := toy_k
  have key : ∀ (q : ChipIn) (hn : q.n ≤ 96), OrbFits q ⟨XT.k + 1, Nock.TraceGenExe.Gold.ofU64 XT.hGen⟩ := by
    intro q hn
    refine ⟨⟨(ho 0).1, (ho 0).2⟩, ?_⟩
    show q.n ≤ 3 * 2 ^ (XT.k + 1)
    rw [hk]; omega
  exact ⟨key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega),
    key _ (by omega), key _ (by omega)⟩

theorem hF1_toy (hsh : shapeOkF famJ9A XT = true) : HF1 := by
  obtain ⟨χe, hχ⟩ := good_exists_toy
  refine ⟨χe, _, LinkJ9AToy.genJ9AX_toy χe, ?_⟩
  obtain ⟨hv, h⟩ := Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHonest.genJ9AX_honest_at genT rfl hax9A hop5A hleafA
    hwalk9A hwalkAA h31A (LinkJ9AToy.genJ9AX_toy χe) hχ orbToyN (toy_orbAdm hsh χe)
  exact ⟨hv, h⟩

open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9) in
theorem toy9_air_closed (hsh : shapeOkF famJ9A XT = true) :
    ∃ χ M tr,
      AccJ9A (DX9 XT hsh hJ_toy 3 1 cToy) χ M tr ∧
      PubP9A (DX9 XT hsh hJ_toy 3 1 cToy) χ (M, fun j => pubVJ9 deltaF powerBasis3 cToy M.m M.ρ M.ρS χ j) :=
  LinkJ9AToy.toy9_air hsh (hF1_toy hsh)

end
end NockvmE2E.J9A.LinkJ9AF1

#print axioms NockvmE2E.J9A.LinkJ9AF1.good_exists_toy
#print axioms NockvmE2E.J9A.LinkJ9AF1.hF1_toy
#print axioms NockvmE2E.J9A.LinkJ9AF1.toy9_air_closed
