/-
  Nock/RedTeam/Batch4856Thm54J9BComplToy.lean

  **J-9 B general completeness: non-vacuity at a BIG claim atom.**  The run
  `*[(p+5) [0 1]] = p+5` (Goldilocks, `K = KC`, `δ = deltaF`, `b = powerBasis3`, the empty registry): the subject and
  the result are the big atom `p + 5`, so J-8's claim binder `hclA` FAILS here (`hclA_fails`), while every binder of
  `complJ9B_closed` (`hax hop5 hleaf hwalk hwalkA hRt hregAx h31`) is a closed lemma below:
  `complJ9B_toy` and `complJ9B_toy_figure` (`ε_c < 2^-120`, an accepting coin) carry no hypothesis.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed
import Nock.RedTeam.Batch4842Thm54J8ComplClose

set_option autoImplicit false

namespace Nock.RedTeam.Batch4856

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.TraceGenExe (KC deltaF powerBasis3)
open Nock.RedTeam.Batch4842 (RtT factRC charPKC algRC card_KC)

noncomputable section

/-! ## 1. The run and its data -/

/-- The big atom `p + 5`. -/
def s9 : Noun := .atom (Nock.Field.p + 5)
/-- The tree of `*[(p+5) [0 1]]`. -/
def t9 : NTree SkelX := mkX .s0 s9 InhabJ8Base.f0 s9 []

theorem gen9 : genX Nock.Jet.VerifiedRegistry.empty.R 1 s9 InhabJ8Base.f0 = some (t9, s9) := by
  simp [genX, genComputeSkeletonX, s9, InhabJ8Base.f0, t9, Noun.slot, Nock.Jet.VerifiedRegistry.empty]

/-- The honest row of `t9`. -/
def r9 : RowNX := { st := .s0, s := s9, f := InhabJ8Base.f0, e := s9, fh := .atom 0, ft := .atom 1 }

theorem row9 : rowOfSkelX t9.label = r9 := rfl

theorem bfs9 : bfsForest [t9] = [t9] := by simp [bfsForest, t9, mkX]

theorem rows9 : ComplJ8Data.rowsOfT t9 = #[r9] := by
  simp only [ComplJ8Data.rowsOfT, bfs9]; rfl

abbrev D9T := j8DataOf Nock.Field.p Nock.Jet.VerifiedRegistry.empty RtT gen9

theorem inTree_t9 (u : NTree SkelX) (h : InTree t9 u) : u = t9 := by
  cases h with
  | here => rfl
  | sub hs _ => simp [t9, mkX] at hs

theorem hcalls9 : Nock.V1J8.Gen.callsOf #[r9] = [] := by decide

theorem calls9 : D9T.calls = [] := by
  show Nock.V1J8.Gen.callsOf (ComplJ8Data.rowsOfT t9) = []
  rw [rows9]; exact hcalls9

theorem reads9 : D9T.reads = [] := by
  show Nock.V1J8.Gen.pathReads (ComplJ8Data.rowsOfT t9) = []
  rw [rows9]; decide

theorem roots9 : D9T.roots = Nock.V1J8.Gen.rootsOf ⟨s9, InhabJ8Base.f0, s9⟩ #[r9] := by
  show Nock.V1J8.Gen.rootsOf _ (ComplJ8Data.rowsOfT t9) ++ _ = _
  rw [rows9]
  simp only [ComplJ8Data.jNounsP, hcalls9]
  simp

theorem hleaf9 : ComplJ8Walk.RootsLeafOK D9T.roots := by
  rw [roots9]
  show ∀ x ∈ Nock.V1J8.Gen.rootsOf ⟨s9, InhabJ8Base.f0, s9⟩ #[r9], x.leaves ≤ 2 ^ 109
  decide

theorem hwalk9 : ComplJ8Walk.WalkDepthOK D9T.reads := by
  rw [reads9]; intro r hr; simp [VclL.pathReads] at hr

theorem preads9 : D9T.preads = [] := by
  show ComplJ8Data.pairReadsP _ _ (ComplJ8Data.rowsOfT t9) = []
  rw [rows9]
  simp [ComplJ8Data.pairReadsP, r9, Nock.V1J8.FillX.isPairB]

theorem hwalkA9 : ComplJ8Walk.WalkDepthOK D9T.preads := by
  rw [preads9]; intro r hr; simp [VclL.pathReads] at hr

theorem jrows9 : D9T.jrows = [] := by
  show ComplJ8Data.mvFixP _ (Nock.Jet.ChipJ8.honestJ8G _ _ (List.map Prod.fst D9T.calls).dedup D9T.calls) _ = []
  rw [calls9]; rfl

theorem cells9 : D9T.cells = [InhabJ8Base.f0] := by
  show Nock.V1J8.Gen.cellsOfRoots D9T.roots = _
  rw [roots9]; decide

theorem bigs9 : D9T.bigs = [Nock.Field.p + 5] := by
  show ComplJ8Data.bigsP _ D9T.roots (ComplJ8Data.rowsOfT t9) = _
  rw [roots9, rows9]
  unfold ComplJ8Data.bigsP
  rw [show (List.filter _ _).dedup = [Nock.Field.p + 5] by decide]
  simp

theorem limbs9 : Nock.Atoms.limbs (Nock.Field.p + 5) = [6, Nock.Atoms.B - 1] := by
  have h := ComplJ8BigBound.limbs_two (a := Nock.Field.p + 5) (by simp [Nock.Atoms.p]) (by simp [Nock.Atoms.p])
  rw [h]; simp [Nock.Atoms.p]; omega

theorem acs9_len : D9T.acs.length ≤ 3 := by
  show (ComplJ8Data.acsP _ D9T.bigs _).length ≤ 3
  rw [bigs9]
  unfold ComplJ8Data.acsP
  simp only [List.foldl_cons, List.foldl_nil, limbs9]
  have hsp : Nock.V1J8.Gen.spineOf [6, Nock.Atoms.B - 1] = [Nock.V1J8.Gen.combOf [6, Nock.Atoms.B - 1]] := rfl
  rw [hsp]
  have hL : Nock.V1J8.Gen.addNew [] [Nock.V1J8.Gen.combOf [6, Nock.Atoms.B - 1]] =
      [Nock.V1J8.Gen.combOf [6, Nock.Atoms.B - 1]] := by simp [Nock.V1J8.Gen.addNew]
  rw [hL]
  have hcell : ∀ x ∈ [Nock.V1J8.Gen.combOf [6, Nock.Atoms.B - 1]], x.isCell = true := by
    intro x hx; simp at hx; subst hx; rfl
  have hlo := ComplJ8Atom.len_le_of_sub (ComplJ8Atom.linkOrder_spec _ hcell).1
    (fun x hx => ((ComplJ8Atom.linkOrder_spec _ hcell).2.1 x).mp hx)
  simp only [List.length_append, List.length_singleton]
  split_ifs <;> simp at hlo ⊢ <;> omega

theorem h31_9 : Rows31 D9T := by
  intro x hx
  simp only [sizesJ8, nVOf, preads9, if_true, List.mem_cons, List.not_mem_nil, or_false] at hx
  have hW : (VclL.GenWalk.walkRows D9T.cells D9T.reads).length ≤ 2 ^ 31 := by
    rw [reads9]
    have := VclL.GenWalk.walkRows_length_le D9T.cells []
    simp [VclL.pathReads] at this
    rw [cells9] at this ⊢
    omega
  have hB : (bfsForest [D9T.t]).length = 1 := by
    show (bfsForest [t9]).length = 1
    rw [bfs9]; rfl
  have hC : D9T.cells.length = 1 := by rw [cells9]; rfl
  have hA := acs9_len
  have hJ : D9T.jrows.length = 0 := by rw [jrows9]; rfl
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem hax9 : ComplJ8.ProgAxOK Nock.Field.p t9 := by
  intro u hu
  rw [inTree_t9 u hu]
  show ComplJ8.AxRowX _ r9
  intro ax hax
  simp [r9] at hax
  subst hax; decide

theorem hop5_9 : ComplJ8.ProgOp5OK Nock.Field.p t9 := by
  intro u hu
  rw [inTree_t9 u hu]
  intro h; rw [row9] at h; simp [r9] at h

theorem called9 : ∀ id, id ∉ ComplJ8Jet.CalledIds t9 := by
  rintro id ⟨u, hu, hst, -⟩
  rw [inTree_t9 u hu, row9] at hst
  simp [r9] at hst

theorem incOps9 : ComplJ8Data.incOpsP Nock.Field.p D9T.rows = [] := by
  show ComplJ8Data.incOpsP _ (ComplJ8Data.rowsOfT t9) = []
  rw [rows9]; decide

theorem hcor9 : ComplJ8Atom.NoIncCornerP Nock.Field.p D9T.acs (ComplJ8Data.incOpsP Nock.Field.p D9T.rows) := by
  rw [incOps9]; intro h; obtain ⟨vc, hvc, -⟩ := h; simp at hvc

/-- **J-8's claim binder fails at this run** (the subject is the big atom `p + 5`): the toy is outside `complJ8_closed`. -/
theorem hclA_fails : ¬ ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s9 InhabJ8Base.f0 s9) k).leafList,
    v < Nock.Field.p := by
  intro h
  have := h 0 (Nock.Field.p + 5) (by simp [FrameVS.claimNoun, ComplJ8.cJ, s9, Noun.leafList])
  omega

/-! ## 2. `complJ9B_balV` at the toy -/

/-- The toy's J-9 B honest record. -/
abbrev B9T := ComplJ9BOf.BRun9 deltaF powerBasis3 RtT gen9 rfl h31_9

open Classical in
/-- **`complJ9B_closed` at `*[(p+5) [0 1]]`**, every binder discharged, nothing carried. -/
theorem complJ9B_toy :
    (∀ χ, B9T.Good χ → AcceptsJ9V.AcceptsJ9V deltaF powerBasis3 B9T.Pb Nock.Jet.VerifiedRegistry.empty.R
      (ComplJ8.cJ s9 InhabJ8Base.f0 s9) χ (B9T.M χ) (B9T.tr χ) B9T.rows B9T.g) ∧
    (((Finset.univ.filter fun χ : Coins frameJ8 KC => ¬ B9T.Good χ).card : ℚ) /
      Fintype.card (Coins frameJ8 KC) ≤ B9T.epsC) ∧
    StJ8 B9T.tr ∧ Nock.Jet.HoldsN (ComplJ8.cJ s9 InhabJ8Base.f0 s9) ∧
    (Fintype.card KC = VclL.Events.cK →
      B9T.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9V.AcceptsJ9V deltaF powerBasis3 B9T.Pb Nock.Jet.VerifiedRegistry.empty.R
        (ComplJ8.cJ s9 InhabJ8Base.f0 s9) χ (B9T.M χ) (B9T.tr χ) B9T.rows B9T.g) :=
  ComplJ9BClosed.complJ9B_closed deltaF powerBasis3 RtT gen9 rfl hax9 hop5_9 hleaf9 hwalk9 hwalkA9
    (fun id h => absurd h (called9 id)) (fun id h => absurd h (called9 id)) h31_9

/-- **The figure at the toy, hypothesis-free**: `ε_c < 2^-120` and an accepting coin. -/
theorem complJ9B_toy_figure :
    B9T.epsC < 1 / 2 ^ 120 ∧
      ∃ χ, AcceptsJ9V.AcceptsJ9V deltaF powerBasis3 B9T.Pb Nock.Jet.VerifiedRegistry.empty.R
        (ComplJ8.cJ s9 InhabJ8Base.f0 s9) χ (B9T.M χ) (B9T.tr χ) B9T.rows B9T.g :=
  complJ9B_toy.2.2.2.2 card_KC

end

end Nock.RedTeam.Batch4856

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BClosed.complJ9B_closed
#print axioms Nock.RedTeam.Batch4856.gen9
#print axioms Nock.RedTeam.Batch4856.h31_9
#print axioms Nock.RedTeam.Batch4856.hcor9
#print axioms Nock.RedTeam.Batch4856.hclA_fails
#print axioms Nock.RedTeam.Batch4856.complJ9B_toy
#print axioms Nock.RedTeam.Batch4856.complJ9B_toy_figure
