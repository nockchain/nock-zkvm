/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalCR.lean

* `colX9_mid`: on a non-`s10S` row the handle columns `17 ≤ c < 123` of `colX9` are J-8's `colX` of `rn`.
  * `xEnt_mem9`: `ComplJ9ABalCX.xEnt_par9` with the extra conclusions "the parent noun is a cell sub-noun of a
    handle root of `rn`" and "the chip is not `s10S`" (old rows: J-8's `ComplJ8Data.xEnt_cell`).
  * `hs3_node9`: the `s3` decode of `rowOfSkelX` at an old `Node9`.
  * `Sub9`: the binder that every handle root of a twin row has its cell sub-nouns in the cell table.
  * `xSum_run9`, `hC_runA`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalC
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalCX

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalCR

open Nock Nock.Noun Nock.Walk Nock.Reified Nock.Framework Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd cc selS)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
  (slotsX9 slot0X9 slot1X9 slot2X9 slot3X9 statesX9 extSlot ents0New ents1New ents2New ents3New sS0B sS10B sS10S)
open Nock.NockVMROM.Thm54.VclL.Handle.HonestCompX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 ChipSt9 SemN9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ACompRow
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castEntX castSlotX DX invQX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG (GC wsum wsum_append wsum_flatMap wsum_filterMap cellHx_eq)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalC (xSum9 termQX9_x acc_rows9)

noncomputable section

section Aux
variable {F : Type} [Field F]

/-- On a non-`s10S` row the handle columns `17 ≤ c < 123` of `colX9` are J-8's `colX` of `rn`. -/
theorem colX9_mid (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (l : LX9)
    (fst lst : F) (hc : l.chip ≠ .s10S) (c : ℕ) (h1 : 17 ≤ c) (h2 : c < 123) :
    colX9 H pd idOf l fst lst c = colX H pd l.rn fst lst c := by
  cases hch : l.chip
  · simp only [colX9, hch]
  · simp only [colX9, hch]; exact colS0B_mid H pd idOf l.rn l.n fst lst c h1 h2
  · simp only [colX9, hch]; exact colS10B_mid H pd idOf l.rn l.n fst lst c h1 h2
  · exact absurd hch hc

end Aux

/-! ## 1. `xEnt_mem9` -/

section Ent

/-- **`ComplJ9ABalCX.xEnt_par9` with the membership of the parent noun**: an active `.x` entry at `colX9 l` is a
parent-cell record, the parent noun is a cell sub-noun of a handle root of `rn`, and the chip is not `s10S`. -/
theorem xEnt_mem9 {p : ℕ} [Fact p.Prime] {R : Nock.Jet.Registry} (H : Noun → ℕ × ℕ)
    (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (l : LX9) (fst lst : ZMod p)
    (hsem : SemN9 R l) (hok : l.chip = .old → HonestCompX.RowOKX p l.rn) (hH : HonestCompX.HdlOK p H)
    (hs3 : l.chip = .old → l.rn.st = .s3 → l.rn.sf1.isCell = true → l.rn.sf1 = .cell l.rn.ftth l.rn.fttt)
    (S : SlotX (ZMod p)) (hS : S ∈ (slotsX9 : List (SlotX (ZMod p)))) (x : EntX (ZMod p)) (hx : x ∈ S.ents)
    (hb : x.bal = .x)
    (hact : x.act.eval (⟨colX9 H pd idOf l fst lst, colX9 H pd idOf l fst lst, fun _ => 0, fun _ => 0⟩ :
      Nock.Reified.Env (ZMod p)) ≠ 0) :
    ∃ kP kL kR, x.rcd = cellRecX (hdX kP) (hdX kL) (hdX kR) ∧
      ((HonestCompX.hN l.rn kP = .cell (HonestCompX.hN l.rn kL) (HonestCompX.hN l.rn kR) ∧
        ∃ n ∈ handleNounsX l.rn, HonestCompX.hN l.rn kP ∈ Nock.Jet.ChipJ8.subs n) ∧ l.chip ≠ .s10S) ∧
      kP < 12 ∧ kL < 12 ∧ kR < 12 := by
  have hsel : (selS x.states : CoeffExpr (ZMod p)).eval
      (⟨colX9 H pd idOf l fst lst, colX9 H pd idOf l fst lst, fun _ => 0, fun _ => 0⟩ :
        Nock.Reified.Env (ZMod p)) ≠ 0 := fun h => hact (by simp [EntX.act, CoeffExpr.eval, h])
  rw [ComplJ9ABalCX.selS_eval9] at hsel
  rcases ComplJ9ABalCX.ent_cases9 S hS x hx with ⟨S0, hS0, hx0⟩ | h0 | h1 | h2 | h3
  · -- an entry of J-8's slots
    have hlt := ComplJ9ABalCX.states_okX S0 hS0 x hx0
    cases hc : l.chip
    · rw [colX9_old H pd idOf l fst lst hc] at hact
      have hact' : x.act.eval (⟨Nock.V1J8.FillX.colXE H pd l.rn fst lst, Nock.V1J8.FillX.colXE H pd l.rn fst lst,
          fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p)) ≠ 0 := by
        rw [Nock.V1J8.FillX.colXE_eq]; exact hact
      obtain ⟨kP, kL, kR, hrc, hpar, h1, h2, h3⟩ :=
        ComplJ8OfBalG.xEnt_par H pd l.rn fst lst (hok hc) hH (hs3 hc) S0 hS0 x hx0 hb hact'
      obtain ⟨k', tail, hr', hcell, hk, n, hn, hsub⟩ :=
        ComplJ8Data.xEnt_cell H pd l.rn fst lst (hok hc) hH S0 hS0 x hx0 hb hact'
      have hkk : k' = kP := by
        rw [hrc] at hr'
        simp [cellRecX, ChipHX.recOf, ChipH.cellRec, hdX] at hr'; omega
      rw [hkk] at hsub
      exact ⟨kP, kL, kR, hrc, ⟨⟨hpar, n, hn, hsub⟩, by simp [hc]⟩, h1, h2, h3⟩
    all_goals
      exfalso; apply hsel
      refine List.sum_eq_zero fun v hv => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
      have := hlt i hi
      simp [colX9, hc, colS0B, colS10B, colS10S, this]
  · -- `ents0New`: `(f; fh; ft)` on `s0B` / `s10B`
    simp only [ents0New, List.mem_singleton] at h0
    subst h0
    refine ⟨1, 5, 6, rfl, ?_, by decide, by decide, by decide⟩
    cases hc : l.chip
    · exfalso; apply hsel
      simp [colX9, hc, colX_ge69, sS0B, sS10B]
    · simp only [SemN9, hc] at hsem
      have h := hsem.1
      simp only [RowNX.SemN, hsem.2.1] at h
      refine ⟨⟨h.2.1, l.rn.f, by simp [handleNounsX], ?_⟩, by simp [hc]⟩
      show l.rn.f ∈ Nock.Jet.ChipJ8.subs l.rn.f
      rw [h.2.1]; simp [Nock.Jet.ChipJ8.subs]
    · simp only [SemN9, hc] at hsem
      have h := hsem.1
      simp only [RowNX.SemN, hsem.2.1] at h
      refine ⟨⟨h.2.1, l.rn.f, by simp [handleNounsX], ?_⟩, by simp [hc]⟩
      show l.rn.f ∈ Nock.Jet.ChipJ8.subs l.rn.f
      rw [h.2.1]; simp [Nock.Jet.ChipJ8.subs]
    · exfalso; apply hsel
      simp [colX9, hc, colS10S, sS0B, sS10B]
  · -- `ents1New`: `(ft; fth; ftt)` on `s10B` (the other entry is `.s`)
    simp only [ents1New, List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with rfl | rfl
    · refine ⟨6, 7, 8, rfl, ?_, by decide, by decide, by decide⟩
      cases hc : l.chip
      · exfalso; apply hsel
        simp [colX9, hc, colX_ge69, sS10B]
      · exfalso; apply hsel
        simp [colX9, hc, colS0B, sS10B]
      · simp only [SemN9, hc] at hsem
        have h := hsem.1
        simp only [RowNX.SemN, hsem.2.1] at h
        refine ⟨⟨h.2.2.1, l.rn.f, by simp [handleNounsX], ?_⟩, by simp [hc]⟩
        show l.rn.ft ∈ Nock.Jet.ChipJ8.subs l.rn.f
        rw [h.2.1, h.2.2.1]; simp [Nock.Jet.ChipJ8.subs]
      · exfalso; apply hsel
        simp [colX9, hc, colS10S, sS10B]
    · simp at hb
  · -- `ents2New`: `(fth; ftth; fttt)` on `s10B`
    simp only [ents2New, List.mem_singleton] at h2
    subst h2
    refine ⟨7, 9, 10, rfl, ?_, by decide, by decide, by decide⟩
    cases hc : l.chip
    · exfalso; apply hsel
      simp [colX9, hc, colX_ge69, sS10B]
    · exfalso; apply hsel
      simp [colX9, hc, colS0B, sS10B]
    · simp only [SemN9, hc] at hsem
      have h := hsem.1
      simp only [RowNX.SemN, hsem.2.1] at h
      refine ⟨⟨h.2.2.2.1, l.rn.f, by simp [handleNounsX], ?_⟩, by simp [hc]⟩
      show l.rn.fth ∈ Nock.Jet.ChipJ8.subs l.rn.f
      rw [h.2.1, h.2.2.1, h.2.2.2.1]; simp [Nock.Jet.ChipJ8.subs]
    · exfalso; apply hsel
      simp [colX9, hc, colS10S, sS10B]
  · -- `ents3New`: both entries are `.s`
    simp only [ents3New, List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with rfl | rfl <;> simp at hb

end Ent

/-! ## 2. The `s3` decode at an old node -/

section Node
variable {p : ℕ} [Fact p.Prime] {R : Nock.Jet.Registry} {t : NTree SkelX}

theorem hs3_node9 {u : NTree LX9} (hu : ComplJ9AGen.Node9 R t u) (hc : u.label.chip = .old) :
    u.label.rn.st = .s3 → u.label.rn.sf1.isCell = true → u.label.rn.sf1 = .cell u.label.rn.ftth u.label.rn.fttt := by
  rcases hu with ⟨v, hvt, hv, rfl⟩ | ⟨v, hv, hax, rfl⟩ | hseg
  · simp only [ComplJ9AGen.genX9T_label]
    exact ComplJ8OfBalG.rowOfSkelX_s3 _
  · simp only [ComplJ9AGen.liftT_label, ComplJ9AGen.liftL]
    exact ComplJ8OfBalG.rowOfSkelX_s3 _
  · rcases hseg with ⟨n, m, s, e, new, -, -, -, rfl⟩ | ⟨X, Y, rfl⟩
    · rw [ComplJ9AGen.segT_label] at hc; simp at hc
    · intro h; simp [ComplJ9AGen.tNode, ComplJ9AGen.tRow] at h

end Node

/-! ## 3. `xSum_run9` -/

section Run
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => ComplJ9ADataRec.j9aDataOf p Rg Rt hgen
local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The cell-closure binder of the twin rows**: every cell sub-noun of a handle root of a twin BFS row is a cell of
the cell table. -/
def Sub9 : Prop :=
  ∀ u ∈ ComplJ9ARun.W9 t, ∀ n ∈ handleNounsX u.label.rn, ∀ z ∈ Nock.Jet.ChipJ8.subs n, z ∈ (DA).cells

set_option maxHeartbeats 1000000 in
/-- **The `.x` reciprocal sum of twin run row `j` is the weighted total of the row's export consumes.** -/
theorem xSum_run9 (hpG : p = Nock.Atoms.p) (hax9 : ComplJ9ABinders.ProgAxOK9A p t)
    (hop5 : ComplJ8.ProgOp5OK p t) (hsub : Sub9 (p := p) Rt hgen)
    (hlen : (DA).cells.length < p) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjC : Function.Injective (powN o (DA).cells.length)) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) (j : ℕ) (hj : j < (ComplJ9ARun.W9 t).length) :
    xSum9 δ b (DA).H (DA).pd (ComplJ9ARun.idOfA (p := p) Rt hgen) (ComplJ9ARun.W9 t) (chalVJ8 b χ) pubVal j =
      wsum (GC δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) o χ)
        (ComplJ9ADataRec.xConsumesX9 p (⟨HonestTraceX9.baseT9 (DA).H (DA).pd (ComplJ9ARun.idOfA (p := p) Rt hgen)
          (ComplJ9ARun.W9 t) j, HonestTraceX9.baseT9 (DA).H (DA).pd (ComplJ9ARun.idOfA (p := p) Rt hgen)
          (ComplJ9ARun.W9 t) j, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))) := by
  set W := ComplJ9ARun.W9 t with hW
  set idOf := ComplJ9ARun.idOfA (p := p) Rt hgen with hidOf
  set e0 := HonestTraceX9.env0 (DA).H (DA).pd idOf W (chalVJ8 b χ) pubVal j with he0
  set e' : Nock.Reified.Env (ZMod p) := ⟨HonestTraceX9.baseT9 (DA).H (DA).pd idOf W j,
    HonestTraceX9.baseT9 (DA).H (DA).pd idOf W j, fun _ => 0, fun _ => 0⟩ with he'
  have hT : e0.trace = e'.trace := rfl
  have hrow : HonestWalkX9.rowAt9 W (j + 1) = (W[j]'hj).label := by
    simp [HonestWalkX9.rowAt9, List.getElem?_eq_getElem hj]
  have hmemW : W[j]'hj ∈ W := List.getElem_mem hj
  have hu : InTree (ComplJ9AGen.genX9T t) (W[j]'hj) := by
    obtain ⟨c, hc, hcu⟩ := (mem_bfsForest _ _).1 hmemW
    simp only [List.mem_singleton] at hc
    subst hc; exact hcu
  have hnode := ComplJ9AGen.genX9T_inTree hgen hu
  have hsem : SemN9 Rg.R (HonestWalkX9.rowAt9 W (j + 1)) := by
    rw [hrow]; exact ComplJ9AGen.semN9_of_node9 hnode
  have hH := ComplJ9AOfComp.hHA' (p := p) Rt hgen
  have hok : (HonestWalkX9.rowAt9 W (j + 1)).chip = .old →
      HonestCompX.RowOKX p (HonestWalkX9.rowAt9 W (j + 1)).rn := by
    intro hc
    rw [hrow] at hc ⊢
    exact (ComplJ9ABase.old_facts hpG hgen hax9 hop5 (DA).H (DA).pd (ComplJ9AOfComp.hpairA Rt hgen hpG hop5)
      hnode hc).1
  have hs3 : (HonestWalkX9.rowAt9 W (j + 1)).chip = .old → (HonestWalkX9.rowAt9 W (j + 1)).rn.st = .s3 →
      (HonestWalkX9.rowAt9 W (j + 1)).rn.sf1.isCell = true →
      (HonestWalkX9.rowAt9 W (j + 1)).rn.sf1 =
        .cell (HonestWalkX9.rowAt9 W (j + 1)).rn.ftth (HonestWalkX9.rowAt9 W (j + 1)).rn.fttt := by
    intro hc
    rw [hrow] at hc ⊢
    exact hs3_node9 hnode hc
  have hH' := ComplJ8Data.hdlOK_hdlP p (DA).cells (DA).acs
  unfold xSum9 ComplJ9ADataRec.xConsumesX9
  rw [wsum_flatMap, ← TeleX9.slotsX9_cast (F := ZMod p), List.map_map]
  refine congrArg List.sum (List.map_congr_left fun S hS => ?_)
  have hS' : castSlotX (F := ZMod p) S ∈ slotsX9 (F := ZMod p) := by
    rw [← TeleX9.slotsX9_cast]; exact List.mem_map_of_mem hS
  simp only [Function.comp_apply]
  rw [show (castSlotX (F := ZMod p) S).ents = S.ents.map castEntX from rfl, List.filter_map, List.filterMap_map,
    wsum_filterMap]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨hxS, hb⟩ := List.mem_filter.mp hx
  have hb' : x.bal = Bal.x := by simpa using hb
  have hmem : castEntX (F := ZMod p) x ∈ (castSlotX (F := ZMod p) S).ents := List.mem_map_of_mem hxS
  have hae : (castEntX (F := ZMod p) x).act.eval e' = ChipHX.evalQX x.act e0 := by
    rw [← TeleCQX.castEntX_act]
    refine HonestTraceX.eval_okC HonestTraceX9.okFs9 _ (ComplJ9AOfComp.hacts9 _ hS' _ hmem) e' e0
      fun k i hk => ?_
    cases k <;> simp [HonestTraceX9.okFs9] at hk
    show e'.trace i = e0.trace i
    rw [hT]
  simp only [Function.comp_apply]
  rw [hae]
  by_cases ha : ChipHX.evalQX x.act e0 = 0
  · rw [ha]; simp
  have hne' : (castEntX (F := ZMod p) x).act.eval e' ≠ 0 := by rwa [hae]
  have hv0 : (ChipHX.evalQX x.act e0).val ≠ 0 := fun h => ha ((ZMod.val_eq_zero _).mp h)
  rw [if_neg hv0]
  obtain ⟨kP, kL, kR, hrc, ⟨⟨hpar, n, hn, hsubn⟩, hchip⟩, h1, h2, h3⟩ :=
    xEnt_mem9 (R := Rg.R) (DA).H (DA).pd idOf (HonestWalkX9.rowAt9 W (j + 1)) (HonestWalkX9.fl1 (j + 1))
      (HonestWalkX9.llW W (j + 1)) hsem hok hH hs3 _ hS' _ hmem hb' hne'
  have hrcd : (castEntX (F := ZMod p) x).rcd = x.rcd := rfl
  have hn' : n ∈ handleNounsX (W[j]'hj).label.rn := by rw [← hrow]; exact hn
  have hcm : HonestCompX.hN (HonestWalkX9.rowAt9 W (j + 1)).rn kP ∈ (DA).cells := by
    rw [hrow]; rw [hrow] at hsubn
    exact hsub _ hmemW n hn' _ hsubn
  rw [hpar] at hcm
  set L := HonestCompX.hN (HonestWalkX9.rowAt9 W (j + 1)).rn kL with hL
  set R := HonestCompX.hN (HonestWalkX9.rowAt9 W (j + 1)).rn kR with hR
  have hjl := List.idxOf_lt_length_of_mem hcm
  obtain ⟨x1, y1, hxy, hxL, hxR⟩ := ComplJ9ABalG1.cells_kids_gen (DA).cells (ComplJ8Data.cells_closed _)
    (fun c hc => (ComplJ8Walk.cellsOfRoots_mem _ c hc).1) _ hcm
  simp only [Noun.cell.injEq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  set x1 := L with hx1def
  set y1 := R with hy1def
  have tr : ∀ c, e0.trace c = colX9 (DA).H (DA).pd idOf (HonestWalkX9.rowAt9 W (j + 1)) (HonestWalkX9.fl1 (j + 1))
      (HonestWalkX9.llW W (j + 1)) c := fun c => rfl
  have tmid : ∀ k, k < 12 → ∀ c, c = 25 + 2 * k ∨ c = 26 + 2 * k →
      e0.trace c = colX (DA).H (DA).pd (HonestWalkX9.rowAt9 W (j + 1)).rn (HonestWalkX9.fl1 (j + 1))
        (HonestWalkX9.llW W (j + 1)) c := fun k hk c hc => by
    rw [tr]; exact colX9_mid _ _ _ _ _ _ hchip c (by omega) (by omega)
  have tP : e0.trace (hdX kP).v = ((((DA).cells.idxOf (Noun.cell x1 y1) : ℕ)) : ZMod p) := by
    rw [show (hdX kP).v = 26 + 2 * kP from rfl, tmid kP h1 _ (Or.inr rfl), HonestCompX.colX_v _ _ _ _ _ _ h1, hpar]
    show (((ComplJ8Data.hdlP p (DA).cells (DA).acs (Noun.cell x1 y1)).2 : ℕ) : ZMod p) = _
    simp only [ComplJ8Data.hdlP]
    rw [ComplJ8OfBal.genIdxOf_eq _ _ hcm]
  have tP' : e'.trace (hdX kP).v = ((((DA).cells.idxOf (Noun.cell x1 y1) : ℕ)) : ZMod p) := by
    rw [← hT]; exact tP
  have hval : (e'.trace (hdX kP).v).val = (DA).cells.idxOf (Noun.cell x1 y1) := by
    rw [tP', ZMod.val_natCast, Nat.mod_eq_of_lt (hjl.trans hlen)]
  have hrc' : x.rcd = cellRecX (hdX kP) (hdX kL) (hdX kR) := hrc
  rw [hrc', hrc]
  simp only [cellRecX, ChipHX.recOf, ChipH.cellRec, List.map_cons]
  rw [hval]
  simp only [GC]
  rw [cellHx_eq δ b (DA) (ComplJ9ADataRec.cellsA_pos Rt hgen) o hinjC χ rfl _ hjl (List.getElem_idxOf hjl) hxL hxR,
    ComplJ8CompPole.den_split δ b e0 χ rfl _ (by simp),
    ← map_natCast (algebraMap (ZMod p) 𝕂′), ZMod.natCast_zmod_val]
  congr 2
  have t1 : e0.trace (hdX kL).k = (((((DA).H x1).1 : ℕ)) : ZMod p) := by
    rw [show (hdX kL).k = 25 + 2 * kL from rfl, tmid kL h2 _ (Or.inl rfl), HonestCompX.colX_k _ _ _ _ _ _ h2]; rfl
  have t2 : e0.trace (hdX kL).v = (((((DA).H x1).2 : ℕ)) : ZMod p) := by
    rw [show (hdX kL).v = 26 + 2 * kL from rfl, tmid kL h2 _ (Or.inr rfl), HonestCompX.colX_v _ _ _ _ _ _ h2]; rfl
  have t3 : e0.trace (hdX kR).k = (((((DA).H y1).1 : ℕ)) : ZMod p) := by
    rw [show (hdX kR).k = 25 + 2 * kR from rfl, tmid kR h3 _ (Or.inl rfl), HonestCompX.colX_k _ _ _ _ _ _ h3]; rfl
  have t4 : e0.trace (hdX kR).v = (((((DA).H y1).2 : ℕ)) : ZMod p) := by
    rw [show (hdX kR).v = 26 + 2 * kR from rfl, tmid kR h3 _ (Or.inr rfl), HonestCompX.colX_v _ _ _ _ _ _ h3]; rfl
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_eight, BalanceQ.liftRec, DenXJ8.keyX, DenXJ8.keyXN, recDen]
  simp [ChipHX.RE.ev, tP, t1, t2, t3, t4, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

/-- The run's twin base columns are the honest stage-1 columns of the BFS rows. -/
theorem basesA_getD (j : ℕ) (hj : j < (ComplJ9ARun.W9 t).length) :
    (ComplJ9ABalX.basesA p Rg Rt hgen).getD j (fun _ => 0) =
      HonestTraceX9.baseT9 (DA).H (DA).pd (ComplJ9ARun.idOfA (p := p) Rt hgen) (ComplJ9ARun.W9 t) j := by
  have hl : j < (ComplJ9ABalX.basesA p Rg Rt hgen).length := by
    simp [ComplJ9ABalX.basesA, ComplJ9ADataRec.basesA9, hj]
  rw [List.getD_eq_getElem _ _ hl]
  simp [ComplJ9ABalX.basesA, ComplJ9ADataRec.basesA9, ComplJ9ARun.idOfA]
  rfl

variable (hpG : p = Nock.Atoms.p) (h31A : ComplJ9ARun.Rows31A (ComplJ9ADataRec.j9aDataOf p Rg Rt hgen))
include hpG h31A

local notation "BA" => ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A

set_option maxHeartbeats 1000000 in
/-- **`hρA`: the twin compute's export total `ρ 3` is the weighted total of the twin compute's export consumes**
(the `hρA` binder of `ComplJ9ABalG1.hGx_A_of`), under the J-9 A axis binder `hax9`, J-9 B's op-5 binder `hop5`
and the cell-closure binder `Sub9`. -/
theorem hC_runA (hax9 : ComplJ9ABinders.ProgAxOK9A p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (hsub : Sub9 (p := p) Rt hgen) :
    ∀ χ, (BA).Good χ → ((BA).M χ).ρ 3 =
      wsum (ComplJ9ABalG1.GA δ b Rt hgen hpG h31A χ) (ComplJ9ABalG1.csA (p := p) Rt hgen) := by
  intro χ hχ
  have hmC : (DA).cells.length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hlen : (DA).cells.length < p :=
    lt_of_le_of_lt (ComplJ9ARun.h31_run (p := p) Rt hgen h31A _ hmC)
      (lt_trans (by norm_num) (ComplJ9AOfComp.p63_of hpG))
  show ComplJ9ARun.ρA δ b Rt hgen χ 3 = _
  have h3 : ComplJ9ARun.ρA δ b Rt hgen χ 3 = Quad.mk _ (ComplJ9ARun.accTA δ b Rt hgen χ 0)
      (ComplJ9ARun.accTA δ b Rt hgen χ 1) := by
    simp [ComplJ9ARun.ρA]
  rw [h3]
  unfold ComplJ9ARun.accTA
  rw [ComplJ9ARun.N9_def]
  rw [acc_rows9 δ b (DA).H (DA).pd (ComplJ9ARun.idOfA (p := p) Rt hgen) (ComplJ9ARun.W9 t) (chalVJ8 b χ)
    (fun _ => 0) ChipHX.Bal.x 0 rfl rfl]
  unfold ComplJ9ABalG1.csA
  rw [wsum_flatMap, ← ComplJ8OfBal.sum_range_getD' (fun _ => 0)]
  have hlb : (ComplJ9ABalX.basesA p Rg Rt hgen).length = (ComplJ9ARun.W9 t).length := by
    simp [ComplJ9ABalX.basesA, ComplJ9ADataRec.basesA9]
  rw [hlb]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [termQX9_x δ b _ _ _ _ _ _ j (ComplJ9AOfComp.s10B_rows hgen j (by rw [ComplJ9ARun.N9_def]; exact hj')),
    xSum_run9 δ b Rt hgen hpG hax9 hop5 hsub hlen _ (powN_ok _ (le_two_pow_ht _ hmC)).1 χ _ j hj',
    basesA_getD Rt hgen j hj']

end Run

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalCR
