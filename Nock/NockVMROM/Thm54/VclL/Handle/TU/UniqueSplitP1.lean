/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/UniqueSplitP1.lean

 **Trace uniqueness on the P1 fragment: breaking the `hkey` / `hreqs` circularity of `UniqueCloseP1`.**

 * §1 `clrRow` (a cell row with its multiplicities `mv mx` zeroed): equal `clrRow` images carry the same
 `CellRel` facts (`cellRel_of_clr`) and the same export records (`exportRecK_clrRow`).
 * §2 the walk over the non-multiplicity cell table: **`walk_closed_nm`** = `WalkCloseP1.walk_closed` with
 `hcell` weakened to `hcellN : tab.map clrRow = tab'.map clrRow` (`walk_labels_eq_nm`, `walk_kv_eq_nm`).
 * §3 (i) `r0M_nm_closed`: the non-multiplicity round-0 cell columns and the aux columns from the noun set alone;
 (ii) `roles_nm` (the fingerprint roles), `keys_of_nm` (= `hkey`), `hcellN_of_nm` (= `hcellN`).
 * §4 `b0_eq_nm` (`CellUniqP1.b0_eq_of_r0M` after `clr`) and `r0C_closed_nm` (`r0C_closed` from the
 non-multiplicity cell round 0).
 * §5 (iii) `vReqs` (the V consumer list, `LinkJ8XUA.rdV`'s right-hand side) and `vReqs_eq`; (iv) the
 multiplicities via `r0M_auxM_closed''`; **`trace_unique_closed'`**: `trace_unique_closed` with `hkey` derived,
 the V part of `hreqs` derived, and the X / H parts reduced to congruence hypotheses `hreqX`, `hreqH` over the
 walk / compute round-0 (and walk round-1) agreement, which the proof supplies AFTER the walk and compute
 closes, so no cycle remains.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueCloseP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1

noncomputable section

open Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1 (MulCol clr)

/-! ## 1. Cell rows modulo the multiplicities -/

section ClrRow
open Nock.NockVMROM.Thm54.VclL
variable {q : ℕ} {Kfp : Type*}

/-- A cell row with the multiplicities of its B0 part zeroed. -/
def clrRow (c : CellRow q Kfp) : CellRow q Kfp := ⟨clr c.b0, c.p, c.l, c.r⟩

theorem mem_of_clr {t t' : List (CellRow q Kfp)} (h : t.map clrRow = t'.map clrRow) {c' : CellRow q Kfp}
    (hc' : c' ∈ t') : ∃ c ∈ t, clrRow c = clrRow c' := by
  have : clrRow c' ∈ t.map clrRow := by rw [h]; exact List.mem_map_of_mem hc'
  exact List.mem_map.mp this

theorem exportRecK_clrRow {c c' : CellRow q Kfp} (h : clrRow c = clrRow c') :
    exportRecK c'.b0 = exportRecK c.b0 := by
  have hb : clr c.b0 = clr c'.b0 := congrArg CellRow.b0 h
  calc exportRecK c'.b0 = exportRecK (clr c'.b0) := rfl
    _ = exportRecK (clr c.b0) := by rw [hb]
    _ = exportRecK c.b0 := rfl

theorem cellRel_of_clr {t t' : List (CellRow q Kfp)} (h : t.map clrRow = t'.map clrRow) {i : ℕ}
    {pp l r : Nock.ComputeTable.FP Kfp} (hr : WalkCloseP1.CellRel t' i pp l r) : WalkCloseP1.CellRel t i pp l r := by
  obtain ⟨c', hc', e1, e2, e3, e4⟩ := hr
  obtain ⟨c, hc, hcc⟩ := mem_of_clr h hc'
  have hb : (clrRow c).b0.idx = (clrRow c').b0.idx := by rw [hcc]
  have hp : (clrRow c).p = (clrRow c').p := by rw [hcc]
  have hl : (clrRow c).l = (clrRow c').l := by rw [hcc]
  have hr' : (clrRow c).r = (clrRow c').r := by rw [hcc]
  exact ⟨c, hc, hb.trans e1, hp.trans e2, hl.trans e3, hr'.trans e4⟩

end ClrRow

/-! ## 2. The walk over the non-multiplicity cell table -/

section WalkNm
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qW qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (WT envQ_eq lbl_cols pF CoversW trieW AgreeW)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkForestP1 (walkW)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1 (rowIx rowIx_val)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K) [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Pb : PubJ8 p}

open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (walkJ8_bfsRows P fo side P_congr root_cols AgreeW r0W_auxW_r1W)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (childHOfK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1

/-- **`walk_labels_eq` over the non-multiplicity cell table.** -/
theorem walk_labels_eq_nm {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {r : RowsJ8} {g : ℕ} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (hout' : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M'.pubsW tr'))
    (hTr : ∀ j < Pb.nW, ∀ col ∈ trieW, (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace col =
      (envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace col)
    (hIr : ∀ j < Pb.kroots, (envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.idx =
      (envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.idx)
    (hX : KeysExported (cellTab δ b (Pb := Pb) χ M.pubsC tr) (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr).X)
    (hX' : KeysExported (cellTab δ b (Pb := Pb) χ M'.pubsC tr') (WT δ b Pb (chalsMJ8 δ χ) M'.pubsW tr').X)
    (hcellN : (cellTab δ b (Pb := Pb) χ M.pubsC tr).map clrRow = (cellTab δ b (Pb := Pb) χ M'.pubsC tr').map clrRow)
    (hfp : ∀ c1 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr, ∀ c2 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      c1.p = c2.p → c1.b0.idx = c2.b0.idx) :
    (∀ i : Fin Pb.nW, (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i) =
      (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i)) ∧
    (∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 →
      ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) := by
  have hA := h.1.1
  have hA' := h'.1.1
  have hq : 2 ^ 63 < ringChar (ZMod p) := two63_lt_ringChar hpG
  have hkp' : Pb.kroots + Pb.nW < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hkp
  obtain ⟨B, hx, hrt, hch⟩ := walk_label_data δ b hA hq hk hkn hkp' hout hX
  obtain ⟨B', hx', hrt', hch'⟩ := walk_label_data δ b hA' hq hk hkn hkp' hout' hX'
  set chals := chalsMJ8 δ χ with hchals
  have hflag : ∀ j < Pb.nW, stW δ b (Pb := Pb) tr' chals M'.pubsW j = stW δ b (Pb := Pb) tr chals M.pubsW j := by
    intro j hj
    have l1 := lbl_cols δ b Pb tr chals M.pubsW hj
    have l2 := lbl_cols δ b Pb tr' chals M'.pubsW hj
    show ((WT δ b Pb chals M'.pubsW tr').lbl (j + 1)).1 = ((WT δ b Pb chals M.pubsW tr).lbl (j + 1)).1
    rw [l1.1, l2.1]
    have c1 := hTr j hj WChip.cL (by simp [trieW, WChip.cL])
    have c2 := hTr j hj WChip.cR (by simp [trieW, WChip.cR])
    rw [c1, c2]
  have hs := cellTab_serial δ b hA
  have hfun := cellRel_fun hs
  have hinj := cellRel_inj hfp
  have key := labels_pair B (CellRel (cellTab δ b (Pb := Pb) χ M.pubsC tr)) hfun hinj
    (ixW δ b (Pb := Pb) tr chals M.pubsW) (ixW δ b (Pb := Pb) tr' chals M'.pubsW)
    (fun j => fpW δ b (Pb := Pb) tr chals M.pubsW j WChip.pR)
    (fun j => fpW δ b (Pb := Pb) tr chals M.pubsW j WChip.lR)
    (fun j => fpW δ b (Pb := Pb) tr chals M.pubsW j WChip.rR)
    (fun j => fpW δ b (Pb := Pb) tr chals M.pubsW j WChip.rootR)
    (fun j => fpW δ b (Pb := Pb) tr' chals M'.pubsW j WChip.pR)
    (fun j => fpW δ b (Pb := Pb) tr' chals M'.pubsW j WChip.lR)
    (fun j => fpW δ b (Pb := Pb) tr' chals M'.pubsW j WChip.rR)
    (fun j => fpW δ b (Pb := Pb) tr' chals M'.pubsW j WChip.rootR)
    (stW δ b (Pb := Pb) tr' chals M'.pubsW) hflag hx
    (fun j hj => cellRel_of_clr hcellN (hx' j hj))
    hrt hrt' hch hch'
    (fun j hj => by
      have e := hIr j hj
      simp only [ixW]
      rw [rowF_idx δ b tr chals M.pubsW (by omega), rowF_idx δ b tr' chals M'.pubsW (by omega)]
      rw [envB_eval δ b Pb tr _ _ (by decide) (by omega), envB_eval δ b Pb tr' _ _ (by decide) (by omega)] at e
      rw [e])
  have hidx : ∀ i : Fin Pb.nW, (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i) =
      (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i) := by
    intro i
    obtain ⟨e, -⟩ := key i i.isLt
    simp only [ixW] at e
    rw [rowF_idx δ b tr chals M.pubsW i.isLt, rowF_idx δ b tr' chals M'.pubsW i.isLt] at e
    exact natOf_inj pF e
  refine ⟨hidx, ?_⟩
  intro jc h25 h97 i
  obtain ⟨-, hP, hL, hR, hRt⟩ := key i i.isLt
  have main : ∀ r0 t k : ℕ, fpW δ b (Pb := Pb) tr chals M.pubsW i r0 = fpW δ b (Pb := Pb) tr' chals M'.pubsW i r0 →
      t < 6 → k < 3 → (jc : ℕ) = 21 + 3 * (r0 + t) + k + 4 →
      (tr.W jc).eval (Pb.nodesW i) = (tr'.W jc).eval (Pb.nodesW i) := by
    intro r0 t k hr0 ht hk hjc
    have h1 := fp_cols δ Pb.kroots b
      (rowF δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) i)
      (rowF δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M'.pubsW (qW δ b Pb tr' chals M'.pubsW) i)
      hr0 t ht k hk
    have hlt : 21 + 3 * (r0 + t) + k < 132 := by
      have := jc.isLt; omega
    rw [rowF_hi δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M.pubsW (qW δ b Pb tr chals M.pubsW) i.isLt
        (by omega) hlt,
      rowF_hi δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals M'.pubsW (qW δ b Pb tr' chals M'.pubsW) i.isLt
        (by omega) hlt] at h1
    have hjc' : jc = ⟨21 + 3 * (r0 + t) + k + 4, by have := jc.isLt; omega⟩ := Fin.ext hjc
    rw [hjc']
    exact h1
  have hq4 : ((jc : ℕ) - 25) / 3 / 6 = 0 ∨ ((jc : ℕ) - 25) / 3 / 6 = 1 ∨ ((jc : ℕ) - 25) / 3 / 6 = 2 ∨ ((jc : ℕ) - 25) / 3 / 6 = 3 := by
    have := jc.isLt; omega
  rcases hq4 with e | e | e | e
  · exact main 0 (((jc : ℕ) - 25) / 3 % 6) (((jc : ℕ) - 25) % 3) hP (by omega) (by omega) (by omega)
  · exact main 6 (((jc : ℕ) - 25) / 3 % 6) (((jc : ℕ) - 25) % 3) hL (by omega) (by omega) (by omega)
  · exact main 12 (((jc : ℕ) - 25) / 3 % 6) (((jc : ℕ) - 25) % 3) hR (by omega) (by omega) (by omega)
  · exact main 18 (((jc : ℕ) - 25) / 3 % 6) (((jc : ℕ) - 25) % 3) hRt (by omega) (by omega) (by omega)


/-- **`walk_kv_eq` over the non-multiplicity cell table.** -/
theorem walk_kv_eq_nm {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {r : RowsJ8} {g : ℕ} (hA : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hidx : ∀ i : Fin Pb.nW, (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i) =
      (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i))
    (hH : ∀ j < Pb.nW, ∃ c' ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j).trace WChip.idx),
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) false,
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) true) = exportRecK c'.b0)
    (hH' : ∀ j < Pb.nW, ∃ c' ∈ cellTab δ b (Pb := Pb) χ M'.pubsC tr',
      (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j).trace WChip.idx),
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j) false,
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j) true) = exportRecK c'.b0)
    (hcellN : (cellTab δ b (Pb := Pb) χ M.pubsC tr).map clrRow = (cellTab δ b (Pb := Pb) χ M'.pubsC tr').map clrRow) :
    AgreeW Pb tr tr' [21, 22, 23, 24] := by
  have hs := cellTab_serial δ b hA
  intro jc hjc i
  obtain ⟨c1, hc1, e1⟩ := hH i i.isLt
  obtain ⟨c2', hc2', e2⟩ := hH' i i.isLt
  obtain ⟨c2, hc2, h22⟩ := mem_of_clr hcellN hc2'
  rw [exportRecK_clrRow h22] at e2
  simp only [exportRecK, Prod.mk.injEq] at e1 e2
  have hid : c1.b0.idx = c2.b0.idx := by
    rw [← e1.1, ← e2.1, walkEnvFA_col δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ i.isLt (Or.inl (by decide))
      (by decide), walkEnvFA_col δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ i.isLt (Or.inl (by decide))
      (by decide)]
    exact congrArg natOf (hidx i)
  have hcc := serial_unique hs c1 hc1 c2 hc2 hid
  subst hcc
  have eL := e1.2.1.trans e2.2.1.symm
  have eR := e1.2.2.trans e2.2.2.symm
  simp only [childHOfK, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at eL eR
  have col : ∀ (cc : ℕ) (hcc : cc < 166), (cc = 21 ∨ cc = 22 ∨ cc = 23 ∨ cc = 24) →
      natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) i).trace cc) =
        natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) i).trace cc) →
      (tr.W ⟨cc, hcc⟩).eval (Pb.nodesW i) = (tr'.W ⟨cc, hcc⟩).eval (Pb.nodesW i) := by
    intro cc hcc hc hn
    rw [walkEnvFA_col δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ i.isLt (Or.inr (by omega)) hcc,
      walkEnvFA_col δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW _ _ _ i.isLt (Or.inr (by omega)) hcc] at hn
    exact natOf_inj pF hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hjc
  have hj166 := jc.isLt
  have hjce : jc = ⟨(jc : ℕ), hj166⟩ := rfl
  rw [hjce]
  refine col jc hj166 (by omega) ?_
  rcases hjc with e | e | e | e
  · rw [e]; exact eL.1
  · rw [e]; exact eL.2
  · rw [e]; exact eR.1
  · rw [e]; exact eR.2

/-- **`walk_closed_nm`**: `WalkCloseP1.walk_closed` with `hcell` weakened to `hcellN`. -/
theorem walk_closed_nm {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Rg : Nock.Jet.Registry}
    {c : P8PublicClaim} {χ : Coins frameJ8 K} {r : RowsJ8} {g : ℕ} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hk : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hout : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr))
    (hout' : (chalsMJ8 δ χ 0, chalsMJ8 δ χ 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (WT δ b Pb (chalsMJ8 δ χ) M'.pubsW tr'))
    -- the walk's export keys are cell rows, the cell tables agree, fingerprints are collision-free
    (hX : KeysExported (cellTab δ b (Pb := Pb) χ M.pubsC tr) (WT δ b Pb (chalsMJ8 δ χ) M.pubsW tr).X)
    (hX' : KeysExported (cellTab δ b (Pb := Pb) χ M'.pubsC tr') (WT δ b Pb (chalsMJ8 δ χ) M'.pubsW tr').X)
    (hcellN : (cellTab δ b (Pb := Pb) χ M.pubsC tr).map clrRow = (cellTab δ b (Pb := Pb) χ M'.pubsC tr').map clrRow)
    (hfp : ∀ c1 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr, ∀ c2 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      c1.p = c2.p → c1.b0.idx = c2.b0.idx)
    -- the handle-export records
    (hH : ∀ j < Pb.nW, ∃ c' ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j).trace WChip.idx),
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) false,
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
            (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) true) = exportRecK c'.b0)
    (hH' : ∀ j < Pb.nW, ∃ c' ∈ cellTab δ b (Pb := Pb) χ M'.pubsC tr',
      (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j).trace WChip.idx),
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j) false,
        childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
          (bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
            (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW)) j) true) = exportRecK c'.b0)
    -- the path-record balance
    (reqs reqs' : List (Fin 5 → K)) (provs provs' : List ((Fin 5 → K) × K))
    (hbal : ∀ r, (reqs.count r : K) = pw provs r) (hd : (provs.map Prod.fst).Nodup)
    (hsub : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW), q ∈ provs)
    (hbal' : ∀ r, (reqs'.count r : K) = pw provs' r) (hd' : (provs'.map Prod.fst).Nodup)
    (hsub' : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
      (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW), q ∈ provs')
    (hreq : ∀ r, reqs.count r = reqs'.count r)
    -- the reads, or the extra pin (E10)
    (noPath : Prop)
    (hE10 : noPath → (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hE10' : noPath → (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hnW1 : noPath → Pb.nW = 1)
    (R : Finset (ℕ × ℕ)) (hsz : ¬ noPath → (readClosure R).card = Pb.nW)
    (hprov : ¬ noPath → ∀ s ∈ R, ∃ j < Pb.nW,
      natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) = s.1 ∧
        natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.pre) = s.2 / 2)
    (hprov' : ¬ noPath → ∀ s ∈ R, ∃ j < Pb.nW,
      natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.ridx) = s.1 ∧
        natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.pre) = s.2 / 2) :
    (∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) ∧
      (∀ j i, (ax.W j).eval (Pb.nodesW i) = (ax'.W j).eval (Pb.nodesW i)) ∧
      (∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 →
        ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) := by
  have hq : 2 ^ 63 < ringChar (ZMod p) := two63_lt_ringChar hpG
  have hkp' : Pb.kroots + Pb.nW < ringChar (ZMod p) := by rw [ZMod.ringChar_zmod_n]; exact hkp
  -- the labels, from the trie
  have lab : AgreeW Pb tr tr' trieW →
      (∀ i : Fin Pb.nW, (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i) =
        (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW i)) ∧
      (∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 →
        ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) := fun hTr =>
    walk_labels_eq_nm δ b h h' hk hkn hkp hout hout' (agreeW_to_envB δ b hTr)
      (rootIdx_of_trie δ b h h' hkn hTr) hX hX' hcellN hfp
  refine r0W_auxW_r1W δ b h h' hk hkn hkp hout hout' (roots_lt δ b h hkn hX) (roots_lt δ b h' hkn hX')
    noPath hE10 hE10' hnW1 ?_ (fun hTr i _ => (lab hTr).1 i) ?_ ?_ (fun hTr _ => (lab hTr).2)
  · intro hnp
    exact ⟨readClosure R, hsz hnp,
      coversW_of_reads δ b h.1.1 hq hk hkn hkp' hout R (hprov hnp),
      coversW_of_reads δ b h'.1.1 hq hk hkn hkp' hout' R (hprov' hnp)⟩
  · intro hTr
    exact walk_mLR_eq δ b reqs reqs' provs provs' hbal hd hsub hbal' hd' hsub' hreq hTr
      (walk_kv_eq_nm δ b h.1.1 (lab hTr).1 hH hH' hcellN)
  · intro hTr
    exact walk_kv_eq_nm δ b h.1.1 (lab hTr).1 hH hH' hcellN

end WalkNm

/-! ## 3. The cell table at trace level without the multiplicities: round 0, the keys, the rows -/

section TraceNm
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qW qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (bitFix)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (childHOfK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A (rAT)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1 (dataA trace_unique_good'')
open Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1 (qCell keyVOf keyXOf keyHOf r0M_auxM_closed'' extB_atoms)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1 (envB)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (WT)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1 (cellTab readClosure walk_closed)
open Nock.Edit.GenX (P1Frag genX SkelX)
open Nock.V1J8.Gen (cellsOfRoots rootsOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)

open Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetP1 (nounSet_of_accepts hset_of_closure)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0MP1 (tableM_of_accepts)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.CellOrderP1 (vM_base vM_aux)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1 (denC hDN_of_accepts hrowsC_of_bridge)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (RowVSX)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1 (RowAgreeX)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **(i) The non-multiplicity round-0 cell columns and the aux columns agree**, from the noun set alone
(`r0M_auxM_closed` without the counts `C`, `C'`, `hreqs`, `hkey`). -/
theorem r0M_nm_closed {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {Pb : PubJ8 p}
    {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ}
    {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsCanon δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)))
    (hS' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')))
    {ext ext' : ℕ → Option Noun} (hext : ∀ j X, ext j = some X → ∃ a, X = .atom a)
    (hext' : ∀ j X, ext' j = some X → ∃ a, X = .atom a)
    {R : Nock.Jet.Registry} {fuel : ℕ} {tg : NTree SkelX} {rr : Noun} (hfrag : P1Frag c.formula)
    (hg : genX R fuel c.subject c.formula = some (tg, rr))
    (hsz : Pb.nC = (cellsOfRoots (rootsOf c (rowsOfT tg))).length)
    {n n' : ℕ} {d d' : ℕ → RowVSX}
    (hB : (bfsForest [tg]).length = n ∧ ∀ j (hj : j < (bfsForest [tg]).length),
      RowAgreeX (denC δ b Pb χ M tr ext) (d j) ((bfsForest [tg])[j]'hj).label)
    (hB' : (bfsForest [tg]).length = n' ∧ ∀ j (hj : j < (bfsForest [tg]).length),
      RowAgreeX (denC δ b Pb χ M' tr' ext') (d' j) ((bfsForest [tg])[j]'hj).label)
    (hs : ∃ hd, denC δ b Pb χ M tr ext hd = some c.subject)
    (hf : ∃ hd, denC δ b Pb χ M tr ext hd = some c.formula)
    (he : ∃ hd, denC δ b Pb χ M tr ext hd = some c.result)
    (hs' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.subject)
    (hf' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.formula)
    (he' : ∃ hd, denC δ b Pb χ M' tr' ext' hd = some c.result) :
    (∀ j : Fin 242, (j : ℕ) < 134 → ¬ MulCol j → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) ∧
      (∀ j i, (ax.M j).eval (Pb.nodesC i) = (ax'.M j).eval (Pb.nodesC i)) := by
  obtain ⟨L, e1⟩ := nounSet_of_accepts δ b h hS (rowsOfT tg) hsz (hDN_of_accepts δ b h hS hext)
    (hrowsC_of_bridge c hfrag hg hB hs hf he)
  obtain ⟨L', e2⟩ := nounSet_of_accepts δ b h' hS' (rowsOfT tg) hsz (hDN_of_accepts δ b h' hS' hext')
    (hrowsC_of_bridge c hfrag hg hB' hs' hf' he')
  obtain ⟨T, K⟩ := tableM_of_accepts δ b h
  obtain ⟨T', K'⟩ := tableM_of_accepts δ b h'
  have hnp : Pb.nC ≤ p := by
    have := h.1.hnpC; rw [ZMod.ringChar_zmod_n] at this; omega
  obtain ⟨-, hcol⟩ := cols_eq_of_set_nm T L K T' L' K' hpG hnp hnp (hset_of_closure e1 e2)
  have hPb := h.2.hPb
  subst hPb
  refine ⟨fun j hj hm i => ?_, fun j i => ?_⟩
  · have := hcol i i.isLt j (by omega) hm
    rw [vM_base tr ax _ i hj, vM_base tr' ax' _ i hj] at this
    exact this
  · have := hcol i i.isLt (SideM.A + j) (by simp only [SideM.A]; omega) (by simp only [MulCol, SideM.A]; omega)
    rw [vM_aux tr ax _ i j.isLt, vM_aux tr' ax' _ i j.isLt] at this
    exact this

/-- The non-multiplicity round-0 agreement, read on the wire chip's base environment. -/
theorem hqkEF_nm {Pb : PubJ8 p} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)}
    (hnm : ∀ j : Fin 242, (j : ℕ) < 134 → ¬ MulCol j → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) :
    ∀ (i : Fin Pb.nC) (j : ℕ), j < 134 → ¬ MulCol j →
      (TwoProviderQ.hqkEF b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) i).trace j =
      (TwoProviderQ.hqkEF b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC) i).trace j := by
  intro i j hj hm
  have hw : j < (CellTwinKW.cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.w := by
    rw [CellTwinKW.cellChipHQKW_width]; omega
  have hw' : j < (CellTwinKW.cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC).rap.w := by
    rw [CellTwinKW.cellChipHQKW_width]; omega
  simp only [TwoProviderQ.hqkEF, Reify.envOfTrace, dif_pos hw, dif_pos hw']
  exact hnm ⟨j, by omega⟩ hj hm i

/-- The non-multiplicity round-0 agreement, read on the restricted cell chip's base environment. -/
theorem cellEnvF_nm {Pb : PubJ8 p} {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)}
    (hnm : ∀ j : Fin 242, (j : ℕ) < 134 → ¬ MulCol j → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) :
    ∀ (i : Fin Pb.nC) (j : ℕ), j < 129 → ¬ MulCol j →
      (cellEnvF b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr) i).trace j =
      (cellEnvF b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr') i).trace j := by
  intro i j hj hm
  have e1 := (CellUniqP1.restr_trace δ b Pb tr (chalsMJ8 δ χ) M.pubsC i hj).1
  have e2 := (CellUniqP1.restr_trace δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC i hj).1
  exact e1.trans ((hnm ⟨j, by omega⟩ (by simp; omega) hm i).trans e2.symm)

/-- **(ii) The fingerprint roles `0 .. 17` of the restricted cell chip agree**, from the non-multiplicity round 0. -/
theorem roles_nm {hpG : p = Nock.Atoms.p} {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim}
    {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h' : AcceptsJ8V δ b Pb Rg c χ M' tr' r g)
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)))
    (hS' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')))
    (hnm : ∀ j : Fin 242, (j : ℕ) < 134 → ¬ MulCol j → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) :
    ∀ (i : Fin Pb.nC), ∀ r < 18,
      (cellEnvK δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr) i).trace r =
      (cellEnvK δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr') i).trace r := by
  have hr1 := cell_round1_eq_nm δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC M'.pubsC
    (GeneratedField.primeFieldElems_zmod p) (two63_lt_ringChar hpG) hz h.hsatC h'.hsatC h.hbindC h'.hbindC h.hinjC
    h.hadjC h.hnpC hS hS' (hqkEF_nm δ b hnm)
  intro i r hr
  rw [RoundsCellP1.cellEnvK_trace_eq δ b Pb.hnC Pb.nodesC Pb.orbitC _ M.pubsC _ i (by omega),
    RoundsCellP1.cellEnvK_trace_eq δ b Pb.hnC Pb.nodesC Pb.orbitC _ M'.pubsC _ i (by omega)]
  exact hr1 i r hr

/-- **(ii) The row keys agree** (`hkey` of `r0M_auxM_closed''`), from the non-multiplicity round 0. -/
theorem keys_of_nm {hpG : p = Nock.Atoms.p} {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim}
    {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h' : AcceptsJ8V δ b Pb Rg c χ M' tr' r g)
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)))
    (hS' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')))
    (hnm : ∀ j : Fin 242, (j : ℕ) < 134 → ¬ MulCol j → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) :
    ∀ i < Pb.nC, keyVOf δ b Pb χ M tr i = keyVOf δ b Pb χ M' tr' i ∧
      keyXOf δ b 0 Pb χ M tr i = keyXOf δ b 0 Pb χ M' tr' i ∧
      keyXOf δ b 1 Pb χ M tr i = keyXOf δ b 1 Pb χ M' tr' i ∧ keyHOf δ b Pb χ M tr i = keyHOf δ b Pb χ M' tr' i := by
  have hK := roles_nm δ b (hpG := hpG) h h' hz hS hS' hnm
  have hF := cellEnvF_nm δ b (χ := χ) (M := M) (M' := M') hnm
  intro i hi
  obtain ⟨kV, kX0, kX1⟩ := keys_cong_nm δ (hK ⟨i, hi⟩) (hF ⟨i, hi⟩ _ (by decide) (by decide))
    (hF ⟨i, hi⟩ _ (by decide) (by decide)) (hF ⟨i, hi⟩ _ (by decide) (by decide))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [keyVOf, dif_pos hi]; exact keyVec_congr δ kV
  · simp only [keyXOf, dif_pos hi]; exact keyVec_congr δ kX0
  · simp only [keyXOf, dif_pos hi]; exact keyVec_congr δ kX1
  · simp only [keyHOf, dif_pos hi]; exact keyVec5_keyHK_congr_nm (hqkEF_nm δ b (χ := χ) (M := M) (M' := M') hnm ⟨i, hi⟩)

/-- **The two cell tables agree modulo the multiplicities** (`hcellN` of `walk_closed_nm`). -/
theorem hcellN_of_nm {hpG : p = Nock.Atoms.p} {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim}
    {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h' : AcceptsJ8V δ b Pb Rg c χ M' tr' r g)
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)))
    (hS' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')))
    (hnm : ∀ j : Fin 242, (j : ℕ) < 134 → ¬ MulCol j → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) :
    (cellTab δ b (Pb := Pb) χ M.pubsC tr).map clrRow = (cellTab δ b (Pb := Pb) χ M'.pubsC tr').map clrRow := by
  have hK := roles_nm δ b (hpG := hpG) h h' hz hS hS' hnm
  have hF := cellEnvF_nm δ b (χ := χ) (M := M) (M' := M') hnm
  simp only [cellTab, cellTableOf, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply, clrRow, cellRowOf]
  have fp : ∀ r0, r0 + 6 ≤ 18 →
      (QFP.var r0 : QFP (ZMod p)).ev δ (cellEnvK δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr) i)
        (cellEnvF b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr) i) =
      (QFP.var r0 : QFP (ZMod p)).ev δ (cellEnvK δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr') i)
        (cellEnvF b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr') i) := by
    intro r0 hr0
    rw [QFP.ev_var, QFP.ev_var, RoundsCellP1.var_cong δ (hK i) r0 (by omega),
      RoundsCellP1.var_cong δ (hK i) (r0 + 2) (by omega), RoundsCellP1.var_cong δ (hK i) (r0 + 4) (by omega)]
  rw [cellB0Of_clr_congr (fun j hj hm => hF i j hj hm), fp Cell.pR (by decide), fp Cell.lR (by decide),
    fp Cell.rR (by decide)]

end TraceNm

/-! ## 4. The compute round 0 and the claim serials without the multiplicities -/

section R0CNm
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.Framework.Reify
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe realize40 realizeJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3
open Nock.NockVMROM.Thm54.VclL.Handle.LinkQ2J8 (valReader)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (rowsMJ8 rowsB0 crA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (censusList2)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z atomTZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_of_ne chalsAJ8Z_ok chalsAJ8Z_agree)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4 (RR4 LL4 hHXV_ofZ)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun claimH isCellN)
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crA crM crW crC staged_eq below_of_mem shV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (mbXs claimCells claimRecsJ8 pinRecsJ8 rkC MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z chalsAJ8Z_zAt)
open Nock.NockVMROM.Thm54.VclL.Handle.RealVJ8
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R4
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R5
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (xS xF xE)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (envCJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP (toMsgJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 St40 sum40 fpx_out v4 v5 v6 v7)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (extY_below shV_round)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z (AcceptsJ8Z)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8 (RowsAccXI)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8 (combN)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinLinkJ8A
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1 (SizesP1 canonPb canonC canonM sideCQ sideMQ AuxP1 padA)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (acceptsJ8ZA_of_V toMsgJ8ZA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A (rAT)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1 (SerialUnique r0C_of_twins claim_of_unique envsN_envC)
open Nock.Edit.GenX (P1Frag genX)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r r' : RowsJ8} {P g P' g' : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CCloseP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1 (MulCol clr preZ2_clr cellB0Of_clr_congr)

/-- **`CellUniqP1.b0_eq_of_r0M` over the non-multiplicity columns**: the restricted cell tables' B0 rows agree
after `clr`. -/
theorem b0_eq_nm (Pb : PubJ8 p) {tr tr' : TrJ8 (ZMod p)} (chals pubs chals' pubs' : ℕ → K)
    (hr : ∀ j : Fin 242, (j : ℕ) < 134 → ¬ MulCol j → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) :
    ((cellTableOf δ b Pb.nodesC Pb.orbitC chals pubs
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs (qM δ b Pb tr chals pubs))).map (·.b0)).map clr =
    ((cellTableOf δ b Pb.nodesC Pb.orbitC chals' pubs'
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC chals' pubs' (qM δ b Pb tr' chals' pubs'))).map (·.b0)).map clr := by
  simp only [cellTableOf, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply]
  refine cellB0Of_clr_congr (fun j hj hm => ?_)
  have e1 := (CellUniqP1.restr_trace δ b Pb tr chals pubs i hj).1
  have e2 := (CellUniqP1.restr_trace δ b Pb tr' chals' pubs' i hj).1
  exact e1.trans ((hr ⟨j, by omega⟩ (by simp; omega) hm i).trans e2.symm)

/-- **`OpenR0CCloseP1.r0C_closed` from the non-multiplicity cell round 0** (`hr0M` weakened to `hnm`): the serial
uniqueness reads the B0 decoder, which reads no multiplicity (`preZ2_clr`). -/
theorem r0C_closed_nm [CharP K p] [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {c : P8PublicClaim} {Pb : PubJ8 p} (hPb : Pb = canonPb hpG sz c) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (χ : Coins frameJ8 K) (M M' : MsgJ8' p K δ) (tr tr' : TrJ8 (ZMod p)) (ax : AuxP1 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (R' : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r' P' g')
    (L' : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r')
    (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hqM' : ∀ x < ringChar (ZMod p), lenL x ≤ r'.maxlen) (hk' : 2 * fuelChip ≤ r'.leaves)
    {r0 r0' : RowsJ8} {g0 g0' : ℕ} (hacc3 : AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M tr r0 g0)
    (hacc3' : AcceptsJ8V.AcceptsJ8V δ b Pb Rg c χ M' tr' r0' g0') (h0 : Pb.krootsV = 0)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b (withLiftC R L) Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV
      Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    (hout' : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b (withLiftC R' L') Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV
      Pb.nodesA Pb.orbitA), ¬ s.mem tr' χ)
    (hl : LinkJ8XUA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M tr) tr R L (rAT b Pb tr))
    (hl' : LinkJ8XUA δ b Pb c χ (toMsgJ8ZA δ b Pb c χ M' tr') tr' R' L' (rAT b Pb tr'))
    (hC : (canonC b Pb).Satisfies (sideCQ tr)) (hC' : (canonC b Pb).Satisfies (sideCQ tr'))
    (hM : (canonM b Pb).Satisfies (sideMQ tr ax))
    (hA : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j))
    (hA' : ∀ j : Fin 349, (j : ℕ) < 205 → tr'.A j = Polynomial.C (padA j))
    (hnm : ∀ j : Fin 242, (j : ℕ) < 134 → ¬ MulCol j → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i))
    (hfrag : P1Frag c.formula) {fuel : ℕ} {tg : NTree Nock.Edit.GenX.SkelX} {res : Noun}
    (hg : genX Rg fuel c.subject c.formula = some (tg, res)) :
    (∀ j : Fin 123, (j : ℕ) < 69 → ∀ i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i)) ∧
    (∀ k, isCellN (claimNoun c k) = true → (M.m k).1 = (M'.m k).1) := by
  subst hPb
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  obtain ⟨-, A, hG, hcell, hden, hAx, z, E, vp, hcons, hE, htab, hvp⟩ :=
    hsoundJ8XUA_exA δ b _ hRg c χ M tr R L hpG hqM hk hacc3 h0 hout hl
  obtain ⟨-, A', hG', hcell', hden', hAx', -⟩ :=
    hsoundJ8XUA_exA δ b _ hRg c χ M' tr' R' L' hpG hqM' hk' hacc3' h0 hout' hl'
  have hacc := acceptsJ8ZA_of_V hacc3 h0
  have hacc' := acceptsJ8ZA_of_V hacc3' h0
  have hext := AtomPadP1.extB_rAT_none b (canonPb hpG sz c) (by omega) hA
  have hext' := AtomPadP1.extB_rAT_none b (canonPb hpG sz c) (by omega) hA'
  -- `hU`: one serial per cell noun (the sorted cell table), no big atom (the atom pad)
  have hU : SerialUnique
      (denJ8 δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC) (rAT b (canonPb hpG sz c) tr))
      (denJ8 δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M'.pubsC (qM δ b (canonPb hpG sz c) tr' (chalsMJ8 δ χ) M'.pubsC) (rAT b (canonPb hpG sz c) tr')) := by
    have ht0 := b0_eq_nm δ b _ (chalsMJ8 δ χ) M.pubsC (chalsMJ8 δ χ) M'.pubsC hnm
    have hq : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
    have hvp0 := hvp
    rw [hext] at hvp0
    have hinj1 := CellUniqP1.serial_inj_table hpG hq hcons hE htab hvp0 (by simp [cellTableOf])
      (CellUniqP1.b0_of_canon δ b ax _ _) (CellUniqP1.tableM_of δ b hM hacc.hsatC hacc.hbindC hacc.hinjC)
      (by have := hacc.hnpC; rw [hrc] at this; omega)
    intro k hk i i' X h1 h2
    rcases hk with rfl | rfl
    · simp only [denJ8, denK] at h1 h2
      rw [hext] at h1
      rw [hext', ← preZ2_clr, ← ht0, preZ2_clr] at h2
      exact hinj1 i i' X h1 h2
    · simp [denJ8, denK, hext] at h1
  have hD := AtomBigJ8.denOKX_extB ((cellTableOf δ b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ)
    M.pubsC (CellTwinKW.restrictHQKWCell δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC
      (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b (canonPb hpG sz c) tr (chalsMJ8 δ χ) M.pubsC))).map (·.b0)) p
    (rAT b (canonPb hpG sz c) tr)
  have hD' := AtomBigJ8.denOKX_extB ((cellTableOf δ b (canonPb hpG sz c).nodesC (canonPb hpG sz c).orbitC (chalsMJ8 δ χ)
    M'.pubsC (CellTwinKW.restrictHQKWCell δ b (canonPb hpG sz c).hnC (canonPb hpG sz c).nodesC
      (canonPb hpG sz c).orbitC (chalsMJ8 δ χ) M'.pubsC (qM δ b (canonPb hpG sz c) tr' (chalsMJ8 δ χ) M'.pubsC))).map (·.b0)) p
    (rAT b (canonPb hpG sz c) tr')
  have hB := hdef_of_bridge (K := K) hp hD (canonPb hpG sz c).hn A hG c (hden 0) (hden 1) hfrag
  have hB' := hdef_of_bridge (K := K) hp hD' (canonPb hpG sz c).hn A' hG' c (hden' 0) (hden' 1) hfrag
  refine ⟨r0C_of_twins δ b _ (K := K) hp hacc.hsatX hacc'.hsatX hacc.hinjX hC hC' hRg hD hD' A hG A' hG' c
    (hden 0) (hden 1) (hden' 0) (hden' 1) hfrag hg hU ?_ ?_ ?_ ?_, claim_of_unique hU hcell hcell'⟩
  · intro i h hh
    have := hB i i.isLt h (by simpa only [envX, envsN_envC] using hh)
    simpa only [envX, envsN_envC] using this
  · intro i h hh
    have := hB' i i.isLt h (by simpa only [envX, envsN_envC] using hh)
    simpa only [envX, envsN_envC] using this
  · intro i y hy
    exact hAx i i.isLt y (by simpa only [envX, envsN_envC] using hy)
  · intro i y hy
    exact hAx' i i.isLt y (by simpa only [envX, envsN_envC] using hy)

end R0CNm

/-! ## 5. The V consumer list, and `trace_unique_closed'` -/

section KeysLR
open Nock Nock.Reified Nock.Framework Polynomial Module
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1
variable {F K : Type} [Field F] [Field K] [Algebra F K] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  {eK eK' : Env K} {eF eF' : Env F}

/-- **The consumed child keys read the roles `6 .. 17` and the child columns only.** -/
theorem keysLR_cong_nm (hK : ∀ r < 18, eK.trace r = eK'.trace r)
    (hF : ∀ j ∈ [Cell.loL, Cell.hiL, Cell.idL, Cell.loR, Cell.hiR, Cell.idR], eF.trace j = eF'.trace j) :
    (∀ e ∈ (Cell.vKeyL : List (QE F)), e.ev δF eK eF = e.ev δF eK' eF') ∧
    (∀ e ∈ (Cell.vKeyR : List (QE F)), e.ev δF eK eF = e.ev δF eK' eF') := by
  have V : ∀ r, r + 1 < 18 → (QE.var r : QE F).ev δF eK eF = (QE.var r : QE F).ev δF eK' eF' :=
    fun r hr => var_cong δF hK r hr
  have B : ∀ j ∈ [Cell.loL, Cell.hiL, Cell.idL, Cell.loR, Cell.hiR, Cell.idR],
      (QE.base (cv j) : QE F).ev δF eK eF = (QE.base (cv j) : QE F).ev δF eK' eF' := fun j hj => by
    rw [ev_base, ev_base]; simp only [CoeffExpr.eval, cv]; rw [hF j hj]
  have Mk : ∀ j ∈ [Cell.loL, Cell.hiL, Cell.idL, Cell.loR, Cell.hiR, Cell.idR],
      ∀ j' ∈ [Cell.loL, Cell.hiL, Cell.idL, Cell.loR, Cell.hiR, Cell.idR],
      (QE.mk2 (cv j) (cv j') : QE F).ev δF eK eF = (QE.mk2 (cv j) (cv j') : QE F).ev δF eK' eF' := fun j hj j' hj' => by
    rw [ev_mk2, ev_mk2]; simp only [CoeffExpr.eval, cv]; rw [hF j hj, hF j' hj']
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [Cell.vKeyL, QFP.entries, QFP.var, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact Mk _ (by simp) _ (by simp)
    · exact B _ (by simp)
  · intro e he
    simp only [Cell.vKeyR, QFP.entries, QFP.var, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact V _ (by decide)
    · exact Mk _ (by simp) _ (by simp)
    · exact B _ (by simp)

end KeysLR

section Final
open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qW qM)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 LayLe)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8 (DataJ8X allJ8X)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (bitFix)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8Q1 (layPb)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (restrictHQKWCell cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (pw)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8 (childHOfK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA)
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8R3A (rAT)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.Comp12P1 (dataA trace_unique_good'')
open Nock.NockVMROM.Thm54.VclL.Handle.TU.NounSetCloseP1 (qCell keyVOf keyXOf keyHOf r0M_auxM_closed'' extB_atoms)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0WP1 (envB)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenCoreWP1 (WT)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.WalkCloseP1 (cellTab readClosure walk_closed)
open Nock.Edit.GenX (P1Frag genX SkelX)
open Nock.V1J8.Gen (cellsOfRoots rootsOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (rowsOfT)

open Nock.NockVMROM.Thm54.VclL.Handle.TU.R0MSplitP1
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (claimRecsJ8 pinRecsJ8 claimCells)
open Nock.NockVMROM.Thm54.VclL.Handle.AbsentVJ8 (toMsgJ8ZA)

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The validity balance's consumer list** at the absent-atom-walk message (`LinkJ8XUA.rdV`'s right-hand side):
the claim and pin records and the cell table's own child consumes. -/
abbrev vReqs (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) :
    List (Fin 5 → 𝕂′) :=
  (toMsgJ8ZA δ b Pb c χ M tr).reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    (qCell δ b Pb χ M tr)

/-- **(iii) The V consumer lists agree**: the claim records read the claim serials (`r0C`'s `claim`), the cell
table's child consumes read the roles `6 .. 17` and the non-multiplicity columns. -/
theorem vReqs_eq {hpG : p = Nock.Atoms.p} {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim}
    {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ}
    (h : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h' : AcceptsJ8V δ b Pb Rg c χ M' tr' r g)
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0)
    (hS : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)))
    (hS' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')))
    (hnm : ∀ j : Fin 242, (j : ℕ) < 134 → ¬ MulCol j → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i))
    (hclaim : ∀ k, isCellN (claimNoun c k) = true → (M.m k).1 = (M'.m k).1) :
    vReqs δ b Pb c χ M tr = vReqs δ b Pb c χ M' tr' := by
  have hK := roles_nm δ b (hpG := hpG) h h' hz hS hS' hnm
  have hF := cellEnvF_nm δ b (χ := χ) (M := M) (M' := M') hnm
  have hcr : claimRecsJ8 δ χ c M.m = claimRecsJ8 δ χ c M'.m := by
    unfold claimRecsJ8
    refine List.map_congr_left fun k hk => ?_
    have hk' : isCellN (claimNoun c k) = true := by simpa [claimCells] using hk
    rw [hclaim k hk']
  have hvi : cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr) =
      cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr') := by
    unfold cellVInternal
    congr 1
    funext i
    have hFi : ∀ j ∈ [Cell.loL, Cell.hiL, Cell.idL, Cell.loR, Cell.hiR, Cell.idR],
        (cellEnvF b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr) i).trace j =
        (cellEnvF b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr') i).trace j := by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hF i _ (by decide) (by decide)
    obtain ⟨kL, kR⟩ := keysLR_cong_nm δ (hK i) hFi
    simp only [cellB, cellKey]
    rw [hF i Cell.wL (by decide) (by decide), hF i Cell.wR (by decide) (by decide), keyVec_congr δ kL,
      keyVec_congr δ kR]
  show (claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ) ++ _ = (claimRecsJ8 δ χ c M'.m ++ pinRecsJ8 δ Pb χ) ++ _
  rw [hcr, hvi]

/-- **`trace_unique_closed'`**: `trace_unique_closed` with `hkey` derived and `hreqs` reduced to the congruence of
the X and H consumer lists in the walk / compute rows. Order: the non-multiplicity cell round 0 (`r0M_nm_closed`),
the keys (`keys_of_nm`), the compute round 0 and claim serials (`r0C_closed_nm`), the walk over the
non-multiplicity cell table (`walk_closed_nm`), the consumer lists (`vReqs_eq`, `hreqX`, `hreqH`), then the
multiplicities and the full cell round 0 (`r0M_auxM_closed''`). -/
theorem trace_unique_closed' [CharP K p] [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
    {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful) {c : P8PublicClaim}
    -- the event data (`LinkJ8A.probJ8V_absent`)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (L0 : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (skel : List Noun) (hs : skel.length ≤ 3) (hL : LayLe (layPb Pb skel hs) r)
    (hP : P = 2 ^ 66) (hnM : (layPb Pb skel hs).nM ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31)
    -- the row parameters
    (hr : WeightsJ8.RowsLe r EncInjJ8.cornerC) (hgN : g ≤ 2 ^ 31) (hmax : Pb.nA + 2 ≤ r.maxlen)
    (hqM : ∀ x < ringChar (ZMod p), Nock.Atoms.lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    {χ : Coins frameJ8 K} {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsCanon2 δ b hpG sz Pb Rg c χ M tr ax r g) (h' : AcceptsCanon2 δ b hpG sz Pb Rg c χ M' tr' ax' r g)
    (hg : ∀ s ∈ allJ8X (dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr χ)
    (hg' : ∀ s ∈ allJ8X (dataA δ b (g := g) Pb c R0 L0 skel hs hL hP hnM hreg), ¬ s.mem tr' χ)
    -- the generated run at the acceptance registry, and the cell-table size
    {fuel : ℕ} {tg : NTree SkelX} {res : Noun} (hrun : genX Rg fuel c.subject c.formula = some (tg, res))
    (hsz : Pb.nC = (cellsOfRoots (rootsOf c (rowsOfT tg))).length)
    -- the cell balances (V, X with an extra provider list; H at `cellProvsW`)
    {reqsX reqsX' : List (Fin 11 → 𝕂′)} {reqsH reqsH' : List (Fin 5 → K)}
    (extraV : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hbalV : ∀ r, ((vReqs δ b Pb c χ M tr).count r : 𝕂′) =
      pw (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)) ++ extraV) r)
    (hdeV : (extraV.map Prod.fst).Nodup)
    (hdisV : ∀ a ∈ (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr))).map
      Prod.fst, ∀ e ∈ extraV.map Prod.fst, a ≠ e)
    (extraX : List ((Fin 11 → 𝕂′) × 𝕂′))
    (hbalX : ∀ r, (reqsX.count r : 𝕂′) =
      pw (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr)) ++ extraX) r)
    (hdeX : (extraX.map Prod.fst).Nodup)
    (hdisX : ∀ a ∈ (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qCell δ b Pb χ M tr))).map
      Prod.fst, ∀ e ∈ extraX.map Prod.fst, a ≠ e)
    (hbalH : ∀ r, (reqsH.count r : K) = pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) r)
    (extraV' : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hbalV' : ∀ r, ((vReqs δ b Pb c χ M' tr').count r : 𝕂′) =
      pw (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')) ++ extraV') r)
    (hdeV' : (extraV'.map Prod.fst).Nodup)
    (hdisV' : ∀ a ∈ (liftWts (cVRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr'))).map
      Prod.fst, ∀ e ∈ extraV'.map Prod.fst, a ≠ e)
    (extraX' : List ((Fin 11 → 𝕂′) × 𝕂′))
    (hbalX' : ∀ r, (reqsX'.count r : 𝕂′) =
      pw (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr')) ++ extraX') r)
    (hdeX' : (extraX'.map Prod.fst).Nodup)
    (hdisX' : ∀ a ∈ (liftWts (cXRec δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC (qCell δ b Pb χ M' tr'))).map
      Prod.fst, ∀ e ∈ extraX'.map Prod.fst, a ≠ e)
    (hbalH' : ∀ r, (reqsH'.count r : K) = pw (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC)) r)
    -- cross-trace: the X and H consumer lists are congruent in the walk / compute rows (open until pinned)
    (hreqX : (∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) →
      reqsX = reqsX')
    (hreqH : (∀ j : Fin 123, (j : ℕ) < 69 → ∀ i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i)) →
      (∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) →
      (∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) →
      reqsH = reqsH')
    -- the walk
    (hk1 : 1 ≤ Pb.kroots) (hkn : Pb.kroots ≤ Pb.nW) (hkp : Pb.kroots + Pb.nW < p)
    (hfp : ∀ c1 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr, ∀ c2 ∈ cellTab δ b (Pb := Pb) χ M.pubsC tr,
      c1.p = c2.p → c1.b0.idx = c2.b0.idx)
    (reqsW reqsW' : List (Fin 5 → K)) (provsW provsW' : List ((Fin 5 → K) × K))
    (hbalW : ∀ r, (reqsW.count r : K) = pw provsW r) (hdW : (provsW.map Prod.fst).Nodup)
    (hsubW : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW), q ∈ provsW)
    (hbalW' : ∀ r, (reqsW'.count r : K) = pw provsW' r) (hdW' : (provsW'.map Prod.fst).Nodup)
    (hsubW' : ∀ q ∈ ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M'.pubsW
      (qW δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW), q ∈ provsW')
    (hreqW : ∀ r, reqsW.count r = reqsW'.count r)
    (noPath : Prop)
    (hE10 : noPath → (tr.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hE10' : noPath → (tr'.W ⟨WChip.idx, by decide⟩).eval (Pb.nodesW ⟨0, by omega⟩) = 0)
    (hnW1 : noPath → Pb.nW = 1)
    (Rd : Finset (ℕ × ℕ)) (hszW : ¬ noPath → (readClosure Rd).card = Pb.nW)
    (hprov : ¬ noPath → ∀ s ∈ Rd, ∃ j < Pb.nW,
      natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.ridx) = s.1 ∧
        natOf ((envB δ b Pb tr (chalsMJ8 δ χ) M.pubsW j).trace WChip.pre) = s.2 / 2)
    (hprov' : ¬ noPath → ∀ s ∈ Rd, ∃ j < Pb.nW,
      natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.ridx) = s.1 ∧
        natOf ((envB δ b Pb tr' (chalsMJ8 δ χ) M'.pubsW j).trace WChip.pre) = s.2 / 2) :
    (tr, ax, M) = (tr', ax', M') := by
  have hPb := h.1.2.hPb
  have h0 : Pb.krootsV = 0 := by rw [hPb]; rfl
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hn : 1 ≤ Pb.n := by rw [hPb]; exact (sz c).hn
  have hfrag : P1Frag c.formula := AsmRowsP1.P1FragC.p1Frag h.1.2.hfrag
  -- the twins, at the producer's atom reader
  have hl := LinkJ8A.linkXUA_of_R5 δ b Pb c χ M tr R0 L0 skel hs hL hP hnM hreg hpG hr hgN hmax h.1.1 h0 hg
  have hl' := LinkJ8A.linkXUA_of_R5 δ b Pb c χ M' tr' R0 L0 skel hs hL hP hnM hreg hpG hr hgN hmax h'.1.1 h0 hg'
  -- the validity-served cell tables (`ServedP1.cell_served_P1`)
  have hS := ServedP1.cell_served_P1 δ b hpG rfl h.1.1 h0 h.1.2.hApad hg hl
  have hS' := ServedP1.cell_served_P1 δ b hpG rfl h'.1.1 h0 h'.1.2.hApad hg' hl'
  -- the J-8 walk event (`Lift40J8.wchain_out` at the walk readout `rdWW`)
  have houtW := Lift40J8.wchain_out _ (ListJ8C.outside40C _ _ (AtomFpxJ8.outsideC_of_outsideX _ hg))
  rw [hl.rdWW, ← (AcceptsJ8.coinW_J8 δ χ).1, ← (AcceptsJ8.coinW_J8 δ χ).2] at houtW
  have houtW' := Lift40J8.wchain_out _ (ListJ8C.outside40C _ _ (AtomFpxJ8.outsideC_of_outsideX _ hg'))
  rw [hl'.rdWW, ← (AcceptsJ8.coinW_J8 δ χ).1, ← (AcceptsJ8.coinW_J8 δ χ).2] at houtW'
  obtain ⟨-, A, hG, -, hden, -⟩ := TwinLinkJ8A.hsoundJ8XUA_exA δ b Pb hRg c χ M tr _ _ hpG hqM hk h.1.1 h0 hg hl
  obtain ⟨-, A', hG', -, hden', -⟩ :=
    TwinLinkJ8A.hsoundJ8XUA_exA δ b Pb hRg c χ M' tr' _ _ hpG hqM hk h'.1.1 h0 hg' hl'
  -- the cell table: round 0 and aux
  have hD := AtomBigJ8.denOKX_extB ((cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    (qCell δ b Pb χ M tr)).map (·.b0)) p (rAT b Pb tr)
  have hD' := AtomBigJ8.denOKX_extB ((cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
    (qCell δ b Pb χ M' tr')).map (·.b0)) p (rAT b Pb tr')
  have hB := RowBridgeP1.rowBridge (K := K) hp hRg hD hn A hG c (hden 0) (hden 1) hfrag hrun
  have hB' := RowBridgeP1.rowBridge (K := K) hp hRg hD' hn A' hG' c (hden' 0) (hden' 1) hfrag hrun
  have hz := zC_of_outside δ rfl hg
  -- (i) the non-multiplicity round-0 cell columns
  obtain ⟨hnm, -⟩ := r0M_nm_closed δ b h.1 h'.1 hS hS' (extB_atoms p (rAT b Pb tr))
    (extB_atoms p (rAT b Pb tr')) hfrag hrun hsz hB hB' ⟨_, hden 0⟩ ⟨_, hden 1⟩ ⟨_, hden 2⟩
    ⟨_, hden' 0⟩ ⟨_, hden' 1⟩ ⟨_, hden' 2⟩
  -- (ii) the keys
  have hkey := keys_of_nm δ b (hpG := hpG) h.1.1 h'.1.1 hz hS hS' hnm
  -- the compute round 0 and the claim serials
  obtain ⟨hr0C, hclaim⟩ := r0C_closed_nm δ b hPb hRg χ M M' tr tr' ax _ _ _ _ hqM hk hqM hk
    h.1.1 h'.1.1 h0 hg hg' hl hl' h.1.2.hC h'.1.2.hC h.1.2.hM h.1.2.hApad h'.1.2.hApad hnm hfrag hrun
  -- the walk, over the non-multiplicity cell table
  have hcellN := hcellN_of_nm δ b (hpG := hpG) h.1.1 h'.1.1 hz hS hS' hnm
  obtain ⟨hr0W, hauxW, hr1W⟩ := walk_closed_nm δ b h h' hk1 hkn hkp houtW houtW' hl.hXW hl'.hXW hcellN hfp
    hl.hHXW hl'.hHXW reqsW reqsW' provsW provsW' hbalW hdW hsubW hbalW' hdW' hsubW' hreqW noPath hE10 hE10' hnW1
    Rd hszW hprov hprov'
  -- (iii) the consumer lists
  have hreqs : vReqs δ b Pb c χ M tr = vReqs δ b Pb c χ M' tr' ∧ reqsX = reqsX' ∧ reqsH = reqsH' :=
    ⟨vReqs_eq δ b (hpG := hpG) h.1.1 h'.1.1 hz hS hS' hnm hclaim, hreqX hr0W, hreqH hr0C hr0W hr1W⟩
  -- (iv) the multiplicities, hence every round-0 and aux cell column
  obtain ⟨hr0M, hauxM⟩ := r0M_auxM_closed'' δ b h.1 h'.1 hS hS' (extB_atoms p (rAT b Pb tr))
    (extB_atoms p (rAT b Pb tr')) hfrag hrun hsz hB hB' ⟨_, hden 0⟩ ⟨_, hden 1⟩ ⟨_, hden 2⟩
    ⟨_, hden' 0⟩ ⟨_, hden' 1⟩ ⟨_, hden' 2⟩
    extraV hbalV hdeV hdisV extraX hbalX hdeX hdisX hbalH
    extraV' hbalV' hdeV' hdisV' extraX' hbalX' hdeX' hdisX' hbalH' hreqs hkey
  exact trace_unique_good'' δ b R0 L0 skel hs hL hP hnM hreg h0 h h' hg
    ⟨hr0C, hr0M, hauxM, hr0W, hauxW, hr1W, hS, hS', hclaim⟩

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.mem_of_clr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.exportRecK_clrRow
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.cellRel_of_clr
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.walk_labels_eq_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.walk_kv_eq_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.walk_closed_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.r0M_nm_closed
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.hqkEF_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.cellEnvF_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.roles_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.keys_of_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.hcellN_of_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.b0_eq_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.r0C_closed_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.keysLR_cong_nm
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.vReqs_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.UniqueSplitP1.trace_unique_closed'
