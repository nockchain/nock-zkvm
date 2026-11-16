/-
  Nock/NockVMROM/Thm54/VclL/Handle/ComplJ8OfBalG.lean

* §1 the cell handle key of a cell row (`cellHx_eq`): `cellHx j = recDen 0 γH (j, H(hd), H(tl))` at the run's
    handle map `H = hdlP`.
  * §2 the cell handle-export terminal is the `mh`-weighted handle sum (`chT_eq`); the J-8 walk handle import is
    the walk-row sum of the same weights (`whX_eq`).
  * §3 the export balance from the counts (`mh_eq_cnt`): `balG1_of` — clause 1 of `balG` with the compute and
    J export totals carried as two exactly stated hypotheses (`hC`, `hJ`).
  * §5–6 the compute publics as row balance terms; the J sibling binder `JSibOK` (`hJsib`, option (a)).
  * §7–9 typed J values are small (`look_small`), pair rows are cells of their operands (`pair_look`), every J
    export-read row carries the node AND both child handles (`ReadKids`, `honestJ8_kids`), hence `hJ_export`.
  * §10–14 one active entry per compute slot (`onehot_slot`), the row's `.x` term (`termQX_x`), the active record's
    parent cell (`xEnt_par`), the row sum as weighted consumes (`xSum_run`), hence `hC_run`.
  * §15 **`balG1_run`: `balG` clause 1 at the run, at every coin, from binders only.**
  * §16 clause 2, compute side: `onehot_slot_pair`, the row's `.p` term `termQX_p` (with the `.p` pair), and
    `hpair_good` (the pair denominators are nonzero outside `compPoles`).
  * §17–19 clause 2 (`balG2_run`), the clause-3 split (`balG3_of`, `balG_closed`), the atom-walk sub-balance
    `hA_run` (`openJ8_with_balG'`).
  * §20 the inc sub-balance `hI_run` (`fold_mi`, `dMI_key`, `incT_run`, `incT_total`, `incSum_eq`) and
    `openJ8_with_balG''` (carries `hJ` only).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

noncomputable section

/-! ## 1. The cell handle key of a cell row -/

section CellKey
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The cell row's coin-free environment reads the honest base columns (`k ∈ [2, 129)`). -/
theorem cEW_trace_col (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.cells.length)) (χ : Coins frameJ8 K)
    (i : Fin D.cells.length) (k : ℕ) (h2 : 2 ≤ k) (hk : k < 129) :
    (cEW δ b D hC o χ i).trace k = cCol δ b D χ k i := by
  have hw : k < (HonestKW.cellTemplateHQKW δ).width 3 := by rw [HonestKW.cellTemplateHQKW_width]; omega
  simp only [cEW, HonestKW.EW, Nock.Framework.Reify.envOfTrace, dif_pos hw]
  rw [honestQ_eval _ _ hinj]
  simp [fullCol, HonestKW.colW, extColF, hk, show k ≠ 0 by omega, show k ≠ 1 by omega,
    show k < 134 by omega]

theorem cEW_trace_kb (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.cells.length)) (χ : Coins frameJ8 K)
    (i : Fin D.cells.length) :
    (cEW δ b D hC o χ i).trace CellTwinK.kbL = ComplJ8Cell.kbLB (bigOf D) D.cells i ∧
    (cEW δ b D hC o χ i).trace CellTwinK.kbR = ComplJ8Cell.kbRB (bigOf D) D.cells i := by
  have hw : ∀ k, k < 134 → k < (HonestKW.cellTemplateHQKW δ).width 3 := fun k hk => by
    rw [HonestKW.cellTemplateHQKW_width]; omega
  refine ⟨?_, ?_⟩
  · simp only [cEW, HonestKW.EW, Nock.Framework.Reify.envOfTrace, dif_pos (hw _ (by decide : CellTwinK.kbL < 134))]
    rw [honestQ_eval _ _ hinj]
    simp [fullCol, HonestKW.colW, extColF, HonestKW.newW, CellTwinK.kbL]
  · simp only [cEW, HonestKW.EW, Nock.Framework.Reify.envOfTrace, dif_pos (hw _ (by decide : CellTwinK.kbR < 134))]
    rw [honestQ_eval _ _ hinj]
    simp [fullCol, HonestKW.colW, extColF, HonestKW.newW, CellTwinK.kbR, CellTwinK.kbL]

/-- The cell part's honest base columns are the cell row's fields (`k < 129`). -/
theorem cCol_base (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (i : Fin D.cells.length) (k : ℕ)
    (hk : k < 129) :
    cCol δ b D χ k i = (ComplJ8Cell.cellRowB δ (zJ δ χ) (bigOf D) D.cells (mvF D) (mxF D) (fun _ => 0)
      D.cells[(i : ℕ)] i).base k := by
  simp only [cCol, cellCol, if_pos hk]
  rw [← ComplJ8Cell.cellRowsB_getElem _ _ _ _ _ _ i.isLt]
  rfl

/-- **A child's handle as the cell row's kind / value columns** (`H = hdlP`, big map `bigIdOfP`). -/
theorem child_key (cs acs : List Noun) (n : Noun) (hn : n.isCell = true → n ∈ cs) :
    ComplJ8Cell.wOf (F := ZMod p) (ComplJ8Data.bigIdOfP p acs) n + ComplJ8Cell.kbOf (ComplJ8Data.bigIdOfP p acs) n =
      (((ComplJ8Data.hdlP p cs acs n).1 : ℕ) : ZMod p) ∧
    ComplJ8Cell.wOf (F := ZMod p) (ComplJ8Data.bigIdOfP p acs) n * ComplJ8Cell.idOf cs (ComplJ8Data.bigIdOfP p acs) n +
        (1 - ComplJ8Cell.wOf (F := ZMod p) (ComplJ8Data.bigIdOfP p acs) n) *
          ComplJ8Cell.aOf (ComplJ8Data.bigIdOfP p acs) n =
      (((ComplJ8Data.hdlP p cs acs n).2 : ℕ) : ZMod p) := by
  cases n with
  | cell x y =>
    have hm := hn rfl
    simp only [ComplJ8Cell.wOf, ComplJ8Cell.kbOf, ComplJ8Cell.isBig, ComplJ8Cell.idOf, ComplJ8Cell.aOf,
      ComplJ8Data.hdlP, Noun.isCell, Bool.true_or, if_true, Bool.not_true, Bool.false_and,
      Bool.false_eq_true, if_false, add_zero, one_mul, sub_self, zero_mul, Nat.cast_one]
    rw [ComplJ8OfBal.genIdxOf_eq _ _ hm]
    simp
  | atom v =>
    by_cases hv : v < p
    · simp [ComplJ8Cell.wOf, ComplJ8Cell.kbOf, ComplJ8Cell.isBig, ComplJ8Cell.idOf, ComplJ8Cell.aOf,
        ComplJ8Data.hdlP, ComplJ8Data.bigIdOfP, Noun.isCell, hv]
    · simp [ComplJ8Cell.wOf, ComplJ8Cell.kbOf, ComplJ8Cell.isBig, ComplJ8Cell.idOf, ComplJ8Cell.aOf,
        ComplJ8Data.hdlP, ComplJ8Data.bigIdOfP, Noun.isCell, hv]
      norm_num

/-- **The cell handle key of a cell row**: `cellHx j = recDen 0 γH (j, H(hd), H(tl))`. -/
theorem cellHx_eq (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.cells.length)) (χ : Coins frameJ8 K)
    (hH : D.H = ComplJ8Data.hdlP p D.cells D.acs)
    (j : ℕ) (hj : j < D.cells.length) {x y : Noun} (hy : D.cells[j] = Noun.cell x y)
    (hx : x.isCell = true → x ∈ D.cells) (hy' : y.isCell = true → y ∈ D.cells) :
    cellHx δ b D hC o j χ =
      recDen 0 (ComplJ8Bad.γH δ χ) (((j : ℕ) : ZMod p), ((((D.H x).1 : ℕ) : ZMod p), (((D.H x).2 : ℕ) : ZMod p)),
        ((((D.H y).1 : ℕ) : ZMod p), (((D.H y).2 : ℕ) : ZMod p))) := by
  have htr := fun k h2 hk => cEW_trace_col δ b D hC o hinj χ ⟨j, hj⟩ k h2 hk
  obtain ⟨kL, kR⟩ := cEW_trace_kb δ b D hC o hinj χ ⟨j, hj⟩
  have hb := fun k hk => cCol_base δ b D χ ⟨j, hj⟩ k hk
  obtain ⟨cx1, cx2⟩ := child_key (p := p) D.cells D.acs x hx
  obtain ⟨cy1, cy2⟩ := child_key (p := p) D.cells D.acs y hy'
  rw [← hH] at cx1 cx2 cy1 cy2
  have hyj : D.cells[(⟨j, hj⟩ : Fin D.cells.length).1] = Noun.cell x y := hy
  have t0 : (cEW δ b D hC o χ ⟨j, hj⟩).trace Cell.idx = ((j : ℕ) : ZMod p) := by
    rw [htr _ (by decide) (by decide), hb _ (by decide), hyj]; rfl
  have t1 : (cEW δ b D hC o χ ⟨j, hj⟩).trace Cell.wL = ComplJ8Cell.wOf (ComplJ8Data.bigIdOfP p D.acs) x := by
    rw [htr _ (by decide) (by decide), hb _ (by decide), hyj]; rfl
  have t2 : (cEW δ b D hC o χ ⟨j, hj⟩).trace Cell.idL =
      ComplJ8Cell.idOf D.cells (ComplJ8Data.bigIdOfP p D.acs) x := by
    rw [htr _ (by decide) (by decide), hb _ (by decide), hyj]; rfl
  have t3 : (cEW δ b D hC o χ ⟨j, hj⟩).trace Cell.aL = ComplJ8Cell.aOf (ComplJ8Data.bigIdOfP p D.acs) x := by
    rw [htr _ (by decide) (by decide), hb _ (by decide), hyj]; rfl
  have t4 : (cEW δ b D hC o χ ⟨j, hj⟩).trace Cell.wR = ComplJ8Cell.wOf (ComplJ8Data.bigIdOfP p D.acs) y := by
    rw [htr _ (by decide) (by decide), hb _ (by decide), hyj]; rfl
  have t5 : (cEW δ b D hC o χ ⟨j, hj⟩).trace Cell.idR =
      ComplJ8Cell.idOf D.cells (ComplJ8Data.bigIdOfP p D.acs) y := by
    rw [htr _ (by decide) (by decide), hb _ (by decide), hyj]; rfl
  have t6 : (cEW δ b D hC o χ ⟨j, hj⟩).trace Cell.aR = ComplJ8Cell.aOf (ComplJ8Data.bigIdOfP p D.acs) y := by
    rw [htr _ (by decide) (by decide), hb _ (by decide), hyj]; rfl
  have t7 : (cEW δ b D hC o χ ⟨j, hj⟩).trace CellTwinK.kbL = ComplJ8Cell.kbOf (ComplJ8Data.bigIdOfP p D.acs) x := by
    rw [kL]; simp only [ComplJ8Cell.kbLB, List.getD_eq_getElem _ _ hj, hy]; rfl
  have t8 : (cEW δ b D hC o χ ⟨j, hj⟩).trace CellTwinK.kbR = ComplJ8Cell.kbOf (ComplJ8Data.bigIdOfP p D.acs) y := by
    rw [kR]; simp only [ComplJ8Cell.kbRB, List.getD_eq_getElem _ _ hj, hy]; rfl
  rw [← cx1, ← cx2, ← cy1, ← cy2]
  unfold cellHx
  rw [dif_pos hj]
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_five, BalanceQ.liftRec, ServeH.keyVec5,
    TwoProviderQ.keyHK, CellH.valE, recDen]
  simp [CoeffExpr.eval, cv, notE, t0, t1, t2, t3, t4, t5, t6, t7, t8,
    IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]
  try ring

end CellKey

/-! ## 2. The cell handle-export terminal and the J-8 walk handle import as weighted handle sums -/

section Terms
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The cell handle weight of serial `j`: `1 / (ρH + cellHx j)`. -/
abbrev GC (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (j : ℕ) : 𝕂′ :=
  (ComplJ8Bad.ρH δ χ + cellHx δ b D hC o j χ)⁻¹

/-- **The cell handle-export terminal is the `mh`-weighted handle sum.** -/
theorem chT_eq (D : J8Data p Rg fuel s f r) (hC : 0 < D.cells.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (χ : Coins frameJ8 K) :
    chT δ b D hC o χ = ∑ j ∈ Finset.range D.cells.length, ((D.mh.getD j 0 : ℕ) : 𝕂′) * GC δ b D hC o χ j := by
  unfold chT
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  simp only [CellTraceH.mN, HonestKW.dNW, dif_pos hj']
  rw [dRowW_split δ b D hC o χ _ ⟨j, hj'⟩]
  simp [mhF, liftQ, map_natCast]

end Terms

section TermsRun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The run's cells are cells, and their cell children are in the list. -/
theorem cells_kids (c : Noun) (hc : c ∈ (j8DataOf p Rg Rt hgen).cells) :
    ∃ x y, c = Noun.cell x y ∧ (x.isCell = true → x ∈ (j8DataOf p Rg Rt hgen).cells) ∧
      (y.isCell = true → y ∈ (j8DataOf p Rg Rt hgen).cells) := by
  have hcc := (ComplJ8Walk.cellsOfRoots_mem _ c hc).1
  cases c with
  | atom v => simp [Noun.isCell] at hcc
  | cell x y =>
    have hcl := ComplJ8Data.cells_closed _ x y hc (by simp)
    refine ⟨x, y, rfl, fun hx => ?_, fun hy => ?_⟩
    · cases x with
      | atom v => simp [Noun.isCell] at hx
      | cell x1 x2 => exact hcl.1 x1 x2 rfl
    · cases y with
      | atom v => simp [Noun.isCell] at hy
      | cell y1 y2 => exact hcl.2 y1 y2 rfl

/-- **The J-8 walk handle import is the walk-row sum of the cell handle weights.** -/
theorem whX_eq {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjC : Function.Injective (powN o (j8DataOf p Rg Rt hgen).cells.length))
    (hinjW : Function.Injective (powN o (walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).length))
    (χ : Coins frameJ8 K) :
    whX δ b (j8DataOf p Rg Rt hgen) o χ =
      ((walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).map fun u =>
        GC δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) o χ
          ((j8DataOf p Rg Rt hgen).cells.idxOf u.label.node)).sum := by
  set D := j8DataOf p Rg Rt hgen with hD
  have hwcell := ComplJ8OfBal.walkRows_node_cells (p := p) Rt hgen
  have hterm : ∀ k ∈ Finset.range (walkRows D.cells D.reads).length, (wdN δ b D o χ WalkHC.xKeyH k)⁻¹ =
      GC δ b D (cells_pos Rt hgen) o χ (D.cells.idxOf (wTrie D.cells D.reads k).label.node) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hmem : (wTrie D.cells D.reads k).label.node ∈ D.cells := hwcell _ (wTrie_mem _ _ hk')
    obtain ⟨x, y, hxy, hx, hy⟩ := cells_kids Rt hgen _ hmem
    have hjl := List.idxOf_lt_length_of_mem hmem
    have hyj : D.cells[D.cells.idxOf (wTrie D.cells D.reads k).label.node] = Noun.cell x y := by
      rw [List.getElem_idxOf hjl]; exact hxy
    have hd : wdN δ b D o χ WalkHC.xKeyH k = ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ)
        ((wValsC δ D χ ⟨k, hk'⟩).idx, (kLW D ⟨k, hk'⟩, vLW D ⟨k, hk'⟩), (kRW D ⟨k, hk'⟩, vRW D ⟨k, hk'⟩)) := by
      simp only [wdN, WalkTraceHQ.dN, dif_pos hk']
      exact (walk_dRow_split δ b D o hinjW χ (pubsW0 δ D χ) ⟨k, hk'⟩).1
    have hv : (wValsC δ D χ ⟨k, hk'⟩).idx = ((D.cells.idxOf (wTrie D.cells D.reads k).label.node : ℕ) : ZMod p) := rfl
    have hkl : kLW D ⟨k, hk'⟩ = (((D.H x).1 : ℕ) : ZMod p) ∧ vLW D ⟨k, hk'⟩ = (((D.H x).2 : ℕ) : ZMod p) ∧
        kRW D ⟨k, hk'⟩ = (((D.H y).1 : ℕ) : ZMod p) ∧ vRW D ⟨k, hk'⟩ = (((D.H y).2 : ℕ) : ZMod p) := by
      simp only [kLW, vLW, kRW, vRW, wNode, hxy]
      exact ⟨rfl, rfl, rfl, rfl⟩
    simp only [GC]
    rw [hd, hv, hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2,
      cellHx_eq δ b D (cells_pos Rt hgen) o hinjC χ rfl _ hjl hyj hx hy]
  unfold whX
  rw [Finset.sum_congr rfl hterm]
  exact ComplJ8OfBal.sum_range_getD' (trie (.atom 0) (.atom 0) [] [])
    (fun u => GC δ b D (cells_pos Rt hgen) o χ (D.cells.idxOf u.label.node)) _

end TermsRun

/-! ## 3. The export balance from the counts -/

section Counts
variable {R : Type} [CommRing R]

/-- A weighted total of `(serial, multiplicity)` pairs. -/
def wsum (G : ℕ → R) (l : List (ℕ × ℕ)) : R := (l.map fun q => (q.2 : R) * G q.1).sum

theorem wsum_append (G : ℕ → R) (l l' : List (ℕ × ℕ)) : wsum G (l ++ l') = wsum G l + wsum G l' := by
  simp [wsum, List.map_append, List.sum_append]

/-- **Counts to totals**: the count-weighted sum over the table's serials is the weighted total of the
records, when every record of positive multiplicity has a serial below the table size. -/
theorem sum_cnt_eq (G : ℕ → R) (L : List ComplJ8Data.NamedRecs) (n : ℕ)
    (hrange : ∀ q ∈ L.flatMap ComplJ8Data.NamedRecs.recs, 0 < q.2 → q.1 < n) :
    ∑ j ∈ Finset.range n, ((ComplJ8Data.cnt L j : ℕ) : R) * G j = wsum G (L.flatMap ComplJ8Data.NamedRecs.recs) := by
  classical
  set S : Finset ℕ := Finset.range n ∪ ((L.flatMap ComplJ8Data.NamedRecs.recs).map Prod.fst).toFinset
  have h1 := ComplJ8Data.totalW_eq_sum_cnt G L S (fun q hq =>
    Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map_of_mem hq)))
  have h2 : ComplJ8Data.totalW G L = wsum G (L.flatMap ComplJ8Data.NamedRecs.recs) := by
    simp [ComplJ8Data.totalW, wsum, nsmul_eq_mul]
  have h0 : ∀ j ∈ S, j ∉ Finset.range n → ComplJ8Data.cnt L j • G j = 0 := by
    intro j _ hj
    have hz : ComplJ8Data.cnt L j = 0 := by
      unfold ComplJ8Data.cnt
      refine List.sum_eq_zero fun m hm => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      obtain ⟨hq, hqj⟩ := List.mem_filter.mp hq
      have hqj : q.1 = j := of_decide_eq_true hqj
      by_contra hne
      exact hj (Finset.mem_range.mpr (hqj ▸ hrange q hq (Nat.pos_of_ne_zero hne)))
    rw [hz, zero_smul]
  rw [← h2, h1, ← Finset.sum_subset Finset.subset_union_left h0]
  simp [nsmul_eq_mul]

/-- A cell-reference list's weighted total is the sum over its cell nouns. -/
theorem wsum_cellPairs (G : ℕ → R) (cs : List Noun) : ∀ l : List Noun,
    wsum G (ComplJ8Data.cellPairs cs l) = (l.map fun n => if n.isCell then G (Nock.V1J8.Gen.idxOf cs n) else 0).sum
  | [] => rfl
  | n :: l => by
    have ih := wsum_cellPairs G cs l
    cases n with
    | atom v =>
      simp only [ComplJ8Data.cellPairs, List.filterMap_cons, List.map_cons, List.sum_cons, Noun.isCell] at ih ⊢
      simp [ih]
    | cell x y =>
      simp only [ComplJ8Data.cellPairs, List.filterMap_cons, wsum, List.map_cons, List.sum_cons,
        Noun.isCell, if_true] at ih ⊢
      rw [ih]; simp

end Counts

/-! ## 4. `balG`'s export clause at the run -/

section Export
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem wsum_keys {ρ κ : Type} (G : ℕ → 𝕂′) (keys : ρ → List κ) (sr : κ → ℕ) : ∀ L : List ρ,
    wsum G (L.flatMap fun row => (keys row).map fun k => (sr k, 1)) = ((L.flatMap keys).map fun k => G (sr k)).sum
  | [] => rfl
  | row :: L => by
    rw [List.flatMap_cons, List.flatMap_cons, wsum_append, List.map_append, List.sum_append, wsum_keys G keys sr L]
    congr 1
    simp [wsum, List.map_map, Function.comp_def]

set_option maxHeartbeats 1000000 in
/-- **`balG`'s export clause at the run, at every coin**, with the compute export total `hC` and the J export
key identity `hJ` carried (exact statements below); the J-8 walk import, the cell handle-export terminal and the
counts are discharged (`whX_eq`, `chT_eq`, `mh_eq_cnt`). -/
theorem balG1_of (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hrange : ∀ q ∈ (ComplJ8Data.xRecs (j8DataOf p Rg Rt hgen)).flatMap ComplJ8Data.NamedRecs.recs, 0 < q.2 →
      q.1 < (j8DataOf p Rg Rt hgen).cells.length)
    (χ : Coins frameJ8 K)
    (hC : ((BRun δ b Rt hgen hpG h31).M χ).ρ 3 =
      wsum (GC δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ)
        ((j8DataOf p Rg Rt hgen).bases.flatMap fun bs =>
          ComplJ8Data.xConsumesP p (⟨bs, bs, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))))
    (hJ : ∀ row ∈ (j8DataOf p Rg Rt hgen).jrows, ∀ κ ∈ Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX row,
      ComplJ8OfBal.fH δ b χ (Nock.Jet.RapJetJ8.keyK 5 κ) =
        GC δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ (κ.headD 0).val) :
    ((BRun δ b Rt hgen hpG h31).M χ).ρ 3 +
        (Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsW WalkHQ.pubXQ)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsW (WalkHQ.pubXQ + 1)) +
        Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 2) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 3)) =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsC CellHQ.pubHQ)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsC (CellHQ.pubHQ + 1)) := by
  set D := j8DataOf p Rg Rt hgen with hD
  set hF := dvdOK_of_rows hpG D h31
  set o := orbJ8 D hF
  have hCp : 0 < D.cells.length := cells_pos Rt hgen
  set G := GC δ b D hCp o χ with hG
  have hmC : D.cells.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hmW : (walkRows D.cells D.reads).length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjC := (powN_ok o (le_two_pow_ht D hmC)).1
  have hinjW := (powN_ok o (le_two_pow_ht D hmW)).1
  have eJ := ComplJ8OfBal.h1J_run δ b Rt hgen hpG h31 χ
  have eW : Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsW WalkHQ.pubXQ)
      (((BRun δ b Rt hgen hpG h31).M χ).pubsW (WalkHQ.pubXQ + 1)) = whX δ b D o χ := by
    show Quad.mk _ (pubsWOf δ b D o χ WalkHQ.pubXQ) (pubsWOf δ b D o χ (WalkHQ.pubXQ + 1)) = _
    have h4 : pubsWOf δ b D o χ WalkHQ.pubXQ = pub2 δ (whX δ b D o χ) 4 := by simp [pubsWOf, WalkHQ.pubXQ]
    have h5 : pubsWOf δ b D o χ (WalkHQ.pubXQ + 1) = pub2 δ (whX δ b D o χ) 5 := by simp [pubsWOf, WalkHQ.pubXQ]
    rw [h4, h5, pub2_mk2 δ _ 4 rfl]
  have eC : Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsC CellHQ.pubHQ)
      (((BRun δ b Rt hgen hpG h31).M χ).pubsC (CellHQ.pubHQ + 1)) = chT δ b D hCp o χ := by
    show Quad.mk _ (pubsCOf δ b D hCp o χ CellHQ.pubHQ) (pubsCOf δ b D hCp o χ (CellHQ.pubHQ + 1)) = _
    have h4 : pubsCOf δ b D hCp o χ CellHQ.pubHQ = pub2 δ (chT δ b D hCp o χ) 4 := by
      simp [pubsCOf, CellHQ.pubHQ]
    have h5 : pubsCOf δ b D hCp o χ (CellHQ.pubHQ + 1) = pub2 δ (chT δ b D hCp o χ) 5 := by
      simp [pubsCOf, CellHQ.pubHQ]
    rw [h4, h5, pub2_mk2 δ _ 4 rfl]
  rw [eW, eC, eJ, hC, whX_eq δ b Rt hgen o hinjC hinjW χ, chT_eq δ b D hCp o χ]
  -- the cell side: counts
  have hcnt : ∑ j ∈ Finset.range D.cells.length, ((D.mh.getD j 0 : ℕ) : 𝕂′) * G j =
      ∑ j ∈ Finset.range D.cells.length, ((ComplJ8Data.cnt (ComplJ8Data.xRecs D) j : ℕ) : 𝕂′) * G j :=
    Finset.sum_congr rfl fun j hj => by rw [ComplJ8Data.mh_eq_cnt p Rg Rt hgen j (Finset.mem_range.mp hj)]
  rw [hcnt, sum_cnt_eq G _ _ hrange]
  simp only [ComplJ8Data.xRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, wsum_append]
  congr 1
  congr 1
  · -- the walk
    rw [wsum_cellPairs]
    have hall : ∀ x ∈ D.reads, VclL.isPathAx x.2 = true := by
      intro x hx
      have : D.reads = Nock.V1J8.Gen.pathReads D.rows := rfl
      rw [this] at hx
      unfold Nock.V1J8.Gen.pathReads at hx
      exact ComplJ8OfBal.isPathAx_of_two_le (by simpa using (List.mem_filter.mp hx).2)
    have h62 : ∀ r ∈ VclL.pathReads D.reads, VclL.depthOf r.2 ≤ 62 :=
      fun r hr => (hwalk r hr).trans (by norm_num)
    have hperm := ComplJ8OfBal.walkGen_nodes_perm D.cells _ hall h62
    have hws : D.ws = (Nock.V1J8.Gen.walkGen (D.cells.headD (.atom 0)) D.reads).1 := rfl
    have hwcell := ComplJ8OfBal.walkRows_node_cells (p := p) Rt hgen
    rw [hws, ((hperm.map fun n => if n.isCell then G (Nock.V1J8.Gen.idxOf D.cells n) else 0).sum_eq),
      List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    have hm := hwcell u hu
    have hc := (ComplJ8Walk.cellsOfRoots_mem _ _ hm).1
    simp only [Function.comp_apply, hc, if_true]
    rw [ComplJ8OfBal.genIdxOf_eq _ _ hm]
  · -- the J reads
    rw [wsum_keys δ G (Nock.Jet.ChipJ8.keysOf (F := ZMod p) Nock.Jet.ChipJ8.entsX) (fun κ : List (ZMod p) => (κ.headD 0).val)]
    simp only [ComplJ8Bal.tots, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      ComplJ8OfBal.tabJX, ComplJ8OfBal.mapTab, ComplJ8Bal.tot, ComplJ8Bal.tabOfRows, List.ofFn_get]
    have hp : ∀ L : List (Nock.Jet.ChipJ8.CRow (ZMod p)),
        (L.flatMap fun _ => ([] : List (List (ZMod p) × 𝕂′))) = [] := fun L => by simp
    rw [hp]
    simp only [List.map_nil, List.sum_nil, sub_zero, List.map_map]
    congr 1
    refine List.map_congr_left fun κ hκ => ?_
    obtain ⟨row, hrow, hk⟩ := List.mem_flatMap.mp hκ
    simp only [Function.comp_apply]
    exact hJ row hrow κ hk

end Export

/-! ## 5. The compute export public as a sum of row terms -/

section ComputeRows
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The honest accumulator term over the cast slots is the `ℚ`-template term. -/
theorem termVal_slotsF (bl : ChipHX.Bal) (im : Bool) (eF : Nock.Reified.Env (ZMod p)) :
    Compute.LogUp.termVal b (HonestTraceX.slotsF bl im) eF = TeleCQX.termValX b (TeleCQX.slotsB bl im) eF := by
  simp only [Compute.LogUp.termVal, TeleCQX.termValX, HonestTraceX.slotsF, HonestTraceX.slotsQ, TeleCQX.slotsB,
    List.map_map, Function.comp_def, castSlot, HonestTraceX.eval_mapC_castX]

/-- **A compute balance's accumulator pair is the sum of the rows' `𝕂′` balance terms.** -/
theorem acc_rows (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX))
    (chalV pubVal : ℕ → ZMod p) (bl : ChipHX.Bal) (a : ℕ)
    (hre : HonestTraceX.accSpec a = (bl, false)) (him : HonestTraceX.accSpec (a + 1) = (bl, true)) :
    Quad.mk (algebraMap (ZMod p) K δ) (HonestTraceX.accV b δ H pd W chalV pubVal a W.length)
        (HonestTraceX.accV b δ H pd W chalV pubVal (a + 1) W.length) =
      ∑ j ∈ Finset.range W.length, TeleCQX.termQX δ b (HonestTraceX.env1 b δ H pd W chalV pubVal j) bl := by
  simp only [HonestTraceX.accV, hre, him]
  rw [← TeleCQX.mk_fsumX]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TeleCQX.termQX_eq, termVal_slotsF, termVal_slotsF]

end ComputeRows

section ComputeRho
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (c : P8PublicClaim)

/-- The compute row environment the honest accumulators read (dummy publics, as `ComplJ8Comp.accT`). -/
abbrev envC (χ : Coins frameJ8 K) (j : ℕ) : Nock.Reified.Env (ZMod p) :=
  HonestTraceX.env1 b δ H pd W (VerJ8.chalVJ8 b χ) (VerJ8.pubVJ8 δ b c (ComplJ8Comp.mCOf H c) 0 0 χ) j

/-- **The compute export public `ρ 3` is the sum of the rows' `.x` balance terms.** -/
theorem rhoC3_rows (χ : Coins frameJ8 K) :
    ComplJ8Comp.ρCOf δ b H pd W c χ 3 = ∑ j ∈ Finset.range W.length, TeleCQX.termQX δ b (envC δ b H pd W c χ j) .x := by
  simp only [ComplJ8Comp.ρCOf, ComplJ8Comp.accT]
  exact acc_rows δ b H pd W _ _ .x 0 rfl rfl

/-- **The compute path public `ρ 4` is the sum of the rows' `.p` balance terms.** -/
theorem rhoC4_rows (χ : Coins frameJ8 K) :
    ComplJ8Comp.ρCOf δ b H pd W c χ 4 = ∑ j ∈ Finset.range W.length, TeleCQX.termQX δ b (envC δ b H pd W c χ j) .p := by
  simp only [ComplJ8Comp.ρCOf, ComplJ8Comp.accT]
  exact acc_rows δ b H pd W _ _ .p 2 rfl rfl

/-- **The compute service public `ρS` is the sum of the rows' `.s` balance terms.** -/
theorem rhoCS_rows (χ : Coins frameJ8 K) :
    ComplJ8Comp.ρSCOf δ b H pd W c χ = ∑ j ∈ Finset.range W.length, TeleCQX.termQX δ b (envC δ b H pd W c χ j) .s := by
  simp only [ComplJ8Comp.ρSCOf, ComplJ8Comp.accT]
  exact acc_rows δ b H pd W _ _ .s 4 rfl rfl

end ComputeRho

/-! ## 6.

The J chip's honest rows give a read node's children the handle `ChipJ8Toy.hOf`, which maps an atom to `(0, v mod p)`.
The cell table provides `hdlP`, which maps an atom `v ≥ p` to `(2, rootIdxP v)`.  Inside typed values every atom is
`< p` (`shapeOK`, `ev` mod `p`).  The `.var` chains walk the CALL SUBJECT along the argument axis, and that walk also
records the off-path siblings, which the template's guard does not check.  The binder asks that every child atom
met along these walks be `< p`.  It is a completeness binder over the run's calls and the registry templates; the J
export key identity `hJ` of `balG1_of` is to be derived from it. -/

section JSib
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- Every child atom of every node on the walk `bs` from `x` is `< p`. -/
def ChainSibsOK (p : ℕ) : List Bool → Noun → Prop
  | [], _ => True
  | bb :: bs, x => (∀ v, Nock.Jet.Autogen.nhd x = .atom v → v < p) ∧
      (∀ v, Nock.Jet.Autogen.ntl x = .atom v → v < p) ∧
      ChainSibsOK p bs (if bb then Nock.Jet.Autogen.ntl x else Nock.Jet.Autogen.nhd x)

/-- **`hJsib`**: along every argument axis of every jet call of the run, the subject walk meets only child atoms
`< p`. -/
def JSibOK (Rt : ℕ → Nock.Jet.Autogen.Tpl) (D : J8Data p Rg fuel s f r) : Prop :=
  ∀ cl ∈ D.calls, ∀ i : Fin (Rt cl.1).k, ChainSibsOK p (Nock.Jet.ChipJ8.axPath ((Rt cl.1).ax i)) cl.2

end JSib


/-! ## 7. Typed J values are small; the pair rows; the `var` axes -/

section Small
open Nock.Jet.Autogen (nhd ntl ntail shapeOK shapeL Ty Ex HasTy ev)
open Nock.Jet.Interp (JNode JOp JRow honestRows z0 exRows gRows gElemsR inRows)
variable {p : ℕ} [Fact p.Prime]

/-- Every atom of the noun is `< p`. -/
def Small (p : ℕ) : Noun → Prop
  | .atom v => v < p
  | .cell a b => Small p a ∧ Small p b

theorem small_zero : Small p (.atom 0) := (Fact.out : p.Prime).pos

theorem small_nhd {x : Noun} (h : Small p x) : Small p (nhd x) := by
  cases x with
  | atom v => exact small_zero
  | cell a b => exact h.1

theorem small_ntl {x : Noun} (h : Small p x) : Small p (ntl x) := by
  cases x with
  | atom v => exact small_zero
  | cell a b => exact h.2

theorem small_ntail : ∀ (j : ℕ) {x : Noun}, Small p x → Small p (ntail j x)
  | 0, _, h => h
  | j + 1, _, h => small_ntl (small_ntail j h)

theorem chainSibs_of_small : ∀ (bs : List Bool) {x : Noun}, Small p x → ChainSibsOK p bs x
  | [], _, _ => trivial
  | bb :: bs, x, h => by
    refine ⟨fun v hv => ?_, fun v hv => ?_, chainSibs_of_small bs ?_⟩
    · have := small_nhd h; rw [hv] at this; exact this
    · have := small_ntl h; rw [hv] at this; exact this
    · cases bb <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact small_nhd h
      · exact small_ntl h

theorem shapeL_small (ok : Noun → Bool) (hok : ∀ v, ok v = true → Small p v) :
    ∀ (n : ℕ) (v : Noun), shapeL ok n v = true → Small p v
  | 0, v, h => by
    simp only [shapeL, decide_eq_true_eq] at h; subst h; exact small_zero
  | n + 1, .atom _, h => by simp [shapeL] at h
  | n + 1, .cell a t, h => by
    simp only [shapeL, Bool.and_eq_true] at h
    exact ⟨hok a h.1, shapeL_small ok hok n t h.2⟩

/-- The type mentions no opaque `N` (an `N` slot may hold any noun, so only `N`-free shapes are small). -/
def NFree : Ty → Prop
  | .F => True
  | .L _ τ => NFree τ
  | .N => False

theorem shape_small : ∀ (τ : Ty), NFree τ → ∀ (v : Noun), shapeOK p τ v = true → Small p v
  | .F, _, .atom v, h => by simp only [shapeOK, decide_eq_true_eq] at h; exact h
  | .F, _, .cell _ _, h => by simp [shapeOK] at h
  | .L n τ, hτ, v, h => by
    rw [Nock.Jet.Autogen.shapeOK_L] at h
    exact shapeL_small _ (shape_small τ hτ) n v h
  | .N, hτ, _, _ => hτ.elim

/-- **Constants of a well-typed expression are `< p`** (typed `F` by `HasTy.const`, or `0` by `HasTy.nil`);
this replaces the type-shape argument (`shape_small`), which is false at `N`. -/
theorem ev_small (hp : 0 < p) {k : ℕ} {inTy : Fin k → Ty} {a : Fin k → Noun}
    (ha : ∀ i, Small p (a i)) {e : Ex k} {τ : Ty} (h : HasTy p inTy e τ) : Small p (Nock.Jet.Autogen.ev p a e) := by
  induction h with
  | var i => exact ha i
  | const hc => exact hc
  | nil _ => exact hp
  | weakN _ ih => exact ih
  | add _ _ _ _ =>
    simp only [Nock.Jet.Autogen.ev]; exact Nat.mod_lt _ hp
  | mul _ _ _ _ =>
    simp only [Nock.Jet.Autogen.ev]; exact Nat.mod_lt _ hp
  | nth _ _ ih => exact small_nhd (small_ntail _ ih)
  | pair _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

theorem exRows_small {k : ℕ} {ax : Fin k → ℕ} {inTy : Fin k → Ty}
    {a : Fin k → Noun} (ha : ∀ i, Small p (a i)) (c : ℕ) {e : Ex k} {τ : Ty}
    (h : HasTy p inTy e τ) : ∀ b, ∀ r ∈ exRows p ax a c b e, Small p r.val := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  induction h with
  | var i =>
    intro b r hr
    simp only [exRows, List.mem_singleton] at hr; subst hr
    exact ha i
  | const hc =>
    intro b r hr
    simp only [exRows, List.mem_singleton] at hr; subst hr
    exact hc
  | nil _ =>
    intro b r hr
    simp only [exRows, List.mem_singleton] at hr; subst hr
    exact small_zero
  | weakN _ ih => exact ih
  | add h₁ h₂ ih₁ ih₂ =>
    intro b r hr
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · exact ev_small hp ha (HasTy.add h₁ h₂)
    · exact ih₁ _ r hr
    · exact ih₂ _ r hr
  | mul h₁ h₂ ih₁ ih₂ =>
    intro b r hr
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · exact ev_small hp ha (HasTy.mul h₁ h₂)
    · exact ih₁ _ r hr
    · exact ih₂ _ r hr
  | pair h₁ h₂ ih₁ ih₂ =>
    intro b r hr
    simp only [exRows, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | hr | hr
    · exact ev_small hp ha (HasTy.pair h₁ h₂)
    · exact ih₁ _ r hr
    · exact ih₂ _ r hr
  | @nth j n τ' e he hj ih =>
    intro b r hr
    simp only [exRows, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ev_small hp ha (HasTy.nth he hj)
    · exact ih _ r hr

theorem gRows_small (c : ℕ) : ∀ (τ : Ty) (b r : ℕ) (v : Noun), Small p v →
    ∀ row ∈ gRows c τ b r v, Small p row.val := by
  intro τ
  induction τ with
  | N => intro b r v hv row hrow; simp [gRows] at hrow
  | F =>
    intro b r v hv row hrow
    simp only [gRows, List.mem_singleton] at hrow; subst hrow; exact hv
  | L n τ ih =>
    intro b r v hv row hrow
    have hel : ∀ (js : List ℕ) (b : ℕ), ∀ row ∈ gElemsR (gRows c τ) (Nock.Jet.Interp.gSz τ) r v c b js,
        Small p row.val := by
      intro js
      induction js with
      | nil => intro b row hrow; simp [gElemsR] at hrow
      | cons j js ihj =>
        intro b row hrow
        simp only [gElemsR, List.mem_cons, List.mem_append] at hrow
        rcases hrow with rfl | hrow | hrow
        · exact small_nhd (small_ntail j hv)
        · exact ih _ _ _ (small_nhd (small_ntail j hv)) row hrow
        · exact ihj _ row hrow
    simp only [gRows, List.mem_cons] at hrow
    rcases hrow with rfl | rfl | hrow
    · exact small_ntail n hv
    · exact small_ntail n hv
    · exact hel _ _ row hrow

theorem inRows_small (T : Nock.Jet.Autogen.Tpl) {a : Fin T.k → Noun} (ha : ∀ i, Small p (a i)) (c : ℕ) :
    ∀ (is : List (Fin T.k)) (b : ℕ), ∀ row ∈ inRows T a c b is, Small p row.val := by
  intro is
  induction is with
  | nil => intro b row hrow; simp [inRows] at hrow
  | cons i is ih =>
    intro b row hrow
    simp only [inRows, List.mem_cons, List.mem_append] at hrow
    rcases hrow with rfl | hrow | hrow
    · exact ha i
    · exact gRows_small c _ _ _ _ (ha i) row hrow
    · exact ih _ row hrow

/-- **Every honest J value of a call in the template's domain is small, when the argument types are
`N`-free** (an `N` argument may be any noun, so the hypothesis cannot be dropped). -/
theorem look_small (T : Nock.Jet.Autogen.Tpl) (hT : T.WellTyped p) (hN : ∀ i, NFree (T.inTy i)) (s : Noun)
    (hsem : ∃ r, T.sem p s = some r) (c n : ℕ) : Small p (Nock.Jet.ChipJ8.honestLook (p := p) T s c n) := by
  obtain ⟨r, h⟩ := hsem
  obtain ⟨a, hs, ha, -⟩ := Nock.Jet.Autogen.sem_eq_some_iff.1 h
  have hA := Nock.Jet.Interp.argsD_eq hs
  have ha' : ∀ i, Small p (a i) := fun i => shape_small _ (hN i) _ (ha i)
  unfold Nock.Jet.ChipJ8.honestLook
  cases hn : (honestRows p T s c)[n]? with
  | none => exact small_zero
  | some row =>
    simp only [Option.map_some, Option.getD_some]
    have hrow := List.mem_of_getElem? hn
    simp only [honestRows, List.mem_append, hA] at hrow
    rcases hrow with hrow | hrow
    · exact exRows_small ha' c hT 0 row hrow
    · exact inRows_small T ha' c _ _ row hrow

/-- **The pair rows**: at a `pair` node the honest value is the cell of the two operand values. -/
theorem pair_look (T : Nock.Jet.Autogen.Tpl) (hT : T.WellTyped p) (s : Noun)
    (hsem : ∃ r, T.sem p s = some r) (c : ℕ) :
    ∀ nd ∈ Nock.Jet.Interp.nodesOf T, nd.op = .pair →
      Nock.Jet.ChipJ8.honestLook (p := p) T s c nd.id =
        .cell (Nock.Jet.ChipJ8.honestLook (p := p) T s c nd.a) (Nock.Jet.ChipJ8.honestLook (p := p) T s c nd.b) := by
  intro nd hnd hop
  obtain ⟨r, h⟩ := hsem
  obtain ⟨-, hnodes, -, -, hread, -⟩ :=
    Nock.Jet.Interp.interp_complete (Fact.out : p.Prime).pos T hT s r c h
  set R := honestRows p T s c with hRdef
  have hlink : Nock.Jet.Interp.LinkIn R R := by
    intro row hrow
    have hrow' := hrow
    simp only [hRdef, honestRows, List.mem_append] at hrow'
    rcases hrow' with hrow' | hrow'
    · exact Nock.Jet.Interp.exRows_link (p := p) T.ax _ c R T.body 0
        (fun x hx => by simp only [hRdef, honestRows, List.mem_append]; exact Or.inl hx) row hrow'
    · exact Nock.Jet.Interp.inRows_link T _ c R _ _
        (fun x hx => by simp only [hRdef, honestRows, List.mem_append]; exact Or.inr hx) row hrow'
  have hids := Nock.Jet.Interp.honestRows_ids p T s c
  rw [← hRdef] at hids
  have hlook : ∀ e ∈ R, Nock.Jet.ChipJ8.honestLook (p := p) T s c e.node.id = e.val := by
    intro e he
    unfold Nock.Jet.ChipJ8.honestLook
    rw [← hRdef, Nock.Jet.Interp.getElem?_of_ids hids he]
    rfl
  rw [← hnodes] at hnd
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hnd
  have hv := hread row hrow
  rw [hop] at hv
  simp only [Nock.Jet.Interp.readOK, decide_eq_true_eq] at hv
  obtain ⟨hx, hy⟩ := hlink row hrow
  rw [hop] at hx hy
  obtain ⟨e₁, he₁, i₁, v₁⟩ := hx (by simp [JOp.arity])
  obtain ⟨e₂, he₂, i₂, v₂⟩ := hy (by simp [JOp.arity])
  rw [hlook row hrow, ← i₁, ← i₂, hlook e₁ he₁, hlook e₂ he₂, v₁, v₂, hv]

theorem exNodes_var {k : ℕ} (ax : Fin k → ℕ) : ∀ (e : Ex k) (b : ℕ), ∀ nd ∈ Nock.Jet.Interp.exNodes ax b e,
    ∀ i x, nd.op = .var i x → ∃ i' : Fin k, x = ax i' := by
  intro e
  induction e with
  | var i' =>
    intro b nd hnd i x hop
    simp only [Nock.Jet.Interp.exNodes, List.mem_singleton] at hnd; subst hnd
    simp only [JOp.var.injEq] at hop
    exact ⟨i', hop.2.symm⟩
  | const c =>
    intro b nd hnd i x hop
    simp only [Nock.Jet.Interp.exNodes, List.mem_singleton] at hnd; subst hnd
    simp at hop
  | add e₁ e₂ ih₁ ih₂ =>
    intro b nd hnd i x hop
    simp only [Nock.Jet.Interp.exNodes, List.mem_cons, List.mem_append] at hnd
    rcases hnd with rfl | hnd | hnd
    · simp at hop
    · exact ih₁ _ nd hnd i x hop
    · exact ih₂ _ nd hnd i x hop
  | mul e₁ e₂ ih₁ ih₂ =>
    intro b nd hnd i x hop
    simp only [Nock.Jet.Interp.exNodes, List.mem_cons, List.mem_append] at hnd
    rcases hnd with rfl | hnd | hnd
    · simp at hop
    · exact ih₁ _ nd hnd i x hop
    · exact ih₂ _ nd hnd i x hop
  | nth j e ih =>
    intro b nd hnd i x hop
    simp only [Nock.Jet.Interp.exNodes, List.mem_cons] at hnd
    rcases hnd with rfl | hnd
    · simp at hop
    · exact ih _ nd hnd i x hop
  | pair e₁ e₂ ih₁ ih₂ =>
    intro b nd hnd i x hop
    simp only [Nock.Jet.Interp.exNodes, List.mem_cons, List.mem_append] at hnd
    rcases hnd with rfl | hnd | hnd
    · simp at hop
    · exact ih₁ _ nd hnd i x hop
    · exact ih₂ _ nd hnd i x hop

theorem gNodes_var : ∀ (τ : Ty) (b r : ℕ), ∀ nd ∈ Nock.Jet.Interp.gNodes τ b r, ∀ i x, nd.op ≠ .var i x := by
  intro τ
  induction τ with
  | F =>
    intro b r nd hnd i x hop
    simp only [Nock.Jet.Interp.gNodes, List.mem_singleton] at hnd; subst hnd
    simp at hop
  | N =>
    intro b r nd hnd i x hop
    simp [Nock.Jet.Interp.gNodes] at hnd
  | L n τ ih =>
    intro b r nd hnd i x
    have hel : ∀ (js : List ℕ) (b : ℕ),
        ∀ nd ∈ Nock.Jet.Interp.gElems (Nock.Jet.Interp.gNodes τ) (Nock.Jet.Interp.gSz τ) r b js, nd.op ≠ .var i x := by
      intro js
      induction js with
      | nil => intro b nd hnd; simp [Nock.Jet.Interp.gElems] at hnd
      | cons j js ihj =>
        intro b nd hnd
        simp only [Nock.Jet.Interp.gElems, List.mem_cons, List.mem_append] at hnd
        rcases hnd with rfl | hnd | hnd
        · simp
        · exact ih _ _ nd hnd i x
        · exact ihj _ nd hnd
    simp only [Nock.Jet.Interp.gNodes, List.mem_cons] at hnd
    rcases hnd with rfl | rfl | hnd
    · simp
    · simp
    · exact hel _ _ nd hnd

theorem inNodes_var (T : Nock.Jet.Autogen.Tpl) : ∀ (is : List (Fin T.k)) (b : ℕ),
    ∀ nd ∈ Nock.Jet.Interp.inNodes T b is, ∀ i x, nd.op = .var i x → ∃ i' : Fin T.k, x = T.ax i' := by
  intro is
  induction is with
  | nil => intro b nd hnd; simp [Nock.Jet.Interp.inNodes] at hnd
  | cons i' is ih =>
    intro b nd hnd i x hop
    simp only [Nock.Jet.Interp.inNodes, List.mem_cons, List.mem_append] at hnd
    rcases hnd with rfl | hnd | hnd
    · simp only [JOp.var.injEq] at hop; exact ⟨i', hop.2.symm⟩
    · exact absurd hop (gNodes_var _ _ _ nd hnd i x)
    · exact ih _ nd hnd i x hop

/-- **The `var` nodes read the template's argument axes.** -/
theorem nodesOf_var (T : Nock.Jet.Autogen.Tpl) : ∀ nd ∈ Nock.Jet.Interp.nodesOf T, ∀ i x, nd.op = .var i x →
    ∃ i' : Fin T.k, x = T.ax i' := by
  intro nd hnd i x hop
  simp only [Nock.Jet.Interp.nodesOf, List.mem_append] at hnd
  rcases hnd with hnd | hnd
  · exact exNodes_var T.ax _ _ nd hnd i x hop
  · exact inNodes_var T _ _ nd hnd i x hop

end Small

/-! ## 8. The J export-read rows: the node and BOTH child handles -/

section Kids
open Nock.Jet.ChipJ8 (CRow chainWG nodeWG nodesWG blockWG honestJ8G hOf mkW callPre regPre honestLook axPath)
open Nock.Jet.Interp (JNode JOp honestRows z0)
open Nock.Jet.Autogen (nhd ntl)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (GoodN ClP goodN_nhd goodN_ntl)
variable {p : ℕ} [Fact p.Prime] {cs : List Noun} {hd : Noun → ZMod p × ZMod p}

/-- **The strengthened export-read shape**: the row's three handles are `hd` of a good node `y` and of its two
children.  No smallness of the children is asked: the handle map `hd` is the cell table's. -/
def ReadKids (p : ℕ) [Fact p.Prime] (cs : List Noun) (hd : Noun → ZMod p × ZMod p) (r : CRow (ZMod p)) : Prop :=
  (r.pre.kd = .rp ∨ r.pre.kd = .sl ∨ r.pre.kd = .sr) →
    ∃ y, GoodN cs y ∧ r.w.kN = (hd y).1 ∧ r.w.vN = (hd y).2 ∧
      r.w.kL = (hd (nhd y)).1 ∧ r.w.vL = (hd (nhd y)).2 ∧
      r.w.kR = (hd (ntl y)).1 ∧ r.w.vR = (hd (ntl y)).2

theorem chainW_kids (hcl : ClP cs []) (c dst : ℕ) : ∀ (bs : List Bool) (src ctr : ℕ) (x : Noun), GoodN cs x →
    ∀ r ∈ chainWG (p := p) hd c dst src ctr bs x, ReadKids p cs hd r
  | [], src, ctr, x, _, r, hr => by
    simp only [chainWG, List.mem_singleton] at hr
    subst hr
    intro h; simp at h
  | b :: bs, src, ctr, x, hx, r, hr => by
    simp only [chainWG, List.mem_cons] at hr
    rcases hr with rfl | hr
    · intro _; exact ⟨x, hx, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact chainW_kids hcl c dst bs ctr (ctr + 1) _
        (by cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact goodN_ntl hcl hx | exact goodN_nhd hcl hx) r hr

theorem nodeW_kids (hcl : ClP cs []) (c S ctr : ℕ) (lk : ℕ → Noun) (s : Noun) (nd : JNode)
    (hs : GoodN cs s) (hlk : ∀ n, GoodN cs (lk n))
    (hpair : nd.op = .pair → lk nd.id = .cell (lk nd.a) (lk nd.b)) :
    ∀ r ∈ nodeWG (p := p) hd c S ctr lk s nd, ReadKids p cs hd r := by
  intro r hr
  unfold nodeWG at hr
  cases hop : nd.op with
  | var i ax => rw [hop] at hr; exact chainW_kids hcl _ _ _ _ _ _ hs r hr
  | nth j => rw [hop] at hr; exact chainW_kids hcl _ _ _ _ _ _ (hlk _) r hr
  | tlN n => rw [hop] at hr; exact chainW_kids hcl _ _ _ _ _ _ (hlk _) r hr
  | pair =>
    rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr
    intro _
    have he := hpair hop
    refine ⟨_, hlk nd.id, rfl, rfl, ?_⟩
    rw [he]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | const k => rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr; intro h; simp at h
  | add => rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr; intro h; simp at h
  | mul => rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr; intro h; simp at h
  | isF => rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr; intro h; simp at h
  | isNil => rw [hop] at hr; simp only [List.mem_singleton] at hr; subst hr; intro h; simp at h

theorem nodesW_kids (hcl : ClP cs []) (c S : ℕ) (lk : ℕ → Noun) (s : Noun) (hs : GoodN cs s)
    (hlk : ∀ n, GoodN cs (lk n)) : ∀ (nds : List JNode) (ctr : ℕ),
    (∀ nd ∈ nds, (nd.op = .pair → lk nd.id = .cell (lk nd.a) (lk nd.b))) →
    ∀ r ∈ nodesWG (p := p) hd c S lk s ctr nds, ReadKids p cs hd r
  | [], _, _, r, hr => by simp [nodesWG] at hr
  | nd :: nds, ctr, hnd, r, hr => by
    simp only [nodesWG, List.mem_append] at hr
    rcases hr with hr | hr
    · exact nodeW_kids hcl c S ctr lk s nd hs hlk (hnd nd (by simp)) r hr
    · exact nodesW_kids hcl c S lk s hs hlk nds _ (fun nd' h => hnd nd' (by simp [h])) r hr

theorem blockW_kids (hcl : ClP cs []) (R : ℕ → Nock.Jet.Autogen.Tpl) (c i : ℕ) (s : Noun) (hs : GoodN cs s)
    (hv : ∀ y ∈ (honestRows p (R i) s c).map Nock.Jet.Interp.JRow.val, GoodN cs y)
    (hT : (R i).WellTyped p) (hsem : ∃ r, (R i).sem p s = some r) :
    ∀ r ∈ blockWG (p := p) hd R c i s, ReadKids p cs hd r := by
  intro r hr
  simp only [blockWG, List.mem_cons] at hr
  rcases hr with rfl | hr
  · intro h; simp [callPre] at h
  · refine nodesW_kids hcl c _ _ s hs ?_ _ _ ?_ r hr
    · intro n
      unfold Nock.Jet.ChipJ8.honestLook
      cases hn : (honestRows p (R i) s c)[n]? with
      | none => intro a b e; simp [z0] at e
      | some row =>
        simp only [Option.map_some, Option.getD_some]
        exact hv _ (List.mem_map.mpr ⟨row, List.mem_of_getElem? hn, rfl⟩)
    · intro nd hnd
      exact pair_look (R i) hT s hsem c nd hnd

theorem honestJ8_kids (hcl : ClP cs []) (R : ℕ → Nock.Jet.Autogen.Tpl) (regs : List ℕ) (calls : List (ℕ × Noun))
    (hgood : ∀ cl ∈ calls.zipIdx, GoodN cs cl.1.2 ∧
      (∀ y ∈ (honestRows p (R cl.1.1) cl.1.2 cl.2).map Nock.Jet.Interp.JRow.val, GoodN cs y) ∧
      (R cl.1.1).WellTyped p ∧ (∃ r, (R cl.1.1).sem p cl.1.2 = some r)) :
    ∀ r ∈ honestJ8G (p := p) hd R regs calls, ReadKids p cs hd r := by
  intro r hr
  unfold honestJ8G at hr
  simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hr
  rcases hr with ⟨i, -, rfl⟩ | ⟨⟨⟨i, s⟩, c⟩, hmem, hr⟩
  · intro h; simp [regPre] at h
  · obtain ⟨h1, h2, h3, h4⟩ := hgood _ hmem
    exact blockW_kids hcl R c i s h1 h2 h3 h4 r hr

/-- `mvFixP` changes only `mv`. -/
theorem mvFixP_mem' (rows : List (CRow (ZMod p))) (pins : List (List (ZMod p))) :
    ∀ x ∈ ComplJ8Data.mvFixP p rows pins, ∃ r ∈ rows, x.pre = r.pre ∧ x.w.kN = r.w.kN ∧ x.w.vN = r.w.vN ∧
      x.w.kL = r.w.kL ∧ x.w.vL = r.w.vL ∧ x.w.kR = r.w.kR ∧ x.w.vR = r.w.vR := by
  intro x hx
  unfold ComplJ8Data.mvFixP at hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  refine ⟨r, hr, ?_⟩
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A small atom or a member cell: the J handle is the cell table's handle `hdlP`. -/
theorem hOf_hdlP (acs : List Noun) (y : Noun) (hat : ∀ v, y = .atom v → v < p) (hc : y.isCell = true → y ∈ cs) :
    hOf (p := p) cs y = ((((ComplJ8Data.hdlP p cs acs y).1 : ℕ) : ZMod p),
      (((ComplJ8Data.hdlP p cs acs y).2 : ℕ) : ZMod p)) := by
  cases y with
  | atom v =>
    have hv := hat v rfl
    simp [hOf, ComplJ8Data.hdlP, hv]
  | cell a b =>
    have hm := hc rfl
    simp only [hOf, ComplJ8Data.hdlP, Nat.cast_one]
    rw [ComplJ8OfBal.genIdxOf_eq _ _ hm]

end Kids

/-! ## 9. `hJ` from the sibling binder -/

section HJ
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The J export key's denominator: `1 / (ρH + recDen 0 γH κ)`. -/
theorem fH_key (χ : Coins frameJ8 K) (a b1 b2 c1 c2 : ZMod p) :
    ComplJ8OfBal.fH δ b χ (Nock.Jet.RapJetJ8.keyK 5 [a, b1, b2, c1, c2]) =
      (ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ) (a, (b1, b2), (c1, c2)))⁻¹ := by
  simp only [ComplJ8OfBal.fH]
  congr 1
  rw [VerJ8.coinsCV_J8]
  have hg : FrameVSQ.gamHQ δ (toVSQ χ) = ComplJ8Bad.γH δ χ := rfl
  have hr : FrameVSQ.rhoHQ δ (toVSQ χ) = ComplJ8Bad.ρH δ χ := rfl
  rw [hg, hr]
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_five, BalanceQ.liftRec, Nock.Jet.RapJetJ8.keyK, recDen]
  simp [IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

set_option maxHeartbeats 1000000 in
/-- **`hJ`**: with the J rows at the cell table's handle `hJd`, no sibling binder: the calls' typing facts (`calls_of_hregC`), the base-gate
fact `kN = 1` on export reads and `|cells| < p`, every J export key's weight is the cell handle weight of its
node serial. -/
theorem hJ_export {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjC : Function.Injective (powN o (j8DataOf p Rg Rt hgen).cells.length)) (χ : Coins frameJ8 K)
    (hcalls : ∀ cl ∈ (j8DataOf p Rg Rt hgen).calls,
      (Rt cl.1).WellTyped p ∧ ∃ r, (Rt cl.1).sem p cl.2 = some r)
    (hlen : (j8DataOf p Rg Rt hgen).cells.length < p)
    (hkN : ∀ x ∈ (j8DataOf p Rg Rt hgen).jrows,
      (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1) :
    ∀ row ∈ (j8DataOf p Rg Rt hgen).jrows, ∀ κ ∈ Nock.Jet.ChipJ8.keysOf Nock.Jet.ChipJ8.entsX row,
      ComplJ8OfBal.fH δ b χ (Nock.Jet.RapJetJ8.keyK 5 κ) =
        GC δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) o χ (κ.headD 0).val := by
  set D := j8DataOf p Rg Rt hgen with hD
  intro x hx κ hκ
  have hκ' : κ = [x.w.vN, x.w.kL, x.w.vL, x.w.kR, x.w.vR] := by
    simp only [Nock.Jet.ChipJ8.keysOf, Nock.Jet.ChipJ8.entsX, List.mem_map, List.mem_filter, List.mem_cons,
      List.not_mem_nil, or_false] at hκ
    obtain ⟨e, ⟨he, hk⟩, rfl⟩ := hκ
    rcases he with rfl | rfl | rfl <;>
      simp [Nock.Jet.ChipJ8.keyX, Nock.Jet.ChipJ8.KE.ev, Nock.Jet.ChipJ8.colOf, Nock.Jet.ChipJ8.Col.vN,
        Nock.Jet.ChipJ8.Col.kL, Nock.Jet.ChipJ8.Col.vL, Nock.Jet.ChipJ8.Col.kR, Nock.Jet.ChipJ8.Col.vR]
  obtain ⟨hkd, -⟩ := ComplJ8Data.keysOf_entsX_head x κ hκ
  have hk1 := hkN x hx hkd
  obtain ⟨r0, hr0, hpre, e1, e2, e3, e4, e5, e6⟩ := mvFixP_mem' _ _ x hx
  have hcl : ComplJ8Data.ClP D.cells [] := ComplJ8Data.cells_closed _
  have hjn := ComplJ8Data.jn_good p Rg Rt hgen
  have hk := honestJ8_kids (p := p) (hd := ComplJ8Data.hJd p D.cells D.acs) hcl Rt D.regs D.calls (by
      intro cl hcl'
      have hc1 := List.fst_mem_of_mem_zipIdx hcl'
      have hc := hcalls cl.1 hc1
      refine ⟨hjn _ ?_, fun y hy => hjn _ ?_, hc.1, hc.2⟩
      · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨cl, hcl', List.mem_cons_self⟩)
      · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨cl, hcl', List.mem_cons_of_mem _ hy⟩))
    r0 hr0 (by rw [← hpre]; exact hkd)
  obtain ⟨y, hy, k1, k2, k3, k4, k5, k6⟩ := hk
  cases y with
  | atom v => rw [e1, k1] at hk1; exact absurd hk1 (ComplJ8Data.hJd_atom_ne p _ _ v)
  | cell yl yr =>
    have hm := hy yl yr rfl
    have hkids := hcl yl yr hm (by simp)
    have hxl : yl.isCell = true → yl ∈ D.cells := fun h => by
      cases yl with
      | atom _ => simp [Noun.isCell] at h
      | cell a b => exact hkids.1 a b rfl
    have hxr : yr.isCell = true → yr ∈ D.cells := fun h => by
      cases yr with
      | atom _ => simp [Noun.isCell] at h
      | cell a b => exact hkids.2 a b rfl
    have hjl := List.idxOf_lt_length_of_mem hm
    have hv : x.w.vN = ((D.cells.idxOf (Noun.cell yl yr) : ℕ) : ZMod p) := by
      rw [e2, k2]
      simp only [ComplJ8Data.hJd, ComplJ8Data.hdlP]
      rw [ComplJ8OfBal.genIdxOf_eq _ _ hm]
    have hval : (κ.headD 0).val = D.cells.idxOf (.cell yl yr) := by
      rw [hκ']
      simp only [List.headD_cons]
      rw [hv, ZMod.val_natCast, Nat.mod_eq_of_lt (hjl.trans hlen)]
    rw [hval]
    simp only [GC]
    rw [cellHx_eq δ b D (cells_pos Rt hgen) o hinjC χ rfl _ hjl (List.getElem_idxOf hjl) hxl hxr, hκ', fH_key]
    have hkl : x.w.kL = (((D.H yl).1 : ℕ) : ZMod p) ∧ x.w.vL = (((D.H yl).2 : ℕ) : ZMod p) ∧
        x.w.kR = (((D.H yr).1 : ℕ) : ZMod p) ∧ x.w.vR = (((D.H yr).2 : ℕ) : ZMod p) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [e3, k3]; rfl
      · rw [e4, k4]; rfl
      · rw [e5, k5]; rfl
      · rw [e6, k6]; rfl
    rw [hv, hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2]

end HJ


/-! ## 10. One active entry per slot -/

section OneHot
variable {ι L : Type} [Field L]

theorem uniq_sum (α : ι → L) : ∀ (l : List ι), l.Pairwise (fun x y => α x * α y = 0) → ∀ x0 ∈ l, α x0 ≠ 0 →
    ∀ g : ι → L, (l.map fun x => α x * g x).sum = α x0 * g x0
  | [], _, x0, h, _, _ => absurd h List.not_mem_nil
  | y :: l, hp, x0, hx0, hne, g => by
    rw [List.pairwise_cons] at hp
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx0 with rfl | hx0'
    · have hz : ∀ z ∈ l, α z = 0 := fun z hz => (mul_eq_zero.mp (hp.1 z hz)).resolve_left hne
      have : (l.map fun x => α x * g x).sum = 0 := List.sum_eq_zero fun v hv => by
        obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hv; rw [hz z hz', zero_mul]
      rw [this, add_zero]
    · by_cases hy : α y = 0
      · rw [hy, zero_mul, zero_add]; exact uniq_sum α l hp.2 x0 hx0' hne g
      · exact absurd (hp.1 x0 hx0') (mul_ne_zero hy hne)

theorem sum_filter_mul (α h : ι → L) (P : ι → Bool) : ∀ l : List ι,
    ((l.filter P).map fun x => α x * h x).sum = (l.map fun x => α x * (if P x = true then h x else 0)).sum
  | [] => rfl
  | y :: l => by
    by_cases hy : P y = true <;> simp [List.filter_cons, hy, sum_filter_mul α h P l]

/-- **One active entry**: with pairwise-exclusive activities and a pair flag that excludes every entry, the slot's
`A · D⁻¹` weighted by the activity into one balance is the sum of that balance's active reciprocals. -/
theorem onehot_slot (l : List ι) (α D : ι → L) (P : ι → Bool) (f A B : L)
    (hp : l.Pairwise fun x y => α x * α y = 0) (hf : f ≠ 0 → ∀ x ∈ l, α x = 0) :
    ((l.filter P).map α).sum * (((l.map α).sum + f * A) * ((l.map fun x => α x * D x).sum + f * B)⁻¹) =
      ((l.filter P).map fun x => α x * (D x)⁻¹).sum := by
  by_cases h0 : ∀ x ∈ l, α x = 0
  · have h1 : ((l.filter P).map α).sum = 0 := List.sum_eq_zero fun v hv => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv; exact h0 z (List.mem_of_mem_filter hz)
    have h2 : ((l.filter P).map fun x => α x * (D x)⁻¹).sum = 0 := List.sum_eq_zero fun v hv => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv; rw [h0 z (List.mem_of_mem_filter hz), zero_mul]
    rw [h1, h2, zero_mul]
  · push Not at h0
    obtain ⟨x0, hx0, hne⟩ := h0
    have hf0 : f = 0 := by
      by_contra hf'; exact hne (hf hf' x0 hx0)
    have e1 : (l.map α).sum = α x0 := by
      have := uniq_sum α l hp x0 hx0 hne (fun _ => 1); simpa using this
    have e2 := uniq_sum α l hp x0 hx0 hne D
    have e3 : ((l.filter P).map α).sum = α x0 * (if P x0 = true then 1 else 0) := by
      have := sum_filter_mul α (fun _ => 1) P l
      simp only [mul_one] at this
      rw [this, uniq_sum α l hp x0 hx0 hne (fun x => if P x = true then 1 else 0)]
    have e4 : ((l.filter P).map fun x => α x * (D x)⁻¹).sum = α x0 * (if P x0 = true then (D x0)⁻¹ else 0) := by
      rw [sum_filter_mul, uniq_sum α l hp x0 hx0 hne (fun x => if P x = true then (D x)⁻¹ else 0)]
    rw [e1, e2, e3, e4, hf0]; simp only [zero_mul, add_zero]
    by_cases hP : P x0 = true
    · simp only [hP, if_true, mul_one]
      rw [mul_inv, mul_inv_cancel_left₀ hne]
    · simp [hP]

end OneHot

/-! ## 11. The compute row's `.x` term -/

section XRow
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (chalV pubVal : ℕ → ZMod p)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (SlotX EntX Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castSlotX castEntX DX invQX)

/-- The `.x` reciprocal sum of a compute row (at the stage-1 environment `env0`). -/
def xSum (j : ℕ) : 𝕂′ :=
  ((ChipHX.slotsX (F := ℚ)).map fun S => ((S.ents.filter fun x => decide (x.bal = Bal.x)).map fun x =>
    algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act (HonestTraceX.env0 H pd W chalV pubVal j)) *
      (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
        (HonestTraceX.env0 H pd W chalV pubVal j) x.rcd)⁻¹).sum).sum

theorem acts_pairwise (j : ℕ) (S : SlotX ℚ) (hS : S ∈ (ChipHX.slotsX : List (SlotX ℚ))) :
    S.ents.Pairwise fun x y =>
      algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act (HonestTraceX.env0 H pd W chalV pubVal j)) *
        algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX y.act (HonestTraceX.env0 H pd W chalV pubVal j)) = 0 := by
  set e0 := HonestTraceX.env0 H pd W chalV pubVal j
  set r := HonestWalkX.rowAtWX W (j + 1)
  have hz : ∀ x ∈ S.ents, Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX.stIdx r.st ∉ x.states →
      ChipHX.evalQX x.act e0 = 0 := by
    intro x hx hn
    rw [← TeleCQX.castEntX_act]
    have hok := (TeleCQX.slotsX_states_ok S hS x hx).1
    exact ComplJ8CompPole.act_zero (castEntX x) e0 H pd r (HonestTraceX.flX j) (HonestTraceX.llX W j) rfl
      fun k hk => ⟨hok k hk, fun h => hn (h ▸ hk)⟩
  have hd := List.pairwise_map.mp (TeleCQX.slotsX_states_disj S hS)
  refine List.Pairwise.imp_of_mem ?_ hd
  intro x y hx hy hxy
  by_cases hj : Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX.stIdx r.st ∈ x.states
  · rw [hz y hy (hxy _ hj), map_zero, mul_zero]
  · rw [hz x hx hj, map_zero, zero_mul]

/-- **The compute row's `.x` balance term is the reciprocal sum of its active export records.** -/
theorem termQX_x (j : ℕ) :
    TeleCQX.termQX δ b (HonestTraceX.env1 b δ H pd W chalV pubVal j) .x = xSum δ b H pd W chalV pubVal j := by
  set e0 := HonestTraceX.env0 H pd W chalV pubVal j with he0
  set e1 := HonestTraceX.env1 b δ H pd W chalV pubVal j with he1
  set r := HonestWalkX.rowAtWX W (j + 1)
  unfold TeleCQX.termQX xSum
  congr 1
  refine List.map_congr_left fun S hS => ?_
  have hS' : castSlotX (F := ZMod p) S ∈ ChipHX.slotsX (F := ZMod p) := by
    rw [← TeleCQX.slotsX_cast]; exact List.mem_map_of_mem hS
  -- the activity reads the base columns
  have htr : ∀ c < 69, e1.trace c = e0.trace c := fun c hc => by
    simp only [he1, he0, HonestTraceX.env1, HonestTraceX.env0, HonestTraceX.preT, if_pos hc]
  have hcong : ∀ g : CoeffExpr ℚ, HonestTraceX.okC HonestTraceX.okFs g = true →
      ChipHX.evalQX g e1 = ChipHX.evalQX g e0 := by
    intro g hg
    rw [← HonestTraceX.eval_mapC_castX, ← HonestTraceX.eval_mapC_castX]
    refine HonestTraceX.eval_okC HonestTraceX.okFs _ (by rw [HonestTraceX.okC_mapC]; exact hg) e1 e0
      fun k i hk => ?_
    cases k <;> simp [HonestTraceX.okFs] at hk
    exact htr i hk
  have hokS := List.all_eq_true.mp HonestTraceX.slotsAct_ok S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hokS
  rw [hcong _ hokS.1.1.1.1]
  obtain ⟨s, hs4, hSs, hinv, hinvIm⟩ := HonestTraceX.slot_index hS'
  have hl1 : Compute.LogUp.limbVal b e1.trace (69 + 6 * s) =
      Quad.re _ (HonestTraceX.invV b δ H pd W chalV pubVal j (HonestTraceX.slotAt s)) := by
    rw [← HonestTraceX.limb_inv b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX.trX_pre b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (by have := k.isLt; omega)]
    rfl
  have hl2 : Compute.LogUp.limbVal b e1.trace (72 + 6 * s) =
      Quad.im _ (HonestTraceX.invV b δ H pd W chalV pubVal j (HonestTraceX.slotAt s)) := by
    rw [← HonestTraceX.limb_invIm b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX.trX_pre b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (by have := k.isLt; omega)]
    rfl
  have hinvQ : invQX δ (Compute.TowerD.gatherEnv b e1) S =
      HonestSlotX.aVal b δ (castSlotX S) e0 * (HonestSlotX.dVal b δ (castSlotX S) e0)⁻¹ := by
    have h1 : S.inv = 69 + 6 * s := hinv
    have h2 : S.invIm = 72 + 6 * s := hinvIm
    show Quad.mk _ (Compute.LogUp.limbVal b e1.trace S.inv) (Compute.LogUp.limbVal b e1.trace S.invIm) = _
    rw [h1, h2, hl1, hl2, Quad.mk_re_im, HonestTraceX.invV, ← hSs]
  rw [hinvQ, TeleCQX.evalQX_actB, ComplJ8CompPole.aVal_expand, ComplJ8CompPole.dVal_expand]
  have hpx : ∀ q, S.pair = some q → q.2.2.2 ≠ Bal.x := by
    intro q hq
    simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl | rfl <;> simp [ChipHX.slot0X, ChipHX.slot1X, ChipHX.slot2X, ChipHX.slot3X] at hq <;>
      rw [← hq] <;> decide
  have hpw := acts_pairwise (K := K) δ H pd W chalV pubVal j S hS
  have hrcd : ∀ x : EntX ℚ, (castEntX (F := ZMod p) x).rcd = x.rcd := fun _ => rfl
  have hact : ∀ x : EntX ℚ, (castEntX (F := ZMod p) x).act.eval e0 = ChipHX.evalQX x.act e0 :=
    fun x => TeleCQX.castEntX_act x e0
  simp only [castSlotX, List.map_map, Function.comp_def, hrcd, hact]
  have hsum : ∀ l : List (EntX ℚ), algebraMap (ZMod p) 𝕂′ (l.map fun x => ChipHX.evalQX x.act e0).sum =
      (l.map fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0)).sum := fun l => by
    rw [map_list_sum, List.map_map]; rfl
  rw [map_add, hsum, hsum]
  cases hp : S.pair with
  | none =>
    simp only [map_zero, add_zero]
    have := onehot_slot S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
      (fun x => DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.x)) 0 0 0 hpw
      (fun h => absurd rfl h)
    simpa using this
  | some q =>
    obtain ⟨fl, a, c, bb⟩ := q
    have hb := hpx _ hp
    simp only [hb, if_false, map_zero, add_zero]
    refine onehot_slot S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
      (fun x => DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.x))
      (algebraMap (ZMod p) 𝕂′ (e0.trace fl)) _ _ hpw ?_
    intro hne x hx
    have hfl : e0.trace fl ≠ 0 := fun h => hne (by rw [h, map_zero])
    have h0 := ComplJ8CompPole.hex_slots (castSlotX S) hS' e0 H pd r (HonestTraceX.flX j) (HonestTraceX.llX W j) rfl
      fl a c bb hp hfl (castEntX x) (List.mem_map_of_mem hx)
    show algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0) = 0
    rw [← hact, h0, map_zero]

end XRow

/-! ## 12. An active compute export consume reads a parent cell and its two children -/

section XPar
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.CoordinateCompiler

/-- **The active export record of an honest row is `(parent, left, right)` with `parent = cell left right`**
(`RowOKX`, and the `s3` decode `sf1 = [ftth fttt]` of `rowOfSkelX`). -/
theorem xEnt_par {p : ℕ} [Fact p.Prime] (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (r : RowNX)
    (fst lst : ZMod p) (hok : HonestCompX.RowOKX p r) (hH : HonestCompX.HdlOK p H)
    (hs3 : r.st = .s3 → r.sf1.isCell = true → r.sf1 = .cell r.ftth r.fttt)
    (S : SlotX (ZMod p)) (hS : S ∈ (ChipHX.slotsX : List (SlotX (ZMod p)))) (x : EntX (ZMod p)) (hx : x ∈ S.ents)
    (hb : x.bal = .x)
    (hact : x.act.eval (⟨Nock.V1J8.FillX.colXE H pd r fst lst, Nock.V1J8.FillX.colXE H pd r fst lst,
      fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p)) ≠ 0) :
    ∃ kP kL kR, x.rcd = cellRecX (hdX kP) (hdX kL) (hdX kR) ∧
      HonestCompX.hN r kP = .cell (HonestCompX.hN r kL) (HonestCompX.hN r kR) ∧ kP < 12 ∧ kL < 12 ∧ kR < 12 := by
  simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl
  all_goals simp only [slot0X, slot1X, slot2X, slot3X, List.mem_cons, List.not_mem_nil, or_false] at hx
  all_goals rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (simp at hb; done) | skip
  all_goals simp only [EntX.act, CoeffExpr.eval] at hact
  all_goals rw [ComplJ8Data.selS_eval H pd r fst lst _ (by decide) (by decide)] at hact
  case inr.inr.inl.inr.inr.inr.inr.inl =>
    refine ⟨3, 9, 10, rfl, ?_, by decide, by decide, by decide⟩
    split_ifs at hact with hm
    swap; · simp at hact
    have hst : r.st = .s3 := by
      have : stIdx r.st = 3 := by simpa using hm
      cases hs : r.st <;> rw [hs] at this <;> simp [stIdx] at this ⊢
    have he : (kcE xSf1 : CoeffExpr (ZMod p)).eval (⟨Nock.V1J8.FillX.colXE H pd r fst lst,
        Nock.V1J8.FillX.colXE H pd r fst lst, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p)) =
        HonestCompX.hk H r.sf1 - 2 * HonestCompX.hb H r.sf1 := by
      simp [kcE, kbE, kbX, ChipH.cc, CoeffExpr.eval, xSf1, hdX, Nock.V1J8.FillX.colXE, HonestCompX.hN]
    rw [he] at hact
    have hc : r.sf1.isCell = true := by
      rcases hsf : r.sf1 with v | ⟨a, b⟩
      · exfalso
        rw [hsf] at hact
        by_cases hv : v < p
        · have := hH.small v hv
          simp [HonestCompX.hk, HonestCompX.hb, this] at hact
        · have := hH.big v (Nat.not_lt.mp hv)
          simp [HonestCompX.hk, HonestCompX.hb, this] at hact
      · rfl
    exact hs3 hst hc
  all_goals
    split_ifs at hact with hm
    swap; · simp at hact
    refine ⟨_, _, _, rfl, ?_, by decide, by decide, by decide⟩
    unfold HonestCompX.RowOKX at hok
    cases hst : r.st <;> rw [hst] at hok <;>
      simp [hst, stIdx, opStatesX, l2X, l3X, ChipH.consCol] at hm <;>
      simp_all [HonestCompX.hN]

end XPar

/-! ## 13. The `.x` reciprocal sum of a run row is the weighted total of its export consumes -/

section XRun
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (SlotX EntX Bal cellRecX hdX)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castSlotX castEntX DX invQX)

theorem wsum_flatMap {R α : Type} [CommRing R] (G : ℕ → R) (f : α → List (ℕ × ℕ)) : ∀ l : List α,
    wsum G (l.flatMap f) = (l.map fun a => wsum G (f a)).sum
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, wsum_append, wsum_flatMap G f l]; simp

theorem wsum_filterMap {R α : Type} [CommRing R] (G : ℕ → R) (f : α → Option (ℕ × ℕ)) : ∀ l : List α,
    wsum G (l.filterMap f) = (l.map fun a => match f a with | none => 0 | some q => (q.2 : R) * G q.1).sum
  | [] => rfl
  | a :: l => by
    rw [List.filterMap_cons]
    cases h : f a with
    | none => simp only [h, List.map_cons, List.sum_cons]; rw [wsum_filterMap G f l]; simp
    | some q =>
      simp only [h, List.map_cons, List.sum_cons]
      rw [← wsum_filterMap G f l]
      simp [wsum]

theorem rowOfSkelX_s3 (sk : SkelX) : (rowOfSkelX sk).st = .s3 → (rowOfSkelX sk).sf1.isCell = true →
    (rowOfSkelX sk).sf1 = .cell (rowOfSkelX sk).ftth (rowOfSkelX sk).fttt := by
  unfold rowOfSkelX
  cases sk.state <;> simp
  intro h
  cases hk : kidE sk 0 with
  | atom v => rw [hk] at h; simp [Noun.isCell] at h
  | cell a c => rfl

set_option maxHeartbeats 1000000 in
/-- **The `.x` reciprocal sum of run row `j` is the weighted total of the row's export consumes.** -/
theorem xSum_run (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataOf p Rg Rt hgen).cells.length < p) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjC : Function.Injective (powN o (j8DataOf p Rg Rt hgen).cells.length)) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) (j : ℕ) (hj : j < (bfsForest [t]).length) :
    xSum δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      wsum (GC δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) o χ)
        (ComplJ8Data.xConsumesP p (⟨Nock.V1J8.FillX.colXE (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
          (HonestWalkX.rowAtWX (bfsForest [t]) (j + 1)) (HonestTraceX.flX j) (HonestTraceX.llX (bfsForest [t]) j),
          Nock.V1J8.FillX.colXE (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
          (HonestWalkX.rowAtWX (bfsForest [t]) (j + 1)) (HonestTraceX.flX j) (HonestTraceX.llX (bfsForest [t]) j),
          fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))) := by
  set D := j8DataOf p Rg Rt hgen with hD
  set W := bfsForest [t] with hW
  set rr := HonestWalkX.rowAtWX W (j + 1) with hrr
  set e0 := HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j with he0
  set e' : Nock.Reified.Env (ZMod p) := ⟨Nock.V1J8.FillX.colXE D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j),
    Nock.V1J8.FillX.colXE D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j), fun _ => 0, fun _ => 0⟩ with he'
  have hT : e0.trace = e'.trace := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c =
      Nock.V1J8.FillX.colXE D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) c
    rw [Nock.V1J8.FillX.colXE_eq]; rfl
  have hin : InTree t (W[j]'hj) :=
    Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton (List.getElem_mem hj)
  have hrow : rr = rowOfSkelX (W[j]'hj).label := by
    simp [hrr, HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  have hok : HonestCompX.RowOKX p rr := by rw [hrow]; exact HonestRowX.rowOKX_of_genX hgen hin (hsm _ hin)
  have hs3 : rr.st = .s3 → rr.sf1.isCell = true → rr.sf1 = .cell rr.ftth rr.fttt := by
    rw [hrow]; exact rowOfSkelX_s3 _
  have hrowm : rr ∈ D.rows.toList := by
    rw [hrow]
    simp only [hD, j8DataOf, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  have hH := ComplJ8Data.hdlOK_hdlP p D.cells D.acs
  unfold xSum ComplJ8Data.xConsumesP
  rw [wsum_flatMap, ← TeleCQX.slotsX_cast (F := ZMod p), List.map_map]
  refine congrArg List.sum (List.map_congr_left fun S hS => ?_)
  have hS' : castSlotX (F := ZMod p) S ∈ ChipHX.slotsX (F := ZMod p) := by
    rw [← TeleCQX.slotsX_cast]; exact List.mem_map_of_mem hS
  simp only [Function.comp_apply]
  rw [show (castSlotX (F := ZMod p) S).ents = S.ents.map castEntX from rfl, List.filter_map, List.filterMap_map,
    wsum_filterMap]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨hxS, hb⟩ := List.mem_filter.mp hx
  have hb' : x.bal = Bal.x := by simpa using hb
  have hmem : castEntX (F := ZMod p) x ∈ (castSlotX (F := ZMod p) S).ents := List.mem_map_of_mem hxS
  have hae : (castEntX (F := ZMod p) x).act.eval e' = ChipHX.evalQX x.act e0 := by
    rw [← TeleCQX.castEntX_act]
    refine HonestTraceX.eval_okC HonestTraceX.okFs _ (ComplJ8CompPole.hacts_slots _ hS' _ hmem) e' e0
      fun k i hk => ?_
    cases k <;> simp [HonestTraceX.okFs] at hk
    show e'.trace i = e0.trace i
    rw [hT]
  simp only [Function.comp_apply]
  rw [hae]
  by_cases ha : ChipHX.evalQX x.act e0 = 0
  · rw [ha]; simp
  have hne' : (castEntX (F := ZMod p) x).act.eval e' ≠ 0 := by rwa [hae]
  have hv0 : (ChipHX.evalQX x.act e0).val ≠ 0 := fun h => ha ((ZMod.val_eq_zero _).mp h)
  rw [if_neg hv0]
  obtain ⟨kP, kL, kR, hrc, hpar, h1, h2, h3⟩ :=
    xEnt_par D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) hok hH hs3 _ hS' _ hmem hb' hne'
  obtain ⟨k', tail, hr', hcell, hk, n, hn, hsub⟩ :=
    ComplJ8Data.xEnt_cell D.H D.pd rr _ _ hok hH _ hS' _ hmem hb' hne'
  have hrcd : (castEntX (F := ZMod p) x).rcd = x.rcd := rfl
  try rw [hrcd] at hr'
  try rw [hrcd] at hrc
  rw [hrc] at hr'
  have hkk : k' = kP := by
    simp [cellRecX, ChipHX.recOf, ChipH.cellRec, hdX] at hr'; omega
  subst hkk
  have hcm : HonestCompX.hN rr k' ∈ D.cells :=
    ComplJ8Data.mem_cells_of_subs (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, hrowm, hn⟩))) _ hsub
  rw [hpar] at hcm
  set L := HonestCompX.hN rr kL with hL
  set R := HonestCompX.hN rr kR with hR
  have hjl := List.idxOf_lt_length_of_mem hcm
  obtain ⟨x1, y1, hxy, hxL, hxR⟩ := cells_kids Rt hgen _ hcm
  simp only [Noun.cell.injEq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  have tr : ∀ c, e0.trace c = HonestCompX.colX D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) c :=
    fun c => rfl
  have tP : e0.trace (hdX k').v = ((D.cells.idxOf (Noun.cell L R) : ℕ) : ZMod p) := by
    rw [tr, show (hdX k').v = 26 + 2 * k' from rfl, HonestCompX.colX_v _ _ _ _ _ _ h1, hpar]
    show (((ComplJ8Data.hdlP p D.cells D.acs (Noun.cell L R)).2 : ℕ) : ZMod p) = _
    simp only [ComplJ8Data.hdlP]
    rw [ComplJ8OfBal.genIdxOf_eq _ _ hcm]
  have tP' : e'.trace (hdX k').v = ((D.cells.idxOf (Noun.cell L R) : ℕ) : ZMod p) := by rw [← hT]; exact tP
  have hval : (e'.trace (hdX k').v).val = D.cells.idxOf (Noun.cell L R) := by
    rw [tP', ZMod.val_natCast, Nat.mod_eq_of_lt (hjl.trans hlen)]
  rw [hrcd, hrc]
  simp only [cellRecX, ChipHX.recOf, ChipH.cellRec, List.map_cons]
  rw [hval]
  simp only [GC]
  rw [cellHx_eq δ b D (cells_pos Rt hgen) o hinjC χ rfl _ hjl (List.getElem_idxOf hjl) hxL hxR,
    ComplJ8CompPole.den_split δ b e0 χ rfl _ (by simp),
    ← map_natCast (algebraMap (ZMod p) 𝕂′), ZMod.natCast_zmod_val]
  congr 2
  have t1 : e0.trace (hdX kL).k = (((D.H L).1 : ℕ) : ZMod p) := by
    rw [tr, show (hdX kL).k = 25 + 2 * kL from rfl, HonestCompX.colX_k _ _ _ _ _ _ h2]; rfl
  have t2 : e0.trace (hdX kL).v = (((D.H L).2 : ℕ) : ZMod p) := by
    rw [tr, show (hdX kL).v = 26 + 2 * kL from rfl, HonestCompX.colX_v _ _ _ _ _ _ h2]; rfl
  have t3 : e0.trace (hdX kR).k = (((D.H R).1 : ℕ) : ZMod p) := by
    rw [tr, show (hdX kR).k = 25 + 2 * kR from rfl, HonestCompX.colX_k _ _ _ _ _ _ h3]; rfl
  have t4 : e0.trace (hdX kR).v = (((D.H R).2 : ℕ) : ZMod p) := by
    rw [tr, show (hdX kR).v = 26 + 2 * kR from rfl, HonestCompX.colX_v _ _ _ _ _ _ h3]; rfl
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_eight, BalanceQ.liftRec, DenXJ8.keyX, DenXJ8.keyXN, recDen]
  simp [ChipHX.RE.ev, tP, t1, t2, t3, t4, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

end XRun

/-! ## 14. `hC`: the compute export public is the weighted total of the compute's export consumes -/

section HC
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The run's compute base columns are the honest stage-1 columns of the BFS rows. -/
theorem bases_getD (j : ℕ) (hj : j < (bfsForest [t]).length) :
    (j8DataOf p Rg Rt hgen).bases.getD j (fun _ => 0) =
      Nock.V1J8.FillX.colXE (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (HonestWalkX.rowAtWX (bfsForest [t]) (j + 1)) (HonestTraceX.flX j) (HonestTraceX.llX (bfsForest [t]) j) := by
  have hl : j < (j8DataOf p Rg Rt hgen).bases.length := by
    simp [j8DataOf, ComplJ8Data.basesP, ComplJ8Data.rowsOfT, hj]
  rw [List.getD_eq_getElem _ _ hl]
  simp only [j8DataOf, ComplJ8Data.basesP, List.getElem_map, List.getElem_zipIdx]
  funext c
  have hrow : HonestWalkX.rowAtWX (bfsForest [t]) (j + 1) = rowOfSkelX ((bfsForest [t])[j]'hj).label := by
    simp [HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  rw [hrow]
  simp only [ComplJ8Data.rowsOfT, List.toList_toArray, List.getElem_map, zero_add, List.size_toArray,
    List.length_map]
  congr 1
  · by_cases h0 : j = 0 <;> simp [ComplJ8Data.flagP, HonestTraceX.flX, h0]
  · by_cases h0 : j + 1 = (bfsForest [t]).length <;> simp [ComplJ8Data.flagP, HonestTraceX.llX, h0]

set_option maxHeartbeats 1000000 in
/-- **`hC`**: `ρ 3 = Σ_{compute export consumes} mult · 1/(ρH + cellHx serial)` at the run, at every coin, under the
run's small-atom bounds `hsm` (`smallX_of_binders`) and `|cells| < p`. -/
theorem hC_run (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataOf p Rg Rt hgen).cells.length < p) (χ : Coins frameJ8 K) :
    ((BRun δ b Rt hgen hpG h31).M χ).ρ 3 =
      wsum (GC δ b (j8DataOf p Rg Rt hgen) (cells_pos Rt hgen) (orbJ8 _ (dvdOK_of_rows hpG _ h31)) χ)
        ((j8DataOf p Rg Rt hgen).bases.flatMap fun bs =>
          ComplJ8Data.xConsumesP p (⟨bs, bs, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))) := by
  set D := j8DataOf p Rg Rt hgen with hD
  set o := orbJ8 _ (dvdOK_of_rows hpG D h31)
  have hmC : D.cells.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjC := (powN_ok o (le_two_pow_ht D hmC)).1
  show ComplJ8Comp.ρCOf δ b D.H D.pd (bfsForest [t]) (ComplJ8.cJ s f r) χ 3 = _
  rw [rhoC3_rows, wsum_flatMap, ← ComplJ8OfBal.sum_range_getD' (fun _ => 0)]
  have hlb : D.bases.length = (bfsForest [t]).length := by
    simp [hD, j8DataOf, ComplJ8Data.basesP, ComplJ8Data.rowsOfT]
  rw [hlb]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [termQX_x, xSum_run δ b Rt hgen hsm hlen o hinjC χ _ j hj', bases_getD Rt hgen j hj']

end HC

/-! ## 15. `balG` clause 1 at the run, closed (binders only) -/

section Clause1
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

set_option maxHeartbeats 1000000 in

theorem balG1_run (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (χ : Coins frameJ8 K) :
    ((BRun δ b Rt hgen hpG h31).M χ).ρ 3 +
        (Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsW WalkHQ.pubXQ)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsW (WalkHQ.pubXQ + 1)) +
        Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 2) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 3)) =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsC CellHQ.pubHQ)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsC (CellHQ.pubHQ + 1)) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hlen : (j8DataOf p Rg Rt hgen).cells.length < p := size_lt_p Rt hgen hp63 h31 (by simp [sizesJ8])
  set D := j8DataOf p Rg Rt hgen with hD
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hsm := ComplJ8.smallX_of_binders hax hop5
  have hkN : ∀ x ∈ D.jrows, (x.pre.kd = .rp ∨ x.pre.kd = .sl ∨ x.pre.kd = .sr) → x.w.kN = 1 :=
    fun x hx => (Nock.Jet.ChipJ8.gate_facts x (ComplJ8Jet.jrows_gate_run Rt hgen hp0 hRt x hx)).2.2.2
  have hcalls : ∀ cl ∈ D.calls, (Rt cl.1).WellTyped p ∧ ∃ r, (Rt cl.1).sem p cl.2 = some r :=
    ComplJ8Jet.calls_of_hregC hgen Rt hRt
  set o := orbJ8 _ (dvdOK_of_rows hpG D h31)
  have hmC : D.cells.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjC := (powN_ok o (le_two_pow_ht D hmC)).1
  exact balG1_of δ b Rt hgen hpG h31 hwalk
    (ComplJ8Data.xRecs_range p Rg Rt hgen hsm hlen (ComplJ8Data.jReads_range p Rg Rt hgen hlen hkN)) χ
    (hC_run δ b Rt hgen hpG h31 hsm hlen χ) (hJ_export δ b Rt hgen o hinjC χ hcalls hlen hkN)

end Clause1


/-! ## 16. `balG` clause 2, compute side: the row's `.p` term (entries and the `.p` pair) -/

section OneHotP
variable {ι L : Type} [Field L]

/-- **One active entry, with a pair into the same balance**: the pair contributes `f · (1/A₁ + 1/A₂)` when its
flag is boolean and its two denominators are nonzero at `f = 1`. -/
theorem onehot_slot_pair (l : List ι) (α D : ι → L) (P : ι → Bool) (f A1 A2 : L)
    (hp : l.Pairwise fun x y => α x * α y = 0) (hf : f ≠ 0 → ∀ x ∈ l, α x = 0)
    (hfb : f = 0 ∨ f = 1) (hA : f = 1 → A1 ≠ 0 ∧ A2 ≠ 0) :
    (((l.filter P).map α).sum + f) * (((l.map α).sum + f * (A1 + A2)) *
        ((l.map fun x => α x * D x).sum + f * (A1 * A2))⁻¹) =
      ((l.filter P).map fun x => α x * (D x)⁻¹).sum + f * (A1⁻¹ + A2⁻¹) := by
  rcases hfb with rfl | rfl
  · simpa using onehot_slot l α D P 0 (A1 + A2) (A1 * A2) hp hf
  · have h0 := hf one_ne_zero
    obtain ⟨h1, h2⟩ := hA rfl
    have e1 : ((l.filter P).map α).sum = 0 := List.sum_eq_zero fun v hv => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv; exact h0 z (List.mem_of_mem_filter hz)
    have e2 : (l.map α).sum = 0 := List.sum_eq_zero fun v hv => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv; exact h0 z hz
    have e3 : (l.map fun x => α x * D x).sum = 0 := List.sum_eq_zero fun v hv => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv; rw [h0 z hz, zero_mul]
    have e4 : ((l.filter P).map fun x => α x * (D x)⁻¹).sum = 0 := List.sum_eq_zero fun v hv => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv; rw [h0 z (List.mem_of_mem_filter hz), zero_mul]
    rw [e1, e2, e3, e4]
    field_simp
    ring

end OneHotP

section PRow
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (chalV pubVal : ℕ → ZMod p)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (SlotX EntX Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castSlotX castEntX DX invQX)

/-- The `.p` reciprocal sum of a compute row (entries, plus the `.p` pair `(flag · (1/Da + 1/Db))`). -/
def pSum (j : ℕ) : 𝕂′ :=
  ((ChipHX.slotsX (F := ℚ)).map fun S => ((S.ents.filter fun x => decide (x.bal = Bal.p)).map fun x =>
    algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act (HonestTraceX.env0 H pd W chalV pubVal j)) *
      (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
        (HonestTraceX.env0 H pd W chalV pubVal j) x.rcd)⁻¹).sum +
    (match S.pair with
     | some (fl, a, c, bb) => if bb = Bal.p then
         algebraMap (ZMod p) 𝕂′ ((HonestTraceX.env0 H pd W chalV pubVal j).trace fl) *
          ((DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
              (HonestTraceX.env0 H pd W chalV pubVal j) a)⁻¹ +
           (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
              (HonestTraceX.env0 H pd W chalV pubVal j) c)⁻¹)
         else 0
     | none => 0)).sum

/-- **The compute row's `.p` balance term**, when the `.p` pair's two denominators are nonzero on its active
rows (the pair poles of `compPoles`, at a good coin). -/
theorem termQX_p (j : ℕ)
    (hpair : ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), ∀ fl a c bb, S.pair = some (fl, a, c, bb) →
      (HonestTraceX.env0 H pd W chalV pubVal j).trace fl = 1 →
      DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
          (HonestTraceX.env0 H pd W chalV pubVal j) a ≠ 0 ∧
        DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
          (HonestTraceX.env0 H pd W chalV pubVal j) c ≠ 0) :
    TeleCQX.termQX δ b (HonestTraceX.env1 b δ H pd W chalV pubVal j) .p = pSum δ b H pd W chalV pubVal j := by
  set e0 := HonestTraceX.env0 H pd W chalV pubVal j with he0
  set e1 := HonestTraceX.env1 b δ H pd W chalV pubVal j with he1
  set r := HonestWalkX.rowAtWX W (j + 1)
  unfold TeleCQX.termQX pSum
  congr 1
  refine List.map_congr_left fun S hS => ?_
  have hS' : castSlotX (F := ZMod p) S ∈ ChipHX.slotsX (F := ZMod p) := by
    rw [← TeleCQX.slotsX_cast]; exact List.mem_map_of_mem hS
  have htr : ∀ c < 69, e1.trace c = e0.trace c := fun c hc => by
    simp only [he1, he0, HonestTraceX.env1, HonestTraceX.env0, HonestTraceX.preT, if_pos hc]
  have hcong : ∀ g : CoeffExpr ℚ, HonestTraceX.okC HonestTraceX.okFs g = true →
      ChipHX.evalQX g e1 = ChipHX.evalQX g e0 := by
    intro g hg
    rw [← HonestTraceX.eval_mapC_castX, ← HonestTraceX.eval_mapC_castX]
    refine HonestTraceX.eval_okC HonestTraceX.okFs _ (by rw [HonestTraceX.okC_mapC]; exact hg) e1 e0
      fun k i hk => ?_
    cases k <;> simp [HonestTraceX.okFs] at hk
    exact htr i hk
  have hokS := List.all_eq_true.mp HonestTraceX.slotsAct_ok S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hokS
  rw [hcong _ hokS.1.1.1.2]
  obtain ⟨s, hs4, hSs, hinv, hinvIm⟩ := HonestTraceX.slot_index hS'
  have hl1 : Compute.LogUp.limbVal b e1.trace (69 + 6 * s) =
      Quad.re _ (HonestTraceX.invV b δ H pd W chalV pubVal j (HonestTraceX.slotAt s)) := by
    rw [← HonestTraceX.limb_inv b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX.trX_pre b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (by have := k.isLt; omega)]
    rfl
  have hl2 : Compute.LogUp.limbVal b e1.trace (72 + 6 * s) =
      Quad.im _ (HonestTraceX.invV b δ H pd W chalV pubVal j (HonestTraceX.slotAt s)) := by
    rw [← HonestTraceX.limb_invIm b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX.trX_pre b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (by have := k.isLt; omega)]
    rfl
  have hinvQ : invQX δ (Compute.TowerD.gatherEnv b e1) S =
      HonestSlotX.aVal b δ (castSlotX S) e0 * (HonestSlotX.dVal b δ (castSlotX S) e0)⁻¹ := by
    have h1 : S.inv = 69 + 6 * s := hinv
    have h2 : S.invIm = 72 + 6 * s := hinvIm
    show Quad.mk _ (Compute.LogUp.limbVal b e1.trace S.inv) (Compute.LogUp.limbVal b e1.trace S.invIm) = _
    rw [h1, h2, hl1, hl2, Quad.mk_re_im, HonestTraceX.invV, ← hSs]
  rw [hinvQ, TeleCQX.evalQX_actB, ComplJ8CompPole.aVal_expand, ComplJ8CompPole.dVal_expand]
  have hpw := acts_pairwise (K := K) δ H pd W chalV pubVal j S hS
  have hrcd : ∀ x : EntX ℚ, (castEntX (F := ZMod p) x).rcd = x.rcd := fun _ => rfl
  have hact : ∀ x : EntX ℚ, (castEntX (F := ZMod p) x).act.eval e0 = ChipHX.evalQX x.act e0 :=
    fun x => TeleCQX.castEntX_act x e0
  simp only [castSlotX, List.map_map, Function.comp_def, hrcd, hact]
  have hsum : ∀ l : List (EntX ℚ), algebraMap (ZMod p) 𝕂′ (l.map fun x => ChipHX.evalQX x.act e0).sum =
      (l.map fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0)).sum := fun l => by
    rw [map_list_sum, List.map_map]; rfl
  rw [map_add, hsum, hsum]
  cases hp : S.pair with
  | none =>
    simp only [map_zero, add_zero]
    have := onehot_slot S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
      (fun x => DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.p)) 0 0 0 hpw
      (fun h => absurd rfl h)
    simpa using this
  | some q =>
    obtain ⟨fl, a, c, bb⟩ := q
    have hf : algebraMap (ZMod p) 𝕂′ (e0.trace fl) ≠ 0 → ∀ x ∈ S.ents,
        algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0) = 0 := by
      intro hne x hx
      have hfl : e0.trace fl ≠ 0 := fun h => hne (by rw [h, map_zero])
      have h0 := ComplJ8CompPole.hex_slots (castSlotX S) hS' e0 H pd r (HonestTraceX.flX j) (HonestTraceX.llX W j) rfl
        fl a c bb hp hfl (castEntX x) (List.mem_map_of_mem hx)
      rw [← hact, h0, map_zero]
    by_cases hb : bb = Bal.p
    · simp only [hb, if_true]
      -- the flag column is boolean (`prX` / `pr2X` honest values)
      have hfb : e0.trace fl = 0 ∨ e0.trace fl = 1 := by
        simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
        rcases hS with rfl | rfl | rfl | rfl <;>
          simp [ChipHX.slot0X, ChipHX.slot1X, ChipHX.slot2X, ChipHX.slot3X] at hp
        · obtain ⟨rfl, -⟩ := hp
          show HonestCompX.colX H pd r (HonestTraceX.flX j) (HonestTraceX.llX W j) ChipHX.prX = 0 ∨
            HonestCompX.colX H pd r (HonestTraceX.flX j) (HonestTraceX.llX W j) ChipHX.prX = 1
          rw [show ChipHX.prX = 24 from rfl, HonestCompX.cx24]
          unfold HonestCompX.cPr
          split
          · split_ifs
            · right; rfl
            · left; rfl
          · right; rfl
          · left; rfl
        · obtain ⟨-, -, -, rfl⟩ := hp; simp at hb
      have hfb' : algebraMap (ZMod p) 𝕂′ (e0.trace fl) = 0 ∨ algebraMap (ZMod p) 𝕂′ (e0.trace fl) = 1 := by
        rcases hfb with h | h <;> simp [h]
      have hpf : TeleCQX.pairFX e0 S = e0.trace fl := by simp [TeleCQX.pairFX, hp]
      rw [hpf]
      refine onehot_slot_pair S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
        (fun x => DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.p))
        (algebraMap (ZMod p) 𝕂′ (e0.trace fl)) _ _ hpw hf hfb' fun h1 => ?_
      have h1' : e0.trace fl = 1 := by
        rcases hfb with h | h
        · rw [h, map_zero] at h1; exact absurd h1 zero_ne_one
        · exact h
      exact hpair S hS fl a c bb hp h1'
    · simp only [hb, if_false, map_zero, add_zero]
      exact onehot_slot S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
        (fun x => DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.p))
        (algebraMap (ZMod p) 𝕂′ (e0.trace fl)) _ _ hpw hf

end PRow

section PGood
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX))

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (SlotX EntX Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castSlotX castEntX DX invQX)

/-- **The pair denominators are nonzero outside the compute pole events** (`compPoles`, the pair `quadPole`s). -/
theorem hpair_good (n : ℕ) (pub : ℕ → ZMod p) (χ : Coins frameJ8 K)
    (hg : ∀ s ∈ ComplJ8CompPole.compPoles (K := K) δ H pd W n, χ ∉ s.ev) (j : ℕ) (hj : j < n) :
    ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), ∀ fl a c bb, S.pair = some (fl, a, c, bb) →
      (HonestTraceX.env0 H pd W (VerJ8.chalVJ8 b χ) pub j).trace fl = 1 →
      DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W (VerJ8.chalVJ8 b χ) pub j))
          (HonestTraceX.env0 H pd W (VerJ8.chalVJ8 b χ) pub j) a ≠ 0 ∧
        DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W (VerJ8.chalVJ8 b χ) pub j))
          (HonestTraceX.env0 H pd W (VerJ8.chalVJ8 b χ) pub j) c ≠ 0 := by
  intro S hS fl a c bb hp _
  have hS' : castSlotX (F := ZMod p) S ∈ ChipHX.slotsX (F := ZMod p) := by
    rw [← TeleCQX.slotsX_cast]; exact List.mem_map_of_mem hS
  have hpS : (castSlotX (F := ZMod p) S).pair = some (fl, a, c, bb) := hp
  obtain ⟨la, lc⟩ := (ComplJ8CompPole.hlen_slots _ hS').2 fl a c bb hpS
  have hmem : ∀ s ∈ ComplJ8CompPole.slotPoles δ (castSlotX (F := ZMod p) S) (ComplJ8CompPole.envT H pd W j),
      χ ∉ s.ev := fun s hs => hg s (by
        simp only [ComplJ8CompPole.compPoles, List.mem_flatMap]
        exact ⟨j, List.mem_range.mpr hj, _, hS', hs⟩)
  have hρ := ComplJ8Bad.ρH_re δ χ
  rw [ComplJ8CompPole.den_split δ b _ χ rfl a la, ComplJ8CompPole.den_split δ b _ χ rfl c lc]
  refine ⟨?_, ?_⟩
  · exact ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 (ComplJ8CompPole.pf δ (ComplJ8CompPole.envT H pd W j) a) χ _ hρ
      (hmem _ (by simp [ComplJ8CompPole.slotPoles, hpS]))
  · exact ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 (ComplJ8CompPole.pf δ (ComplJ8CompPole.envT H pd W j) c) χ _ hρ
      (hmem _ (by simp [ComplJ8CompPole.slotPoles, hpS]))

end PGood

/-! ## 17. `balG` clause 2 at the run: the compute path public is the J-8 walk's handle provide

Both sides are totals of the read-indexed path weight `Wp` (`1 / (ρH + recDenP(idx, axis, H(slot axis
cells[idx])))`, its third argument ignored, since the walk records carry `hdl` and the compute `hdlP`): the walk
side through `WalkRecH.walk_provide_total`, the compute side row by row (`pSum_expand`, `pRow_row`, `pSum_run`). -/


section WalkP
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The child handle a path weight reads: the handle of the slot `axis` of the cell with serial `idx`. -/
def hcP (D : J8Data p Rg fuel s f r) (k : ZMod p × ZMod p × (ZMod p × ZMod p)) : ZMod p × ZMod p :=
  ((((D.H ((Noun.slot k.2.1.val (D.cells.getD k.1.val (.atom 0))).getD (.atom 0))).1 : ℕ) : ZMod p),
   (((D.H ((Noun.slot k.2.1.val (D.cells.getD k.1.val (.atom 0))).getD (.atom 0))).2 : ℕ) : ZMod p))

/-- **The read-indexed path weight** `1 / (ρH + recDenP(idx, axis, H(slot axis cells[idx])))`; its third
argument is ignored (the walk records carry `hdl`, the compute `hdlP`). -/
def Wp (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (k : ZMod p × ZMod p × (ZMod p × ZMod p)) : 𝕂′ :=
  (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (k.1, k.2.1, hcP D k))⁻¹

theorem Wp_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (root ch : Noun) (i a : ℕ)
    (hroot : root ∈ D.cells) (hi : D.cells.idxOf root = i) (hlen : D.cells.length < p) (ha : a < p)
    (hsl : Noun.slot a root = some ch) :
    Wp δ D χ (((i : ℕ) : ZMod p), ((a : ℕ) : ZMod p), (0, 0)) =
      (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (((i : ℕ) : ZMod p), ((a : ℕ) : ZMod p),
        ((((D.H ch).1 : ℕ) : ZMod p), (((D.H ch).2 : ℕ) : ZMod p))))⁻¹ := by
  have hil : i < D.cells.length := hi ▸ List.idxOf_lt_length_of_mem hroot
  have hv1 : ((i : ℕ) : ZMod p).val = i := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hil.trans hlen)]
  have hv2 : ((a : ℕ) : ZMod p).val = a := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
  have hg : D.cells.getD i (.atom 0) = root := by
    rw [List.getD_eq_getElem _ _ hil]; subst hi; exact List.getElem_idxOf _
  simp only [Wp, hcP, hv1, hv2, hg, hsl, Option.getD_some]

/-- `Wp` ignores its third argument. -/
theorem Wp_third (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (x y : ZMod p) (c c' : ZMod p × ZMod p) :
    Wp δ D χ (x, y, c) = Wp δ D χ (x, y, c') := rfl


section WalkRun
variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- A walk row's chain from its root, and its root is a cell of the table. -/
theorem walk_row_chain (cells : List Noun) (rs : List (Noun × ℕ))
    (hn : ∀ u ∈ walkRows cells rs, u.label.node ∈ cells) :
    ∀ u ∈ walkRows cells rs, chainWalk u.label.root u.label.bits = some u.label.node ∧ u.label.root ∈ cells := by
  intro u hu
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
  have hcw : c ∈ walkRows cells rs := (mem_bfsForest _ _).mpr ⟨c, hc, InTree.here c⟩
  obtain ⟨R, T, rfl⟩ : ∃ R T, c = trie R R [] T := by
    rcases mem_walkForest hc with ⟨-, rfl⟩ | ⟨r, -, rfl⟩
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  have hR : R ∈ cells := by have := hn _ hcw; rwa [(trie_label _ _ _ _).1] at this
  let Q : Noun → List Bool → List (List Bool) → Prop := fun n bs _ => chainWalk R bs = some n
  have hQ : ∀ l r bs T (b : Bool), Q (.cell l r) bs T → cont b T = true →
      Q (if b then r else l) (bs ++ [b]) (contT b T) := by
    intro l r bs T b hq _
    show chainWalk R (bs ++ [b]) = _
    rw [chainWalk_append, show chainWalk R bs = some (.cell l r) from hq]
  obtain ⟨n', bs', T', rfl, hq'⟩ := inTree_trie_inv _ Q hQ hin _ _ _ rfl (show chainWalk R [] = some R from rfl)
  rw [(trie_label _ _ _ _).1, (trie_label _ _ _ _).2.1, (trie_label _ _ _ _).2.2]
  exact ⟨hq', hR⟩

set_option maxHeartbeats 1000000 in
/-- **The J-8 walk handle provide is the walk rows' provided total at the path weight `Wp`.** -/
theorem whP_eq {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinjW : Function.Injective (powN o (walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).length))
    (χ : Coins frameJ8 K) (hlen : (j8DataOf p Rg Rt hgen).cells.length < p)
    (hpre : ∀ u ∈ walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads,
      2 * axisFold u.label.bits + 1 < p) :
    whP δ b (j8DataOf p Rg Rt hgen) o χ =
      ((walkRows (j8DataOf p Rg Rt hgen).cells (j8DataOf p Rg Rt hgen).reads).map fun u =>
        provH (Wp δ (j8DataOf p Rg Rt hgen) χ) (j8DataOf p Rg Rt hgen).cells u.label).sum := by
  set D := j8DataOf p Rg Rt hgen with hD
  have hwcell := ComplJ8OfBal.walkRows_node_cells (p := p) Rt hgen
  unfold whP
  rw [← ComplJ8OfBal.sum_range_getD' (trie (.atom 0) (.atom 0) [] [])
    (fun u => provH (Wp δ D χ) D.cells u.label)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [show (walkRows D.cells D.reads).getD k (trie (.atom 0) (.atom 0) [] []) = wTrie D.cells D.reads k from rfl]
  obtain ⟨-, eL, eR⟩ := walk_dRow_split δ b D o hinjW χ (pubsW0 δ D χ) ⟨k, hk'⟩
  simp only [wdN, WalkTraceHQ.dN, WalkTraceH.cN, dif_pos hk', eL, eR]
  have hu : wTrie D.cells D.reads k ∈ walkRows D.cells D.reads := wTrie_mem _ _ hk'
  obtain ⟨hch, hroot⟩ := walk_row_chain D.cells D.reads hwcell _ hu
  obtain ⟨l, rr, hlr, -, -⟩ := cells_kids Rt hgen _ (hwcell _ hu)
  have hp2 := hpre _ hu
  set w := (wTrie D.cells D.reads k).label with hw
  have hgw : (D.reads.length = D.reads.length) := rfl
  have hmL : wCol δ b D χ WChip.mL ⟨k, hk'⟩ = ((w.mL : ℕ) : ZMod p) := rfl
  have hmR : wCol δ b D χ WChip.mR ⟨k, hk'⟩ = ((w.mR : ℕ) : ZMod p) := rfl
  rw [hmL, hmR]
  have hsL : Noun.slot (2 * axisFold w.bits) w.root = some l := by
    rw [show 2 * axisFold w.bits = axisFold (w.bits ++ [false]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have hsR : Noun.slot (2 * axisFold w.bits + 1) w.root = some rr := by
    rw [show 2 * axisFold w.bits + 1 = axisFold (w.bits ++ [true]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have eWL : Wp δ D χ (recLH D.cells w) = (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ)
      (((D.cells.idxOf w.root : ℕ) : ZMod p), ((2 * axisFold w.bits : ℕ) : ZMod p),
        ((((D.H l).1 : ℕ) : ZMod p), (((D.H l).2 : ℕ) : ZMod p))))⁻¹ := by
    rw [recLH, Wp_third δ D χ _ _ _ (0, 0)]
    exact Wp_eq δ D χ w.root l _ _ hroot rfl hlen (by omega) hsL
  have eWR : Wp δ D χ (recRH D.cells w) = (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ)
      (((D.cells.idxOf w.root : ℕ) : ZMod p), ((2 * axisFold w.bits + 1 : ℕ) : ZMod p),
        ((((D.H rr).1 : ℕ) : ZMod p), (((D.H rr).2 : ℕ) : ZMod p))))⁻¹ := by
    rw [recRH, Wp_third δ D χ _ _ _ (0, 0)]
    exact Wp_eq δ D χ w.root rr _ _ hroot rfl hlen hp2 hsR
  rw [provH, nsmul_eq_mul, nsmul_eq_mul, eWL, eWR]
  have hkl : kLW D ⟨k, hk'⟩ = (((D.H l).1 : ℕ) : ZMod p) ∧ vLW D ⟨k, hk'⟩ = (((D.H l).2 : ℕ) : ZMod p) ∧
      kRW D ⟨k, hk'⟩ = (((D.H rr).1 : ℕ) : ZMod p) ∧ vRW D ⟨k, hk'⟩ = (((D.H rr).2 : ℕ) : ZMod p) := by
    simp only [kLW, vLW, kRW, vRW, wNode, ← hw, hlr]
    exact ⟨rfl, rfl, rfl, rfl⟩
  rw [hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2]
  have hri : (wValsC δ D χ ⟨k, hk'⟩).ridx = ((D.cells.idxOf w.root : ℕ) : ZMod p) := rfl
  have hpr : (wValsC δ D χ ⟨k, hk'⟩).pre = ((axisFold w.bits : ℕ) : ZMod p) := rfl
  rw [hri, hpr]
  push_cast
  simp [liftQ, map_natCast]

end WalkRun

section PExp
variable (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX))
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (SlotX EntX Bal walkRecX)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castSlotX castEntX DX invQX)

/-- **A compute walk-record denominator** `ρH + recDenP(root, axis, child)` at the row's columns. -/
theorem DX_walk (e : Nock.Reified.Env (ZMod p)) (χ : Coins frameJ8 K) (hch : e.chal = VerJ8.chalVJ8 b χ)
    (root : ChipH.Hd) (ax : ℕ) (ch : ChipH.Hd) :
    DX δ (Compute.TowerD.gatherEnv b e) e (walkRecX root ax ch) =
      ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (e.trace root.v, e.trace ax, (e.trace ch.k, e.trace ch.v)) := by
  rw [ComplJ8CompPole.den_split δ b e χ hch _ (by simp [walkRecX, ChipHX.recOf, ChipH.walkRec])]
  congr 1
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_eight, BalanceQ.liftRec, DenXJ8.keyX, DenXJ8.keyXN, recDenP]
  simp [ChipHX.RE.ev, walkRecX, ChipHX.recOf, ChipH.walkRec, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

/-- The `.p` reciprocal sum of a row in terms of its columns. -/
def pRow (tr : ℕ → ZMod p) (χ : Coins frameJ8 K) : 𝕂′ :=
  algebraMap (ZMod p) 𝕂′ (tr 0 * (1 - tr 19)) *
      (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (tr 26, tr 38, (tr 29, tr 30)))⁻¹ +
    algebraMap (ZMod p) 𝕂′ (tr 9 * (1 - tr 19)) *
      (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (tr 32, tr 40, (tr 47, tr 48)))⁻¹ +
    algebraMap (ZMod p) 𝕂′ (tr 24) *
      ((ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (tr 32, tr 48, (tr 43, tr 44)))⁻¹ +
        (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (tr 34, tr 48, (tr 45, tr 46)))⁻¹) +
    algebraMap (ZMod p) 𝕂′ (tr 11 * (1 - tr 19)) *
      (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (tr 30, tr 20, (tr 31, tr 32)))⁻¹

theorem pSum_expand (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) (j : ℕ) :
    pSum δ b H pd W (VerJ8.chalVJ8 b χ) pubVal j =
      pRow δ (HonestTraceX.env0 H pd W (VerJ8.chalVJ8 b χ) pubVal j).trace χ := by
  unfold pSum pRow
  set e := HonestTraceX.env0 H pd W (VerJ8.chalVJ8 b χ) pubVal j with he
  have hch : e.chal = VerJ8.chalVJ8 b χ := rfl
  simp only [ChipHX.slotsX, ChipHX.slot0X, ChipHX.slot1X, ChipHX.slot2X, ChipHX.slot3X, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.filter_cons, List.filter_nil]
  simp [DX_walk δ b e χ hch, EntX.act, ChipHX.evalQX, ChipH.selS, ChipH.notC, ChipH.cc, CoeffExpr.sumList, ChipHX.xS, ChipHX.xE,
    ChipHX.xSf1, ChipHX.xSf2, ChipHX.xFt, ChipHX.xFth, ChipHX.xFtth, ChipHX.xFttt, ChipHX.xM, ChipHX.hdX,
    ChipHX.vX, ChipHX.z1X, ChipHX.prX, ChipHX.sS10, ChipHX.pr2X]
  ring


/-- A consumed walk entry's reciprocal at its handles: `1 / (ρH + recDenP((H root).2, axis, H child))`. -/
def Tc (χ : Coins frameJ8 K) (x : Noun × ℕ × Noun) : 𝕂′ :=
  (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) ((((H x.1).2 : ℕ) : ZMod p), ((x.2.1 : ℕ) : ZMod p),
    ((((H x.2.2).1 : ℕ) : ZMod p), (((H x.2.2).2 : ℕ) : ZMod p))))⁻¹

set_option maxHeartbeats 2000000 in
theorem pRow_row (χ : Coins frameJ8 K) (rr : RowNX) (fl ll : ZMod p) (hok : HonestCompX.RowOKX p rr)
    (hH : HonestCompX.HdlOK p H) :
    pRow δ (HonestCompX.colX H pd rr fl ll) χ = ((consEntriesX rr).map (Tc δ H χ)).sum := by
  have hva : ∀ a, a < p → HonestCompX.hv H (.atom a) = ((a : ℕ) : ZMod p) := fun a ha => by
    show (((H (.atom a)).2 : ℕ) : ZMod p) = _
    rw [hH.small a ha]
  have c0 := HonestCompX.colX_st H pd rr fl ll 0 (by decide)
  have c9 := HonestCompX.colX_st H pd rr fl ll 9 (by decide)
  have c11 := HonestCompX.colX_st H pd rr fl ll 11 (by decide)
  unfold pRow
  rw [c0, c9, c11]
  simp only [HonestCompX.cx19, HonestCompX.cx20, HonestCompX.cx24, HonestCompX.cxS_v, HonestCompX.cxE_k,
    HonestCompX.cxE_v, HonestCompX.cxSf1_k, HonestCompX.cxSf1_v, HonestCompX.cxSf2_v, HonestCompX.cxFt_v,
    HonestCompX.cxFth_v, HonestCompX.cxFtth_k, HonestCompX.cxFtth_v, HonestCompX.cxFttt_k, HonestCompX.cxFttt_v,
    HonestCompX.cxM_k, HonestCompX.cxM_v]
  unfold HonestCompX.RowOKX at hok
  cases hst : rr.st <;> simp only [hst] at hok <;>
    simp [hst, RowDecodeVSX.stIdx, HonestCompX.cZ1, HonestCompX.cPr, HonestCompX.cV, consEntriesX]
  case s0 =>
    obtain ⟨-, -, ax, hax, hft, -⟩ := hok
    rw [hft]
    by_cases h1 : ax = 1
    · subst h1; simp
    · have h1' : Noun.atom ax ≠ Noun.atom 1 := by simpa using h1
      simp [h1', Tc, hva ax hax, hH.small ax hax, atomVal, HonestCompX.hv, HonestCompX.hk]
  case s9 =>
    obtain ⟨-, -, -, -, ⟨ax, hax, hft, -⟩, -⟩ := hok
    rw [hft]
    by_cases h1 : ax = 1
    · subst h1; simp
    · have h1' : Noun.atom ax ≠ Noun.atom 1 := by simpa using h1
      simp [h1', Tc, hva ax hax, hH.small ax hax, atomVal, HonestCompX.hv, HonestCompX.hk]
  case s10 =>
    obtain ⟨-, -, -, -, ⟨ax, hax, hft, -⟩, -⟩ := hok
    rw [hft]
    by_cases h1 : ax = 1
    · subst h1; simp
    · have h1' : Noun.atom ax ≠ Noun.atom 1 := by simpa using h1
      simp [h1', Tc, hva ax hax, hH.small ax hax, atomVal, HonestCompX.hv, HonestCompX.hk]
  case s5 =>
    obtain ⟨-, -, -, -, -, -, -, -, hm, hP⟩ := hok
    have hiff : rr.m = Noun.atom 1 ↔ (fdN rr.sf1 rr.sf2).1 = [] := by
      rw [hm]
      constructor
      · intro h
        by_contra hne
        have := two_le_axisOfPath hne
        simp only [Noun.atom.injEq] at h
        omega
      · intro h; rw [h]; rfl
    simp only [hiff]
    split_ifs
    · simp [Tc, hm, hva _ hP, hH.small _ hP, atomVal, HonestCompX.hv, HonestCompX.hk]
    · simp
  case s10L =>
    obtain ⟨-, a, -, -, ha1, -, -, hm, -⟩ := hok
    have hx : a ^^^ 1 < p := by rw [Nock.Edit.xor_one_eq]; split <;> omega
    simp [Tc, hm, hva _ hx, hH.small _ hx, atomVal, HonestCompX.hv, HonestCompX.hk]


end PExp

section PRun
variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

theorem ax_lt_of_depth {a : ℕ} (ha : 1 ≤ a) (hd : VclL.depthOf a ≤ 61) : a < 2 ^ 62 := by
  have h1 := axisFold_lt (VclL.axisBits a)
  rw [VclL.axisFold_axisBits a ha] at h1
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by simp only [VclL.depthOf] at hd; omega))

theorem slot_atom_two {a v : ℕ} (ha : 2 ≤ a) : Noun.slot a (.atom v) = none := by
  rw [VclL.slot_eq_chainWalk a (by omega), VclL.axisBits_of_two_le ha, chainWalk_append]
  cases h : VclL.axisBits (a / 2) with
  | nil => rfl
  | cons c l => rfl

/-- The run's reads are its rows' walk entries (the `2 ≤ axis` filter is vacuous). -/
theorem reads_eq :
    (j8DataOf p Rg Rt hgen).reads =
      (bfsForest [t]).flatMap fun u => (consEntriesX (rowOfSkelX u.label)).map fun x => (x.1, x.2.1) := by
  have hrows : (j8DataOf p Rg Rt hgen).rows.toList = (bfsForest [t]).map fun u => rowOfSkelX u.label := by
    show (ComplJ8Data.rowsOfT t).toList = _
    simp [ComplJ8Data.rowsOfT]
  show Nock.V1J8.Gen.pathReads (j8DataOf p Rg Rt hgen).rows = _
  unfold Nock.V1J8.Gen.pathReads
  rw [hrows, List.flatMap_map]
  refine List.filter_eq_self.mpr fun x hx => ?_
  obtain ⟨u, hu, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hu
  rw [List.mem_singleton] at hc; subst hc
  simpa using (consEntriesX_sound u.label (inTree_rowSem hgen hin) e he).1

set_option maxHeartbeats 2000000 in
/-- **The `.p` reciprocal sum of run row `j` is the path weight total of the row's walk entries.** -/
theorem pSum_run (hsm : ∀ u, InTree t u → HonestRowX.SmallX p (rowOfSkelX u.label))
    (hlen : (j8DataOf p Rg Rt hgen).cells.length < p) (hp62 : 2 ^ 62 < p)
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) (j : ℕ) (hj : j < (bfsForest [t]).length) :
    pSum δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((consEntriesX (rowOfSkelX ((bfsForest [t])[j]'hj).label)).map fun x =>
        Wp δ (j8DataOf p Rg Rt hgen) χ (readRecH (j8DataOf p Rg Rt hgen).cells (x.1, x.2.1))).sum := by
  set D := j8DataOf p Rg Rt hgen with hD
  set W := bfsForest [t] with hW
  have hin : InTree t (W[j]'hj) :=
    Nock.NockVMROM.Thm54.TraceGen.inTree_of_mem_bfsForest_singleton (List.getElem_mem hj)
  have hrow : HonestWalkX.rowAtWX W (j + 1) = rowOfSkelX (W[j]'hj).label := by
    simp [HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  have hok : HonestCompX.RowOKX p (rowOfSkelX (W[j]'hj).label) := HonestRowX.rowOKX_of_genX hgen hin (hsm _ hin)
  have hrowm : rowOfSkelX (W[j]'hj).label ∈ D.rows.toList := by
    simp only [hD, j8DataOf, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  have hH := ComplJ8Data.hdlOK_hdlP p D.cells D.acs
  rw [pSum_expand]
  have htr : (HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      HonestCompX.colX D.H D.pd (rowOfSkelX (W[j]'hj).label) (HonestTraceX.flX j) (HonestTraceX.llX W j) := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c = _
    unfold HonestTraceX.baseT; rw [hrow]
  rw [htr, pRow_row δ D.H D.pd χ _ _ _ hok hH]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨h2, hsl⟩ := consEntriesX_sound _ (inTree_rowSem hgen hin) x hx
  have hroot := consEntriesX_root _ x hx
  have hcell : x.1 ∈ D.cells ∧ ∃ a c, x.1 = .cell a c := by
    rcases ComplJ8Data.handle_noun_cases p Rg Rt hgen hrowm hroot with ⟨⟨a, c, hac⟩, hm⟩ | ⟨v, ev, _⟩ | ⟨v, ev, _⟩
    · exact ⟨hm, a, c, hac⟩
    · rw [ev, slot_atom_two h2] at hsl; cases hsl
    · rw [ev, slot_atom_two h2] at hsl; cases hsl
  obtain ⟨hmem, a, c, hac⟩ := hcell
  have hread : (x.1, x.2.1) ∈ D.reads := by
    rw [reads_eq Rt hgen]
    exact List.mem_flatMap.mpr ⟨_, List.getElem_mem hj, List.mem_map_of_mem hx⟩
  have hpr : (x.1, x.2.1) ∈ VclL.pathReads D.reads := by
    unfold VclL.pathReads
    exact List.mem_dedup.mpr (List.mem_filter.mpr ⟨hread, ComplJ8OfBal.isPathAx_of_two_le h2⟩)
  have hax : x.2.1 < p := (ax_lt_of_depth (by omega) (hwalk _ hpr)).trans hp62
  have hidx : ((D.H x.1).2 : ℕ) = D.cells.idxOf x.1 := by
    show (ComplJ8Data.hdlP p D.cells D.acs x.1).2 = _
    rw [hac]
    simp only [ComplJ8Data.hdlP]
    rw [← hac, ComplJ8OfBal.genIdxOf_eq _ _ hmem]
  unfold Tc readRecH
  rw [Wp_third δ D χ _ _ _ (0, 0), Wp_eq δ D χ x.1 x.2.2 _ _ hmem rfl hlen hax hsl, hidx]


theorem sum_flatMap_map {α β γ : Type} [AddCommMonoid γ] (f : α → List β) (g : β → γ) : ∀ l : List α,
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap_map f g l]; simp

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK) in
set_option maxHeartbeats 2000000 in
/-- **`balG` clause 2 at the run, at every good coin**: the compute path public `ρ 4` is the J-8 walk's handle
provide `whP`, from the run binders `hax hop5`, the row binder `h31` and the walk-depth binder `hwalk`. -/
theorem balG2_run (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads) (χ : Coins frameJ8 K)
    (hχ : (BRun δ b Rt hgen hpG h31).Good χ) :
    ((BRun δ b Rt hgen hpG h31).M χ).ρ 4 =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsW WalkHQ.pubPQ)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsW (WalkHQ.pubPQ + 1)) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hp62 : 2 ^ 62 < p := lt_trans (by norm_num) hp63
  have hlen : (j8DataOf p Rg Rt hgen).cells.length < p := size_lt_p Rt hgen hp63 h31 (by simp [sizesJ8])
  have hg0 : ∀ e ∈ ComplJ8Bad.badOf (ComplJ8Bad.badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf p Rg Rt hgen).t]).length)]
      (famsOf δ b (j8DataOf p Rg Rt hgen) (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen))), χ ∉ e.1 := hχ
  set D := j8DataOf p Rg Rt hgen with hD
  set o := orbJ8 _ (dvdOK_of_rows hpG D h31)
  have hsm := ComplJ8.smallX_of_binders hax hop5
  have hmW : (walkRows D.cells D.reads).length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjW := (powN_ok o (le_two_pow_ht D hmW)).1
  have hg : ∀ e ∈ ComplJ8CompPole.compPoles (K := K) δ D.H D.pd (bfsForest [t]) (bfsForest [t]).length,
      χ ∉ e.ev := fun e he =>
    ComplJ8Bad.good_spec hg0 (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_cons_self, he⟩))
  -- the walk side
  have eW : Quad.mk (algebraMap (ZMod p) K δ) (((BRun δ b Rt hgen hpG h31).M χ).pubsW WalkHQ.pubPQ)
      (((BRun δ b Rt hgen hpG h31).M χ).pubsW (WalkHQ.pubPQ + 1)) = whP δ b D o χ := by
    show Quad.mk _ (pubsWOf δ b D o χ WalkHQ.pubPQ) (pubsWOf δ b D o χ (WalkHQ.pubPQ + 1)) = _
    have h6 : pubsWOf δ b D o χ WalkHQ.pubPQ = pub2 δ (whP δ b D o χ) 6 := by simp [pubsWOf, WalkHQ.pubPQ]
    have h7 : pubsWOf δ b D o χ (WalkHQ.pubPQ + 1) = pub2 δ (whP δ b D o χ) 7 := by simp [pubsWOf, WalkHQ.pubPQ]
    rw [h6, h7, pub2_mk2 δ _ 6 rfl]
  rw [eW]
  have hpre : ∀ u ∈ walkRows D.cells D.reads, 2 * axisFold u.label.bits + 1 < p := by
    intro u hu
    have h60 := ComplJ8Walk.walkRows_len_le60 hwalk hu
    have h1 := axisFold_lt u.label.bits
    have h2 : 2 ^ (u.label.bits.length + 1) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 62 = 2 * 2 ^ 61 := by norm_num
    omega
  have hall : ∀ x ∈ D.reads, VclL.isPathAx x.2 = true := by
    intro x hx
    have : D.reads = Nock.V1J8.Gen.pathReads D.rows := rfl
    rw [this] at hx
    unfold Nock.V1J8.Gen.pathReads at hx
    exact ComplJ8OfBal.isPathAx_of_two_le (by simpa using (List.mem_filter.mp hx).2)
  have hslot : ∀ x ∈ VclL.pathReads D.reads, (Noun.slot x.2 x.1).isSome := fun x hx =>
    ComplJ8OfBal.reads_slot Rt hgen x (List.mem_filter.mp (List.mem_dedup.mp hx)).1
  rw [whP_eq δ b Rt hgen o hinjW χ hlen hpre, walk_provide_total (Wp δ D χ) D.cells D.reads hslot (fun _ => rfl),
    ComplJ8OfBal.pathKind_of_all hall]
  -- the compute side
  show ComplJ8Comp.ρCOf δ b D.H D.pd (bfsForest [t]) (ComplJ8.cJ s f r) χ 4 = _
  rw [rhoC4_rows]
  set g : NTree SkelX → 𝕂′ := fun u => ((consEntriesX (rowOfSkelX u.label)).map fun x =>
    Wp δ D χ (readRecH D.cells (x.1, x.2.1))).sum with hgdef
  have hrow : ∀ j ∈ Finset.range (bfsForest [t]).length,
      TeleCQX.termQX δ b (envC δ b D.H D.pd (bfsForest [t]) (ComplJ8.cJ s f r) χ j) .p =
        g ((bfsForest [t]).getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [termQX_p δ b _ _ _ _ _ j (hpair_good δ b _ _ _ _ _ χ hg j hj'), pSum_run δ b Rt hgen hsm hlen hp62 hwalk χ _ j hj',
      List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t g, reads_eq Rt hgen, sum_flatMap_map]
  simp only [hgdef, List.map_map, Function.comp_def]

end PRun
end WalkP

/-! ## 18. `balG` clause 3: the compute service public split into its three sub-balances; `balG_closed`

The `.s` row term (`termQX_s`, as `termQX_p` with the slot-3 pair flag `pr2X = cPr2`) is the row's inc consume,
jet consume and atom-walk pair consume (`sSum_expand`: `incT`, `jetT`, `awT`).  `balG3_of` closes clause 3 from
the three sub-balances (carried: `hI` inc against atom MI, `hA` pair against the atom walk's `vhP`, `hJ` jets +
pins + J terminal `= 0`); `balG_closed` is `OpenJ8.balG` at the run (`openJ8_with_balG` checks the type). -/

section SRow
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (chalV pubVal : ℕ → ZMod p)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (SlotX EntX Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (castSlotX castEntX DX invQX)

/-- The `.s` reciprocal sum of a compute row (entries, plus the `.s` pair `(flag · (1/Da + 1/Db))`). -/
def sSum (j : ℕ) : 𝕂′ :=
  ((ChipHX.slotsX (F := ℚ)).map fun S => ((S.ents.filter fun x => decide (x.bal = Bal.s)).map fun x =>
    algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act (HonestTraceX.env0 H pd W chalV pubVal j)) *
      (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
        (HonestTraceX.env0 H pd W chalV pubVal j) x.rcd)⁻¹).sum +
    (match S.pair with
     | some (fl, a, c, bb) => if bb = Bal.s then
         algebraMap (ZMod p) 𝕂′ ((HonestTraceX.env0 H pd W chalV pubVal j).trace fl) *
          ((DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
              (HonestTraceX.env0 H pd W chalV pubVal j) a)⁻¹ +
           (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
              (HonestTraceX.env0 H pd W chalV pubVal j) c)⁻¹)
         else 0
     | none => 0)).sum

/-- **The compute row's `.s` balance term**, when the `.s` pair's two denominators are nonzero on its active
rows (the pair poles of `compPoles`, at a good coin). -/
theorem termQX_s (j : ℕ)
    (hpair : ∀ S ∈ (ChipHX.slotsX : List (SlotX ℚ)), ∀ fl a c bb, S.pair = some (fl, a, c, bb) →
      (HonestTraceX.env0 H pd W chalV pubVal j).trace fl = 1 →
      DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
          (HonestTraceX.env0 H pd W chalV pubVal j) a ≠ 0 ∧
        DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
          (HonestTraceX.env0 H pd W chalV pubVal j) c ≠ 0) :
    TeleCQX.termQX δ b (HonestTraceX.env1 b δ H pd W chalV pubVal j) .s = sSum δ b H pd W chalV pubVal j := by
  set e0 := HonestTraceX.env0 H pd W chalV pubVal j with he0
  set e1 := HonestTraceX.env1 b δ H pd W chalV pubVal j with he1
  set r := HonestWalkX.rowAtWX W (j + 1)
  unfold TeleCQX.termQX sSum
  congr 1
  refine List.map_congr_left fun S hS => ?_
  have hS' : castSlotX (F := ZMod p) S ∈ ChipHX.slotsX (F := ZMod p) := by
    rw [← TeleCQX.slotsX_cast]; exact List.mem_map_of_mem hS
  have htr : ∀ c < 69, e1.trace c = e0.trace c := fun c hc => by
    simp only [he1, he0, HonestTraceX.env1, HonestTraceX.env0, HonestTraceX.preT, if_pos hc]
  have hcong : ∀ g : CoeffExpr ℚ, HonestTraceX.okC HonestTraceX.okFs g = true →
      ChipHX.evalQX g e1 = ChipHX.evalQX g e0 := by
    intro g hg
    rw [← HonestTraceX.eval_mapC_castX, ← HonestTraceX.eval_mapC_castX]
    refine HonestTraceX.eval_okC HonestTraceX.okFs _ (by rw [HonestTraceX.okC_mapC]; exact hg) e1 e0
      fun k i hk => ?_
    cases k <;> simp [HonestTraceX.okFs] at hk
    exact htr i hk
  have hokS := List.all_eq_true.mp HonestTraceX.slotsAct_ok S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hokS
  rw [hcong _ hokS.1.1.2]
  obtain ⟨s, hs4, hSs, hinv, hinvIm⟩ := HonestTraceX.slot_index hS'
  have hl1 : Compute.LogUp.limbVal b e1.trace (69 + 6 * s) =
      Quad.re _ (HonestTraceX.invV b δ H pd W chalV pubVal j (HonestTraceX.slotAt s)) := by
    rw [← HonestTraceX.limb_inv b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX.trX_pre b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (by have := k.isLt; omega)]
    rfl
  have hl2 : Compute.LogUp.limbVal b e1.trace (72 + 6 * s) =
      Quad.im _ (HonestTraceX.invV b δ H pd W chalV pubVal j (HonestTraceX.slotAt s)) := by
    rw [← HonestTraceX.limb_invIm b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j s hs4]
    unfold Compute.LogUp.limbVal
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [HonestTraceX.trX_pre b δ H pd W chalV pubVal (fun _ => (0 : K)) (fun _ => 0) (fun _ => 0) j _
      (by have := k.isLt; omega)]
    rfl
  have hinvQ : invQX δ (Compute.TowerD.gatherEnv b e1) S =
      HonestSlotX.aVal b δ (castSlotX S) e0 * (HonestSlotX.dVal b δ (castSlotX S) e0)⁻¹ := by
    have h1 : S.inv = 69 + 6 * s := hinv
    have h2 : S.invIm = 72 + 6 * s := hinvIm
    show Quad.mk _ (Compute.LogUp.limbVal b e1.trace S.inv) (Compute.LogUp.limbVal b e1.trace S.invIm) = _
    rw [h1, h2, hl1, hl2, Quad.mk_re_im, HonestTraceX.invV, ← hSs]
  rw [hinvQ, TeleCQX.evalQX_actB, ComplJ8CompPole.aVal_expand, ComplJ8CompPole.dVal_expand]
  have hpw := acts_pairwise (K := K) δ H pd W chalV pubVal j S hS
  have hrcd : ∀ x : EntX ℚ, (castEntX (F := ZMod p) x).rcd = x.rcd := fun _ => rfl
  have hact : ∀ x : EntX ℚ, (castEntX (F := ZMod p) x).act.eval e0 = ChipHX.evalQX x.act e0 :=
    fun x => TeleCQX.castEntX_act x e0
  simp only [castSlotX, List.map_map, Function.comp_def, hrcd, hact]
  have hsum : ∀ l : List (EntX ℚ), algebraMap (ZMod p) 𝕂′ (l.map fun x => ChipHX.evalQX x.act e0).sum =
      (l.map fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0)).sum := fun l => by
    rw [map_list_sum, List.map_map]; rfl
  rw [map_add, hsum, hsum]
  cases hp : S.pair with
  | none =>
    simp only [map_zero, add_zero]
    have := onehot_slot S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
      (fun x => DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.s)) 0 0 0 hpw
      (fun h => absurd rfl h)
    simpa using this
  | some q =>
    obtain ⟨fl, a, c, bb⟩ := q
    have hf : algebraMap (ZMod p) 𝕂′ (e0.trace fl) ≠ 0 → ∀ x ∈ S.ents,
        algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0) = 0 := by
      intro hne x hx
      have hfl : e0.trace fl ≠ 0 := fun h => hne (by rw [h, map_zero])
      have h0 := ComplJ8CompPole.hex_slots (castSlotX S) hS' e0 H pd r (HonestTraceX.flX j) (HonestTraceX.llX W j) rfl
        fl a c bb hp hfl (castEntX x) (List.mem_map_of_mem hx)
      rw [← hact, h0, map_zero]
    by_cases hb : bb = Bal.s
    · simp only [hb, if_true]
      -- the flag column is boolean (`prX` / `pr2X` honest values)
      have hfb : e0.trace fl = 0 ∨ e0.trace fl = 1 := by
        simp only [ChipHX.slotsX, List.mem_cons, List.not_mem_nil, or_false] at hS
        rcases hS with rfl | rfl | rfl | rfl <;>
          simp [ChipHX.slot0X, ChipHX.slot1X, ChipHX.slot2X, ChipHX.slot3X] at hp
        · obtain ⟨-, -, -, rfl⟩ := hp; simp at hb
        · obtain ⟨rfl, -⟩ := hp
          show HonestCompX.colX H pd r (HonestTraceX.flX j) (HonestTraceX.llX W j) ChipHX.pr2X = 0 ∨
            HonestCompX.colX H pd r (HonestTraceX.flX j) (HonestTraceX.llX W j) ChipHX.pr2X = 1
          rw [show ChipHX.pr2X = 64 from rfl, HonestCompX.cx64]
          unfold HonestCompX.cPr2
          split_ifs
          · right; rfl
          · left; rfl
      have hfb' : algebraMap (ZMod p) 𝕂′ (e0.trace fl) = 0 ∨ algebraMap (ZMod p) 𝕂′ (e0.trace fl) = 1 := by
        rcases hfb with h | h <;> simp [h]
      have hpf : TeleCQX.pairFX e0 S = e0.trace fl := by simp [TeleCQX.pairFX, hp]
      rw [hpf]
      refine onehot_slot_pair S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
        (fun x => DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.s))
        (algebraMap (ZMod p) 𝕂′ (e0.trace fl)) _ _ hpw hf hfb' fun h1 => ?_
      have h1' : e0.trace fl = 1 := by
        rcases hfb with h | h
        · rw [h, map_zero] at h1; exact absurd h1 zero_ne_one
        · exact h
      exact hpair S hS fl a c bb hp h1'
    · simp only [hb, if_false, map_zero, add_zero]
      exact onehot_slot S.ents (fun x => algebraMap (ZMod p) 𝕂′ (ChipHX.evalQX x.act e0))
        (fun x => DX δ (Compute.TowerD.gatherEnv b e0) e0 x.rcd) (fun x => decide (x.bal = Bal.s))
        (algebraMap (ZMod p) 𝕂′ (e0.trace fl)) _ _ hpw hf

end SRow

section SExp
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (W : List (NTree SkelX)) (chalV pubVal : ℕ → ZMod p)

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (SlotX EntX Bal)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQX (DX)

/-- Row `j`'s inc consume (`s4`, slow): `[s4]·(1 − fast) / D(incRec)`. -/
def incT (j : ℕ) : 𝕂′ :=
  algebraMap (ZMod p) 𝕂′ ((HonestTraceX.env0 H pd W chalV pubVal j).trace 4 *
      (1 - (HonestTraceX.env0 H pd W chalV pubVal j).trace 61)) *
    (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
      (HonestTraceX.env0 H pd W chalV pubVal j) ChipHX.incRecX)⁻¹

/-- Row `j`'s jet consume (`s11j`): `[s11j] / D(jetRec)`. -/
def jetT (j : ℕ) : 𝕂′ :=
  algebraMap (ZMod p) 𝕂′ ((HonestTraceX.env0 H pd W chalV pubVal j).trace 16) *
    (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
      (HonestTraceX.env0 H pd W chalV pubVal j) ChipHX.jetRecX)⁻¹

/-- Row `j`'s atom-walk pair consume (`pr2`): `pr2 · (1/D(walkRecA ftth l₁) + 1/D(walkRecA fttt l₂))`. -/
def awT (j : ℕ) : 𝕂′ :=
  algebraMap (ZMod p) 𝕂′ ((HonestTraceX.env0 H pd W chalV pubVal j).trace 64) *
    ((DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
        (HonestTraceX.env0 H pd W chalV pubVal j) (ChipHX.walkRecAX ChipHX.xFtth ChipHX.xL1))⁻¹ +
      (DX δ (Compute.TowerD.gatherEnv b (HonestTraceX.env0 H pd W chalV pubVal j))
        (HonestTraceX.env0 H pd W chalV pubVal j) (ChipHX.walkRecAX ChipHX.xFttt ChipHX.xL2))⁻¹)

theorem sSum_expand (j : ℕ) :
    sSum δ b H pd W chalV pubVal j = incT δ b H pd W chalV pubVal j + jetT δ b H pd W chalV pubVal j +
      awT δ b H pd W chalV pubVal j := by
  unfold sSum incT jetT awT
  simp [ChipHX.slotsX, ChipHX.slot0X, ChipHX.slot1X, ChipHX.slot2X, ChipHX.slot3X, EntX.act, ChipHX.evalQX,
    ChipH.selS, ChipH.notC, ChipH.cc, CoeffExpr.sumList, ChipHX.fastX, ChipHX.sS11j, ChipHX.pr2X]
  ring

end SExp

section Clause3
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The compute row environment's publics at the run (as `envC`). -/
abbrev pubC (χ : Coins frameJ8 K) : ℕ → ZMod p :=
  VerJ8.pubVJ8 δ b (ComplJ8.cJ s f r) (ComplJ8Comp.mCOf (j8DataOf p Rg Rt hgen).H (ComplJ8.cJ s f r)) 0 0 χ

set_option maxHeartbeats 2000000 in
/-- **`balG` clause 3 at the run, at every good coin, from its three sub-balances**: the compute service public
`ρS` splits row by row into the inc consumes (`incT`), the jet consumes (`jetT`) and the atom-walk pair consumes
(`awT`); the clause holds once the inc consumes total the atom MI terminal (`hI`), the pair consumes total the atom
walk's handle provide (`hA`), and the jet consumes, the registry pins and the J terminal sum to zero (`hJ`). -/
theorem balG3_of (hpG : p = Nock.Atoms.p) (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K)
    (hχ : (BRun δ b Rt hgen hpG h31).Good χ)
    (hI : ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMI)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMI + 1)))
    (hA : ∑ j ∈ Finset.range (bfsForest [t]).length, awT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubPQ)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubPQ + 1)))
    (hJ : ∑ j ∈ Finset.range (bfsForest [t]).length, jetT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j +
      ((pinCons (p := p) (K := K) (BRun δ b Rt hgen hpG h31).Pb.regs (BRun δ b Rt hgen hpG h31).Pb.idx).map fun x =>
        (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 1) = 0) :
    ((BRun δ b Rt hgen hpG h31).M χ).ρS +
        ((pinCons (p := p) (K := K) (BRun δ b Rt hgen hpG h31).Pb.regs (BRun δ b Rt hgen hpG h31).Pb.idx).map fun x =>
          (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
        Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 1) =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMI)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubPQ)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubPQ + 1)) := by
  have hg0 : ∀ e ∈ ComplJ8Bad.badOf (ComplJ8Bad.badList [(⟨13, by decide⟩, (bfsForest [(j8DataOf p Rg Rt hgen).t]).length)]
      (famsOf δ b (j8DataOf p Rg Rt hgen) (dvdOK_of_rows hpG _ h31) (cells_pos Rt hgen))), χ ∉ e.1 := hχ
  set D := j8DataOf p Rg Rt hgen with hD
  have hg : ∀ e ∈ ComplJ8CompPole.compPoles (K := K) δ D.H D.pd (bfsForest [t]) (bfsForest [t]).length,
      χ ∉ e.ev := fun e he =>
    ComplJ8Bad.good_spec hg0 (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_cons_self, he⟩))
  have hS : ((BRun δ b Rt hgen hpG h31).M χ).ρS =
      ∑ j ∈ Finset.range (bfsForest [t]).length, (incT δ b D.H D.pd (bfsForest [t]) (VerJ8.chalVJ8 b χ)
        (pubC δ b Rt hgen χ) j + jetT δ b D.H D.pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j +
        awT δ b D.H D.pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j) := by
    show ComplJ8Comp.ρSCOf δ b D.H D.pd (bfsForest [t]) (ComplJ8.cJ s f r) χ = _
    rw [rhoCS_rows]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [termQX_s δ b _ _ _ _ _ j (hpair_good δ b _ _ _ _ _ χ hg j (Finset.mem_range.mp hj)), sSum_expand]
  rw [hS, Finset.sum_add_distrib, Finset.sum_add_distrib]
  linear_combination hI + hA + hJ


open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds) in
set_option maxHeartbeats 2000000 in
/-- **`OpenJ8.balG` at the run**: clauses 1 and 2 from the binders `hax hop5 hRt h31 hwalk`; clause 3 from
its three sub-balances `hI hA hJ` (carried, exact statements as in `balG3_of`). -/
theorem balG_closed (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen))
    (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (hI : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMI)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMI + 1)))
    (hA : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, awT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubPQ)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubPQ + 1)))
    (hJ : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, jetT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j +
      ((pinCons (p := p) (K := K) (BRun δ b Rt hgen hpG h31).Pb.regs (BRun δ b Rt hgen hpG h31).Pb.idx).map fun x =>
        (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 1) = 0) :
    ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ((BRun δ b Rt hgen hpG h31).M χ).ρ 3 +
          (Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsW WalkHQ.pubXQ)
            (((BRun δ b Rt hgen hpG h31).M χ).pubsW (WalkHQ.pubXQ + 1)) +
          Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 2) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 3)) =
        Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsC CellHQ.pubHQ)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsC (CellHQ.pubHQ + 1)) ∧
      ((BRun δ b Rt hgen hpG h31).M χ).ρ 4 =
        Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsW WalkHQ.pubPQ)
          (((BRun δ b Rt hgen hpG h31).M χ).pubsW (WalkHQ.pubPQ + 1)) ∧
      ((BRun δ b Rt hgen hpG h31).M χ).ρS +
          ((pinCons (p := p) (K := K) (BRun δ b Rt hgen hpG h31).Pb.regs (BRun δ b Rt hgen hpG h31).Pb.idx).map
            fun x => (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
          Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 1) =
        Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMI)
            (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMI + 1)) +
          Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubPQ)
            (((BRun δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubPQ + 1)) := fun χ hχ =>
  ⟨balG1_run δ b Rt hgen hpG hax hop5 hRt h31 hwalk χ,
   balG2_run δ b Rt hgen hpG hax hop5 h31 hwalk χ hχ,
   balG3_of δ b Rt hgen hpG h31 χ hχ (hI χ hχ) (hA χ hχ) (hJ χ hχ)⟩

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds) in
/-- `balG_closed` has exactly the type of `OpenJ8.balG` at the run: it replaces that field of any `OpenJ8`. -/
theorem openJ8_with_balG (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (O : OpenJ8 δ b (BRun δ b Rt hgen hpG h31))
    (hI : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMI)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMI + 1)))
    (hA : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, awT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubPQ)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubPQ + 1)))
    (hJ : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, jetT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j +
      ((pinCons (p := p) (K := K) (BRun δ b Rt hgen hpG h31).Pb.regs (BRun δ b Rt hgen hpG h31).Pb.idx).map fun x =>
        (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 1) = 0) :
    OpenJ8 δ b (BRun δ b Rt hgen hpG h31) :=
  { O with balG := balG_closed δ b Rt hgen hpG hax hop5 hRt h31 hwalk hI hA hJ }

end Clause3

/-! ## 19. Clause 3's atom-walk sub-balance `hA` at the run

`hA_run` needs the
claim-leaf binder `hclA` (as `balF_closed`); `openJ8_with_balG'` carries `hI hJ` only. -/


section AW
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The atom-walk path weight: `Wp` over the atom cell list `acs`. -/
def WvA (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (k : ZMod p × ZMod p × (ZMod p × ZMod p)) : 𝕂′ :=
  (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (k.1, k.2.1,
    ((((D.H ((Noun.slot k.2.1.val (D.acs.getD k.1.val (.atom 0))).getD (.atom 0))).1 : ℕ) : ZMod p),
     (((D.H ((Noun.slot k.2.1.val (D.acs.getD k.1.val (.atom 0))).getD (.atom 0))).2 : ℕ) : ZMod p))))⁻¹

theorem WvA_eq (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (root ch : Noun) (i a : ℕ)
    (hroot : root ∈ D.acs) (hi : D.acs.idxOf root = i) (hlen : D.acs.length < p) (ha : a < p)
    (hsl : Noun.slot a root = some ch) (c : ZMod p × ZMod p) :
    WvA δ D χ (((i : ℕ) : ZMod p), ((a : ℕ) : ZMod p), c) =
      (ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (((i : ℕ) : ZMod p), ((a : ℕ) : ZMod p),
        ((((D.H ch).1 : ℕ) : ZMod p), (((D.H ch).2 : ℕ) : ZMod p))))⁻¹ := by
  have hil : i < D.acs.length := hi ▸ List.idxOf_lt_length_of_mem hroot
  have hv1 : ((i : ℕ) : ZMod p).val = i := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hil.trans hlen)]
  have hv2 : ((a : ℕ) : ZMod p).val = a := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
  have hg : D.acs.getD i (.atom 0) = root := by
    rw [List.getD_eq_getElem _ _ hil]; subst hi; exact List.getElem_idxOf _
  simp only [WvA, hv1, hv2, hg, hsl, Option.getD_some]

section AWRun
variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

set_option maxHeartbeats 1000000 in
/-- **The atom walk's handle provide is its rows' provided total at `WvA`** (a read present). -/
theorem vhP_eq {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h) (hne : (j8DataOf p Rg Rt hgen).preads ≠ [])
    (hinjV : Function.Injective (powN o (nVOf (j8DataOf p Rg Rt hgen))))
    (χ : Coins frameJ8 K) (hlen : (j8DataOf p Rg Rt hgen).acs.length < p)
    (hwn : ∀ u ∈ walkRows (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).preads,
      u.label.node ∈ (j8DataOf p Rg Rt hgen).acs)
    (hcl : ∀ c ∈ (j8DataOf p Rg Rt hgen).acs, c.isCell = true)
    (hpre : ∀ u ∈ walkRows (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).preads,
      2 * axisFold u.label.bits + 1 < p) :
    vhP δ b (j8DataOf p Rg Rt hgen) o χ =
      ((walkRows (j8DataOf p Rg Rt hgen).acs (j8DataOf p Rg Rt hgen).preads).map fun u =>
        provH (WvA δ (j8DataOf p Rg Rt hgen) χ) (j8DataOf p Rg Rt hgen).acs u.label).sum := by
  set D := j8DataOf p Rg Rt hgen with hD
  have hn : nVOf D = (walkRows D.acs D.preads).length := by simp [nVOf, hne]
  unfold vhP
  rw [show Finset.range (nVOf D) = Finset.range (walkRows D.acs D.preads).length by rw [hn],
    ← ComplJ8OfBal.sum_range_getD' (trie (.atom 0) (.atom 0) [] [])
    (fun u => provH (WvA δ D χ) D.acs u.label)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hkV : k < nVOf D := hn ▸ hk'
  rw [show (walkRows D.acs D.preads).getD k (trie (.atom 0) (.atom 0) [] []) = wTrie D.acs D.preads k from rfl]
  obtain ⟨-, eL, eR⟩ := ComplJ8OfAtom.aw_dRow_split δ b D o hinjV χ (pubsV0 δ D χ) ⟨k, hkV⟩
  simp only [vdN, WalkTraceHQ.dN, WalkTraceH.cN, dif_pos hkV]
  rw [show krVOf D = krW D.acs D.preads by simp [krVOf, hne], eL, eR]
  have hu : wTrie D.acs D.preads k ∈ walkRows D.acs D.preads := wTrie_mem _ _ hk'
  obtain ⟨hch, hroot⟩ := walk_row_chain D.acs D.preads hwn _ hu
  have hc := hcl _ (hwn _ hu)
  obtain ⟨l, rr, hlr⟩ : ∃ l rr, (wTrie D.acs D.preads k).label.node = .cell l rr := by
    cases h : (wTrie D.acs D.preads k).label.node with
    | atom v => rw [h] at hc; simp [Noun.isCell] at hc
    | cell l rr => exact ⟨l, rr, rfl⟩
  have hp2 := hpre _ hu
  set w := (wTrie D.acs D.preads k).label with hw
  have hmL : vCol δ b D χ WChip.mL ⟨k, hkV⟩ = ((w.mL : ℕ) : ZMod p) := rfl
  have hmR : vCol δ b D χ WChip.mR ⟨k, hkV⟩ = ((w.mR : ℕ) : ZMod p) := rfl
  rw [hmL, hmR]
  have hsL : Noun.slot (2 * axisFold w.bits) w.root = some l := by
    rw [show 2 * axisFold w.bits = axisFold (w.bits ++ [false]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have hsR : Noun.slot (2 * axisFold w.bits + 1) w.root = some rr := by
    rw [show 2 * axisFold w.bits + 1 = axisFold (w.bits ++ [true]) by rw [axisFold_append]; simp, chain_slot,
      chainWalk_append, hch, hlr]
    rfl
  have eWL := WvA_eq δ D χ w.root l _ (2 * axisFold w.bits) hroot rfl hlen (by omega) hsL
    (hdl D.acs (hdN w.node))
  have eWR := WvA_eq δ D χ w.root rr _ (2 * axisFold w.bits + 1) hroot rfl hlen hp2 hsR
    (hdl D.acs (tlN w.node))
  rw [provH, nsmul_eq_mul, nsmul_eq_mul, recLH, recRH, eWL, eWR]
  have hkl : kLV D ⟨k, hkV⟩ = (((D.H l).1 : ℕ) : ZMod p) ∧ vLV D ⟨k, hkV⟩ = (((D.H l).2 : ℕ) : ZMod p) ∧
      kRV D ⟨k, hkV⟩ = (((D.H rr).1 : ℕ) : ZMod p) ∧ vRV D ⟨k, hkV⟩ = (((D.H rr).2 : ℕ) : ZMod p) := by
    simp only [kLV, vLV, kRV, vRV, vNode, ← hw, hlr]
    exact ⟨rfl, rfl, rfl, rfl⟩
  rw [hkl.1, hkl.2.1, hkl.2.2.1, hkl.2.2.2]
  have hri : (ComplJ8OfAtom.vValsC δ D χ ⟨k, hkV⟩).ridx = ((D.acs.idxOf w.root : ℕ) : ZMod p) := rfl
  have hpr : (ComplJ8OfAtom.vValsC δ D χ ⟨k, hkV⟩).pre = ((axisFold w.bits : ℕ) : ZMod p) := rfl
  rw [hri, hpr]
  push_cast
  simp [liftQ, map_natCast]


open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX (walkRecAX) in
/-- An atom-walk record's compute denominator `ρH + recDenP(root, ax2, leaf)`. -/
theorem DX_walkA (e : Nock.Reified.Env (ZMod p)) (χ : Coins frameJ8 K) (hch : e.chal = VerJ8.chalVJ8 b χ)
    (root l : ChipH.Hd) :
    TeleCQX.DX δ (Compute.TowerD.gatherEnv b e) e (walkRecAX root l) =
      ComplJ8Bad.ρH δ χ + recDenP 0 (ComplJ8Bad.γH δ χ) (e.trace root.v, e.trace 63, (e.trace l.k, e.trace l.v)) := by
  rw [ComplJ8CompPole.den_split δ b e χ hch _ (by simp [walkRecAX])]
  congr 1
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_eight, BalanceQ.liftRec, DenXJ8.keyX, DenXJ8.keyXN, recDenP]
  simp [ChipHX.RE.ev, walkRecAX, ChipHX.ax2X, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

/-- **An honest op-5 pair row's two atom-walk reads**: both leaves are big atoms of the run with the two-limb
comb in `acs`, the first-difference axis is `2` or `3`, and the comb's slot there is the recorded small limb. -/
theorem pair_facts (hpG : p = Nock.Atoms.p)
    (hbig : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    {row : RowNX} (hrow : row ∈ (j8DataOf p Rg Rt hgen).rows.toList)
    (hpair : HonestCompX.isPair (j8DataOf p Rg Rt hgen).H row) :
    ∃ a c, row.ftth = .atom a ∧ row.fttt = .atom c ∧ a ∈ (j8DataOf p Rg Rt hgen).bigs ∧
      c ∈ (j8DataOf p Rg Rt hgen).bigs ∧
      ((j8DataOf p Rg Rt hgen).pd row).1 < p ∧ ((j8DataOf p Rg Rt hgen).pd row).2.1.1 = 0 ∧
      ((j8DataOf p Rg Rt hgen).pd row).2.2.1 = 0 ∧ ((j8DataOf p Rg Rt hgen).pd row).2.1.2 < p ∧
      ((j8DataOf p Rg Rt hgen).pd row).2.2.2 < p ∧
      Noun.slot ((j8DataOf p Rg Rt hgen).pd row).1 (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) =
        some (.atom ((j8DataOf p Rg Rt hgen).pd row).2.1.2) ∧
      Noun.slot ((j8DataOf p Rg Rt hgen).pd row).1 (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs c)) =
        some (.atom ((j8DataOf p Rg Rt hgen).pd row).2.2.2) := by
  set D := j8DataOf p Rg Rt hgen with hD
  obtain ⟨-, -, h1, h2⟩ := hpair
  have hkind : ∀ n : Noun, n ∈ rowHandleNounsX row → (D.H n).1 = 2 →
      ∃ a, n = .atom a ∧ a ∈ D.bigs := by
    intro n hn hk
    have hH : D.H = ComplJ8Data.hdlP p D.cells D.acs := rfl
    rw [hH] at hk
    cases n with
    | cell l r' => simp [ComplJ8Data.hdlP] at hk
    | atom a =>
      have hpa : p ≤ a := by
        by_contra hlt
        simp [ComplJ8Data.hdlP, show a < p by omega] at hk
      refine ⟨a, rfl, ?_⟩
      show a ∈ ComplJ8Data.bigsP p D.roots D.rows
      refine (ComplJ8Atom.mem_bigsP p _ _ a).mpr ⟨?_, hpa⟩
      refine List.mem_flatMap.mpr ⟨.atom a, List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, hrow, hn⟩), ?_⟩
      simp [leavesOf]
  obtain ⟨a, ha', ha⟩ := hkind row.ftth (by simp [rowHandleNounsX]) h1
  obtain ⟨c, hc', hc⟩ := hkind row.fttt (by simp [rowHandleNounsX]) h2
  have hB : Nock.Atoms.B - 1 < p := by rw [hpG]; simp [Nock.Atoms.B, Nock.Atoms.p, Nock.Field.p]
  have hp3 : 3 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hxa : a + 1 - p < p := by
    have := HonestPairX.limbs_lt a (a + 1 - p) (by rw [(hbig a ha).2]; simp)
    omega
  have hxc : c + 1 - p < p := by
    have := HonestPairX.limbs_lt c (c + 1 - p) (by rw [(hbig c hc).2]; simp)
    omega
  have e : D.pd row = HonestPairX.pdX (ComplJ8Data.sxPP p D.acs D.rows) row := rfl
  refine ⟨a, c, ha', hc', ha, hc, ?_⟩
  rw [e]
  unfold HonestPairX.pdX
  rw [ha', hc']
  simp only [(hbig a ha).2, (hbig c hc).2, HonestPairX.combFD, Nock.V1J8.Gen.combOf]
  split_ifs <;> simp [Noun.slot]
  all_goals refine ⟨by omega, ?_⟩ <;> omega


set_option maxHeartbeats 2000000 in
/-- **Run row `j`'s atom-walk pair consume** is the `WvA` total of the row's atom-walk reads (`pairReadsP`). -/
theorem awT_run (hpG : p = Nock.Atoms.p)
    (hbig : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hrt : ∀ a, ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a =
      Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)))
    (hix : ∀ n ∈ (j8DataOf p Rg Rt hgen).acs, Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).acs n =
      List.idxOf n (j8DataOf p Rg Rt hgen).acs)
    (hlen : (j8DataOf p Rg Rt hgen).acs.length < p) (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) (j : ℕ)
    (hj : j < (bfsForest [t]).length) :
    awT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((if Nock.V1J8.FillX.isPairB (j8DataOf p Rg Rt hgen).H (rowOfSkelX ((bfsForest [t])[j]'hj).label) then
          [(Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX ((bfsForest [t])[j]'hj).label).ftth)),
              ((j8DataOf p Rg Rt hgen).pd (rowOfSkelX ((bfsForest [t])[j]'hj).label)).1),
           (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX ((bfsForest [t])[j]'hj).label).fttt)),
              ((j8DataOf p Rg Rt hgen).pd (rowOfSkelX ((bfsForest [t])[j]'hj).label)).1)]
        else []).map fun x => WvA δ (j8DataOf p Rg Rt hgen) χ (readRecH (j8DataOf p Rg Rt hgen).acs x)).sum := by
  set D := j8DataOf p Rg Rt hgen with hD
  set W := bfsForest [t] with hW
  set rr := rowOfSkelX (W[j]'hj).label with hrr
  have hrow : HonestWalkX.rowAtWX W (j + 1) = rr := by
    simp [hrr, HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  have hrowm : rr ∈ D.rows.toList := by
    simp only [hrr, hD, j8DataOf, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  have hH : HonestCompX.HdlOK p D.H := ComplJ8Data.hdlOK_hdlP p D.cells D.acs
  have htr : (HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      HonestCompX.colX D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c = _
    unfold HonestTraceX.baseT; rw [hrow]
  unfold awT
  rw [DX_walkA δ b _ χ rfl, DX_walkA δ b _ χ rfl, htr]
  simp only [ChipHX.xFtth, ChipHX.xFttt, ChipHX.xL1, ChipHX.xL2, ChipHX.hdX, HonestCompX.cx64, HonestCompX.cx63,
    HonestCompX.cx65, HonestCompX.cx66, HonestCompX.cx67, HonestCompX.cx68]
  rw [show (26 + 2 * 9 : ℕ) = 44 from rfl, show (26 + 2 * 10 : ℕ) = 46 from rfl, HonestCompX.cxFtth_v,
    HonestCompX.cxFttt_v]
  by_cases hp : HonestCompX.isPair D.H rr
  · have hpB : Nock.V1J8.FillX.isPairB D.H rr = true := (Nock.V1J8.FillX.isPairB_iff D.H rr).mpr hp
    rw [if_pos hpB]
    obtain ⟨a, c, ha', hc', ha, hc, hax, hk1, hk2, hv1, hv2, hs1, hs2⟩ := pair_facts Rt hgen hpG hbig hrowm hp
    have hst : rr.st = .s5 := hp.1
    have hma := ComplJ8OfBal.comb_mem_acs Rt hgen hpG ha (by rw [(hbig a ha).2]; simp)
    have hmc := ComplJ8OfBal.comb_mem_acs Rt hgen hpG hc (by rw [(hbig c hc).2]; simp)
    have hra : ((D.H (.atom a)).2 : ℕ) = D.acs.idxOf (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)) := by
      show (ComplJ8Data.hdlP p D.cells D.acs (.atom a)).2 = _
      have : ¬ a < p := Nat.not_lt.mpr (hbig a ha).1
      simp only [ComplJ8Data.hdlP, this, if_false]
      rw [hrt, hix _ hma]
    have hrc : ((D.H (.atom c)).2 : ℕ) = D.acs.idxOf (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs c)) := by
      show (ComplJ8Data.hdlP p D.cells D.acs (.atom c)).2 = _
      have : ¬ c < p := Nat.not_lt.mpr (hbig c hc).1
      simp only [ComplJ8Data.hdlP, this, if_false]
      rw [hrt, hix _ hmc]
    have e1 := WvA_eq δ D χ _ _ _ _ hma rfl hlen hax hs1 (hdl D.acs ((Noun.slot (D.pd rr).1
      (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a))).getD (.atom 0)))
    have e2 := WvA_eq δ D χ _ _ _ _ hmc rfl hlen hax hs2 (hdl D.acs ((Noun.slot (D.pd rr).1
      (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs c))).getD (.atom 0)))
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, readRecH, ha', hc',
      Nock.V1J8.Gen.atomV]
    rw [e1, e2, hH.small _ hv1, hH.small _ hv2]
    simp only [HonestCompX.cPr2, HonestCompX.cAx2, HonestCompX.cL, hst, if_pos hp, HonestCompX.hv, hra, hrc,
      map_one, one_mul]
    simp only [show (D.pd rr).2.1.1 = 0 from hk1, show (D.pd rr).2.2.1 = 0 from hk2, Nat.cast_zero]
    rfl
  · have hpB : Nock.V1J8.FillX.isPairB D.H rr = false := by
      cases h : Nock.V1J8.FillX.isPairB D.H rr
      · rfl
      · exact absurd ((Nock.V1J8.FillX.isPairB_iff D.H rr).mp h) hp
    rw [if_neg (by simp [hpB])]
    simp [HonestCompX.cPr2, hp]


/-- The run's atom-walk reads are its rows' pair reads. -/
theorem preads_eq :
    (j8DataOf p Rg Rt hgen).preads = (bfsForest [t]).flatMap fun u =>
      if Nock.V1J8.FillX.isPairB (j8DataOf p Rg Rt hgen).H (rowOfSkelX u.label) then
        [(Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).ftth)),
            ((j8DataOf p Rg Rt hgen).pd (rowOfSkelX u.label)).1),
         (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).fttt)),
            ((j8DataOf p Rg Rt hgen).pd (rowOfSkelX u.label)).1)]
      else [] := by
  have hrows : (j8DataOf p Rg Rt hgen).rows.toList = (bfsForest [t]).map fun u => rowOfSkelX u.label := by
    show (ComplJ8Data.rowsOfT t).toList = _
    simp [ComplJ8Data.rowsOfT]
  show ComplJ8Data.pairReadsP (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd (j8DataOf p Rg Rt hgen).rows = _
  unfold ComplJ8Data.pairReadsP
  rw [hrows, List.flatMap_map]

open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds) in
set_option maxHeartbeats 2000000 in
/-- **`hA`: the compute's atom-walk pair consumes total the atom walk's handle provide**, at every coin, from
`complJ8`'s binders `hpG hop5 hclA hRt h31`. -/
theorem hA_run (hpG : p = Nock.Atoms.p) (hop5 : ComplJ8.ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (χ : Coins frameJ8 K) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, awT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsV WalkHQ.pubPQ)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsV (WalkHQ.pubPQ + 1)) := by
  have hp63 : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]
  have hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataOf p Rg Rt hgen).t]).length (by simp [sizesJ8])
    rw [ComplJ8BigBound.data_rows hgen]
    simpa [ComplJ8Data.rowsOfT, j8DataOf] using h
  obtain ⟨hb, -, -, -, -, -, -, hix, hrt⟩ := ComplJ8BigBound.bigBound_single hgen hpG (hclA 0) (hclA 1) hRt hop5 hN
  have hbig : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1] :=
    fun a ha => ⟨(hb a ha).1, (hb a ha).2.2⟩
  have hlenA : (j8DataOf p Rg Rt hgen).acs.length < p := size_lt_p Rt hgen hp63 h31 (by simp [sizesJ8])
  set D := j8DataOf p Rg Rt hgen with hD
  set o := orbJ8 _ (dvdOK_of_rows hpG D h31)
  set W := bfsForest [t] with hW
  set g : NTree SkelX → 𝕂′ := fun u => ((if Nock.V1J8.FillX.isPairB D.H (rowOfSkelX u.label) then
        [(Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).ftth)),
            (D.pd (rowOfSkelX u.label)).1),
         (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (Nock.V1J8.Gen.atomV (rowOfSkelX u.label).fttt)),
            (D.pd (rowOfSkelX u.label)).1)]
      else []).map fun x => WvA δ D χ (readRecH D.acs x)).sum with hgdef
  have hrow : ∀ j ∈ Finset.range W.length,
      awT δ b D.H D.pd W (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j = g (W.getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [awT_run δ b Rt hgen hpG hbig hrt hix hlenA χ _ j hj', List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t g]
  have hsum : (W.map g).sum = (D.preads.map fun x => WvA δ D χ (readRecH D.acs x)).sum := by
    rw [preads_eq Rt hgen, sum_flatMap_map]
  rw [hsum]
  show _ = Quad.mk _ (pubsVOf δ b D o χ WalkHQ.pubPQ) (pubsVOf δ b D o χ (WalkHQ.pubPQ + 1))
  by_cases h0 : D.preads = []
  · rw [h0]
    have hz : (0 : 𝕂′) = Quad.mk _ 0 0 := ((Quad.mk_eq_zero_iff _ (0 : K) 0).mpr ⟨rfl, rfl⟩).symm
    simp [pubsVOf, h0, hz]
  have hsh := ComplJ8OfBal.preads_shape Rt hgen hbig
  have h6 : pubsVOf δ b D o χ WalkHQ.pubPQ = pub2 δ (vhP δ b D o χ) 6 := by simp [pubsVOf, h0, WalkHQ.pubPQ]
  have h7 : pubsVOf δ b D o χ (WalkHQ.pubPQ + 1) = pub2 δ (vhP δ b D o χ) 7 := by
    simp [pubsVOf, h0, WalkHQ.pubPQ]
  rw [h6, h7, pub2_mk2 δ _ 6 rfl]
  have hall : ∀ x ∈ D.preads, VclL.isPathAx x.2 = true := by
    intro x hx
    obtain ⟨a, -, -, h⟩ := hsh x hx
    exact ComplJ8OfBal.isPathAx_of_two_le (by omega)
  have hmem : ∀ x ∈ VclL.pathReads D.preads, x ∈ D.preads := fun x hx =>
    (List.mem_filter.mp (List.mem_dedup.mp hx)).1
  have hslot : ∀ x ∈ VclL.pathReads D.preads, (Noun.slot x.2 x.1).isSome := by
    intro x hx
    obtain ⟨a, ha, h1, h2⟩ := hsh x (hmem x hx)
    rw [h1, (hbig a ha).2]
    rcases h2 with h | h <;> rw [h, VclL.slot_eq_chainWalk _ (by norm_num)] <;> rfl
  have hd61 : ComplJ8Walk.WalkDepthOK D.preads := by
    intro x hx
    obtain ⟨a, -, -, h⟩ := hsh x (hmem x hx)
    rcases h with h | h <;> rw [h] <;> decide
  have hpre : ∀ u ∈ walkRows D.acs D.preads, 2 * axisFold u.label.bits + 1 < p := by
    intro u hu
    have h60 := ComplJ8Walk.walkRows_len_le60 hd61 hu
    have h1 := axisFold_lt u.label.bits
    have h2 : 2 ^ (u.label.bits.length + 1) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 63 = 4 * 2 ^ 61 := by norm_num
    omega
  have hwn : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs := by
    refine ComplJ8OfBal.walkRows_nodes_mem _ _ (List.ne_nil_of_length_pos (acs_pos (p := p) Rt hgen))
      (ComplJ8OfBal.acs_closed_run Rt hgen hpG) ?_
    intro x hx _
    obtain ⟨a, ha, h1, h2⟩ := hsh x hx
    have hl := (hbig a ha).2
    refine ⟨h1 ▸ ComplJ8OfBal.comb_mem_acs Rt hgen hpG ha (by rw [hl]; simp), ?_⟩
    rw [h1, hl]
    rcases h2 with h | h <;> rw [h, VclL.slot_eq_chainWalk _ (by norm_num)] <;> rfl
  have hmV : nVOf D ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjV := (powN_ok o (le_two_pow_ht D hmV)).1
  rw [vhP_eq δ b Rt hgen o h0 hinjV χ hlenA hwn (ComplJ8OfBal.acs_cell Rt hgen hpG) hpre,
    walk_provide_total (WvA δ D χ) D.acs D.preads hslot (fun _ => rfl), ComplJ8OfBal.pathKind_of_all hall]


open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK) in
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds) in
open Nock.Jet.PinJ8 (pinCons) in
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV) in
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec) in
open Nock.NockVMROM.Thm54.FiniteIO (compress) in
/-- **`OpenJ8.balG` at the run with `hA` discharged** (binder `hclA` added, as `balF_closed`): carries the inc
sub-balance `hI` and the jet sub-balance `hJ` only. -/
theorem openJ8_with_balG' (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (O : OpenJ8 δ b (BRun δ b Rt hgen hpG h31))
    (hI : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMI)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMI + 1)))
    (hJ : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, jetT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j +
      ((pinCons (p := p) (K := K) (BRun δ b Rt hgen hpG h31).Pb.regs (BRun δ b Rt hgen hpG h31).Pb.idx).map fun x =>
        (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 1) = 0) :
    OpenJ8 δ b (BRun δ b Rt hgen hpG h31) :=
  openJ8_with_balG δ b Rt hgen hpG hax hop5 hRt h31 hwalk O hI
    (fun χ _ => hA_run δ b Rt hgen hpG hop5 hclA hRt h31 χ) hJ

end AWRun
end AW

/-! ## 20. Clause 3's inc sub-balance `hI` at the run

Both sides are `Σ_{(v, c) ∈ incOps} c · FI v`, the weighted inc record of the slow OP4 operands. Compute side
(`incT_run`, `incT_total`): an `s4` row with `v + 1 ≥ p` consumes `FI v` (`DX_inc`), every other row nothing; the
rows' operands are counted by `incOps` (`sum_count_dedup`). `hI_run` closes `hI` from `complJ8`'s binders; `openJ8_with_balG''` carries `hJ`
only. -/

section IncFoldG
open Nock.V1J8.Gen (AInfo idxOf combOf spineOf incChain)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom (wrA stepF fuelOf getD_modify inc_wrA size_wrA incChain_step
  spineOf_cons2 spineOf_short Cnd)
variable (p : ℕ) (acsL : List Noun) (rows : Array Nock.Edit.GenX.RowNX)

theorem miConv_wrA (ln lo : List ℕ) (a : Array AInfo) (k : ℕ) :
    ((wrA p acsL rows ln lo a).getD k AInfo.z).mi = (a.getD k AInfo.z).mi ∧
      ((wrA p acsL rows ln lo a).getD k AInfo.z).conv = (a.getD k AInfo.z).conv := by
  simp only [wrA]
  rw [getD_modify, getD_modify]
  simp only [Array.size_modify]
  split_ifs <;> simp

/-- One fold step, read at row `k < size`: the target `rootIdx (v + 1)` gets the count in `mi`; a conversion
operand sets `conv` at `rootIdx p`; a two-limb operand makes `idxOf (comb (v + 1))` an inc row. -/
theorem stepF_mi (a : Array AInfo) (vc : ℕ × ℕ) (k : ℕ) (hk : k < a.size)
    (h2 : vc.1 + 1 ≠ p → (Nock.Atoms.limbs vc.1).length = 2 ∧ (Nock.Atoms.limbs (vc.1 + 1)).length = 2) :
    (stepF p acsL rows a vc).size = a.size ∧
    ((stepF p acsL rows a vc).getD k AInfo.z).mi = (a.getD k AInfo.z).mi +
      (if ComplJ8Data.rootIdxP p acsL (vc.1 + 1) = k then vc.2 else 0) ∧
    (((stepF p acsL rows a vc).getD k AInfo.z).conv = true ↔ (a.getD k AInfo.z).conv = true ∨
      (vc.1 + 1 = p ∧ ComplJ8Data.rootIdxP p acsL p = k)) ∧
    (((stepF p acsL rows a vc).getD k AInfo.z).inc = true ↔ (a.getD k AInfo.z).inc = true ∨
      (vc.1 + 1 ≠ p ∧ k = idxOf acsL (combOf (Nock.Atoms.limbs (vc.1 + 1))))) := by
  by_cases hp : vc.1 + 1 = p
  · simp only [stepF, if_pos hp]
    rw [hp]
    refine ⟨by simp, ?_, ?_, ?_⟩
    · rw [getD_modify]; split_ifs <;> simp_all
    · rw [getD_modify]; split_ifs <;> simp_all
    · rw [getD_modify]; split_ifs <;> simp_all
  · obtain ⟨ho, hn⟩ := h2 hp
    have hf : fuelOf vc.1 = 1 + 1 := by
      unfold fuelOf
      rw [spineOf_cons2 _ (by omega), spineOf_short _ (by simp [ho])]; simp
    have hc : ¬ Cnd (Nock.Atoms.limbs vc.1) := fun h => by have := h.2; omega
    simp only [stepF, if_neg hp]
    rw [hf, incChain_step p acsL 1 _ _ a (by omega) (by omega), if_neg hc]
    have hk' : k < (wrA p acsL rows (Nock.Atoms.limbs (vc.1 + 1)) (Nock.Atoms.limbs vc.1) a).size := by
      rw [size_wrA]; exact hk
    obtain ⟨m1, c1⟩ := miConv_wrA p acsL rows (Nock.Atoms.limbs (vc.1 + 1)) (Nock.Atoms.limbs vc.1) a k
    refine ⟨by simp [size_wrA], ?_, ?_, ?_⟩
    · rw [getD_modify, if_congr Iff.rfl rfl rfl]
      by_cases hq : ComplJ8Data.rootIdxP p acsL (vc.1 + 1) = k
      · rw [if_pos ⟨hq, hk'⟩, if_pos hq, m1]
      · rw [if_neg (fun h => hq h.1), if_neg hq, m1]; simp
    · rw [getD_modify]
      have e : ∀ (c : Prop) [Decidable c] (x : AInfo), (if c then { x with mi := x.mi + vc.2 } else x).conv = x.conv :=
        fun c _ x => by split_ifs <;> rfl
      rw [e, c1]; simp [hp]
    · have e : ∀ (c : Prop) [Decidable c] (x : AInfo), (if c then { x with mi := x.mi + vc.2 } else x).inc = x.inc :=
        fun c _ x => by split_ifs <;> rfl
      rw [getD_modify, e, inc_wrA]
      simp [hp, hk]

/-- **The `infoOf` fold, read per row** (two-limb operands): `mi` sums the counts of the operands targeting the
row, `conv` marks `rootIdx p` for a conversion operand, inc rows are the combs of the two-limb `v + 1`. -/
theorem fold_mi : ∀ (l : List (ℕ × ℕ)) (a : Array AInfo),
    (∀ vc ∈ l, vc.1 + 1 ≠ p → (Nock.Atoms.limbs vc.1).length = 2 ∧ (Nock.Atoms.limbs (vc.1 + 1)).length = 2) →
    (l.foldl (stepF p acsL rows) a).size = a.size ∧ ∀ k < a.size,
      ((l.foldl (stepF p acsL rows) a).getD k AInfo.z).mi = (a.getD k AInfo.z).mi +
        ((l.filter fun vc => ComplJ8Data.rootIdxP p acsL (vc.1 + 1) = k).map Prod.snd).sum ∧
      (((l.foldl (stepF p acsL rows) a).getD k AInfo.z).conv = true ↔ (a.getD k AInfo.z).conv = true ∨
        ∃ vc ∈ l, vc.1 + 1 = p ∧ ComplJ8Data.rootIdxP p acsL p = k) ∧
      (((l.foldl (stepF p acsL rows) a).getD k AInfo.z).inc = true ↔ (a.getD k AInfo.z).inc = true ∨
        ∃ vc ∈ l, vc.1 + 1 ≠ p ∧ k = idxOf acsL (combOf (Nock.Atoms.limbs (vc.1 + 1))))
  | [], a, _ => ⟨rfl, fun k _ => ⟨by simp, by simp, by simp⟩⟩
  | vc :: l, a, h => by
    have hs0 : (stepF p acsL rows a vc).size = a.size := by
      unfold stepF; split_ifs
      · simp
      · simp [ComplJ8Atom.size_incChain]
    obtain ⟨ih1, ih2⟩ := fold_mi l (stepF p acsL rows a vc) fun w hw => h w (List.mem_cons_of_mem _ hw)
    simp only [List.foldl_cons]
    refine ⟨ih1.trans hs0, fun k hk => ?_⟩
    have hk' : k < (stepF p acsL rows a vc).size := hs0 ▸ hk
    obtain ⟨-, s2, s3, s4⟩ := stepF_mi p acsL rows a vc k hk (h vc List.mem_cons_self)
    obtain ⟨i2, i3, i4⟩ := ih2 k hk'
    refine ⟨?_, ?_, ?_⟩
    · rw [i2, s2, List.filter_cons]
      by_cases hq : ComplJ8Data.rootIdxP p acsL (vc.1 + 1) = k
      · simp only [hq, if_true, decide_true, List.map_cons, List.sum_cons]; ring
      · simp [hq]
    · rw [i3, s3]
      constructor
      · rintro ((h1 | ⟨h1, h3⟩) | ⟨w, hw, h1, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨vc, List.mem_cons_self, h1, h3⟩
        · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, h1, h3⟩
      · rintro (h1 | ⟨w, hw, h1, h3⟩)
        · exact Or.inl (Or.inl h1)
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact Or.inl (Or.inr ⟨h1, h3⟩)
          · exact Or.inr ⟨w, hw, h1, h3⟩
    · rw [i4, s4]
      constructor
      · rintro ((h1 | ⟨h1, h3⟩) | ⟨w, hw, h1, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨vc, List.mem_cons_self, h1, h3⟩
        · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, h1, h3⟩
      · rintro (h1 | ⟨w, hw, h1, h3⟩)
        · exact Or.inl (Or.inl h1)
        · rcases List.mem_cons.mp hw with rfl | hw
          · exact Or.inl (Or.inr ⟨h1, h3⟩)
          · exact Or.inr ⟨w, hw, h1, h3⟩

end IncFoldG

section IncAtom
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem newBA_conv (D : J8Data p Rg fuel s f r) (i : Fin D.acs.length) :
    newBA D AtomChipHQ.conv i = if (D.info.getD i Nock.V1J8.Gen.AInfo.z).conv then 1 else 0 := by
  show (((ComplJ8Atom.tabOf D.acs D.info D.mb D.rows).row i).conv : ZMod p) = _
  simp only [ComplJ8Atom.AtomTab.row, ComplJ8Atom.tabOf]
  split_ifs <;> simp <;> first | assumption | rfl | simp_all

theorem newBA_idxO (D : J8Data p Rg fuel s f r) (i : Fin D.acs.length) :
    newBA D AtomChipHQ.idxO i = ((((ComplJ8Atom.tabOf D.acs D.info D.mb D.rows).row i).idxO : ℕ) : ZMod p) := rfl

theorem newBA_mi (D : J8Data p Rg fuel s f r) (i : Fin D.acs.length) :
    newBA D AtomChipHQ.mi i = (((D.info.getD i Nock.V1J8.Gen.AInfo.z).mi : ℕ) : ZMod p) := rfl

/-- **The atom table's inc denominator, read off the row**: `dMI = ρH + recDen 0 γH (2(1 − conv),
((1 − conv) idx_o − conv, 2), (idx, 4))`. -/
theorem dMI_key (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ}
    (o : StrictOrbitDomain (ZMod p) 3 h) (hinj : Function.Injective (powN o D.acs.length)) (χ : Coins frameJ8 K)
    (pubs : ℕ → K) (i : Fin D.acs.length) :
    HonestA8.dMI δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) i =
      ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ)
        (2 * (1 - newBA D AtomChipHQ.conv i),
          ((1 - newBA D AtomChipHQ.conv i) * newBA D AtomChipHQ.idxO i - newBA D AtomChipHQ.conv i, 2),
          (((i : ℕ) : ZMod p), 4)) := by
  rw [ComplJ8OfAtom.dMI_eq]
  have ht : ∀ k, 2 ≤ k → k < 205 → (ComplJ8OfAtom.ezA δ b D hA o χ pubs i).trace k =
      if k < 130 then colAH δ b D hA o χ pubs k i else newBA D k i := by
    intro k h1 h2
    exact ComplJ8Atom.EZ_trace δ b hA (powN o _) o _ pubs _ _ hinj i k h1 h2
  have t0 := ht AtomChipHQ.conv (by decide) (by decide)
  have t1 := ht AtomChipHQ.idxO (by decide) (by decide)
  have t2 := ht Cell.idx (by decide) (by decide)
  obtain ⟨f0, -⟩ := ComplJ8OfAtom.colAH_fields δ b D hA o χ pubs i
  simp only [show ¬ AtomChipHQ.conv < 130 by decide, show ¬ AtomChipHQ.idxO < 130 by decide,
    show Cell.idx < 130 by decide, if_true, if_false, f0] at t0 t1 t2
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_five, BalanceQ.liftRec, ServeH.keyVec5, AtomChipHQ.incKey,
    recDen]
  simp [CoeffExpr.eval, cv, notE, t0, t1, t2, AtomChipHQ.tagInc, IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

end IncAtom

section IncComp
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The inc record's compute denominator `ρH + recDen 0 γH (sf1.k, (sf1.v, e.k), (e.v, 4))`. -/
theorem DX_inc (e : Nock.Reified.Env (ZMod p)) (χ : Coins frameJ8 K) (hch : e.chal = VerJ8.chalVJ8 b χ) :
    TeleCQX.DX δ (Compute.TowerD.gatherEnv b e) e ChipHX.incRecX =
      ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ) (e.trace 31, (e.trace 32, e.trace 29), (e.trace 30, 4)) := by
  rw [ComplJ8CompPole.den_split δ b e χ hch _ (by simp [ChipHX.incRecX])]
  congr 1
  simp only [FiniteIO.compress, Walk.rlc, Fin.sum_univ_eight, BalanceQ.liftRec, DenXJ8.keyX, DenXJ8.keyXN, recDen]
  simp [ChipHX.RE.ev, ChipHX.incRecX, ChipHX.xSf1, ChipHX.xE, ChipHX.hdX,
    IsScalarTower.algebraMap_apply (ZMod p) K 𝕂′]

/-- The slow-OP4 operand of a compute row (`incOpsP`'s filter). -/
def optI (p : ℕ) (rr : RowNX) : Option ℕ :=
  match rr.st, rr.sf1 with
  | .s4, .atom v => if p ≤ v + 1 then some v else none
  | _, _ => none

/-- The inc record weight of operand `v`: `1 / (ρH + recDen 0 γH (H v, H (v + 1), 4))`. -/
def FI (D : J8Data p Rg fuel s f r) (χ : Coins frameJ8 K) (v : ℕ) : 𝕂′ :=
  (ComplJ8Bad.ρH δ χ + recDen 0 (ComplJ8Bad.γH δ χ)
    ((((D.H (.atom v)).1 : ℕ) : ZMod p), ((((D.H (.atom v)).2 : ℕ) : ZMod p), (((D.H (.atom (v + 1))).1 : ℕ) : ZMod p)),
      ((((D.H (.atom (v + 1))).2 : ℕ) : ZMod p), 4)))⁻¹

section IncRun
variable [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  (Rt : ℕ → Nock.Jet.Autogen.Tpl) {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

set_option maxHeartbeats 1000000 in
/-- **Run row `j`'s inc consume** is the inc weight of its slow-OP4 operand (zero on every other row). -/
theorem incT_run (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (χ : Coins frameJ8 K) (pubVal : ℕ → ZMod p) (j : ℕ) (hj : j < (bfsForest [t]).length) :
    incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      (optI p (rowOfSkelX ((bfsForest [t])[j]'hj).label)).elim 0 (FI δ (j8DataOf p Rg Rt hgen) χ) := by
  set D := j8DataOf p Rg Rt hgen with hD
  set W := bfsForest [t] with hW
  set rr := rowOfSkelX (W[j]'hj).label with hrr
  have hrow : HonestWalkX.rowAtWX W (j + 1) = rr := by
    simp [hrr, HonestWalkX.rowAtWX, List.getElem?_eq_getElem hj]
  have hrowm : rr ∈ (ComplJ8Data.rowsOfT t).toList := by
    simp only [hrr, ComplJ8Data.rowsOfT, List.toList_toArray]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  have hH : HonestCompX.HdlOK p D.H := ComplJ8Data.hdlOK_hdlP p D.cells D.acs
  have htr : (HonestTraceX.env0 D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j).trace =
      HonestCompX.colX D.H D.pd rr (HonestTraceX.flX j) (HonestTraceX.llX W j) := by
    funext c
    show HonestTraceX.baseT D.H D.pd W j c = _
    unfold HonestTraceX.baseT; rw [hrow]
  unfold incT
  rw [DX_inc δ b _ χ rfl, htr, HonestCompX.colX_st _ _ _ _ _ 4 (by decide)]
  simp only [HonestCompX.cx61, HonestCompX.cxSf1_k, HonestCompX.cxSf1_v, HonestCompX.cxE_k, HonestCompX.cxE_v]
  by_cases hst : rr.st = .s4
  · obtain ⟨n, h1, h2⟩ := ComplJ8Atom.s4_row hgen hax hop5 hrowm hst
    have ho : optI p rr = if p ≤ n + 1 then some n else none := by
      unfold optI; rw [hst, h1]
    rw [ho]
    simp only [HonestCompX.cFast, hst, h2, RowDecodeVSX.stIdx, if_true]
    by_cases hp : p ≤ n + 1
    · have hb := hH.big (n + 1) hp
      rw [if_pos hp, if_neg (by omega)]
      simp only [Option.elim, FI, h1, HonestCompX.hk, HonestCompX.hv, hb, sub_zero, mul_one, map_one, one_mul]
    · have hs := hH.small (n + 1) (by omega)
      rw [if_neg hp, if_pos (by rw [hs])]
      simp
  · have ho : optI p rr = none := by
      unfold optI
      cases h : rr.st <;> simp_all
    rw [ho, if_neg]
    · simp
    · cases h : rr.st <;> simp_all [RowDecodeVSX.stIdx]

end IncRun
end IncComp

section IncSum
variable {ι R : Type} [CommRing R]

/-- **Weighted consumers by serial**: `Σ_{x ∈ C} w x · g (idx x) = Σ_{j < n} (Σ_{x ∈ C, idx x = j} w x) · g j`. -/
theorem sum_serialW (n : ℕ) (idx : ι → ℕ) (w : ι → ℕ) (g : ℕ → R) : ∀ C : List ι, (∀ x ∈ C, idx x < n) →
    (C.map fun x => (w x : R) * g (idx x)).sum =
      ∑ j ∈ Finset.range n, ((((C.filter fun x => idx x = j).map w).sum : ℕ) : R) * g j
  | [], _ => by simp
  | x :: C, h => by
    rw [List.map_cons, List.sum_cons, sum_serialW n idx w g C (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have hx : idx x ∈ Finset.range n := Finset.mem_range.mpr (h x List.mem_cons_self)
    have hc : ∀ j, ((((List.filter (fun y => decide (idx y = j)) (x :: C)).map w).sum : ℕ) : R) =
        (if idx x = j then (w x : R) else 0) +
          ((((List.filter (fun y => decide (idx y = j)) C).map w).sum : ℕ) : R) := by
      intro j
      by_cases hj : idx x = j
      · simp [List.filter_cons, hj]
      · simp [List.filter_cons, hj]
    simp only [hc, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq _ _ _, if_pos hx]

theorem sum_filterMap_elim {α β M : Type} [AddCommMonoid M] (o : α → Option β) (F : β → M) : ∀ l : List α,
    (l.map fun x => (o x).elim 0 F).sum = ((l.filterMap o).map F).sum
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.sum_cons, sum_filterMap_elim o F l, List.filterMap_cons]
    cases o x <;> simp

theorem sum_count_dedup {α M : Type} [DecidableEq α] [CommRing M] (F : α → M) (l : List α) :
    (l.map F).sum = ((l.dedup.map fun v => (v, l.count v)).map fun vc => (vc.2 : M) * F vc.1).sum := by
  rw [Finset.sum_list_map_count, List.map_map, ← List.sum_toFinset _ (List.nodup_dedup l),
    show l.dedup.toFinset = l.toFinset from by ext; simp]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [nsmul_eq_mul]

end IncSum

section IncClose
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The compute's inc consumes, by operand**: the slow-OP4 rows' inc weights total `Σ_{(v, c) ∈ incOps} c · FI v`. -/
theorem incT_total (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t) (χ : Coins frameJ8 K)
    (pubVal : ℕ → ZMod p) :
    ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) pubVal j =
      ((ComplJ8Data.incOpsP p (j8DataOf p Rg Rt hgen).rows).map fun vc =>
        (vc.2 : 𝕂′) * FI δ (j8DataOf p Rg Rt hgen) χ vc.1).sum := by
  set D := j8DataOf p Rg Rt hgen with hD
  set W := bfsForest [t] with hW
  set g : NTree SkelX → 𝕂′ := fun u => (optI p (rowOfSkelX u.label)).elim 0 (FI δ D χ) with hg
  have hrow : ∀ j ∈ Finset.range W.length,
      incT δ b D.H D.pd W (VerJ8.chalVJ8 b χ) pubVal j = g (W.getD j t) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [incT_run δ b Rt hgen hax hop5 χ _ j hj', List.getD_eq_getElem _ _ hj']
  rw [Finset.sum_congr rfl hrow, ComplJ8OfBal.sum_range_getD' t g, hg,
    sum_filterMap_elim (fun u => optI p (rowOfSkelX u.label)) (FI δ D χ) W, sum_count_dedup]
  have hrows : D.rows.toList = W.map fun u => rowOfSkelX u.label := by
    show (ComplJ8Data.rowsOfT t).toList = _
    simp [ComplJ8Data.rowsOfT, hW]
  have hvs : D.rows.toList.filterMap (optI p) = W.filterMap fun u => optI p (rowOfSkelX u.label) := by
    rw [hrows, List.filterMap_map]; rfl
  show _ = (((D.rows.toList.filterMap (optI p)).dedup.map fun v =>
    (v, (D.rows.toList.filterMap (optI p)).count v)).map fun vc => (vc.2 : 𝕂′) * FI δ D χ vc.1).sum
  rw [hvs]

end IncClose

section IncAtomSum
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The atom row `j`'s inc weight `1 / dMI j` (zero past the table). -/
def GAt (D : J8Data p Rg fuel s f r) (hA : 0 < D.acs.length) {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (χ : Coins frameJ8 K) (pubs : ℕ → K) (j : ℕ) : 𝕂′ :=
  if hj : j < D.acs.length then
    (HonestA8.dMI δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs) (newBA D) ⟨j, hj⟩)⁻¹
  else 0

set_option maxHeartbeats 2000000 in
/-- **The atom table's inc terminal, by operand**: the `mi`-weighted inc-key LogUp total is
`Σ_{(v, c) ∈ incOps} c · FI v` — the row `rootIdx (v + 1)` carries `mi = c` and the inc key of `v`'s compute record
(old handle `(0, p − 1)` on the conversion row, `(2, rootIdx v)` on the inc row of `v`'s two-limb comb). -/
theorem incSum_eq (hpG : p = Nock.Atoms.p) (hax : ComplJ8.ProgAxOK p t) (hop5 : ComplJ8.ProgOp5OK p t)
    (hbig : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1])
    (hrt : ∀ a, ComplJ8Data.rootIdxP p (j8DataOf p Rg Rt hgen).acs a =
      Nock.V1J8.Gen.idxOf (j8DataOf p Rg Rt hgen).acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a)))
    (hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (j8DataOf p Rg Rt hgen).acs.length)) (χ : Coins frameJ8 K) (pubs : ℕ → K) :
    ∑ j ∈ Finset.range (j8DataOf p Rg Rt hgen).acs.length,
        liftQ δ (HonestA8.cNat j (newBA (j8DataOf p Rg Rt hgen) AtomChipHQ.mi)) *
          (HonestA8.dNat δ (HonestA8.dMI δ b (acs_pos Rt hgen) (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs
            (colAH δ b (j8DataOf p Rg Rt hgen) (acs_pos Rt hgen) o χ pubs) (newBA (j8DataOf p Rg Rt hgen))) j)⁻¹ =
      ((ComplJ8Data.incOpsP p (j8DataOf p Rg Rt hgen).rows).map fun vc =>
        (vc.2 : 𝕂′) * FI δ (j8DataOf p Rg Rt hgen) χ vc.1).sum := by
  subst hpG
  set D := j8DataOf Nock.Atoms.p Rg Rt hgen with hD
  have hA : 0 < D.acs.length := acs_pos Rt hgen
  have hg := ComplJ8Atom.genHyp_j8 Rg Rt hgen hax hop5 hN
  set ops := ComplJ8Data.incOpsP Nock.Atoms.p D.rows with hops
  have hl2 : ∀ a ∈ D.bigs, Nock.Atoms.limbs a = [a + 1 - Nock.Atoms.p, Nock.Atoms.B - 1] := fun a ha => (hbig a ha).2
  have hopB : ∀ vc ∈ ops, vc.1 + 1 ≠ Nock.Atoms.p → vc.1 ∈ D.bigs ∧ vc.1 + 1 ∈ D.bigs :=
    fun vc hvc hp => (hg.ops vc hvc).2 hp
  have hopT : ∀ vc ∈ ops, vc.1 + 1 ∈ D.bigs := by
    intro vc hvc
    by_cases hp : vc.1 + 1 = Nock.Atoms.p
    · rw [hp]; exact (hg.ops vc hvc).1 hp
    · exact (hopB vc hvc hp).2
  have hlen : ∀ vc ∈ ops, vc.1 + 1 ≠ Nock.Atoms.p →
      (Nock.Atoms.limbs vc.1).length = 2 ∧ (Nock.Atoms.limbs (vc.1 + 1)).length = 2 := by
    intro vc hvc hp
    obtain ⟨h1, h2⟩ := hopB vc hvc hp
    rw [hl2 _ h1, hl2 _ h2]; simp
  obtain ⟨-, hfold⟩ := fold_mi Nock.Atoms.p D.acs D.rows ops (Array.replicate D.acs.length Nock.V1J8.Gen.AInfo.z) hlen
  have hinfo : D.info = ComplJ8Data.infoOfP Nock.Atoms.p D.acs D.rows := rfl
  have hF0 : ComplJ8Atom.infoFold Nock.Atoms.p D.acs D.rows =
      ops.foldl (ComplJ8Atom.stepF Nock.Atoms.p D.acs D.rows) (Array.replicate D.acs.length Nock.V1J8.Gen.AInfo.z) := rfl
  have hz : ∀ k < D.acs.length, (Array.replicate D.acs.length Nock.V1J8.Gen.AInfo.z).getD k Nock.V1J8.Gen.AInfo.z =
      Nock.V1J8.Gen.AInfo.z := by
    intro k hk; simp [Array.getD_eq_getD_getElem?, hk]
  set tgt : ℕ × ℕ → ℕ := fun vc => ComplJ8Data.rootIdxP Nock.Atoms.p D.acs (vc.1 + 1) with htgt
  have hmi : ∀ k < D.acs.length, (D.info.getD k Nock.V1J8.Gen.AInfo.z).mi = ((ops.filter fun vc => tgt vc = k).map Prod.snd).sum := by
    intro k hk
    rw [hinfo, (ComplJ8Atom.info_fields _ _ _ k).2.2.2.2.2.2, hF0, (hfold k (by simpa using hk)).1, hz k hk]
    simp [Nock.V1J8.Gen.AInfo.z, htgt]
  have hconv : ∀ k < D.acs.length, ((D.info.getD k Nock.V1J8.Gen.AInfo.z).conv = true ↔
      ∃ vc ∈ ops, vc.1 + 1 = Nock.Atoms.p ∧ ComplJ8Data.rootIdxP Nock.Atoms.p D.acs Nock.Atoms.p = k) := by
    intro k hk
    rw [hinfo, (ComplJ8Atom.info_fields _ _ _ k).2.1, hF0, (hfold k (by simpa using hk)).2.1, hz k hk]
    simp [Nock.V1J8.Gen.AInfo.z]
  have hinc : ∀ k < D.acs.length, ((D.info.getD k Nock.V1J8.Gen.AInfo.z).inc = true ↔
      ∃ vc ∈ ops, vc.1 + 1 ≠ Nock.Atoms.p ∧
        k = Nock.V1J8.Gen.idxOf D.acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (vc.1 + 1)))) := by
    intro k hk
    rw [hinfo, (ComplJ8Atom.info_fields _ _ _ k).1, hF0, (hfold k (by simpa using hk)).2.2, hz k hk]
    simp [Nock.V1J8.Gen.AInfo.z]
  have hmem : ∀ a ∈ D.bigs, Nock.V1J8.Gen.combOf (Nock.Atoms.limbs a) ∈ D.acs :=
    fun a ha => ComplJ8OfBal.comb_mem_acs Rt hgen rfl ha (by rw [hl2 a ha]; simp)
  have hlt : ∀ c ∈ D.acs, Nock.V1J8.Gen.idxOf D.acs c < D.acs.length := by
    intro c hc; rw [ComplJ8OfBal.genIdxOf_eq _ _ hc]; exact List.idxOf_lt_length_of_mem hc
  have hgetE : ∀ c (hc : c ∈ D.acs), D.acs[Nock.V1J8.Gen.idxOf D.acs c]'(hlt c hc) = c := by
    intro c hc
    simp only [ComplJ8OfBal.genIdxOf_eq _ _ hc]
    exact List.getElem_idxOf _
  have hgetD : ∀ c ∈ D.acs, ∀ d, D.acs.getD (Nock.V1J8.Gen.idxOf D.acs c) d = c := by
    intro c hc d
    rw [List.getD_eq_getElem _ _ (hlt c hc)]; exact hgetE c hc
  have htl : ∀ vc ∈ ops, tgt vc < D.acs.length := by
    intro vc hvc
    simp only [htgt, hrt]
    exact hlt _ (hmem _ (hopT vc hvc))
  -- the atom rows' weight
  have hterm : ∀ j ∈ Finset.range D.acs.length,
      liftQ δ (HonestA8.cNat j (newBA D AtomChipHQ.mi)) *
        (HonestA8.dNat δ (HonestA8.dMI δ b hA (powN o _) o (ChalsAZJ8.chalsAJ8Z δ χ) pubs (colAH δ b D hA o χ pubs)
          (newBA D)) j)⁻¹ =
      ((((ops.filter fun vc => tgt vc = j).map Prod.snd).sum : ℕ) : Quad (algebraMap (ZMod Nock.Atoms.p) K δ)) * GAt δ b D hA o χ pubs j := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [HonestA8.cNat, HonestA8.dNat, dif_pos hj', GAt, newBA_mi, hmi j hj', liftQ, map_natCast]
  rw [Finset.sum_congr rfl hterm, ← sum_serialW D.acs.length tgt Prod.snd (GAt δ b D hA o χ pubs) ops htl]
  refine congrArg List.sum (List.map_congr_left fun vc hvc => ?_)
  congr 1
  -- the matching: the target row's inc key is `vc.1`'s compute record
  rcases vc with ⟨v, c⟩
  dsimp only
  have hk := htl (v, c) hvc
  have hkt : tgt (v, c) = Nock.V1J8.Gen.idxOf D.acs (Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (v + 1))) := by
    simp only [htgt, hrt]
  have hH : HonestCompX.HdlOK Nock.Atoms.p D.H := ComplJ8Data.hdlOK_hdlP Nock.Atoms.p D.cells D.acs
  have hHb : ∀ a, Nock.Atoms.p ≤ a → D.H (.atom a) = (2, ComplJ8Data.rootIdxP Nock.Atoms.p D.acs a) := by
    intro a ha
    show ComplJ8Data.hdlP Nock.Atoms.p D.cells D.acs (.atom a) = _
    simp [ComplJ8Data.hdlP, Nat.not_lt.mpr ha]
  obtain ⟨x, hx, -, -, hle⟩ := ComplJ8Atom.mem_incOpsP _ _ (v, c) hvc
  simp only [GAt, dif_pos hk, FI, ← hD]
  rw [dMI_key δ b D hA o hinj χ pubs ⟨tgt (v, c), hk⟩, newBA_conv, newBA_idxO]
  refine congrArg (fun x => (ComplJ8Bad.ρH δ χ + x)⁻¹) ?_
  by_cases hp : v + 1 = Nock.Atoms.p
  · have hc : (D.info.getD (tgt (v, c)) Nock.V1J8.Gen.AInfo.z).conv = true :=
      (hconv _ hk).mpr ⟨(v, c), hvc, hp, by simp only [htgt, hp]⟩
    have hsm : D.H (.atom v) = (0, v) := hH.small v (by omega)
    have hv1 : ((v : ℕ) : ZMod Nock.Atoms.p) = -1 := by
      have : ((v + 1 : ℕ) : ZMod Nock.Atoms.p) = 0 := by rw [hp, ZMod.natCast_self]
      push_cast at this; linear_combination this
    simp only [hc, if_true, hsm, hHb (v + 1) (by omega), hv1]
    simp only [htgt]
    norm_num
  · have hpv : Nock.Atoms.p ≤ v := by omega
    have hc : (D.info.getD (tgt (v, c)) Nock.V1J8.Gen.AInfo.z).conv = false := by
      cases hcc : (D.info.getD (tgt (v, c)) Nock.V1J8.Gen.AInfo.z).conv
      · rfl
      · exfalso
        obtain ⟨wc, hwc, hwp, hwk⟩ := (hconv _ hk).mp hcc
        have m1 := hmem _ ((hg.ops wc hwc).1 hwp)
        have m2 := hmem _ (hopT (v, c) hvc)
        rw [hrt, hkt] at hwk
        have e1 : Nock.V1J8.Gen.combOf (Nock.Atoms.limbs Nock.Atoms.p) =
            Nock.V1J8.Gen.combOf (Nock.Atoms.limbs (v + 1)) := by
          rw [← hgetD _ m1 Nock.V1J8.Gen.padN, ← hgetD _ m2 Nock.V1J8.Gen.padN, hwk]
        have e2 : Nock.Atoms.limbs Nock.Atoms.p = Nock.Atoms.limbs (v + 1) := by
          rw [← ComplJ8Atom.unComb_combOf (Nock.Atoms.limbs Nock.Atoms.p) (by rw [Nock.Atoms.limbs_p]; simp),
            ← ComplJ8Atom.unComb_combOf (Nock.Atoms.limbs (v + 1)) (by rw [(hlen (v, c) hvc hp).2]), e1]
        have e3 : Nock.Atoms.p = v + 1 := by
          rw [← Nock.Atoms.val_limbs Nock.Atoms.p, ← Nock.Atoms.val_limbs (v + 1), e2]
        exact hp e3.symm
    have hi : (D.info.getD (tgt (v, c)) Nock.V1J8.Gen.AInfo.z).inc = true := (hinc _ hk).mpr ⟨(v, c), hvc, hp, hkt⟩
    set T := ComplJ8Atom.tabOf D.acs D.info D.mb D.rows with hT
    have hsp : T.sp (tgt (v, c)) = Nock.Atoms.limbs (v + 1) := by
      show ComplJ8Atom.unComb (D.acs.getD (tgt (v, c)) Nock.V1J8.Gen.padN) = _
      rw [hkt, hgetD _ (hmem _ (hopT (v, c) hvc)), ComplJ8Atom.unComb_combOf _ (by rw [(hlen (v, c) hvc hp).2])]
    have hidx : (T.row (tgt (v, c))).idxO = ComplJ8Data.rootIdxP Nock.Atoms.p D.acs v := by
      rw [hkt]; exact ComplJ8Atom.idxO_root _ _ _ _ hg (v, c) hvc hp
    simp only [hc, Bool.false_eq_true, if_false, hidx, hHb v hpv, hHb (v + 1) (by omega)]
    simp only [htgt]
    norm_num

end IncAtomSum

section IncFinal
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (ProgAxOK ProgOp5OK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

set_option maxHeartbeats 2000000 in
/-- **`hI`: the compute's inc consumes total the atom table's inc terminal**, at every coin, from `complJ8`'s
binders `hpG hax hop5 hclA hRt h31`: both sides are `Σ_{(v, c) ∈ incOps} c · FI v`
(`incT_total`, `incSum_eq`). -/
theorem hI_run (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) :
    ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, incT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j =
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsA AtomChipHQ.pubMI)
        (((BRun δ b Rt hgen hpG h31).M χ).pubsA (AtomChipHQ.pubMI + 1)) := by
  intro χ _
  have hN : (j8DataOf p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
    have h := h31 (bfsForest [(j8DataOf p Rg Rt hgen).t]).length (by simp [sizesJ8])
    rw [ComplJ8BigBound.data_rows hgen]
    simpa [ComplJ8Data.rowsOfT, j8DataOf] using h
  obtain ⟨hb, -, -, -, -, -, -, -, hrt⟩ := ComplJ8BigBound.bigBound_single hgen hpG (hclA 0) (hclA 1) hRt hop5 hN
  have hbig : ∀ a ∈ (j8DataOf p Rg Rt hgen).bigs, p ≤ a ∧ Nock.Atoms.limbs a = [a + 1 - p, Nock.Atoms.B - 1] :=
    fun a ha => ⟨(hb a ha).1, (hb a ha).2.2⟩
  set D := j8DataOf p Rg Rt hgen with hD
  set o := orbJ8 D (dvdOK_of_rows hpG D h31)
  have hA : 0 < D.acs.length := acs_pos Rt hgen
  have hmA : D.acs.length ∈ sizesJ8 D := by simp [sizesJ8]
  have hinjA := (powN_ok o (le_two_pow_ht D hmA)).1
  obtain ⟨-, -, -, -, -, tMI⟩ := ComplJ8OfAtom.atomTerms δ b D hA o χ
  show _ = Quad.mk _ (pubsAOf δ b D hA o χ AtomChipHQ.pubMI) (pubsAOf δ b D hA o χ (AtomChipHQ.pubMI + 1))
  rw [tMI, incT_total δ b Rt hgen hax hop5 χ _, incSum_eq δ b Rt hgen hpG hax hop5 hbig hrt hN o hinjA χ _]

/-- **`OpenJ8.balG` at the run with `hA` and `hI` discharged**: carries the jet sub-balance `hJ` only (exact
statement as in `balG_closed`). -/
theorem openJ8_with_balG'' (hpG : p = Nock.Atoms.p) (hax : ProgAxOK p t) (hop5 : ProgOp5OK p t)
    (hclA : ∀ k : Fin 3, ∀ v ∈ (FrameVS.claimNoun (ComplJ8.cJ s f r) k).leafList, v < p)
    (hRt : ∀ id ∈ CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (h31 : Rows31 (j8DataOf p Rg Rt hgen)) (hwalk : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).reads)
    (O : OpenJ8 δ b (BRun δ b Rt hgen hpG h31))
    (hJ : ∀ χ, (BRun δ b Rt hgen hpG h31).Good χ →
      ∑ j ∈ Finset.range (bfsForest [t]).length, jetT δ b (j8DataOf p Rg Rt hgen).H (j8DataOf p Rg Rt hgen).pd
        (bfsForest [t]) (VerJ8.chalVJ8 b χ) (pubC δ b Rt hgen χ) j +
      ((pinCons (p := p) (K := K) (BRun δ b Rt hgen hpG h31).Pb.regs (BRun δ b Rt hgen hpG h31).Pb.idx).map fun x =>
        (compress (coinsCV b δ (VerJ8.chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 0) (((BRun δ b Rt hgen hpG h31).M χ).pubsJ 1) = 0) :
    OpenJ8 δ b (BRun δ b Rt hgen hpG h31) :=
  openJ8_with_balG' δ b Rt hgen hpG hax hop5 hclA hRt h31 hwalk O
    (hI_run δ b Rt hgen hpG hax hop5 hclA hRt h31) hJ

end IncFinal

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfBalG
