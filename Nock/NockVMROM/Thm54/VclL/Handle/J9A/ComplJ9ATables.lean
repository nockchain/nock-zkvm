/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ATables.lean

* **`cellOK_runA`**: the cell table (`cellChipHQKW`), satisfied and bound, at every coin outside the bad list of
    `honestJ8Of δ b DA hF hC hA AV fams` with `famCellV DA`, `famCellH DA` in `fams` (L6's `cellOK_run`, the data
    swapped: the cells are `DD`'s, so `j8_cells_ok` under `hleaf` applies verbatim).
  * **`walkOK_runA`**: the J-8 walk chip at the J-9 A cell-walk reads, under `Rows31 DA` and
    `WalkDepthOK DA.reads` (`ComplJ9ADataRec.walkDepthOK_readsA` from `hwalk9`).
  * **`awOK_runA`**: J-9 B's atom walk at `DA`, i.e. over the J-9 A atom-walk
    reads `DD.preads ++ axReads9`, at the record with atom part `AVA = avOf9 DA (avOf DA)`; binders `hax9`, `hwalkA`.
  * **`atomOK_runA`** (section 3): the atom table, both views (`atomChipHQ`, `atomChipHQL`), at `DA` (same `acs info
    mb` as J-9 B's `D9`), WITHOUT J-8's `hax` / `hop5`: `s4_rowA`, `genHypA`, `acs_okA`, `atomOK_mbA` are the J-8 /
    J-9 B proofs with the binders dropped (their only use was `SmallX` at an OP4 row, which is `True`).
  Binders: `hF : DvdOK DA`, `h31 : Rows31 DA` are the J-9 A data's (its walk / atom-walk sizes differ from
  `DD`'s); `hC hA` from `cellsA_pos` / `acsA_pos`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ADataRec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ATables

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)

noncomputable section

/-- A table size under `Rows31` is `< p` when `2^63 < p`. -/
theorem lt31 {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
    {D : J8Data p Rg fuel s f r} (hp63 : 2 ^ 63 < p) (h31 : Rows31 D) {x : ℕ} (hx : x ∈ sizesJ8 D) : x < p := by
  have := h31 x hx; have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
  omega

/-! ## 1–2. The cell table and the J-8 walk at the J-9 A data -/

section Obl
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => j9aDataOf p Rg Rt hgen

variable (hF : DvdOK (j9aDataOf p Rg Rt hgen)) (hC : 0 < (j9aDataOf p Rg Rt hgen).cells.length)
  (hA : 0 < (j9aDataOf p Rg Rt hgen).acs.length) (AV : AVPart p K) (fams : List (List (BadSpec K)))

theorem cellOK_runA (hpG : p = Nock.Atoms.p) (hp63 : 2 ^ 63 < p) (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    (hV : famCellV δ (DA) ∈ fams)
    (hH : famCellH δ b (DA) hC (orbJ8 _ hF) ∈ fams) (χ : Coins frameJ8 K)
    (hχ : (honestJ8Of δ b (DA) hF hC hA AV fams).Good χ) :
    let B := honestJ8Of δ b (DA) hF hC hA AV fams
    (CellTwinKW.cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).rap.Satisfies
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) ∧
    (CellTwinKW.cellChipHQKW δ b B.Pb.hnC B.Pb.nodesC B.Pb.orbitC (chalsMJ8 δ χ) (B.M χ).pubsC).BindsPreprocessing
      (qM δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsC) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(DA).t]).length)] fams),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  obtain ⟨hz, hrows⟩ := famCellV_good δ (DA) χ (hin _ hV)
  obtain ⟨hcell, hrank⟩ := ComplJ8Walk.j8_cells_ok p Rg Rt hgen hleaf
  obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ hF) (n := (DA).cells.length)
    (le_two_pow_ht _ (by simp [sizesJ8]))
  refine ⟨ComplJ8Enc.cellChipHQKW_honest_listE δ b hC (powN (orbJ8 _ hF) _) (orbJ8 _ hF) (chalsMJ8 δ χ)
    (pubsCOf δ b _ hC (orbJ8 _ hF) χ) (by rw [hrc]; exact hp63) (γV δ χ) (ρV δ χ) (encR δ χ) (zJ δ χ) (bigOf _) _
    (mvF _) (mxF _)
    (fun _ => 0) (mhF _) hcell hrank rfl hinj hadj (ProbJ8.chalsOK_J8 δ χ) (InhabJ8MemMain.zJ_chals δ χ) hz
    (encR_cell δ χ) (encR_small δ hpG χ _)
    (fun j hj => (hrows j hj).1) (fun j hj _ => (hrows j hj).2.1) (fun j hj _ => (hrows j hj).2.2.1)
    (fun j hj => (hrows j hj).2.2.2.1) (fun j hj => (hrows j hj).2.2.2.2) ?_ ?_ ?_ ?_,
    ComplJ8Enc.cellChipHQKW_honest_list_bindE δ b hC _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  · exact (pub2_mk2 δ (cvT δ _ χ) 0 rfl).symm
  · exact (pub2_mk2 δ (cxT δ _ χ) 2 rfl).symm
  · intro i
    rw [dRowW_split]
    exact ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 _ χ _ (ComplJ8Bad.ρH_re δ χ)
      (hin _ hH _ (List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, rfl⟩))
  · show Quad.mk _ (pub2 δ (chT δ b _ hC (orbJ8 _ hF) χ) 4) (pub2 δ (chT δ b _ hC (orbJ8 _ hF) χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    unfold chT
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dNW_pubs δ b _ hC (orbJ8 _ hF) χ (pubsC0 δ _ χ) (pubsCOf δ b _ hC (orbJ8 _ hF) χ)]

theorem walkOK_runA (hp63 : 2 ^ 63 < p) (h31 : Rows31 (DA))
    (hwalk : ComplJ8Walk.WalkDepthOK (DA).reads)
    (hV : famWalkV δ (DA) ∈ fams) (hH : famWalkH δ (DA) ∈ fams)
    (χ : Coins frameJ8 K) (hχ : (honestJ8Of δ b (DA) hF hC hA AV fams).Good χ) :
    let B := honestJ8Of δ b (DA) hF hC hA AV fams
    (WalkJ8.walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).rap.Satisfies
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW) ∧
    (WalkJ8.walkChipJ8 δ B.Pb.kroots b B.Pb.hnW B.Pb.nodesW B.Pb.orbitW (chalsMJ8 δ χ) (B.M χ).pubsW).BindsPreprocessing
      (qW δ b B.Pb (B.tr χ) (chalsMJ8 δ χ) (B.M χ).pubsW) := by
  intro B
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(DA).t]).length)] fams),
      χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  have hmW : (walkRows (DA).cells (DA).reads).length ∈
      sizesJ8 (DA) := by simp [sizesJ8]
  obtain ⟨hinj, hadj⟩ := powN_ok (orbJ8 _ hF) (le_two_pow_ht _ hmW)
  have hrows := famWalkV_good δ (DA) χ (hin _ hV)
  have hcl : (DA).cells.length < ringChar (ZMod p) := by
    rw [hrc]; exact lt31 hp63 h31 (by simp [sizesJ8])
  have hkp : krW (DA).cells (DA).reads +
      (walkRows (DA).cells (DA).reads).length < ringChar (ZMod p) := by
    have := h31 _ hmW
    have := krW_le_rows (DA).cells (DA).reads
    have : (2 : ℕ) ^ 31 + 2 ^ 31 < 2 ^ 63 := by norm_num
    rw [hrc]; omega
  have hpoleH : ∀ (i : Fin (walkRows (DA).cells (DA).reads).length),
      ∀ x ∈ walkHx δ (DA) i (K := K), ComplJ8Bad.ρH δ χ + x χ ≠ 0 := by
    intro i x hx
    refine ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 x χ _ (ComplJ8Bad.ρH_re δ χ) (hin _ hH _ ?_)
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hsplit := walk_dRow_split δ b (DA) (orbJ8 _ hF) hinj χ
    (pubsWOf δ b (DA) (orbJ8 _ hF) χ)
  have hwalk' := ComplJ8Enc.walkChipJ8_honest_listE δ b (walk_pos _ _) (powN (orbJ8 _ hF) _) (orbJ8 _ hF)
    (chalsMJ8 δ χ) (pubsWOf δ b (DA) (orbJ8 _ hF) χ) (encR δ χ) (γV δ χ) (ρV δ χ) _ _ (kLW _) (vLW _) (kRW _) (vRW _)
    (GeneratedField.primeFieldElems_zmod p) (by rw [hrc]; exact hp63) hcl hwalk hkp rfl hinj hadj
    (ProbJ8.chalsOK_J8 δ χ) (fun j hj => (hrows j hj).1) (fun j hj => (hrows j hj).2.1)
    (fun j hj => (hrows j hj).2.2) (pub2_mk2 δ (wxT δ (DA) χ) 0 rfl).symm (pub2_mk2 δ (wpT δ (DA) χ) 2 rfl).symm
    (fun i => hdl_kind _ _ _) (fun i => hdl_kind _ _ _)
    (fun i => by
      rw [(hsplit i).1]
      exact hpoleH i (fun χ => recDen 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).idx, (kLW _ i, vLW _ i),
        (kRW _ i, vRW _ i))) (by simp only [walkHx, dif_pos i.isLt]; exact List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.1]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).ridx, 2 * (wValsC δ _ χ i).pre,
        (kLW _ i, vLW _ i))) (by simp only [walkHx, dif_pos i.isLt]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun i => by
      rw [(hsplit i).2.2]
      exact hpoleH i (fun χ => recDenP 0 (ComplJ8Bad.γH δ χ) ((wValsC δ _ χ i).ridx, 2 * (wValsC δ _ χ i).pre + 1,
        (kRW _ i, vRW _ i))) (by
          simp only [walkHx, dif_pos i.isLt]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    ?_ ?_
  · exact hwalk'
  · show Quad.mk _ (pub2 δ (whX δ b (DA) (orbJ8 _ hF) χ) 4) (pub2 δ (whX δ b (DA) (orbJ8 _ hF) χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b (DA) (orbJ8 _ hF) hinj χ (pubsW0 δ (DA) χ) (pubsWOf δ b (DA) (orbJ8 _ hF) χ) _ (Or.inl rfl)]
  · show Quad.mk _ (pub2 δ (whP δ b (DA) (orbJ8 _ hF) χ) 6) (pub2 δ (whP δ b (DA) (orbJ8 _ hF) χ) 7) = _
    rw [pub2_mk2 δ _ 6 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b (DA) (orbJ8 _ hF) hinj χ (pubsW0 δ (DA) χ) (pubsWOf δ b (DA) (orbJ8 _ hF) χ) _ (Or.inr (Or.inl rfl)),
      dN_pubs δ b (DA) (orbJ8 _ hF) hinj χ (pubsW0 δ (DA) χ) (pubsWOf δ b (DA) (orbJ8 _ hF) χ) _ (Or.inr (Or.inr rfl))]


/-! ### The J-9 A atom part (J-9 B's atom walk `avOf9` and the atom table `avOf`, both at `DA`) and the atom walk -/


abbrev AVA (hF : DvdOK (j9aDataOf p Rg Rt hgen)) (hA : 0 < (j9aDataOf p Rg Rt hgen).acs.length) : AVPart p K :=
  ComplJ9BBalF.avOf9 δ b (DA) hF (avOf δ b (DA) hF hA)

/-- **`awOK` at the J-9 A record**: at a coin outside
the bad list, with `famAWV9 DA`, `famAWH9 DA` in `fams`, the J-9 B atom walk accepts the honest atom-walk trace over
the J-9 A atom-walk reads.  Binders `hp63`, `h31 : Rows31 DA`, `hax9`, J-9 B's `hwalkA`. -/
theorem awOK_runA (hp63 : 2 ^ 63 < p) (h31 : Rows31 (DA)) (hax9 : ComplJ9ABinders.ProgAxOK9A p t)
    (hwalkA : ComplJ8Walk.WalkDepthOK (j8DataOf p Rg Rt hgen).preads)
    (hV : ComplJ9BBalF.famAWV9 δ (DA) ∈ fams) (hH : ComplJ9BBalF.famAWH9 δ (DA) ∈ fams)
    (χ : Coins frameJ8 K) (hχ : (honestJ8Of δ b (DA) hF hC hA (AVA δ b Rt hgen hF hA) fams).Good χ) :
    let B := honestJ8Of δ b (DA) hF hC hA (AVA δ b Rt hgen hF hA) fams
    AcceptsJ8V.AWChipOK δ b B.Pb.krootsV B.Pb.hnV B.Pb.nodesV B.Pb.orbitV (ChalsAZJ8.chalsAJ8Z δ χ)
      (B.M χ).pubsV (AcceptsJ8.qV δ b B.Pb (B.tr χ) (ChalsAZJ8.chalsAJ8Z δ χ) (B.M χ).pubsV) := by
  intro B
  have hg : ∀ e ∈ badOf (badList [(⟨13, by decide⟩, (bfsForest [(DA).t]).length)] fams), χ ∉ e.1 := hχ
  have hin : ∀ L ∈ fams, ∀ e ∈ L, χ ∉ e.ev := fun L hL e he =>
    ComplJ8Bad.good_spec hg (List.mem_append_right _ (List.mem_flatten.mpr ⟨L, hL, he⟩))
  exact ComplJ9BBalF.awOK_D9 δ b (DA) hF hp63 h31
    (ComplJ9ADataRec.walkDepthOK_preadsA Rt hgen hax9 hwalkA) hA χ (hin _ hV) (hin _ hH)

end Obl


/-! ## 3. The atom table at the J-9 A data, with no J-8 axis binder

`ComplJ9BAtom.atomOK_run9` takes J-8's `hax : ProgAxOK p t`, which J-9 A replaces by the weaker `hax9`.  Its only
use is `GenHyp`'s `ops` clause (`ComplJ8Atom.s4_row`: an OP4 row increments its operand), and that needs `SmallX`
at an OP4 row only, which is `True`.  So `genHypA` / `acs_okA` / `atomOK_mbA` are the J-8 / J-9 B proofs verbatim
with no run binder, and `atomOK_runA` is `atomOK_run9` at `DA` (whose `acs info mb` are `D9`'s). -/

section GenA
open Nock.V1J8.Gen
open Nock.Atoms (B val limbs)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom (internal_combOf spineOf_facts)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

/-- **An OP4 row of a generated run increments its operand**, with no run binder (`ComplJ8Atom.s4_row` asks for
`hax hop5` only to get `SmallX` at the row, which is `True` at an OP4 row). -/
theorem s4_rowA {R : Nock.Jet.Registry} {fuel : ℕ} {s f r : Noun} {t : NTree SkelX}
    (hgen : genX R fuel s f = some (t, r)) (q : ℕ)
    {x : RowNX} (hx : x ∈ (rowsOfT t).toList) (hst : x.st = .s4) :
    ∃ n, x.sf1 = .atom n ∧ x.e = .atom (n + 1) := by
  simp only [rowsOfT, List.toList_toArray, List.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  have hin : InTree t u := by
    obtain ⟨c, hc, h⟩ := (mem_bfsForest [t] u).mp hu
    simp at hc; subst hc; exact h
  have hsm : HonestRowX.SmallX q (rowOfSkelX u.label) := by
    unfold HonestRowX.SmallX; rw [hst]; trivial
  have hok := HonestRowX.rowOKX_of_genX hgen hin hsm
  simp only [HonestCompX.RowOKX, hst] at hok
  exact hok.2.2.2

variable (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **The run facts of a generated run** at Goldilocks (`GenHyp` of `j8DataOf`), with NO run binder (twin of `ComplJ8Atom.genHyp_j8`: its only binder use is `SmallX` at an OP4 row, which is `True`). -/
theorem genHypA (hN : (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31) :
    GenHyp (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs (j8DataOf Nock.Atoms.p Rg Rt hgen).dupP
      (j8DataOf Nock.Atoms.p Rg Rt hgen).rows (j8DataOf Nock.Atoms.p Rg Rt hgen).mb := by
  have hB : ∀ a, a ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs ↔
      a ∈ ((j8DataOf Nock.Atoms.p Rg Rt hgen).roots ++
        (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.toList.flatMap rowHandleNounsX).flatMap leavesOf ∧
        Nock.Atoms.p ≤ a :=
    fun a => mem_bigsP Nock.Atoms.p _ _ a
  have hrowB : ∀ x ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.toList, ∀ y ∈ rowHandleNounsX x, ∀ a ∈ leavesOf y,
      Nock.Atoms.p ≤ a → a ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs := by
    intro x hx y hy a ha hp
    exact (hB a).mpr ⟨List.mem_flatMap.mpr ⟨y, List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hy⟩), ha⟩, hp⟩
  refine ⟨fun a ha => ((hB a).mp ha).2, fun vc hvc => ?_, fun ⟨vc, hvc, hp⟩ => ?_, fun j hj hm => ?_, hN⟩
  · obtain ⟨x, hx, hst, hs1, hle⟩ := mem_incOpsP _ _ vc hvc
    obtain ⟨n, hn1, he⟩ := s4_rowA hgen Nock.Atoms.p hx hst
    rw [hs1] at hn1; cases hn1
    have hsf : x.sf1 ∈ rowHandleNounsX x := by simp [rowHandleNounsX]
    have hee : x.e ∈ rowHandleNounsX x := by simp [rowHandleNounsX]
    refine ⟨fun hp => hrowB x hx _ hee _ (by rw [he]; simp [leavesOf, hp]) (by omega), fun hp => ⟨?_, ?_⟩⟩
    · exact hrowB x hx _ hsf _ (by rw [hs1]; simp [leavesOf]) (by omega)
    · exact hrowB x hx _ hee _ (by rw [he]; simp [leavesOf]) hle
  · show (incOpsP Nock.Atoms.p (rowsOfT t)).any (fun x => x.1 + 1 = Nock.Atoms.p) = true
    exact List.any_eq_true.mpr ⟨vc, hvc, by simp [hp]⟩
  · rw [mb_eq_cnt Nock.Atoms.p Rg Rt hgen j hj] at hm
    obtain ⟨q, hq, hq0⟩ : ∃ q ∈ ((mbRecs (j8DataOf Nock.Atoms.p Rg Rt hgen)).flatMap NamedRecs.recs).filter
        (fun q => q.1 = j), q.2 ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_and, ne_eq, not_not] at hc
      apply hm
      unfold cnt
      exact List.sum_eq_zero fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact hc q hq
    simp only [List.mem_filter, decide_eq_true_eq] at hq
    obtain ⟨hq, rfl⟩ := hq
    simp only [mbRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_filterMap,
      Option.map_eq_some_iff] at hq
    obtain ⟨n, hn, i, hi, rfl⟩ := hq
    obtain ⟨c, hc, hnc⟩ := List.mem_flatMap.mp hn
    cases n with
    | cell u w => simp [bigIdOfP] at hi
    | atom a =>
      simp only [bigIdOfP] at hi
      split_ifs at hi with hlt
      cases hi
      refine ⟨a, (hB a).mpr ⟨?_, by omega⟩, rfl⟩
      have hla : a ∈ leavesOf c := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hnc
        cases c with
        | atom b => rcases hnc with h | h <;> simp [hdN', tlN'] at h <;> subst h <;> simp [leavesOf]
        | cell u w => rcases hnc with h | h <;> simp [hdN', tlN'] at h <;> subst h <;> simp [leavesOf]
      have := leaves_cellsOfRoots _ c hc a hla
      exact List.mem_flatMap.mpr (by
        obtain ⟨y, hy, hay⟩ := List.mem_flatMap.mp this
        exact ⟨y, List.mem_append_left _ hy, hay⟩)

/-- **The atom cell list of a generated run** (Goldilocks; twin of `ComplJ8OfAtom.acs_ok` with no run binder): every row is a cell, has rank `< 2^110` (from
`|acs| ≤ 2^31`: a spine's rows are distinct members of `acs`, so a comb has at most `|acs| + 1` limbs), and the
tail of a row is a row when it is a cell. -/
theorem acs_okA
    (hN : (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31)
    (h31 : (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length ≤ 2 ^ 31) :
    (∀ c ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).acs, c.isCell = true) ∧
    (∀ c ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).acs, rankOf c < 2 ^ 110) ∧
    (∀ c ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).acs, (tlN' c).isCell = true →
      tlN' c ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).acs) := by
  have hg := genHypA Rg Rt hgen hN
  have hsp : ∀ a ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs, ∀ x ∈ spineOf (Nock.Atoms.limbs a),
      x ∈ (j8DataOf Nock.Atoms.p Rg Rt hgen).acs := fun a ha x hx =>
    (mem_acsP _ _ x).mpr (Or.inl ((mem_spineL _ x).mpr ⟨a, ha, hx⟩))
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc htl => ?_⟩
  · obtain ⟨l, h2, -, hy, -⟩ := shape_acsP _ _ hg.big c hc
    rw [hy]; exact combOf_isCell l h2
  · obtain ⟨l, h2, -, hy, h3⟩ := shape_acsP _ _ hg.big c hc
    show c.internal < 2 ^ 110
    have e := internal_combOf l h2
    rw [hy]
    by_cases hl : 3 ≤ l.length
    · obtain ⟨-, a, ha, d, rfl⟩ := h3 hl
      have hs := len_le_of_sub (spineOf_facts (Nock.Atoms.limbs a)).1 (hsp a ha)
      have h4 := (spineOf_facts (Nock.Atoms.limbs a)).2
      have h5 : ((Nock.Atoms.limbs a).drop d).length ≤ (Nock.Atoms.limbs a).length := by
        rw [List.length_drop]; omega
      have : (2 : ℕ) ^ 31 + 2 < 2 ^ 110 := by norm_num
      omega
    · have : (2 : ℕ) < 2 ^ 110 := by norm_num
      omega
  · obtain ⟨l, h2, -, hy, h3⟩ := shape_acsP _ _ hg.big c hc
    rw [hy, tl_combOf l h2] at htl ⊢
    by_cases hl : 3 ≤ l.length
    · rw [if_pos hl]
      obtain ⟨-, a, ha, d, rfl⟩ := h3 hl
      refine hsp a ha _ ((mem_spineOf _ _).mpr ⟨d + 1, ?_, ?_⟩)
      · rw [List.length_drop] at hl ⊢; omega
      · rw [List.tail_drop]
    · rw [if_neg hl] at htl; simp [Noun.isCell] at htl

/-- `GenHyp` at J-9 B's claim-bumped `mb` (`ComplJ9BAtom.genHyp_mbX` at `L = [s, f, r]`), with no run binder. -/
theorem genHyp_mbXA (hN : (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31) :
    GenHyp (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs (j8DataOf Nock.Atoms.p Rg Rt hgen).dupP
      (j8DataOf Nock.Atoms.p Rg Rt hgen).rows (ComplJ9BAtom.mbX (j8DataOf Nock.Atoms.p Rg Rt hgen) [s, f, r]) :=
  have hg := genHypA Rg Rt hgen hN
  ⟨hg.big, hg.ops, hg.dup, ComplJ9BAtom.mbX_roots Nock.Atoms.p Rg Rt hgen [s, f, r]
    (fun a ha hp => ComplJ9BAtom.claim_leaf_big Nock.Atoms.p Rg Rt hgen ha a (by simp [leavesOf]) hp) hg.mb, hN⟩

/-- **The rows bound from `Rows31 DA`** (`ComplJ8OfAtom.rows_le_of_rows31` at the J-9 A data, whose `t` is `j8DataOf`'s). -/
theorem rows_leA (h31 : Rows31 (j9aDataOf Nock.Atoms.p Rg Rt hgen)) :
    (j8DataOf Nock.Atoms.p Rg Rt hgen).rows.size ≤ 2 ^ 31 := by
  have h : (bfsForest [(j8DataOf Nock.Atoms.p Rg Rt hgen).t]).length ≤ 2 ^ 31 :=
    h31 _ (by simp [sizesJ8, j9aDataOf, ComplJ9BOf.j9DataOf])
  rw [ComplJ8BigBound.data_rows hgen]
  simpa [ComplJ8Data.rowsOfT, j8DataOf] using h

end GenA

section AtomMbA
open Nock.V1J8.Gen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (atomChipHQ pubMB pubC pubMI mb inc mi)

variable {K : Type} [Field K] [Algebra (ZMod Nock.Atoms.p) K] [FiniteDimensional (ZMod Nock.Atoms.p) K]
  [Fintype K] (δ : ZMod Nock.Atoms.p) [Fact (¬ IsSquare (algebraMap (ZMod Nock.Atoms.p) K δ))]
  (b : Basis (Fin 3) (ZMod Nock.Atoms.p) K)
  (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  {hA : ℕ} (hn : 0 < (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length)
  (nodes : Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length → ZMod Nock.Atoms.p)
  (orbit : StrictOrbitDomain (ZMod Nock.Atoms.p) 3 hA) (chals pubs : ℕ → K)
  (col : ℕ → Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length → ZMod Nock.Atoms.p) (mbA : Array ℕ)

/-- **`ComplJ9BAtom.atomOK_mb` without its two unused run binders** (verbatim proof): L3's `atomOK_j8` at a generic `mb` whose nonzero entries are big roots (`hmb`; the J-9 B claim-bumped
`mbX` meets it, `genHyp_mbX`).  No limb count is assumed anywhere (`valid_gen` covers every big atom). -/
theorem atomOK_mbA
    (hmb : ComplJ8Atom.GenHyp (j8DataOf Nock.Atoms.p Rg Rt hgen).bigs (j8DataOf Nock.Atoms.p Rg Rt hgen).dupP
      (j8DataOf Nock.Atoms.p Rg Rt hgen).rows mbA)
    (hinj : Function.Injective nodes)
    (hadj : ∀ (i : Fin _) (hi : (i : ℕ) + 1 < (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length),
      nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (hcol : ∀ i : Fin (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      let y := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs[(i : ℕ)]
      col Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      col Cell.idR i = (((if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (j8DataOf Nock.Atoms.p Rg Rt hgen).acs
          (j8DataOf Nock.Atoms.p Rg Rt hgen).rows y else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.wL i = (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.wR i = (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      col Cell.aL i = ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      col Cell.aR i = ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p))
    (hsat0 : (cellChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies (honestQ hn nodes col _))
    (hz1 : ∀ i, HonestA8.dMB δ b hn nodes orbit chals pubs col (newOf (ComplJ9BAtom.rowsMb Rg Rt hgen mbA)) i ≠ 0)
    (hz2 : ∀ i, HonestA8.dC δ b hn nodes orbit chals pubs col (newOf (ComplJ9BAtom.rowsMb Rg Rt hgen mbA)) i ≠ 0)
    (hz3 : ∀ i, HonestA8.dMI δ b hn nodes orbit chals pubs col (newOf (ComplJ9BAtom.rowsMb Rg Rt hgen mbA)) i ≠ 0)
    (hpMB : Quad.mk _ (pubs pubMB) (pubs (pubMB + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (ComplJ9BAtom.rowsMb Rg Rt hgen mbA) mb)) *
        (HonestA8.dNat δ (HonestA8.dMB δ b hn nodes orbit chals pubs col (newOf (ComplJ9BAtom.rowsMb Rg Rt hgen mbA))) j)⁻¹)
    (hpC : Quad.mk _ (pubs pubC) (pubs (pubC + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (ComplJ9BAtom.rowsMb Rg Rt hgen mbA) inc)) *
        (HonestA8.dNat δ (HonestA8.dC δ b hn nodes orbit chals pubs col (newOf (ComplJ9BAtom.rowsMb Rg Rt hgen mbA))) j)⁻¹)
    (hpMI : Quad.mk _ (pubs pubMI) (pubs (pubMI + 1)) = ∑ j ∈ Finset.range (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      liftQ δ (HonestA8.cNat j (newOf (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) (ComplJ9BAtom.rowsMb Rg Rt hgen mbA) mi)) *
        (HonestA8.dNat δ (HonestA8.dMI δ b hn nodes orbit chals pubs col (newOf (ComplJ9BAtom.rowsMb Rg Rt hgen mbA))) j)⁻¹) :
    (atomChipHQ δ b hn nodes orbit chals pubs).rap.Satisfies
        (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (ComplJ9BAtom.rowsMb Rg Rt hgen mbA))) ∧
      (atomChipHQ δ b hn nodes orbit chals pubs).BindsPreprocessing
        (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (ComplJ9BAtom.rowsMb Rg Rt hgen mbA))) ∧
      (AtomChipHQL.atomChipHQL δ b hn nodes orbit chals pubs).rap.Satisfies
        (AtomChipHQL.ofHQ δ b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (ComplJ9BAtom.rowsMb Rg Rt hgen mbA)))) ∧
      (AtomChipHQL.atomChipHQL δ b hn nodes orbit chals pubs).BindsPreprocessing
        (AtomChipHQL.ofHQ δ b hn nodes orbit chals pubs
          (HonestA8.atomTraceHQ δ b hn nodes orbit chals pubs col (newOf (ComplJ9BAtom.rowsMb Rg Rt hgen mbA)))) := by
  have hv : (tabOf (j8DataOf Nock.Atoms.p Rg Rt hgen).acs (j8DataOf Nock.Atoms.p Rg Rt hgen).info mbA
      (j8DataOf Nock.Atoms.p Rg Rt hgen).rows).Valid :=
    valid_gen _ _ _ _ hmb
  obtain ⟨hok, hlast⟩ := AtomTab.rows_ok hv (n := (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length) rfl
  have hB : Nock.Atoms.B < ringChar (ZMod Nock.Atoms.p) := by
    rw [ZMod.ringChar_zmod_n]; exact Nock.Atoms.B_lt_p
  refine atomOK_of_rows δ b hn nodes orbit chals pubs col hinj hadj hB (ComplJ9BAtom.rowsMb Rg Rt hgen mbA) (fun i => ?_) hok hlast
    hsat0 hz1 hz2 hz3 hpMB hpC hpMI
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcol i
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := row_cell _ _ _ _ hmb (j8DataOf Nock.Atoms.p Rg Rt hgen).info i i.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c1]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e1.symm
  · rw [c2]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e6.symm
  · rw [c3]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e4.symm
  · rw [c4]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e5.symm
  · rw [c5]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e2.symm
  · rw [c6]; exact congrArg (fun x : ℕ => (x : ZMod Nock.Atoms.p)) e3.symm

end AtomMbA

section AtomRunA
open Nock.V1J8.Gen (hdN' tlN' atomV)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DA" => j9aDataOf p Rg Rt hgen

/-- **`atomOK` at the J-9 A data** (twin of `ComplJ9BAtom.atomOK_run9` at `L = [s, f, r]`, the data `D9` swapped for
`j9aDataOf`, which has the same `acs info mb`): at a coin outside the six atom pole families of `DA`, the honest
atom trace at `DA` is accepted and bound by `atomChipHQ` and `atomChipHQL`.  Binders: `hpG h31` (`Rows31 DA`),
; no J-8 axis / op-5 binder (`genHypA`, `acs_okA`, `atomOK_mbA`). -/
theorem atomOK_runA (hpG : p = Nock.Atoms.p)
    (hF : DvdOK (DA)) (hA : 0 < (DA).acs.length) (h31 : Rows31 (DA))
    (χ : Coins frameJ8 K)
    (gZ : ∀ e ∈ famAZ (K := K), χ ∉ e.ev) (gV : ∀ e ∈ famAV δ (DA) (K := K), χ ∉ e.ev)
    (gH : ∀ e ∈ famAH δ b (DA) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev)
    (gMB : ∀ e ∈ famMB δ b (DA) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev)
    (gC : ∀ e ∈ famC δ b (DA) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev)
    (gMI : ∀ e ∈ famMI δ b (DA) hA (orbJ8 _ hF) (K := K), χ ∉ e.ev) :
    let o := orbJ8 (DA) hF
    let P := pubsAOf δ b (DA) hA o χ
    let tr := HonestA8.atomTraceHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P (colAH δ b (DA) hA o χ P)
      (newBA (DA))
    (AtomChipHQ.atomChipHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P).rap.Satisfies tr ∧
    (AtomChipHQ.atomChipHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P).BindsPreprocessing tr ∧
    (atomChipHQL δ b hA (powN o _) o (chalsAJ8Z δ χ) P).rap.Satisfies
      (AtomChipHQL.ofHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P tr) ∧
    (atomChipHQL δ b hA (powN o _) o (chalsAJ8Z δ χ) P).BindsPreprocessing
      (AtomChipHQL.ofHQ δ b hA (powN o _) o (chalsAJ8Z δ χ) P tr) := by
  intro o P tr
  subst hpG
  have hz := famAZ_good δ χ gZ
  have hv := famAV_good δ (j9aDataOf Nock.Atoms.p Rg Rt hgen) χ gV
  obtain ⟨hpH, hpMB, hpC, hpMI⟩ := atomPoles_good δ b (j9aDataOf Nock.Atoms.p Rg Rt hgen) hA o χ gH gMB gC gMI P
  have hmA : (j8DataOf Nock.Atoms.p Rg Rt hgen).acs.length ∈ sizesJ8 (j8DataOf Nock.Atoms.p Rg Rt hgen) := by
    simp [sizesJ8]
  have hmA9 : (j9aDataOf Nock.Atoms.p Rg Rt hgen).acs.length ∈ sizesJ8 (j9aDataOf Nock.Atoms.p Rg Rt hgen) := by simp [sizesJ8]
  have hN := rows_leA Rg Rt hgen h31
  obtain ⟨hcell, hrank, htl⟩ := acs_okA Rg Rt hgen hN (h31 _ hmA9)
  obtain ⟨hinj, hadj⟩ := powN_ok o (le_two_pow_ht _ hmA9)
  obtain ⟨tV, tX, tH, tMB, tC, tMI⟩ := atomTerms δ b (j9aDataOf Nock.Atoms.p Rg Rt hgen) hA o χ
  have hsat0 := ComplJ8Cell.cellChipHQ_honest_listP δ b hA (powN o _) o (chalsAJ8Z δ χ) P (γV δ χ) (ρV δ χ)
    (zA δ χ) (fun _ => none) (j9aDataOf Nock.Atoms.p Rg Rt hgen).acs (mvA _) (mxAF _) (fun _ => 0) (ptA _) (mhvA _) hcell hrank rfl hinj hadj
    (ChalsAZJ8.chalsAJ8Z_ok δ χ) rfl hz (fun j hj => (hv j hj).1) (fun j hj _ => (hv j hj).2.1)
    (fun j hj _ => (hv j hj).2.2.1) (fun j hj => (hv j hj).2.2.2.1) (fun j hj => (hv j hj).2.2.2.2)
    tV tX hpH tH
  have hcol : ∀ i : Fin (j9aDataOf Nock.Atoms.p Rg Rt hgen).acs.length,
      let y := (j9aDataOf Nock.Atoms.p Rg Rt hgen).acs[(i : ℕ)]
      colAH δ b _ hA o χ P Cell.idx i = ((i : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.idR i =
        (((if (tlN' y).isCell then ComplJ8Data.ptrP Nock.Atoms.p (j9aDataOf Nock.Atoms.p Rg Rt hgen).acs
            (j9aDataOf Nock.Atoms.p Rg Rt hgen).rows y else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.wL i = (((if (hdN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.wR i = (((if (tlN' y).isCell then 1 else 0 : ℕ)) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.aL i = ((atomV (hdN' y) : ℕ) : ZMod Nock.Atoms.p) ∧
      colAH δ b _ hA o χ P Cell.aR i = ((atomV (tlN' y) : ℕ) : ZMod Nock.Atoms.p) := by
    intro i y
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := colAH_fields δ b (j9aDataOf Nock.Atoms.p Rg Rt hgen) hA o χ P i
    refine ⟨c1, ?_, c3, c4, c5, c6⟩
    rw [c2]
    by_cases hc : (tlN' y).isCell = true
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]; simp
  exact atomOK_mbA δ b Rg Rt hgen hA (powN o _) o (chalsAJ8Z δ χ) P (colAH δ b (j9aDataOf Nock.Atoms.p Rg Rt hgen) hA o χ P)
    (ComplJ9BAtom.mbX (j8DataOf Nock.Atoms.p Rg Rt hgen) [s, f, r]) (genHyp_mbXA Rg Rt hgen hN) hinj hadj hcol hsat0
    hpMB hpC hpMI tMB tC tMI

end AtomRunA

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ATables

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ATables
#print axioms cellOK_runA
#print axioms walkOK_runA
#print axioms awOK_runA
#print axioms s4_rowA
#print axioms genHypA
#print axioms acs_okA
#print axioms atomOK_mbA
#print axioms atomOK_runA
end Axioms
