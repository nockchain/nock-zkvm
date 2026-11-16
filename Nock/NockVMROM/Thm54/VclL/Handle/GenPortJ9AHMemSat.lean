/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHMemSat.lean

* The nodes are `powN o n` (the exec nodes `ω^i`), with `hinj hadj` taken as hypotheses (the J-9 A lemmas get them
    from `powN_ok` and `n ≤ 2^h`; here only `Injective (powN o n)` and the adjacency are needed).
  * The coin hypothesis is the family-wise `∀ e ∈ fam, χ ∉ e.ev` (what `Good χ` gives through
    `ComplJ8Bad.good_spec`), so no `fams`, `AV`, `hF`, `hA` binders.
  * The trace is `cellTrME` / `walkTrWE` / `trJ` at the orbit `o`, i.e. the J-8 trace `trOf` with its compute-part orbit
    replaced; the publics are `pubsCOf … o`, `pubsWOf … o`, `pubsJOf`.
  Statements `*_at`; no row beyond `n` is mentioned.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ATables

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMemSat

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
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ATables (lt31)

noncomputable section

section Obl
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

/-- **`cellOK_runA` at an arbitrary orbit `o`** (nodes `powN o n`, `hinj hadj` as hypotheses). -/
theorem cellOK_run_at (hC : 0 < (j9aDataOf p Rg Rt hgen).cells.length)
    (hpG : p = Nock.Atoms.p) (hp63 : 2 ^ 63 < p)
    (hleaf : ComplJ8Walk.RootsLeafOK (j8DataOf p Rg Rt hgen).roots)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (DA).cells.length))
    (hadj : ∀ (i : Fin (DA).cells.length) (hi : (i : ℕ) + 1 < (DA).cells.length),
      powN o (DA).cells.length ⟨(i : ℕ) + 1, hi⟩ = powN o (DA).cells.length i * o.ω)
    (χ : Coins frameJ8 K)
    (hV : ∀ e ∈ famCellV δ (DA) (K := K), χ ∉ e.ev)
    (hH : ∀ e ∈ famCellH δ b (DA) hC o (K := K), χ ∉ e.ev) :
    (CellTwinKW.cellChipHQKW δ b hC (powN o (DA).cells.length) o (chalsMJ8 δ χ)
        (pubsCOf δ b (DA) hC o χ)).rap.Satisfies
      (ComplJ8Enc.cellTrME δ b hC (powN o (DA).cells.length) o (chalsMJ8 δ) (pubsCOf δ b (DA) hC o)
        (γV δ) (ρV δ) (zJ δ) (encR δ) (bigOf (DA)) (DA).cells (mvF (DA)) (mxF (DA)) (fun _ => 0) (mhF (DA)) χ) ∧
    (CellTwinKW.cellChipHQKW δ b hC (powN o (DA).cells.length) o (chalsMJ8 δ χ)
        (pubsCOf δ b (DA) hC o χ)).BindsPreprocessing
      (ComplJ8Enc.cellTrME δ b hC (powN o (DA).cells.length) o (chalsMJ8 δ) (pubsCOf δ b (DA) hC o)
        (γV δ) (ρV δ) (zJ δ) (encR δ) (bigOf (DA)) (DA).cells (mvF (DA)) (mxF (DA)) (fun _ => 0) (mhF (DA)) χ) := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  obtain ⟨hz, hrows⟩ := famCellV_good δ (DA) χ hV
  obtain ⟨hcell, hrank⟩ := ComplJ8Walk.j8_cells_ok p Rg Rt hgen hleaf
  refine ⟨ComplJ8Enc.cellChipHQKW_honest_listE δ b hC (powN o _) o (chalsMJ8 δ χ)
    (pubsCOf δ b _ hC o χ) (by rw [hrc]; exact hp63) (γV δ χ) (ρV δ χ) (encR δ χ) (zJ δ χ) (bigOf _) _
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
      (hH _ (List.mem_map.mpr ⟨i, List.mem_range.mpr i.isLt, rfl⟩))
  · show Quad.mk _ (pub2 δ (chT δ b _ hC o χ) 4) (pub2 δ (chT δ b _ hC o χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    unfold chT
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dNW_pubs δ b _ hC o χ (pubsC0 δ _ χ) (pubsCOf δ b _ hC o χ)]

/-- **`walkOK_runA` at an arbitrary orbit `o`** (nodes `powN o n`, `hinj hadj` as hypotheses). -/
theorem walkOK_run_at (hp63 : 2 ^ 63 < p) (h31 : Rows31 (DA))
    (hwalk : ComplJ8Walk.WalkDepthOK (DA).reads)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : Function.Injective (powN o (walkRows (DA).cells (DA).reads).length))
    (hadj : ∀ (i : Fin (walkRows (DA).cells (DA).reads).length)
      (hi : (i : ℕ) + 1 < (walkRows (DA).cells (DA).reads).length),
      powN o (walkRows (DA).cells (DA).reads).length ⟨(i : ℕ) + 1, hi⟩ =
        powN o (walkRows (DA).cells (DA).reads).length i * o.ω)
    (χ : Coins frameJ8 K)
    (hV : ∀ e ∈ famWalkV δ (DA) (K := K), χ ∉ e.ev)
    (hH : ∀ e ∈ famWalkH δ (DA) (K := K), χ ∉ e.ev) :
    (WalkJ8.walkChipJ8 δ (krW (DA).cells (DA).reads) b (walk_pos (DA).cells (DA).reads)
        (powN o (walkRows (DA).cells (DA).reads).length) o (chalsMJ8 δ χ) (pubsWOf δ b (DA) o χ)).rap.Satisfies
      (fun j => ComplJ8Enc.walkTrWE δ b (walk_pos (DA).cells (DA).reads)
        (powN o (walkRows (DA).cells (DA).reads).length) o (chalsMJ8 δ) (pubsWOf δ b (DA) o) (γV δ) (ρV δ)
        (encR δ) (DA).cells (DA).reads (kLW (DA)) (vLW (DA)) (kRW (DA)) (vRW (DA)) χ
        (Fin.cast (WalkJ8.walkChipJ8_width δ (krW (DA).cells (DA).reads) b (walk_pos (DA).cells (DA).reads)
          (powN o (walkRows (DA).cells (DA).reads).length) o (chalsMJ8 δ χ) (pubsWOf δ b (DA) o χ)) j)) ∧
    (WalkJ8.walkChipJ8 δ (krW (DA).cells (DA).reads) b (walk_pos (DA).cells (DA).reads)
        (powN o (walkRows (DA).cells (DA).reads).length) o (chalsMJ8 δ χ) (pubsWOf δ b (DA) o χ)).BindsPreprocessing
      (fun j => ComplJ8Enc.walkTrWE δ b (walk_pos (DA).cells (DA).reads)
        (powN o (walkRows (DA).cells (DA).reads).length) o (chalsMJ8 δ) (pubsWOf δ b (DA) o) (γV δ) (ρV δ)
        (encR δ) (DA).cells (DA).reads (kLW (DA)) (vLW (DA)) (kRW (DA)) (vRW (DA)) χ
        (Fin.cast (WalkJ8.walkChipJ8_width δ (krW (DA).cells (DA).reads) b (walk_pos (DA).cells (DA).reads)
          (powN o (walkRows (DA).cells (DA).reads).length) o (chalsMJ8 δ χ) (pubsWOf δ b (DA) o χ)) j)) := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hmW : (walkRows (DA).cells (DA).reads).length ∈ sizesJ8 (DA) := by simp [sizesJ8]
  have hrows := famWalkV_good δ (DA) χ hV
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
    refine ComplJ8Bad.quadPole_ne δ InhabJ8Good.c12 x χ _ (ComplJ8Bad.ρH_re δ χ) (hH _ ?_)
    exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hsplit := walk_dRow_split δ b (DA) o hinj χ
    (pubsWOf δ b (DA) o χ)
  have hwalk' := ComplJ8Enc.walkChipJ8_honest_listE δ b (walk_pos _ _) (powN o _) o
    (chalsMJ8 δ χ) (pubsWOf δ b (DA) o χ) (encR δ χ) (γV δ χ) (ρV δ χ) _ _ (kLW _) (vLW _) (kRW _) (vRW _)
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
  · show Quad.mk _ (pub2 δ (whX δ b (DA) o χ) 4) (pub2 δ (whX δ b (DA) o χ) 5) = _
    rw [pub2_mk2 δ _ 4 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b (DA) o hinj χ (pubsW0 δ (DA) χ) (pubsWOf δ b (DA) o χ) _ (Or.inl rfl)]
  · show Quad.mk _ (pub2 δ (whP δ b (DA) o χ) 6) (pub2 δ (whP δ b (DA) o χ) 7) = _
    rw [pub2_mk2 δ _ 6 rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold wdN
    rw [dN_pubs δ b (DA) o hinj χ (pubsW0 δ (DA) χ) (pubsWOf δ b (DA) o χ) _ (Or.inr (Or.inl rfl)),
      dN_pubs δ b (DA) o hinj χ (pubsW0 δ (DA) χ) (pubsWOf δ b (DA) o χ) _ (Or.inr (Or.inr rfl))]

/-- **The J chip, absent case at any orbit** (`jOK_absent` at `DA`: no jet row, the four J publics are `0`). -/
theorem jOK_absent_at (h0 : (DA).jrows.length = 0) (χ : Coins frameJ8 K)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (PJ : Fin (Nock.Jet.ChipJ8.jetChipJ8 δ b (powN o (DA).jrows.length) o (chalsJJ8 χ) (pubsJOf δ (DA) χ)
      (Nock.Jet.ChipJ8T.HonestRAP.layJ (DA).jrows.get)).rap.w → Polynomial (ZMod p)) :
    JGenJ8.JChipOK δ b (powN o (DA).jrows.length) o (chalsJJ8 χ) (pubsJOf δ (DA) χ)
      (Nock.Jet.ChipJ8T.HonestRAP.layJ (DA).jrows.get) PJ := by
  refine ComplJ8Jet.jOK_absent δ b _ _ _ _ _ _ h0 ?_
  have hs : ∀ (g : Fin (DA).jrows.length → Quad (algebraMap (ZMod p) K δ)), ∑ k, g k = 0 := by
    intro g; exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
  have hz : Quad.re _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 ∧ Quad.im _ (0 : Quad (algebraMap (ZMod p) K δ)) = 0 :=
    (Quad.mk_eq_zero_iff _ _ _).mp (Quad.mk_re_im _ 0)
  have e : ∀ i, pubsJOf δ (DA) χ i = 0 := by
    intro i
    unfold pubsJOf
    rw [hs, hs]
    split_ifs <;> simp [pub2, hz.1, hz.2]
  exact ⟨e 0, e 1, e 2, e 3⟩

/-- **`jOK_A8` at an arbitrary orbit `o`** (J-9 B's `jOK_run9` at `DA`; nodes `powN o n`, `hinj hadj` as hypotheses,
used only when the J table is present). -/
theorem jOK_at
    (hRt : ∀ id ∈ ComplJ8Jet.CalledIds t, Rg.R id = some ⟨(Rt id).toTemplate p, Nock.Jet.Autogen.compile p (Rt id)⟩ ∧
      Nock.Jet.ChipJ8.axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    {h : ℕ} (o : StrictOrbitDomain (ZMod p) 3 h)
    (hinj : 0 < (DA).jrows.length → Function.Injective (powN o (DA).jrows.length))
    (hadj : 0 < (DA).jrows.length → ∀ (i : Fin (DA).jrows.length) (hi : (i : ℕ) + 1 < (DA).jrows.length),
      powN o (DA).jrows.length ⟨(i : ℕ) + 1, hi⟩ = powN o (DA).jrows.length i * o.ω)
    (χ : Coins frameJ8 K)
    (hJ : ∀ e ∈ famJ δ (DA) (K := K), χ ∉ e.ev) :
    JGenJ8.JChipOK δ b (powN o (DA).jrows.length) o (chalsJJ8 χ) (pubsJOf δ (DA) χ)
      (Nock.Jet.ChipJ8T.HonestRAP.layJ (DA).jrows.get)
      (fun j => ComplJ8Jet.trJ δ b (powN o (DA).jrows.length) (chalsJJ8 χ) (DA).jrows.get
        (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width δ b (powN o (DA).jrows.length) o (chalsJJ8 χ)
          (pubsJOf δ (DA) χ) (Nock.Jet.ChipJ8T.HonestRAP.layJ (DA).jrows.get)) j)) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases h0 : (DA).jrows.length = 0
  · exact jOK_absent_at δ b Rt hgen h0 χ o _
  · have hn : 0 < (DA).jrows.length := Nat.pos_of_ne_zero h0
    have hpole := ComplJ8Bad.jNoPole δ (ComplJ8Jet.jKeysT (DA).jrows.get)
      (ComplJ8Jet.jKeysX (DA).jrows.get) χ hJ
    exact ComplJ8Jet.jOK_present_trJ δ b (powN o _) o (chalsJJ8 χ) (pubsJOf δ _ χ)
      (DA).jrows.get (hinj hn) hn (hadj hn)
      (fun i => ComplJ8Jet.jrows_gate_run Rt hgen hp hRt _ (List.get_mem _ _))
      (ComplJ8Jet.notJPole_of_keys δ _ _ hpole.1 hpole.2)
      (by simp only [pubsJOf]; exact pub2_mk δ _)
      (by simp only [pubsJOf]; simp [pub2, Quad.mk_re_im])

end Obl

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMemSat

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHMemSat
#print axioms cellOK_run_at
#print axioms walkOK_run_at
#print axioms jOK_absent_at
#print axioms jOK_at
end Axioms
