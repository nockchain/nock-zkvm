/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AOf.lean

* The new chips, in the concrete form of the record's fields (`axOnA`, `nXA_pos`, `powN oA`, `pubsXA`, `trXA`;
    resp. the split's): `axOK_A` (`axChipOK_honest` when present, the zero publics when absent), `spOK_A`
    (`spChipOK_honest` / zero publics).  Pitfall (measured): rewrite `pubsXA` / `pubsSA` with `rw` (every
    occurrence, incl. the `Fin.cast` width proofs), never `simp only` — a leftover instance forces a whnf of the chip
    width and times out.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ARun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOf

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8 (cJ HonestJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Bad (BadSpec badOf badList)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 genX9T rowsOfT9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData (fieldAx9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axKeys9 axChains9 splitVals9)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AXChipOK SPChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AObl (HonestJ9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun

noncomputable section

section Chips
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (hpG : p = Nock.Atoms.p) (h31A : Rows31A (j9aDataOf p Rg Rt hgen))

local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "BA" => BRun9A δ b Rt hgen hpG h31A

include hpG in
theorem hp63_A : 2 ^ 63 < p := by rw [hpG]; simp [Nock.Atoms.p, Nock.Field.p]

/-! ### The axis chip -/

/-- **`AXChipOK` at the run's axis part** (concrete form: the record's `axOn hnX nodesX orbitX pubsX` and trace `X`
are these by definition). -/
theorem axOK_A (χ : Coins frameJ8 K) (hχ : (BA).Good χ) :
    AXChipOK δ b (axOnA t) (nXA_pos (p := p) Rt hgen) (powN (oA Rt hgen hpG h31A) (nXA (p := p) Rt hgen))
      (oA Rt hgen hpG h31A) (chalsMJ8 δ χ) (pubsXA δ Rt hgen χ)
      (fun j => trXA δ b Rt hgen hpG h31A χ (Fin.cast (AxisChipJ9.width_eq δ b _ _ _ _ _) j)) := by
  cases h : axOnA t with
  | true =>
    have hP : pubsXA δ Rt hgen χ = ComplJ9AChipsOK.pubsXOf δ (nXA_pos (p := p) Rt hgen)
        (csA p (DA).acs.length (DA).H t) (nXA_eq (p := p) Rt hgen h) χ := by
      unfold pubsXA; rw [dif_pos h]
    have hT : trXA δ b Rt hgen hpG h31A χ = fun j =>
        ComplJ9AAxisH.polyAx δ b (nXA_pos (p := p) Rt hgen) (powN (oA Rt hgen hpG h31A) (nXA (p := p) Rt hgen))
          (oA Rt hgen hpG h31A) (chalsMJ8 δ χ) (pubsXA δ Rt hgen χ)
          (ComplJ9AAxisRows.tableCol (ComplJ9AAxisRows.tableRows (csA p (DA).acs.length (DA).H t))
            (nXA_pos (p := p) Rt hgen) (nXA_eq (p := p) Rt hgen h)) j := by
      unfold trXA; rw [dif_pos h]; rfl
    have hcs := ComplJ9AChainsRun.axChains9_OK (p0 := p) (DA).acs.length (DA).H hgen hpG
      (fun a c => (ComplJ8CompRun.hH_run (p := p) Rt hgen).cell a c)
    have hn : nXA (p := p) Rt hgen ≤ 2 ^ htA (DA) := by
      have := le_two_pow_htA _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self) :
        nXOf p (DA).acs.length (DA).H (DA).t ∈ sizesA (DA))
      rwa [ComplJ9ADataRec.j9aDataOf_t] at this
    obtain ⟨hinj, hadj⟩ := powN_ok (oA Rt hgen hpG h31A) hn
    have hnp : nXA (p := p) Rt hgen < p := by
      have := h31A _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self) :
        nXOf p (DA).acs.length (DA).H (DA).t ∈ sizesA (DA))
      rw [ComplJ9ADataRec.j9aDataOf_t] at this
      change nXA (p := p) Rt hgen ≤ 2 ^ 31 at this
      have := hp63_A hpG
      have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
      omega
    have hg : ∀ e ∈ ComplJ9AChipsOK.famAX δ (nXA_pos (p := p) Rt hgen) (csA p (DA).acs.length (DA).H t)
        (nXA_eq (p := p) Rt hgen h) (K := K), χ ∉ e.ev := by
      have := good_fam δ b Rt hgen hpG h31A hχ (famAXA δ Rt hgen)
        (List.mem_append_right _ List.mem_cons_self)
      simpa only [famAXA, dif_pos h] using this
    rw [hT]
    rw [hP]
    exact ComplJ9AChipsOK.axChipOK_honest δ b (nXA_pos (p := p) Rt hgen) _ (nXA_eq (p := p) Rt hgen h) hcs _ _
      hinj hadj hnp χ hg
  | false =>
    have hP : pubsXA δ Rt hgen χ = fun _ => 0 := by unfold pubsXA; rw [dif_neg (by simp [h])]
    refine Or.inr ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> rw [hP]

/-! ### The split chip -/

/-- **`SPChipOK` at the run's split part** (concrete form). -/
theorem spOK_A (hax9 : ComplJ9ABinders.ProgAxOK9A p t) (χ : Coins frameJ8 K) (hχ : (BA).Good χ) :
    SPChipOK δ b (nAA (p := p) Rt hgen) (spOnA p t) (nSOf_pos p t) (powN (oA Rt hgen hpG h31A) (nSOf p t))
      (oA Rt hgen hpG h31A) (chalsMJ8 δ χ) (pubsSA δ Rt hgen χ)
      (fun j => trSA δ b Rt hgen hpG h31A χ (Fin.cast (SplitChipJ9.width_eq δ _ b _ _ _ _ _) j)) := by
  cases h : spOnA p t with
  | true =>
    have hP : pubsSA δ Rt hgen χ = ComplJ9AChipsOK.pubsSOf δ (nAA (p := p) Rt hgen) (vSA (p := p) (t := t))
        (mSA (p := p) (t := t)) χ := by
      unfold pubsSA; rw [if_pos h]
    have hT : trSA δ b Rt hgen hpG h31A χ = fun j =>
        ComplJ9ASplitH.polySC δ (nAA (p := p) Rt hgen) b (nSOf_pos p t) (powN (oA Rt hgen hpG h31A) (nSOf p t))
          (oA Rt hgen hpG h31A) (chalsMJ8 δ χ) (pubsSA δ Rt hgen χ) (vSA (p := p) (t := t)) (mSA (p := p) (t := t)) j := by
      unfold trSA; rw [if_pos h]; rfl
    have hn : nSOf p t ≤ 2 ^ htA (DA) := by
      have := le_two_pow_htA _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)) : nSOf p (DA).t ∈ sizesA (DA))
      rwa [ComplJ9ADataRec.j9aDataOf_t] at this
    obtain ⟨hinj, hadj⟩ := powN_ok (oA Rt hgen hpG h31A) hn
    have hnp : nSOf p t < p := by
      have := h31A _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) :
        nSOf p (DA).t ∈ sizesA (DA))
      rw [ComplJ9ADataRec.j9aDataOf_t] at this
      have := hp63_A hpG
      have : (2 : ℕ) ^ 31 < 2 ^ 63 := by norm_num
      omega
    have hp32 : 2 ^ 32 < p := by
      have := hp63_A hpG
      have : (2 : ℕ) ^ 32 < 2 ^ 63 := by norm_num
      omega
    have hv : ∀ i, 2 ^ 32 ≤ vSA (p := p) (t := t) i ∧ vSA (p := p) (t := t) i < 2 ^ 64 := by
      intro i
      have hi : (i : ℕ) < (splitVals9 p (rowsOfT9 t)).length := by
        have h1 := i.isLt; have h2 := nSOf_eq (p := p) (t := t) h; omega
      unfold vSA
      rw [List.getD_eq_getElem _ _ hi]
      exact ComplJ9AChainsRun.splitVals9_range hgen hpG hax9 _ (List.getElem_mem hi)
    have hg : ∀ e ∈ ComplJ9AChipsOK.famSP δ (nAA (p := p) Rt hgen) (vSA (p := p) (t := t)) (K := K), χ ∉ e.ev :=
      good_fam δ b Rt hgen hpG h31A hχ (famSPA δ Rt hgen)
        (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [hT]
    rw [hP]
    exact ComplJ9AChipsOK.spChipOK_honest δ b (nAA (p := p) Rt hgen) _ _ (nSOf_pos p t) _ _ hp32 hv hinj hadj hnp χ hg
  | false =>
    have hP : pubsSA δ Rt hgen χ = fun _ => 0 := by unfold pubsSA; rw [if_neg (by simp [h])]
    refine Or.inr ⟨rfl, ?_, ?_⟩ <;> rw [hP]

end Chips

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOf

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AOf
#print axioms axOK_A
#print axioms spOK_A
end Axioms
