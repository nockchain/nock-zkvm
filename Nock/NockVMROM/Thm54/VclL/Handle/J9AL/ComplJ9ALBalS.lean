/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/ComplJ9ALBalS.lean

  **The service balance `hGS_L` at the J-9 AL mixed record.**
  * Abbrevs with explicit section arguments (`SS` added).
  * The ALU service terminal at the honest table (`SS_run`): `Σ_i tS i` over the table `tbR` is
    `− Σ_calls fS(κp) − Σ_{psRun} (fS(keyRg pin) + fS(op pin))`: a hdr row consumes its call's keyRg and op record
    and provides its `keyJet` (`κp`, `ComplJ9ALBalSJ.prim_key`: the compute consume's key); a preg row provides both
    keys with multiplicity `mRun = c + 1`; slot and padding rows carry no service weight.
  * `hGS_L`: the `hGS` field of `AcceptsJ9AL` at the mixed record, from `ComplJ9ABalS.hGSA`'s proof with
    `old_part` replaced by `ComplJ9ALBalSJ.old_part_L` + `sum_jetT_L` + `hJ_LJ` + `SS_run`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALBalSJ
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluSatRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalS

open Nock Nock.Reified Nock.Walk Nock.Edit Nock.Edit.GenX Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf rowsOfT hJd)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (j9alDataOf cellsL_pos acsL_pos pcallsR primsC idxPOf opOf
  opOf_of_mem)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec (j9aDataOf)
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows (BRow QRow CallL hdrRow pregRow padRow blockB slotRow slotRows
  slotsOf opIx envB)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSatRows (tS rowAt dK eFM eKM tblP zipB)
open Nock.NockVMROM.Thm54.VclL.Handle.AluPoles (yOf)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (chalsALJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.FiniteIO (compress)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.RapJetJ8 (keyK)
open Nock.Jet.Autogen (Tpl compile)
open Nock.Jet.ChipJ8 (axPosB)
open Nock.Jet.Prim (PrimOp primSpec)
open Nock.V1J8.Gen (atomV)

noncomputable section

/-! ## 0. The IFACE block -/

section Iface
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (prims : List (ℕ × PrimOp)) (hpG : p = Nock.Atoms.p)
  (h31A : ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
  (h31 : ComplJ9ARun.Rows31A (j9alDataOf p Rg Rt prims hgen))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => ComplJ9ALData.j9alDataOf p Rg Rt prims hgen
local notation "BA" => ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A
include hpG h31 in
theorem hFL : DvdOK (DL) := ComplJ9ARun.dvdOK_of_A (ComplJ9ARun.dvdA_of_rows hpG _ h31)
end Iface

/-! ## 1. The ALU service terms at the honest table -/

section Alu
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The service weight of a key (the compute side's `fS`). -/
abbrev Wk (χ : Coins frameJ8 K) (v : Fin 8 → K) : 𝕂′ := ComplJ8Bal.fS δ b χ v

theorem keyVecL_re (l : List ChipHX.RE) (eF : Env (ZMod p)) :
    AxisChipJ9.keyVecL (K := K) 8 (l.map AluSZChipJ9.reE) eF = keyK 8 (l.map (ChipHX.RE.ev eF.trace)) := by
  funext c
  simp only [AxisChipJ9.keyVecL, keyK]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map]
  cases l[(c : ℕ)]? with
  | none => simp [CoeffExpr.eval]
  | some e => cases e <;> simp [AluSZChipJ9.reE, ChipHX.RE.ev, CoeffExpr.eval, cv]

/-- **An ALU key denominator's inverse is the compute side's service weight of the key.** -/
theorem dK_inv (χ : Coins frameJ8 K) (tb : List (BRow (ZMod p) × QRow 𝕂′)) (l : List ChipHX.RE)
    (hl : l.length ≤ 8) (i : ℕ) :
    (dK δ (chalsALJ8 δ χ) tb (HQ.denKeyQ δ (l.map AluSZChipJ9.reE)) i)⁻¹ =
      Wk δ b χ (keyK 8 (l.map (ChipHX.RE.ev (rowAt δ tb i).1.col))) := by
  unfold dK
  rw [AxisTeleJ9.denKeyQ_evL δ _ _ 8 _ (by simpa using hl), AluPoles.coinsQ_AL, keyVecL_re]
  simp only [Wk, ComplJ8Bal.fS]
  rw [VerJ8.coinsCV_J8, ← ComplJ8CompPole.γH_eq, ← ComplJ8CompPole.ρH_eq]
  rfl

theorem liftQ_zero : liftQ δ (0 : ZMod p) = (0 : 𝕂′) := by
  show algebraMap K 𝕂′ (algebraMap (ZMod p) K 0) = 0
  simp

/-- The service term of a base row. -/
def gS (χ : Coins frameJ8 K) (r : BRow (ZMod p)) : 𝕂′ :=
  liftQ δ (r.sH - r.sP * r.mP) * (Wk δ b χ (keyK 8 (AluSZChipJ9.keyRgRE.map (ChipHX.RE.ev r.col))) +
      Wk δ b χ (keyK 8 (AluSZChipJ9.opRecRE.map (ChipHX.RE.ev r.col)))) -
    liftQ δ (r.sH * r.mJ) * Wk δ b χ (keyK 8 (AluSZChipJ9.keyJetRE.map (ChipHX.RE.ev r.col)))

theorem tS_eq {n : ℕ} (χ : Coins frameJ8 K) (tb : List (BRow (ZMod p) × QRow 𝕂′)) (i : Fin n) :
    tS δ (chalsALJ8 δ χ) tb i = gS δ b χ (rowAt δ tb i).1 := by
  simp only [tS, AluSatRows.dR, AluSatRows.dO, AluSatRows.dJ, AluSatRows.wSv, AluSZChipJ9.keyRgE,
    AluSZChipJ9.opRecE, AluSZChipJ9.keyJetE]
  rw [dK_inv δ b χ tb _ (by decide), dK_inv δ b χ tb _ (by decide), dK_inv δ b χ tb _ (by decide)]
  unfold gS
  ring

theorem gS_pad (χ : Coins frameJ8 K) : gS δ b χ (padRow : BRow (ZMod p)) = 0 := by
  have e1 : (padRow : BRow (ZMod p)).sH = 0 := rfl
  have e2 : (padRow : BRow (ZMod p)).sP = 0 := rfl
  have e3 : (padRow : BRow (ZMod p)).mJ = 0 := rfl
  simp only [gS, e1, e2, e3, zero_mul, sub_zero, liftQ_zero]

theorem sum_tS {n : ℕ} (χ : Coins frameJ8 K) (tb : List (BRow (ZMod p) × QRow 𝕂′)) (hlen : tb.length ≤ n) :
    ∑ i : Fin n, tS δ (chalsALJ8 δ χ) tb i = (tb.map fun x => gS δ b χ x.1).sum := by
  rw [Finset.sum_congr rfl (fun i _ => tS_eq δ b χ tb i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => gS δ b χ (rowAt δ tb i).1) n]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlen
  rw [Finset.sum_range_add]
  have hz : ∑ x ∈ Finset.range k, gS δ b χ (rowAt δ tb (tb.length + x)).1 = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp only [rowAt]
    rw [List.getD_eq_default _ _ (by omega)]
    exact gS_pad δ b χ
  rw [hz, add_zero]
  exact ComplJ8OfBal.sum_range_getD' (padRow, QRow.zero) (fun x => gS δ b χ x.1) tb

theorem gS_slot (χ : Coins frameJ8 K) (pp : ℕ) (cl : CallL) (sl : AluHonestRows.SlotL) (i : ℕ) :
    gS δ b χ (slotRow pp cl sl i : BRow (ZMod p)) = 0 := by
  have h1 : (slotRow pp cl sl i : BRow (ZMod p)).sH = 0 := rfl
  have h2 : (slotRow pp cl sl i : BRow (ZMod p)).sP = 0 := rfl
  have h3 : (slotRow pp cl sl i : BRow (ZMod p)).mJ = 0 := rfl
  simp only [gS, h1, h2, h3, zero_mul, sub_zero, liftQ_zero]

theorem sum_block (χ : Coins frameJ8 K) (pp : ℕ) (cl : CallL) :
    ((blockB pp cl : List (BRow (ZMod p))).map (gS δ b χ)).sum = gS δ b χ (hdrRow cl) := by
  unfold blockB
  rw [List.map_cons, List.sum_cons, List.sum_eq_zero, add_zero]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  obtain ⟨sl, -, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact gS_slot δ b χ pp cl sl i

theorem map_fst_tblP (pp : ℕ) (y : 𝕂′) (pregs : List (BRow (ZMod p))) (cls : List CallL) :
    (tblP δ pp y pregs cls).map Prod.fst = pregs ++ cls.flatMap (blockB pp) ++ [padRow] := by
  unfold tblP
  rw [List.map_append, List.map_append, List.map_map, List.map_flatMap]
  have h1 : (Prod.fst ∘ fun r : BRow (ZMod p) => (r, (QRow.zero : QRow 𝕂′))) = id := rfl
  rw [h1, List.map_id]
  have h2 : (fun cl => (zipB δ pp y cl).map Prod.fst) = blockB (F := ZMod p) pp :=
    funext fun cl => List.map_fst_zip (by rw [AluSatRows.blockQ_length (F := ZMod p) pp y cl])
  rw [h2]
  rfl

/-- **The ALU service terminal at the honest table**: preg rows, hdr rows, nothing else. -/
theorem sum_tS_tblP {n : ℕ} (χ : Coins frameJ8 K) (pp : ℕ) (y : 𝕂′) (pregs : List (BRow (ZMod p)))
    (cls : List CallL) (hlen : (tblP δ pp y pregs cls).length ≤ n) :
    ∑ i : Fin n, tS δ (chalsALJ8 δ χ) (tblP δ pp y pregs cls) i =
      (pregs.map (gS δ b χ)).sum + (cls.map fun cl => gS δ b χ (hdrRow cl)).sum := by
  rw [sum_tS δ b χ _ hlen]
  have e : ((tblP δ pp y pregs cls).map fun x => gS δ b χ x.1) = ((tblP δ pp y pregs cls).map Prod.fst).map (gS δ b χ) := by
    rw [List.map_map]; rfl
  rw [e, map_fst_tblP]
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, Nock.Jet.RapJetJ8.sum_flatMap]
  simp only [sum_block, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, gS_pad, add_zero]

/-- A preg row's service term. -/
theorem gS_preg (χ : Coins frameJ8 K) (pid pcode pvc pm : ℕ) :
    gS δ b χ (pregRow pid pcode pvc pm : BRow (ZMod p)) =
      -(liftQ δ (pm : ZMod p) * (Wk δ b χ (AcceptsJ9AL.pinRgVec (p := p) (K := K) pid pvc) +
        Wk δ b χ (keyK 8 [(pid : ZMod p), (pcode : ZMod p), 0, 0, 0, 0, 0, ((AluSZChipJ9.tagOp : ℕ) : ZMod p)]))) := by
  simp only [gS, AcceptsJ9AL.pinRgVec]
  have e1 : (pregRow pid pcode pvc pm : BRow (ZMod p)).sH = 0 := rfl
  have e2 : (pregRow pid pcode pvc pm : BRow (ZMod p)).sP = 1 := rfl
  have e3 : (pregRow pid pcode pvc pm : BRow (ZMod p)).mP = (pm : ZMod p) := rfl
  have e4 : (pregRow pid pcode pvc pm : BRow (ZMod p)).mJ = 0 := rfl
  rw [e1, e2, e3, e4]
  have k1 : AluSZChipJ9.keyRgRE.map (ChipHX.RE.ev (pregRow pid pcode pvc pm : BRow (ZMod p)).col) =
      [(pid : ZMod p), 1, (pvc : ZMod p), 0, 0, 0, 0, ((AluSZChipJ9.tagRgP : ℕ) : ZMod p)] := by
    simp [AluSZChipJ9.keyRgRE, ChipHX.RE.ev, AluSZChipJ9.idc, AluSZChipJ9.kc, AluSZChipJ9.vc, BRow.col, pregRow,
      BRow.zero]
  have k2 : AluSZChipJ9.opRecRE.map (ChipHX.RE.ev (pregRow pid pcode pvc pm : BRow (ZMod p)).col) =
      [(pid : ZMod p), (pcode : ZMod p), 0, 0, 0, 0, 0, ((AluSZChipJ9.tagOp : ℕ) : ZMod p)] := by
    simp [AluSZChipJ9.opRecRE, ChipHX.RE.ev, AluSZChipJ9.idc, AluSZChipJ9.opc, BRow.col, pregRow, BRow.zero]
  rw [k1, k2]
  simp [liftQ]

/-- A hdr row's service term: its keyRg and op-record consumes, its `keyJet` provide. -/
theorem gS_hdr (χ : Coins frameJ8 K) (cl : CallL) :
    gS δ b χ (hdrRow cl : BRow (ZMod p)) =
      Wk δ b χ (AcceptsJ9AL.pinRgVec (p := p) (K := K) cl.id cl.vc) +
        Wk δ b χ (keyK 8 [(cl.id : ZMod p), ((opIx cl.op + 1 : ℕ) : ZMod p), 0, 0, 0, 0, 0,
          ((AluSZChipJ9.tagOp : ℕ) : ZMod p)]) -
        Wk δ b χ (keyK 8 [(cl.id : ZMod p), 1, (cl.vc : ZMod p), 1, (cl.vS : ZMod p), (cl.kE : ZMod p),
          (cl.vE : ZMod p), ((3 : ℕ) : ZMod p)]) := by
  simp only [gS, AcceptsJ9AL.pinRgVec]
  have e1 : (hdrRow cl : BRow (ZMod p)).sH = 1 := rfl
  have e2 : (hdrRow cl : BRow (ZMod p)).sP = 0 := rfl
  have e4 : (hdrRow cl : BRow (ZMod p)).mJ = 1 := rfl
  rw [e1, e2, e4]
  have k1 : AluSZChipJ9.keyRgRE.map (ChipHX.RE.ev (hdrRow cl : BRow (ZMod p)).col) =
      [(cl.id : ZMod p), 1, (cl.vc : ZMod p), 0, 0, 0, 0, ((AluSZChipJ9.tagRgP : ℕ) : ZMod p)] := by
    simp [AluSZChipJ9.keyRgRE, ChipHX.RE.ev, AluSZChipJ9.idc, AluSZChipJ9.kc, AluSZChipJ9.vc, BRow.col, hdrRow,
      BRow.zero]
  have k2 : AluSZChipJ9.opRecRE.map (ChipHX.RE.ev (hdrRow cl : BRow (ZMod p)).col) =
      [(cl.id : ZMod p), ((opIx cl.op + 1 : ℕ) : ZMod p), 0, 0, 0, 0, 0, ((AluSZChipJ9.tagOp : ℕ) : ZMod p)] := by
    simp [AluSZChipJ9.opRecRE, ChipHX.RE.ev, AluSZChipJ9.idc, AluSZChipJ9.opc, BRow.col, hdrRow, BRow.zero]
  have k3 : AluSZChipJ9.keyJetRE.map (ChipHX.RE.ev (hdrRow cl : BRow (ZMod p)).col) =
      [(cl.id : ZMod p), 1, (cl.vc : ZMod p), 1, (cl.vS : ZMod p), (cl.kE : ZMod p), (cl.vE : ZMod p),
        ((3 : ℕ) : ZMod p)] := by
    simp [AluSZChipJ9.keyJetRE, ChipHX.RE.ev, AluSZChipJ9.idc, AluSZChipJ9.kc, AluSZChipJ9.vc, AluSZChipJ9.kS,
      AluSZChipJ9.vS, AluSZChipJ9.kE, AluSZChipJ9.vE, BRow.col, hdrRow, BRow.zero]
  rw [k1, k2, k3]
  simp [liftQ]

end Alu

/-! ## 2. Counting: the calls of an id -/

section Count
variable {M : Type} [AddCommGroup M]

theorem sum_ite_eq_nd {α : Type} (g : ℕ → M) (a : ℕ) :
    ∀ ps : List (ℕ × α), (ps.map Prod.fst).Nodup → a ∈ ps.map Prod.fst →
      (ps.map fun q => if q.1 = a then g q.1 else 0).sum = g a
  | [], _, h => absurd h List.not_mem_nil
  | q :: ps, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    by_cases hq : q.1 = a
    · rw [if_pos hq, hq]
      have : (ps.map fun q => if q.1 = a then g q.1 else 0).sum = 0 := by
        refine List.sum_eq_zero fun y hy => ?_
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hy
        have : q'.1 ≠ a := fun e => hnd.1 (hq ▸ e ▸ List.mem_map_of_mem hq')
        rw [if_neg this]
      rw [this, add_zero]
    · rw [if_neg hq, zero_add]
      rw [List.map_cons, List.mem_cons] at h
      exact sum_ite_eq_nd g a ps hnd.2 (h.resolve_left (Ne.symm hq))

theorem sum_map_sub' {α : Type} (f g : α → M) : ∀ l : List α,
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.sum_cons, sum_map_sub' f g l]
    abel

/-- **A sum over the calls is a count-weighted sum over the (nodup) called ids.** -/
theorem sum_by_id {α β : Type} (g : ℕ → M) (ps : List (ℕ × α)) (hnd : (ps.map Prod.fst).Nodup) :
    ∀ pc : List (ℕ × β), (∀ x ∈ pc, x.1 ∈ ps.map Prod.fst) →
      (pc.map fun x => g x.1).sum = (ps.map fun q => (pc.countP fun x => x.1 = q.1) • g q.1).sum
  | [], _ => by simp
  | x :: pc, h => by
    rw [List.map_cons, List.sum_cons, sum_by_id g ps hnd pc (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rw [← sum_ite_eq_nd g x.1 ps hnd (h x List.mem_cons_self), ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    rw [List.countP_cons]
    by_cases hq : q.1 = x.1
    · simp [hq, add_smul, add_comm]
    · have : ¬ (x.1 = q.1) := fun e => hq e.symm
      simp [hq, this]

end Count

/-! ## 3. The run: the ALU terminal, then `hGS_L` -/

section Run
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun (BRun9A W9 N9 N9_def idOfA spOnA)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains (idOf9 idOf9_big)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSC (incT9 jetT9 awT9 gT9 sSum9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSAx (limbRecs limbW)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS (split3 pubsX_S pubsS_S)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalSJ (κp)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ} {s f r : Noun}
  {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))
  (prims : List (ℕ × PrimOp)) (hpG : p = Nock.Atoms.p)
  (h31A : ComplJ9ARun.Rows31A (j9aDataOf p Rg Rt hgen))
  (h31 : ComplJ9ARun.Rows31A (j9alDataOf p Rg Rt prims hgen))

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen
local notation "DL" => ComplJ9ALData.j9alDataOf p Rg Rt prims hgen
local notation "BA" => ComplJ9ARun.BRun9A δ b Rt hgen hpG h31A
local notation "PIDS" => prims.map Prod.fst
-- the IFACE abbrevs as local notations (their section arguments are explicit; assembly identifies them by `rfl`)
set_option quotPrecheck false
local notation "FL" => hFL (Rt := Rt) (hgen := hgen) (prims := prims) hpG h31
local notation "psRun" => ComplJ9ALData.primsC prims ((DA).calls.map Prod.fst)
local notation "vcRun" => ComplJ9ALData.idxPOf (DA).cells prims
local notation "mRun" => fun id : ℕ =>
  ((ComplJ9ALData.pcallsR (prims.map Prod.fst) (rowsOfT t)).countP fun x => x.1 = id) + 1   -- mP = c+1
local notation "tbR" y:max => AluSatRun.tblRun δ Rt prims hgen psRun vcRun mRun y
local notation "famsJL" => famsOf δ b (DL) FL (cellsL_pos Rt prims hgen) ++
  ComplJ9BOf.famsA9 δ b (DL) (DL) FL (acsL_pos Rt prims hgen)
local notation "AVL" => ComplJ9BBalF.avOf9 δ b (DL) FL (avOf δ b (DL) FL (acsL_pos Rt prims hgen))
local notation "B8L" => honestJ8Of δ b (DL) FL (cellsL_pos Rt prims hgen) (acsL_pos Rt prims hgen) AVL famsJL
local notation "SS" n:max χ:max => ∑ i : Fin n, AluSatRows.tS δ (chalsALJ8 δ χ) (tbR (AluPoles.yOf δ χ)) i

theorem primCode_eq (op : PrimOp) (h : op ≠ .dec) : RealIOJ9AL.primCode op = opIx op + 1 := by
  cases op <;> simp_all [RealIOJ9AL.primCode, opIx]

theorem psRun_sub : ∀ q ∈ (psRun), q ∈ prims := fun q hq => (List.mem_filter.mp hq).1

theorem psRun_nodup (hnd : (prims.map Prod.fst).Nodup) : ((psRun).map Prod.fst).Nodup :=
  hnd.sublist (List.Sublist.map _ List.filter_sublist)

theorem pcalls_mem : ∀ x ∈ pcallsR PIDS (rowsOfT t), x.1 ∈ (psRun).map Prod.fst := by
  intro x hx
  have h1 : (x.1, x.2.1) ∈ ComplJ9ALData.aCallsP PIDS (Nock.V1J8.Gen.callsOf (rowsOfT t)) := by
    rw [← ComplJ9ALData.pcallsR_fst]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨hc, hid⟩ := ComplJ9ALData.aCallsP_sub _ _ _ h1
  obtain ⟨q, hq, hq1⟩ := List.mem_map.mp hid
  refine List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, ?_⟩, hq1⟩
  simp only [decide_eq_true_eq]
  rw [hq1]
  exact List.mem_map.mpr ⟨_, hc, rfl⟩

/-- **The ALU service terminal at the run** (honest table `tbR`, every `n` above its length): with the verifier's
two pins per called primitive and the compute consumes of the primitive calls (`κp`), it sums to zero. -/
theorem SS_run (hnd : (prims.map Prod.fst).Nodup) (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    (χ : Coins frameJ8 K) (n : ℕ) (hlen : (tbR (AluPoles.yOf δ χ)).length ≤ n) :
    SS n χ +
      (((psRun).map fun q => AcceptsJ9AL.pinRgVec (p := p) (K := K) q.1 (vcRun q.1)).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      (((psRun).map fun q => keyK (K := K) 8 [(q.1 : ZMod p), (RealIOJ9AL.primCode q.2 : ZMod p), 0, 0, 0, 0, 0,
          (AluSZChipJ9.tagOp : ZMod p)]).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      ((pcallsR PIDS (rowsOfT t)).map fun x =>
        ComplJ8Bal.fS δ b χ (keyK 8 (κp (p := p) prims (DL).cells (DL).H x))).sum = 0 := by
  unfold AluSatRun.tblRun at hlen ⊢
  rw [sum_tS_tblP δ b χ _ _ _ _ hlen]
  set pc := pcallsR PIDS (rowsOfT t) with hpc
  set V : ℕ → 𝕂′ := fun id => Wk δ b χ (AcceptsJ9AL.pinRgVec (p := p) (K := K) id (vcRun id)) +
    Wk δ b χ (keyK 8 [(id : ZMod p), ((opIx (opOf prims id) + 1 : ℕ) : ZMod p), 0, 0, 0, 0, 0,
      ((AluSZChipJ9.tagOp : ℕ) : ZMod p)]) with hV
  have hopq : ∀ q ∈ (psRun), opOf prims q.1 = q.2 := fun q hq => opOf_of_mem hnd (psRun_sub Rt hgen prims q hq)
  have hpreg : ((AluSatPreg.pregsP psRun vcRun mRun : List (BRow (ZMod p))).map (gS δ b χ)).sum =
      ((psRun).map fun q => -((((mRun q.1 : ℕ)) : 𝕂′) * V q.1)).sum := by
    unfold AluSatPreg.pregsP
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    simp only [Function.comp, gS_preg, hV, hopq q hq]
    congr 2
    simp [liftQ]
  have hhdr : ((AluSatRun.clsRun (p := p) Rt prims hgen).map fun cl => gS δ b χ (hdrRow cl)).sum =
      (pc.map fun x => V x.1).sum -
        (pc.map fun x => ComplJ8Bal.fS δ b χ (keyK 8 (κp (p := p) prims (DL).cells (DL).H x))).sum := by
    rw [← sum_map_sub' (fun x : ℕ × Noun × Noun => V x.1)]
    unfold AluSatRun.clsRun AluHonestTable.callsLOf
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp]
    rw [gS_hdr]
    rfl
  have hpin : (((psRun).map fun q => AcceptsJ9AL.pinRgVec (p := p) (K := K) q.1 (vcRun q.1)).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      (((psRun).map fun q => keyK (K := K) 8 [(q.1 : ZMod p), (RealIOJ9AL.primCode q.2 : ZMod p), 0, 0, 0, 0, 0,
          (AluSZChipJ9.tagOp : ZMod p)]).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum =
      ((psRun).map fun q => V q.1).sum := by
    rw [List.map_map, List.map_map, ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    simp only [Function.comp, hV, hopq q hq,
      primCode_eq q.2 (hnoDec q (psRun_sub Rt hgen prims q hq))]
  have hcount := sum_by_id V psRun (psRun_nodup Rt hgen prims hnd) pc (pcalls_mem Rt hgen prims)
  have hz : ((psRun).map fun q => -((((mRun q.1 : ℕ)) : 𝕂′) * V q.1)).sum +
      ((psRun).map fun q => (pc.countP fun x => x.1 = q.1) • V q.1).sum + ((psRun).map fun q => V q.1).sum = 0 := by
    rw [← List.sum_map_add, ← List.sum_map_add]
    refine List.sum_eq_zero fun y hy => ?_
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hy
    simp only [Nat.cast_add, Nat.cast_one, nsmul_eq_mul]
    ring
  rw [hpreg, hhdr]
  linear_combination hpin + hcount + hz

theorem eK_L (χ : Coins frameJ8 K) : ((axKeys9 (rowsOfT9 t)).map fun k =>
      ((limbRecs (idOfA (p := p) Rt hgen k.2) k.2).map (limbW δ χ)).sum).sum =
    ((((axKeys9 (rowsOfT9 t)).filter fun k => decide (p ≤ k.2)).map fun k =>
        ((limbRecs (p := p) ((DA).H (.atom k.2)).2 k.2).map (limbW δ χ)).sum).sum) +
      ((((axKeys9 (rowsOfT9 t)).filter fun k => decide (k.2 < p)).map fun k =>
        ((limbRecs (idOfA (p := p) Rt hgen k.2) k.2).map (limbW δ χ)).sum).sum) := by
  have := split3 (fun k : Noun × ℕ => ((limbRecs (idOfA (p := p) Rt hgen k.2) k.2).map (limbW δ χ)).sum)
    (fun _ => true) (fun k => decide (p ≤ k.2)) (fun k => decide (k.2 < p))
    (fun k => by simp only [Bool.true_eq, Bool.or_eq_true, decide_eq_true_eq]; omega)
    (fun k => by simp only [decide_eq_true_eq]; omega) (axKeys9 (rowsOfT9 t))
  simp only [List.filter_true] at this
  rw [this]
  refine congrArg (· + _) (congrArg List.sum (List.map_congr_left fun k hk => ?_))
  have hpk : p ≤ k.2 := by simpa using (List.mem_filter.1 hk).2
  rw [show idOfA (p := p) Rt hgen k.2 = ((DA).H (.atom k.2)).2 from idOf9_big hpk]

theorem eR_L (χ : Coins frameJ8 K) : ((((rowsOfT9 t).toList.filter fun l => decide (l.chip = ChipSt9.s10B)).map fun l =>
      ((limbRecs (p := p) (idOfA (p := p) Rt hgen l.n) l.n).map (limbW δ χ)).sum)).sum =
    ((((rowsOfT9 t).toList.filter fun l => decide (l.chip = .s10B ∧ p ≤ l.n)).map fun l =>
        ((limbRecs (p := p) ((DA).H (.atom l.n)).2 l.n).map (limbW δ χ)).sum).sum) +
      ((((rowsOfT9 t).toList.filter fun l => decide (l.chip = .s10B ∧ l.n < p)).map fun l =>
        ((limbRecs (idOfA (p := p) Rt hgen l.n) l.n).map (limbW δ χ)).sum).sum) := by
  rw [split3 (fun l : LX9 => ((limbRecs (idOfA (p := p) Rt hgen l.n) l.n).map (limbW δ χ)).sum)
    (fun l => decide (l.chip = ChipSt9.s10B)) (fun l => decide (l.chip = .s10B ∧ p ≤ l.n))
    (fun l => decide (l.chip = .s10B ∧ l.n < p))
    (fun l => by
      by_cases h : l.chip = .s10B <;> by_cases h2 : p ≤ l.n <;> simp [h, h2] <;> omega)
    (fun l => by simp only [decide_eq_true_eq]; omega) (rowsOfT9 t).toList]
  refine congrArg (· + _) (congrArg List.sum (List.map_congr_left fun l hl => ?_))
  have hpl : p ≤ l.n := by
    have := (List.mem_filter.1 hl).2
    simp only [decide_eq_true_eq] at this
    exact this.2
  rw [show idOfA (p := p) Rt hgen l.n = ((DA).H (.atom l.n)).2 from idOf9_big hpl]

theorem hsplit_L (χ : Coins frameJ8 K) : ∑ j ∈ Finset.range (N9 t), sSum9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t)
      (VerJ8.chalVJ8 b χ) (fun _ => 0) j =
    ∑ j ∈ Finset.range (N9 t),
      (incT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
        jetT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
        awT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j) +
    ∑ j ∈ Finset.range (N9 t),
      (gT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) 123
          (ChipHX9.axRecX ChipHX.xS ChipHX.xFt ChipHX.xE) j +
        gT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) 124
          (ChipHX9.axRecX ChipHX.xE ChipHX.xFtth ChipHX.xSf1) j) +
    ∑ j ∈ Finset.range (N9 t),
      gT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) 125
        ChipHX9.limbRecX j := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ComplJ9ABalSC.sSum9_expand]
  ring

/-- **`hGS_L`: the service balance `hGS` of `AcceptsJ9AL` at the J-9 AL mixed record** (compute, walk, axis and split
publics from `BA`, J and atom publics from `B8L`, the ALU service terminal `SS`), at every good coin.  Binders: the
§0 run binders only (`hpG h31A h31 hax9 hwalkA hRtJ hnd hprim hnoDec`, the good-coin `hχA hχL`, `hlen`). -/
theorem hGS_L (hax9 : ProgAxOK9A p t)
    (hwalkA : Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Walk.WalkDepthOK (DD).preads)
    (hRtJ : ∀ id ∈ CalledIds t, id ∉ prims.map Prod.fst →
      Rg.R id = some ⟨(Rt id).toTemplate p, compile p (Rt id)⟩ ∧ axPosB (Rt id) = true ∧ (Rt id).WellTyped p)
    (hnd : (prims.map Prod.fst).Nodup) (hprim : ∀ q ∈ prims, Rg.R q.1 = some (primSpec q.2))
    (hnoDec : ∀ q ∈ prims, q.2 ≠ .dec)
    (χ : Coins frameJ8 K) (hχA : (BA).Good χ) (hχL : (B8L).Good χ) (n : ℕ)
    (hlen : (tbR (AluPoles.yOf δ χ)).length ≤ n) :
    ((BA).M χ).ρS + ((pinCons (p := p) (K := K) (DL).regs (DA).idx).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum
      + (((psRun).map fun q => AcceptsJ9AL.pinRgVec (p := p) (K := K) q.1 (vcRun q.1)).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum
      + (((psRun).map fun q => keyK (K := K) 8 [(q.1 : ZMod p), (RealIOJ9AL.primCode q.2 : ZMod p), 0, 0, 0, 0, 0,
          (AluSZChipJ9.tagOp : ZMod p)]).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum
      + Quad.mk _ (((B8L).M χ).pubsJ 0) (((B8L).M χ).pubsJ 1)
      + Quad.mk _ (((BA).M χ).pubsX AxisChipJ9.pubAXs) (((BA).M χ).pubsX (AxisChipJ9.pubAXs + 1)) + SS n χ
    = Quad.mk _ (((B8L).M χ).pubsA AtomChipHQ.pubMI) (((B8L).M χ).pubsA (AtomChipHQ.pubMI + 1))
      + Quad.mk _ (((BA).M χ).pubsV WalkHQ.pubPQ) (((BA).M χ).pubsV (WalkHQ.pubPQ + 1))
      + Quad.mk _ (((BA).M χ).pubsS SplitChipJ9.pubSPs) (((BA).M χ).pubsS (SplitChipJ9.pubSPs + 1)) := by
  have hH : HonestCompX.HdlOK p (DA).H := ComplJ8Data.hdlOK_hdlP p (DA).cells (DA).acs
  have hρ : ((BA).M χ).ρS = Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ARun.ρSA δ b Rt hgen χ := rfl
  -- the old part at the overlay: MI (overlay atom table) + the jet total + the atom-walk pair reads
  have hold := ComplJ9ALBalSJ.old_part_L δ b Rt prims hgen hpG h31A FL χ
  have hjet := ComplJ9ALBalSJ.sum_jetT_L δ b Rt prims hgen hax9 hRtJ hnd hprim hnoDec χ (fun _ => 0)
  have hJ := ComplJ9ALBalSJ.hJ_LJ δ b Rt prims hgen hpG hax9 h31 hRtJ χ
  have hJ' : ((DL).calls.map fun cl => ComplJ8Bal.fS δ b χ
        (keyK 8 (ComplJ8OfBalJ.κc (p := p) Rt (hJd p (DL).cells (DL).acs) cl))).sum +
      ((pinCons (p := p) (K := K) (DL).regs (DA).idx).map fun x =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) x))⁻¹).sum +
      Quad.mk _ (((B8L).M χ).pubsJ 0) (((B8L).M χ).pubsJ 1) = 0 := hJ
  have hSS := SS_run δ b Rt hgen prims hnd hnoDec χ n hlen
  have hold' : ∑ j ∈ Finset.range (N9 t),
        (incT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
          jetT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
          awT9 δ b (DA).H (DA).pd (idOfA (p := p) Rt hgen) (W9 t) (VerJ8.chalVJ8 b χ) (fun _ => 0) j) =
      Quad.mk _ (((B8L).M χ).pubsA AtomChipHQ.pubMI) (((B8L).M χ).pubsA (AtomChipHQ.pubMI + 1)) +
      ∑ j ∈ Finset.range (bfsForest [t]).length,
        ComplJ8OfBalG.jetT δ b (DD).H (DD).pd (bfsForest [t]) (VerJ8.chalVJ8 b χ) (fun _ => 0) j +
      ((DD).preads.map fun x => ComplJ9BBalG.WA9 δ (DD) χ x).sum := hold
  have htag := ComplJ9ABalS.tag_total δ b hgen (DA).acs.length (DA).H hH (DA).pd χ (fun _ => 0)
  have hlimb := ComplJ9ABalS.limb_total δ b hgen hpG hax9 (DA).H (DA).pd (idOfA (p := p) Rt hgen) χ (fun _ => 0)
  have hX := pubsX_S δ b Rt hgen hpG h31A χ
  have hS := pubsS_S δ b Rt hgen hpG h31A hax9 χ
  have hV : Quad.mk _ (((BA).M χ).pubsV Nock.NockVMROM.Thm54.VclL.Handle.WalkHQ.pubPQ)
        (((BA).M χ).pubsV (Nock.NockVMROM.Thm54.VclL.Handle.WalkHQ.pubPQ + 1)) =
      ((DA).preads.map (ComplJ9BBalG.WA9 δ (DA) χ)).sum :=
    Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSV.vhP9_BA δ b Rt hgen hpG h31A hax9 hwalkA χ
  have hSL := Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSL.axReadsK9_sum δ Rt hgen hpG χ
  rw [ComplJ9ADataRec.j9aDataOf_preads, List.map_append, List.sum_append] at hV
  have hSL' : ((Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun.axReadsK9 p (rowsOfT9 t)).map
      (ComplJ9BBalG.WA9 δ (DA) χ)).sum = _ := hSL
  rw [hSL'] at hV
  have eK := eK_L δ Rt hgen χ
  have eR := eR_L δ Rt hgen χ
  have hsplit := hsplit_L δ b Rt hgen χ
  rw [hρ, Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalS.rhoS_total δ b Rt hgen hpG h31A χ hχA, hsplit]
  have hWA : ((DD).preads.map fun x => ComplJ9BBalG.WA9 δ (DD) χ x).sum =
      ((DD).preads.map (ComplJ9BBalG.WA9 δ (DA) χ)).sum := rfl
  linear_combination hold' + hjet + hJ' + hSS + htag + hlimb + hX + eK + eR - hV - hS + hWA

end Run

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALBalS
