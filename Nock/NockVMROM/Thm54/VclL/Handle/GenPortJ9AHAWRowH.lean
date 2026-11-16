/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAWRowH.lean

  One trie row
  `t ∈ walkRows D.acs D.preads` at a time, generic `D`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Walk
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Of
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow
open Nock.V1J8.Gen (P)

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRowH

theorem hdl_fst_cell (cs : List Noun) (n : Noun) (h : n.isCell = true) : (Nock.V1J8.Gen.hdl cs n).1 = 1 := by
  cases n with
  | atom a => simp [Noun.isCell] at h
  | cell a b => rfl

section
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))] [Fact (ringChar (ZMod P)).Prime]
  [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

theorem algQ (x : ZMod P) : algebraMap (ZMod P) (Quad (algebraMap (ZMod P) KC deltaF)) x =
    liftQ (K := KC) deltaF x := IsScalarTower.algebraMap_apply (ZMod P) KC _ x

theorem algQ' (x : ZMod P) : algebraMap (ZMod P) (Quad ((AdjoinRoot.of cubicPoly) deltaF)) x =
    liftQ (K := KC) deltaF x := by
  first | exact IsScalarTower.algebraMap_apply (ZMod P) KC _ x | rfl | (simp only [liftQ]; rfl)

theorem comb5 {R : Type*} [CommRing R] (ρ a b c d e : R) :
    ρ + (a + b + c + d + e) = ρ + (0 + a + b + c + d + e) := by
  rw [zero_add]

theorem comb4 {R : Type*} [CommRing R] (ρ a b c d : R) :
    ρ + (a + b + c + d) = ρ + (0 + a + b + c + d) := by
  rw [zero_add]

theorem hγQ (χe : CoinsE) : K6.toQ (γHE χe) = ComplJ8Bad.γH deltaF (toχ χe) := rfl
theorem hρQ (χe : CoinsE) : K6.toQ (ρHE χe) = ComplJ8Bad.ρH deltaF (toχ χe) := rfl

/-- The right child's handle pair at the pointer (`kRV9`, `vRV9`). -/
noncomputable def hRn (D : J8Data P Rg fuel s f r) (t : NTree WN) : ℕ × ℕ :=
  if (Nock.NockVMROM.Thm54.VclL.tlN t.label.node).isCell then (1, ComplJ8Data.ptrP P D.acs D.rows t.label.node)
  else Nock.V1J8.Gen.hdl D.acs (Nock.NockVMROM.Thm54.VclL.tlN t.label.node)

theorem hRn_fst (D : J8Data P Rg fuel s f r) (t : NTree WN) :
    (hRn D t).1 = (Nock.V1J8.Gen.hdl D.acs (Nock.NockVMROM.Thm54.VclL.tlN t.label.node)).1 := by
  unfold hRn
  split_ifs with h
  · exact (hdl_fst_cell _ _ h).symm
  · rfl

variable (χe : CoinsE) (D : J8Data P Rg fuel s f r) (t : NTree WN) (j : ℕ)

theorem dE_hXi :
    (dE χe D t j).hXi =
      (compressE (coOfA χe).γH (coOfA χe).ρH
        (![lq (dE χe D t j).idx, (Nock.V1J8.Gen.hK (Nock.V1J8.Gen.hdl D.acs) (Nock.V1J8.Gen.hdN' t.label.node)).1,
          (Nock.V1J8.Gen.hK (Nock.V1J8.Gen.hdl D.acs) (Nock.V1J8.Gen.hdN' t.label.node)).2,
          lq (hRn D t).1, lq (hRn D t).2] : Fin 5 → K6))⁻¹ := by
  unfold dE Nock.V1J8.Gen.walkDBE hRn
  simp only [GenPortJ9AHAtomRow.tlN'_eq, GenPortJ9AHWalkBfs.wrowOf]
  split_ifs <;> rfl

theorem dE_hPRi :
    (dE χe D t j).hPRi =
      (compressE (coOfA χe).γH (coOfA χe).ρH
        (![lq (dE χe D t j).ridx, lq (2 * (VclL.axisFold t.label.bits) + 1),
          lq (hRn D t).1, lq (hRn D t).2] : Fin 4 → K6))⁻¹ := by
  unfold dE Nock.V1J8.Gen.walkDBE hRn
  simp only [GenPortJ9AHAtomRow.tlN'_eq, GenPortJ9AHWalkBfs.wrowOf]
  split_ifs <;> rfl

variable (hwA : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs)
  (hsm : ∀ y ∈ D.acs, GenPortJ9AHAtomRow.Small y) (ht : t ∈ walkRows D.acs D.preads)
  (hcl : ∀ y ∈ D.acs, y.isCell = true)
include hwA hsm ht hcl

theorem toQ_hXi :
    K6.toQ (dE χe D t j).hXi =
      (ComplJ8Bad.ρH deltaF (toχ χe) + recDen 0 (ComplJ8Bad.γH deltaF (toχ χe))
        (((ComplJ9BAWR.idxRW D.acs (ComplJ8Data.rIAP P D.acs) t : ℕ) : ZMod P),
          ((((Nock.V1J8.Gen.hdl D.acs (VclL.hdN t.label.node)).1 : ℕ) : ZMod P),
            (((Nock.V1J8.Gen.hdl D.acs (VclL.hdN t.label.node)).2 : ℕ) : ZMod P)),
          ((((Nock.V1J8.Gen.hdl D.acs (VclL.tlN t.label.node)).1 : ℕ) : ZMod P),
            (if (VclL.tlN t.label.node).isCell then ((ComplJ8Data.ptrP P D.acs D.rows t.label.node : ℕ) : ZMod P)
              else (((Nock.V1J8.Gen.hdl D.acs (VclL.tlN t.label.node)).2 : ℕ) : ZMod P)))))⁻¹ := by
  have hidx := walkDBE_idx χe D t j hwA ht hcl
  rw [dE_hXi, hidx]
  show K6.toQ (compressE (coOfA χe).γH (coOfA χe).ρH _)⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  have hs : ((hRn D t).2 : ZMod P) =
      (if (VclL.tlN t.label.node).isCell then ((ComplJ8Data.ptrP P D.acs D.rows t.label.node : ℕ) : ZMod P)
        else (((Nock.V1J8.Gen.hdl D.acs (VclL.tlN t.label.node)).2 : ℕ) : ZMod P)) := by
    unfold hRn; split_ifs <;> rfl
  have hf := hRn_fst D t
  congr 1
  simp [FiniteIO.compress, Walk.rlc, recDen, Fin.sum_univ_five, toQ_lq, algQ, GenPortJ9AHAtomRow.hdN'_eq,
    Nock.V1J8.Gen.hK, coOfA, hγQ, hρQ, algQ', ← hs, hf]
  first
    | (rw [zero_add]; rfl)
    | (rw [zero_add]; simp only [algQ']; rfl)
    | (rw [zero_add]; simp only [algQ])
    | exact comb5 (R := Quad ((AdjoinRoot.of cubicPoly) deltaF)) _ _ _ _ _ _
    | exact comb4 (R := Quad ((AdjoinRoot.of cubicPoly) deltaF)) _ _ _ _ _

omit hwA hsm ht hcl in
theorem toQ_hPLi :
    K6.toQ (dE χe D t j).hPLi =
      (ComplJ8Bad.ρH deltaF (toχ χe) + recDenP 0 (ComplJ8Bad.γH deltaF (toχ χe))
        (((ComplJ8Data.rIAP P D.acs t.label.root : ℕ) : ZMod P),
          (2 * ((VclL.axisFold t.label.bits : ℕ) : ZMod P)),
          ((((Nock.V1J8.Gen.hdl D.acs (VclL.hdN t.label.node)).1 : ℕ) : ZMod P),
            (((Nock.V1J8.Gen.hdl D.acs (VclL.hdN t.label.node)).2 : ℕ) : ZMod P))))⁻¹ := by
  have hridx := walkDBE_ridx χe D t j
  have : (dE χe D t j).hPLi = (dB χe D t j).hPLi := by
    unfold dE Nock.V1J8.Gen.walkDBE; split <;> rfl
  rw [this]
  show K6.toQ (compressE (coOfA χe).γH (coOfA χe).ρH _)⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  have hridx' : Nock.V1J8.Gen.wIdx (ComplJ8Data.rIAP P D.acs) D.acs (GenPortJ9AHWalkBfs.wrowOf t) = _ := rfl
  have hr : ComplJ8Data.rIAP P D.acs t.label.root = (dB χe D t j).ridx := rfl
  congr 1
  simp [FiniteIO.compress, Walk.rlc, recDenP, Fin.sum_univ_four, toQ_lq, algQ, GenPortJ9AHAtomRow.hdN'_eq,
    Nock.V1J8.Gen.hK, coOfA, hγQ, hρQ, algQ', GenPortJ9AHWalkBfs.wrowOf]
  first
    | (erw [zero_add]; rfl)
    | (erw [zero_add]; simp only [algQ'])
    | (congr 1; erw [zero_add]; rfl)
    | (exact (congrArg _ (by erw [zero_add]; rfl)))

omit hwA hsm ht hcl in
theorem toQ_hPRi :
    K6.toQ (dE χe D t j).hPRi =
      (ComplJ8Bad.ρH deltaF (toχ χe) + recDenP 0 (ComplJ8Bad.γH deltaF (toχ χe))
        (((ComplJ8Data.rIAP P D.acs t.label.root : ℕ) : ZMod P),
          (2 * ((VclL.axisFold t.label.bits : ℕ) : ZMod P) + 1),
          ((((Nock.V1J8.Gen.hdl D.acs (VclL.tlN t.label.node)).1 : ℕ) : ZMod P),
            (if (VclL.tlN t.label.node).isCell then ((ComplJ8Data.ptrP P D.acs D.rows t.label.node : ℕ) : ZMod P)
              else (((Nock.V1J8.Gen.hdl D.acs (VclL.tlN t.label.node)).2 : ℕ) : ZMod P)))))⁻¹ := by
  have hridx := walkDBE_ridx χe D t j
  rw [dE_hPRi]
  show K6.toQ (compressE (coOfA χe).γH (coOfA χe).ρH _)⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  have hs : ((hRn D t).2 : ZMod P) =
      (if (VclL.tlN t.label.node).isCell then ((ComplJ8Data.ptrP P D.acs D.rows t.label.node : ℕ) : ZMod P)
        else (((Nock.V1J8.Gen.hdl D.acs (VclL.tlN t.label.node)).2 : ℕ) : ZMod P)) := by
    unfold hRn; split_ifs <;> rfl
  have hf := hRn_fst D t
  rw [hridx]
  congr 1
  simp [FiniteIO.compress, Walk.rlc, recDenP, Fin.sum_univ_four, toQ_lq, algQ, coOfA, hγQ, hρQ, algQ',
    ← hs, hf]
  first
    | (erw [zero_add]; rfl)
    | (erw [zero_add]; simp only [algQ'])
    | (congr 1; erw [zero_add]; rfl)
    | (exact (congrArg _ (by erw [zero_add]; rfl)))

/-! ## The node value -/

omit hwA hsm ht hcl in
theorem toK_reim(x : K6) (y : KQ) (h : K6.toQ x = y) :
    K3.toK x.re = Quad.re _ y ∧ K3.toK x.im = Quad.im _ y := by
  subst h
  exact ⟨(Quad.re_mk _ _ _).symm, (Quad.im_mk _ _ _).symm⟩

omit hwA hsm ht hcl in
theorem toK_natG(n : ℕ) : K3.toK (g3 (natG n)) = algebraMap (ZMod P) KC (n : ZMod P) := by
  rw [toK_g3, toZ_natG]

theorem toK_curD (γ : K3) (γ' : KC) (hγ : K3.toK γ = γ') :
    K3.toK (Nock.V1J8.Gen.curD γ (dE χe D t j)) =
      ComplJ9BAWR.wNodeValR deltaF (GlobalCarryRecognizer.enc (ComplJ8Of.zA deltaF (toχ χe)))
        (ComplJ8Data.rIAP P D.acs) γ' t := by
  obtain ⟨p1, p2⟩ := toK_reim _ _ (congrArg ComputeTable.FP.size (toQ_pE χe D t j hwA hsm ht))
  obtain ⟨p3, p4⟩ := toK_reim _ _ (congrArg ComputeTable.FP.dyck (toQ_pE χe D t j hwA hsm ht))
  obtain ⟨p5, p6⟩ := toK_reim _ _ (congrArg ComputeTable.FP.leaf (toQ_pE χe D t j hwA hsm ht))
  obtain ⟨r1, r2⟩ := toK_reim _ _ (congrArg ComputeTable.FP.size (toQ_rootE χe D t j hwA hsm ht))
  obtain ⟨r3, r4⟩ := toK_reim _ _ (congrArg ComputeTable.FP.dyck (toQ_rootE χe D t j hwA hsm ht))
  obtain ⟨r5, r6⟩ := toK_reim _ _ (congrArg ComputeTable.FP.leaf (toQ_rootE χe D t j hwA hsm ht))
  have hridx := walkDBE_ridx χe D t j
  have hw := dE_w χe D t j
  have hpre : (dE χe D t j).w.pre = VclL.axisFold t.label.bits := by rw [hw]; rfl
  have hlen : (dE χe D t j).w.len = t.label.bits.length := by rw [hw]; rfl
  subst hγ
  simp only [Nock.V1J8.Gen.curD, Nock.V1J8.Gen.rlcE, Nock.V1J8.Gen.encW,ComplJ9BAWR.wNodeValR, Walk.rlc, WalkVCL.enc, ComplJ9BAWR.lblWR,
    ComplJ9BAWR.dtWR, List.foldl,
    Fin.sum_univ_succ, Fin.sum_univ_zero, K3.toK_add, K3.toK_mul, K3.toK_zero, K3.toK_one, toK_natG, hpre,
    hridx, hlen, p1, p2, p3, p4, p5, p6, r1, r2, r3, r4, r5, r6]
  simp
  ring

theorem toK_curD_chals :
    K3.toK (Nock.V1J8.Gen.curD (chalsAJ8ZE χe 1) (dE χe D t j)) =
      ComplJ9BAWR.wNodeValR deltaF (GlobalCarryRecognizer.enc (ComplJ8Of.zA deltaF (toχ χe)))
        (ComplJ8Data.rIAP P D.acs) (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe) 1) t :=
  toK_curD χe D t j hwA hsm ht hcl _ _ (toK_chalsA χe 1)

/-! ## Columns `2 … 24` -/

theorem walkColDBE_lo (hne : D.preads ≠ []) (hjN : j < nVOf D) (hjt : wTrie D.acs D.preads j = t)
    (N kr q : ℕ) (ln cnt acc : K3) (xa pa hxa hpa : K6) (c : ℕ) (hc2 : 2 ≤ c) (hc25 : c < 25)
    (hq : (q : ZMod P) = ((GenWalk.qH (krW D.acs D.preads) (foCol (walkRows D.acs D.preads)) (j + 1) : ℕ) : ZMod P)) :
    (if c = 24 ∧ (Nock.V1J8.Gen.tlN' (dE χe D t j).w.node).isCell then
        ((ComplJ8Data.ptrP P D.acs D.rows (dE χe D t j).w.node : ℕ) : ZMod P)
      else Nock.V1J8.Gen.walkColDB Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8.certB (Nock.V1J8.Gen.hdl D.acs) N kr q
        (dE χe D t j) ln cnt acc xa pa hxa hpa c) =
      (if c < 21 then (ComplJ9BBalF.vRow9 deltaF D (toχ χe) j).base kr j c
       else if c = 21 then kLV9 D ⟨j, hjN⟩ else if c = 22 then vLV9 D ⟨j, hjN⟩
       else if c = 23 then kRV9 D ⟨j, hjN⟩ else vRV9 D ⟨j, hjN⟩) := by
  subst hjt
  have hidx := walkDBE_idx χe D _ j hwA ht hcl
  have hridx := walkDBE_ridx χe D (wTrie D.acs D.preads j) j
  have hw := dE_w χe D (wTrie D.acs D.preads j) j
  have hj' : (dE χe D (wTrie D.acs D.preads j) j).j = j := by rw [walkDBE_j]; rfl
  have hb : ∀ b b' : Bool, Nock.V1J8.Gen.flag (b && b') =
      (if b then (1 : ZMod P) else 0) * (if b' then 1 else 0) := by
    intro b b'; cases b <;> cases b' <;> simp [Nock.V1J8.Gen.flag]
  interval_cases c <;>
    (simp [Nock.V1J8.Gen.walkColDB, Nock.V1J8.Gen.walkColD, WalkVals.base, WalkVals.named, ComplJ9BAWR.walkRow0R,
      hidx, hridx, hw, hj', GenPortJ9AHWalkBfs.wrowOf, Nock.V1J8.Gen.flag, hb, hq, GenPortJ9AHAtomRow.tlN'_eq,
      GenPortJ9AHAtomRow.hdN'_eq, Nat.cast_mul, certB_cast, kLV9, vLV9, kRV9, vRV9, ComplJ9BBalF.HA, vNode,
      ComplJ9BBalF.vRow9]) <;> (try (split_ifs <;> simp_all))

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRowH

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRowH in
#print axioms toQ_hXi
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRowH in
#print axioms toQ_hPLi
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRowH in
#print axioms toQ_hPRi
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRowH in
#print axioms toK_curD
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRowH in
#print axioms toK_curD_chals
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRowH in
#print axioms walkColDBE_lo
