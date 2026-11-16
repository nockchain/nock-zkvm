/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAWRow.lean

  One trie row
  `t ∈ walkRows D.acs D.preads` at a time, generic `D`. -/
import Nock.V1J8.FillAtom
import Nock.V1J8.GenAtom
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9BBalF
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAtomRow
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCellRow
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkBfs

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
open Nock.V1J8.Gen (P)

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow

/-! ## 1. Preliminary lemmas -/

theorem certB_cast (L i : ℕ) :
    (((Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8.certB L i : ℕ) : ZMod P)) =
      certBit (F := ZMod P) (61 - L) i := by
  unfold Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8.certB Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8.certS certBit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one ((61 - L) / 2 ^ i) with h | h <;> simp [h]

theorem combP_eq : Nock.V1J8.Gen.combP = ComplJ8Data.combPP P := rfl

/-! ## 2. Small nodes, roots, serials -/

theorem small_hdN {n : Noun} (h : GenPortJ9AHAtomRow.Small n) :
    GenPortJ9AHAtomRow.Small (Nock.NockVMROM.Thm54.VclL.hdN n) := by
  cases n with
  | atom a => exact h
  | cell a b => exact h.1

theorem small_tlN {n : Noun} (h : GenPortJ9AHAtomRow.Small n) :
    GenPortJ9AHAtomRow.Small (Nock.NockVMROM.Thm54.VclL.tlN n) := by
  cases n with
  | atom a => exact h
  | cell a b => exact h.2

/-- Every row's root is some row's node (the walk's root row, at side bits `[]`). -/
theorem root_is_node (cells : List Noun) (preads : List (Noun × ℕ)) {t : NTree WN}
    (ht : t ∈ walkRows cells preads) :
    ∃ u ∈ walkRows cells preads, u.label.node = t.label.root := by
  have hb := (mem_bfsForest (walkForest cells preads) t).1 ht
  obtain ⟨c, hc, hIn⟩ := hb
  have hcm : c ∈ walkRows cells preads :=
    (mem_bfsForest (walkForest cells preads) c).2 ⟨c, hc, InTree.here c⟩
  rcases mem_walkForest hc with ⟨-, hc'⟩ | ⟨r, -, hc'⟩
  · obtain ⟨n', bs', T', ht', -⟩ := inTree_trie_inv (cells.headD (.atom 0)) (fun _ _ _ => True)
      (fun _ _ _ _ _ _ _ => trivial) hIn _ _ _ hc' trivial
    refine ⟨c, hcm, ?_⟩
    rw [ht', hc', (trie_label _ _ _ _).1, (trie_label _ _ _ _).2.2]
  · obtain ⟨n', bs', T', ht', -⟩ := inTree_trie_inv r (fun _ _ _ => True)
      (fun _ _ _ _ _ _ _ => trivial) hIn _ _ _ hc' trivial
    refine ⟨c, hcm, ?_⟩
    rw [ht', hc', (trie_label _ _ _ _).1, (trie_label _ _ _ _).2.2]

section
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))] [Fact (ringChar (ZMod P)).Prime]
  [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

theorem toK_chalsA (χe : CoinsE) (i : ℕ) :
    K3.toK (chalsAJ8ZE χe i) = ChalsAZJ8.chalsAJ8Z deltaF (toχ χe) i :=
  chalsAJ8ZE_spec χe i

/-- The executable atom-walk row at trie row `t` (index `j`), at the generator's pointer, handles and serials. -/
noncomputable abbrev dE (χe : CoinsE) (D : J8Data P Rg fuel s f r) (t : NTree WN) (j : ℕ) : Nock.V1J8.Gen.WalkD :=
  Nock.V1J8.Gen.walkDBE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) (Nock.V1J8.Gen.hdl D.acs)
    (ComplJ8Data.rIAP P D.acs) D.acs (GenPortJ9AHWalkBfs.wrowOf t) j

/-- The matching plain `walkDB` row. -/
abbrev dB (χe : CoinsE) (D : J8Data P Rg fuel s f r) (t : NTree WN) (j : ℕ) : Nock.V1J8.Gen.WalkD :=
  Nock.V1J8.Gen.walkDB (coOfA χe) (yE χe) (Nock.V1J8.Gen.hdl D.acs)
    (ComplJ8Data.rIAP P D.acs) D.acs (GenPortJ9AHWalkBfs.wrowOf t) j

variable (χe : CoinsE) (D : J8Data P Rg fuel s f r) (t : NTree WN) (j : ℕ)

/-! ## 3. `walkDBE`'s fields are `walkDB`'s (all but `hXi`, `hPRi`) -/

theorem walkDBE_w : (dE χe D t j).w = (dB χe D t j).w := by
  unfold dE dB Nock.V1J8.Gen.walkDBE; split <;> rfl
theorem walkDBE_j : (dE χe D t j).j = (dB χe D t j).j := by
  unfold dE dB Nock.V1J8.Gen.walkDBE; split <;> rfl
theorem walkDBE_pE : (dE χe D t j).pE = (dB χe D t j).pE := by
  unfold dE dB Nock.V1J8.Gen.walkDBE; split <;> rfl
theorem walkDBE_lE : (dE χe D t j).lE = (dB χe D t j).lE := by
  unfold dE dB Nock.V1J8.Gen.walkDBE; split <;> rfl
theorem walkDBE_rE : (dE χe D t j).rE = (dB χe D t j).rE := by
  unfold dE dB Nock.V1J8.Gen.walkDBE; split <;> rfl
theorem walkDBE_rootE : (dE χe D t j).rootE = (dB χe D t j).rootE := by
  unfold dE dB Nock.V1J8.Gen.walkDBE; split <;> rfl
theorem walkDBE_idx' : (dE χe D t j).idx = (dB χe D t j).idx := by
  unfold dE dB Nock.V1J8.Gen.walkDBE; split <;> rfl
theorem walkDBE_ridx' : (dE χe D t j).ridx = (dB χe D t j).ridx := by
  unfold dE dB Nock.V1J8.Gen.walkDBE; split <;> rfl
theorem walkDBE_xInv : (dE χe D t j).xInv = (dB χe D t j).xInv := by
  unfold dE dB Nock.V1J8.Gen.walkDBE; split <;> rfl
theorem walkDBE_pInvL : (dE χe D t j).pInvL = (dB χe D t j).pInvL := by
  unfold dE dB Nock.V1J8.Gen.walkDBE; split <;> rfl
theorem walkDBE_pInvR : (dE χe D t j).pInvR = (dB χe D t j).pInvR := by
  unfold dE dB Nock.V1J8.Gen.walkDBE; split <;> rfl

theorem dE_w : (dE χe D t j).w = GenPortJ9AHWalkBfs.wrowOf t := walkDBE_w χe D t j

/-! ## 4. Encodings -/

variable (hwA : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs)
  (hsm : ∀ y ∈ D.acs, GenPortJ9AHAtomRow.Small y) (ht : t ∈ walkRows D.acs D.preads)
include hwA hsm ht

theorem small_node : GenPortJ9AHAtomRow.Small t.label.node := hsm _ (hwA _ ht)

theorem small_root : GenPortJ9AHAtomRow.Small t.label.root := by
  obtain ⟨u, hu, hue⟩ := root_is_node D.acs D.preads ht
  rw [← hue]; exact hsm _ (hwA _ hu)

omit hwA hsm ht in
theorem toQ_encA (n : Noun) (hn : GenPortJ9AHAtomRow.Small n) :
    (encE (yE χe) (yE χe) n).toQ = GlobalCarryRecognizer.enc (ComplJ8Of.zA deltaF (toχ χe)) n := by
  rw [GenPortJ9AHAtomRow.toQ_encE_small _ _ n hn, GenPortJ9AHAtomRow.toQ_yE_zA]

theorem toQ_pE : (dE χe D t j).pE.toQ =
    GlobalCarryRecognizer.enc (ComplJ8Of.zA deltaF (toχ χe)) t.label.node := by
  rw [walkDBE_pE]
  exact toQ_encA χe t.label.node (small_node D t hwA hsm ht)

theorem toQ_lE : (dE χe D t j).lE.toQ =
    GlobalCarryRecognizer.enc (ComplJ8Of.zA deltaF (toχ χe)) (Nock.NockVMROM.Thm54.VclL.hdN t.label.node) := by
  rw [walkDBE_lE]
  have := toQ_encA χe (Nock.V1J8.Gen.hdN' t.label.node) (by
    rw [GenPortJ9AHAtomRow.hdN'_eq]; exact small_hdN (small_node D t hwA hsm ht))
  rw [GenPortJ9AHAtomRow.hdN'_eq] at this
  exact this

theorem toQ_rE : (dE χe D t j).rE.toQ =
    GlobalCarryRecognizer.enc (ComplJ8Of.zA deltaF (toχ χe)) (Nock.NockVMROM.Thm54.VclL.tlN t.label.node) := by
  rw [walkDBE_rE]
  have := toQ_encA χe (Nock.V1J8.Gen.tlN' t.label.node) (by
    rw [GenPortJ9AHAtomRow.tlN'_eq]; exact small_tlN (small_node D t hwA hsm ht))
  rw [GenPortJ9AHAtomRow.tlN'_eq] at this
  exact this

theorem toQ_rootE : (dE χe D t j).rootE.toQ =
    GlobalCarryRecognizer.enc (ComplJ8Of.zA deltaF (toχ χe)) t.label.root := by
  rw [walkDBE_rootE]
  exact toQ_encA χe t.label.root (small_root D t hwA hsm ht)

/-! ## 5. Serials -/

omit hsm in
theorem walkDBE_idx (hcl : ∀ y ∈ D.acs, y.isCell = true) :
    (dE χe D t j).idx = ComplJ9BAWR.idxRW D.acs (ComplJ8Data.rIAP P D.acs) t := by
  rw [walkDBE_idx']
  show Nock.V1J8.Gen.wIdx (ComplJ8Data.rIAP P D.acs) D.acs (GenPortJ9AHWalkBfs.wrowOf t) = _
  unfold Nock.V1J8.Gen.wIdx ComplJ9BAWR.idxRW
  have hlen : (GenPortJ9AHWalkBfs.wrowOf t).len = 0 ↔ t.label.bits = [] := by
    show t.label.bits.length = 0 ↔ _
    exact List.length_eq_zero_iff
  by_cases hb : t.label.bits = []
  · rw [if_pos (hlen.2 hb), if_pos hb]; rfl
  · rw [if_neg (fun h => hb (hlen.1 h)), if_neg hb]
    have key : ∀ n : Noun, n.isCell = true → n ∈ D.acs →
        Nock.V1J8.Gen.idxN D.acs n = D.acs.idxOf n := by
      intro n h hm
      cases n with
      | atom a => simp [Noun.isCell] at h
      | cell a b => exact GenPortJ9AHCellRow.idxOf_mem D.acs _ hm
    exact key _ (hcl _ (hwA _ ht)) (hwA _ ht)

omit hwA hsm ht in
theorem walkDBE_ridx : (dE χe D t j).ridx = ComplJ8Data.rIAP P D.acs t.label.root := by
  rw [walkDBE_ridx']; rfl

/-! ## 6. The `𝕂′` inverses against the honest filled row -/

/-- The honest J-9 atom-walk row at trie row `j` (root serial `rIAP`, encoder `enc zA`). -/
noncomputable abbrev rowW (α γ : KC) : WalkVals (ZMod P) KC (Quad (algebraMap (ZMod P) KC deltaF)) :=
  ComplJ9BAWR.walkRow0R deltaF (GlobalCarryRecognizer.enc (ComplJ8Of.zA deltaF (toχ χe))) D.acs
    (ComplJ8Data.rIAP P D.acs) D.preads α γ j

theorem toQ_xInv0 (hcl : ∀ y ∈ D.acs, y.isCell = true) (α γ : KC) (hjt : wTrie D.acs D.preads j = t) :
    K6.toQ (dE χe D t j).xInv =
      (FiniteIO.compress (m := 11)
        (⟨ComplJ8Of.γV deltaF (toχ χe), ComplJ8Of.ρV deltaF (toχ χe)⟩ : FiniteIO.IOCoins _)
        (wxKeyV deltaF (rowW χe D j α γ)))⁻¹ := by
  subst hjt
  have hp := toQ_pE χe D _ j hwA hsm ht
  have hl := toQ_lE χe D _ j hwA hsm ht
  have hr := toQ_rE χe D _ j hwA hsm ht
  rw [walkDBE_pE] at hp
  rw [walkDBE_lE] at hl
  rw [walkDBE_rE] at hr
  have hi : liftQ (K := KC) deltaF (((dB χe D (wTrie D.acs D.preads j) j).idx : ℕ) : ZMod P) =
      liftQ (K := KC) deltaF (rowW χe D j α γ).idx := by
    rw [← walkDBE_idx', walkDBE_idx χe D _ j hwA ht hcl]; rfl
  rw [walkDBE_xInv]
  show K6.toQ (compressE (coOfA χe).γ (coOfA χe).ρ _)⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  fin_cases c
  · exact congrArg ComputeTable.FP.size hp
  · exact congrArg ComputeTable.FP.dyck hp
  · exact congrArg ComputeTable.FP.leaf hp
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · exact (toQ_lq _).trans hi
  · exact (toQ_lq 0).trans (by rw [Nat.cast_zero]; rfl)

theorem toQ_pInvL0 (α γ : KC) (hjt : wTrie D.acs D.preads j = t) :
    K6.toQ (dE χe D t j).pInvL =
      (FiniteIO.compress (m := 8)
        (⟨ComplJ8Of.γV deltaF (toχ χe), ComplJ8Of.ρV deltaF (toχ χe)⟩ : FiniteIO.IOCoins _)
        (wrecLV deltaF (rowW χe D j α γ)))⁻¹ := by
  subst hjt
  have hq := toQ_rootE χe D _ j hwA hsm ht
  have hl := toQ_lE χe D _ j hwA hsm ht
  rw [walkDBE_rootE] at hq
  rw [walkDBE_lE] at hl
  have hi : liftQ (K := KC) deltaF (((dB χe D (wTrie D.acs D.preads j) j).ridx : ℕ) : ZMod P) =
      liftQ (K := KC) deltaF (rowW χe D j α γ).ridx := by
    rw [← walkDBE_ridx', walkDBE_ridx]; rfl
  have hpre : liftQ (K := KC) deltaF
      ((2 * (dB χe D (wTrie D.acs D.preads j) j).w.pre : ℕ) : ZMod P) =
      liftQ (K := KC) deltaF (2 * (rowW χe D j α γ).pre) := by
    push_cast; rfl
  rw [walkDBE_pInvL]
  show K6.toQ (compressE (coOfA χe).γ (coOfA χe).ρ _)⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  fin_cases c
  · exact congrArg ComputeTable.FP.size hq
  · exact congrArg ComputeTable.FP.dyck hq
  · exact congrArg ComputeTable.FP.leaf hq
  · exact congrArg ComputeTable.FP.size hl
  · exact congrArg ComputeTable.FP.dyck hl
  · exact congrArg ComputeTable.FP.leaf hl
  · exact (toQ_lq _).trans hpre
  · exact (toQ_lq _).trans hi

theorem toQ_pInvR0 (α γ : KC) (hjt : wTrie D.acs D.preads j = t) :
    K6.toQ (dE χe D t j).pInvR =
      (FiniteIO.compress (m := 8)
        (⟨ComplJ8Of.γV deltaF (toχ χe), ComplJ8Of.ρV deltaF (toχ χe)⟩ : FiniteIO.IOCoins _)
        (wrecRV deltaF (rowW χe D j α γ)))⁻¹ := by
  subst hjt
  have hq := toQ_rootE χe D _ j hwA hsm ht
  have hr := toQ_rE χe D _ j hwA hsm ht
  rw [walkDBE_rootE] at hq
  rw [walkDBE_rE] at hr
  have hi : liftQ (K := KC) deltaF (((dB χe D (wTrie D.acs D.preads j) j).ridx : ℕ) : ZMod P) =
      liftQ (K := KC) deltaF (rowW χe D j α γ).ridx := by
    rw [← walkDBE_ridx', walkDBE_ridx]; rfl
  have hpre : liftQ (K := KC) deltaF
      ((2 * (dB χe D (wTrie D.acs D.preads j) j).w.pre + 1 : ℕ) : ZMod P) =
      liftQ (K := KC) deltaF (2 * (rowW χe D j α γ).pre + 1) := by
    push_cast; rfl
  rw [walkDBE_pInvR]
  show K6.toQ (compressE (coOfA χe).γ (coOfA χe).ρ _)⁻¹ = _
  rw [K6.toQ_inv, toQ_compressE]
  congr 2
  funext c
  fin_cases c
  · exact congrArg ComputeTable.FP.size hq
  · exact congrArg ComputeTable.FP.dyck hq
  · exact congrArg ComputeTable.FP.leaf hq
  · exact congrArg ComputeTable.FP.size hr
  · exact congrArg ComputeTable.FP.dyck hr
  · exact congrArg ComputeTable.FP.leaf hr
  · exact (toQ_lq _).trans hpre
  · exact (toQ_lq _).trans hi

/-! ## 7. The card's statements, against `walkFillInv` -/

theorem toQ_xInv (hcl : ∀ y ∈ D.acs, y.isCell = true) (α γ : KC) (hjt : wTrie D.acs D.preads j = t) :
    K6.toQ (dE χe D t j).xInv =
      (walkFillInv deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe))
        (rowW χe D j α γ)).xInv := toQ_xInv0 χe D t j hwA hsm ht hcl α γ hjt

theorem toQ_pInvL (α γ : KC) (hjt : wTrie D.acs D.preads j = t) :
    K6.toQ (dE χe D t j).pInvL =
      (walkFillInv deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe))
        (rowW χe D j α γ)).pInvL := toQ_pInvL0 χe D t j hwA hsm ht α γ hjt

theorem toQ_pInvR (α γ : KC) (hjt : wTrie D.acs D.preads j = t) :
    K6.toQ (dE χe D t j).pInvR =
      (walkFillInv deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe))
        (rowW χe D j α γ)).pInvR := toQ_pInvR0 χe D t j hwA hsm ht α γ hjt

end

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms certB_cast
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms combP_eq
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms root_is_node
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms toK_chalsA
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms walkDBE_idx
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms walkDBE_ridx
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms toQ_pE
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms toQ_lE
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms toQ_rE
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms toQ_rootE
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms toQ_xInv
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms toQ_pInvL
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRow in
#print axioms toQ_pInvR
