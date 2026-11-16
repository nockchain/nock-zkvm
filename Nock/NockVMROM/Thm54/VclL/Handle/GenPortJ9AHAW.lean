/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHAW.lean

  Reuses `dE`, `toQ_*`, `toK_curD_chals`, `walkColDBE_lo`, `q_eq`, `walkLCA_eq` and the scan lemmas. -/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRowH
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkAcc
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHCell

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
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAWRowH
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8OfAtom (chalsAZ_0 chalsAZ_1 zA_eq)
open Nock.V1J8.Gen (P WRow WalkD walkDBE walkColDB walkColD wroleD hsD fpD ioD pTermD hPTermD scanN scanK6
  lastK6 childSums walkLCA curD foW walkGenRowsBE hdl tlN' hdN')

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW

/-! ## 0. `wrowOf` -/

theorem wrowOf_eq : GenPortJ9AHWalkBfs.wrowOf = GenPortJ9AHWalkAcc.wrowOf := funext fun _ => rfl

/-! ## 1. The exec table's cell access -/

/-- The executable row data list of `walkGenRowsBE`. -/
def dsL (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun) (ws : List WRow) :
    List WalkD :=
  (ws.zipIdx 0).map fun (w, j) => walkDBE ptr k y H rI cs w j

/-- The executable `(ln, cnt, acc)` list. -/
def lcaL (ptr : Noun → ℕ) (k : Co) (y : K6) (α γ : K3) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (ws : List WRow) (kr : ℕ) : List (K3 × K3 × K3) :=
  walkLCA α kr (ws.map foW) (childSums α kr (ws.map foW) ((dsL ptr k y H rI cs ws).map (curD γ)).toArray)
    ((dsL ptr k y H rI cs ws).map (curD γ))

theorem dsL_getD (ptr : Noun → ℕ) (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun)
    (ws : List WRow) (j : ℕ) (hj : j < ws.length) (z : WalkD) (d : WRow) :
    (dsL ptr k y H rI cs ws).getD j z = walkDBE ptr k y H rI cs (ws.getD j d) j := by
  unfold dsL
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hj]

theorem walkGenRowsBE_getD (ptr : Noun → ℕ) (k : Co) (y : K6) (α γ : K3) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ)
    (cert : ℕ → ℕ → ℕ) (cs : List Noun) (ws : List WRow) (kr : ℕ) (i c : ℕ) (hi : i < ws.length) (hc : c < 166)
    (d : WalkD)
    (hd : d = (dsL ptr k y H rI cs ws).getD i
      (walkDBE ptr k y H rI cs (ws.getD i ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩) i)) :
    ((walkGenRowsBE ptr k y α γ H rI cert cs ws kr).1.getD i #[]).getD c 0 =
      (if c = 24 ∧ (tlN' d.w.node).isCell then ((ptr d.w.node : ℕ) : ZMod P) else
        walkColDB cert H ws.length kr (kr + (scanN (ws.map foW)).getD i 0 - (i + 1)) d
          ((lcaL ptr k y α γ H rI cs ws kr).getD i (0, 0, 0)).1
          ((lcaL ptr k y α γ H rI cs ws kr).getD i (0, 0, 0)).2.1
          ((lcaL ptr k y α γ H rI cs ws kr).getD i (0, 0, 0)).2.2
          ((scanK6 ((dsL ptr k y H rI cs ws).map (·.xInv))).getD i 0)
          ((scanK6 ((dsL ptr k y H rI cs ws).map pTermD)).getD i 0)
          ((scanK6 ((dsL ptr k y H rI cs ws).map (·.hXi))).getD i 0)
          ((scanK6 ((dsL ptr k y H rI cs ws).map hPTermD)).getD i 0) c) := by
  subst hd
  unfold walkGenRowsBE
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  simp only [Array.getElem?_ofFn]
  rw [dif_pos hc]
  have e24 : ((⟨c, hc⟩ : Fin 166) = 24) ↔ c = 24 := by simp [Fin.ext_iff]
  simp only [Option.getD_some, e24]
  rfl

theorem coordN_toK' (x : K3) (m : ℕ) : coordN powerBasis3 (K3.toK x) m = limbZ x (m % 3) := by
  rw [coordN, coord_K _ _ (Nat.mod_lt _ (by norm_num))]

/-! ## 2. Role / handle column unfoldings of the exec column -/

theorem walkColDB_role (cert : ℕ → ℕ → ℕ) (H : Noun → ℕ × ℕ) (N kr q : ℕ) (d : WalkD) (ln cnt acc : K3)
    (xa pa hxa hpa : K6) (c : ℕ) (h1 : 25 ≤ c) (h2 : c < 136) :
    walkColDB cert H N kr q d ln cnt acc xa pa hxa hpa c =
      limbZ (wroleD d ln cnt acc xa pa ((c - 25) / 3)) ((c - 25) % 3) := by
  have n0 : c ≠ 0 := by omega
  have n1 : c ≠ 1 := by omega
  have n2 : c ≠ 2 := by omega
  have n3 : c ≠ 3 := by omega
  have n4 : c ≠ 4 := by omega
  have n5 : c ≠ 5 := by omega
  have n6 : c ≠ 6 := by omega
  have n7 : c ≠ 7 := by omega
  have n8 : c ≠ 8 := by omega
  have n9 : c ≠ 9 := by omega
  have n10 : c ≠ 10 := by omega
  have n11 : c ≠ 11 := by omega
  have n12 : c ≠ 12 := by omega
  have n13 : c ≠ 13 := by omega
  have n14 : c ≠ 14 := by omega
  have n21 : c ≠ 21 := by omega
  have n22 : c ≠ 22 := by omega
  have n23 : c ≠ 23 := by omega
  have n24 : c ≠ 24 := by omega
  have l21 : ¬ c < 21 := by omega
  have l2 : ¬ (15 ≤ c ∧ c < 21) := by omega
  have l136 : c < 136 := h2
  simp only [walkColDB, walkColD, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n21, n22, n23,
    n24, l21, l2, l136, if_false, if_true, and_false]

theorem walkColDB_hand (cert : ℕ → ℕ → ℕ) (H : Noun → ℕ × ℕ) (N kr q : ℕ) (d : WalkD) (ln cnt acc : K3)
    (xa pa hxa hpa : K6) (c : ℕ) (h1 : 136 ≤ c) :
    walkColDB cert H N kr q d ln cnt acc xa pa hxa hpa c =
      limbZ (if ((c - 136) / 3) % 2 = 0 then (hsD d hxa hpa (((c - 136) / 3) / 2)).re
        else (hsD d hxa hpa (((c - 136) / 3) / 2)).im) ((c - 136) % 3) := by
  have n0 : c ≠ 0 := by omega
  have n1 : c ≠ 1 := by omega
  have n2 : c ≠ 2 := by omega
  have n3 : c ≠ 3 := by omega
  have n4 : c ≠ 4 := by omega
  have n5 : c ≠ 5 := by omega
  have n6 : c ≠ 6 := by omega
  have n7 : c ≠ 7 := by omega
  have n8 : c ≠ 8 := by omega
  have n9 : c ≠ 9 := by omega
  have n10 : c ≠ 10 := by omega
  have n11 : c ≠ 11 := by omega
  have n12 : c ≠ 12 := by omega
  have n13 : c ≠ 13 := by omega
  have n14 : c ≠ 14 := by omega
  have n21 : c ≠ 21 := by omega
  have n22 : c ≠ 22 := by omega
  have n23 : c ≠ 23 := by omega
  have n24 : c ≠ 24 := by omega
  have l21 : ¬ c < 21 := by omega
  have l2 : ¬ (15 ≤ c ∧ c < 21) := by omega
  have l136 : ¬ c < 136 := by omega
  simp only [walkColDB, walkColD, n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n21, n22, n23,
    n24, l21, l2, l136, if_false, if_true, and_false]

theorem getD_map_lt {α β : Type} (f : α → β) (l : List α) (j : ℕ) (hj : j < l.length) (d : α) (z : β) :
    (l.map f).getD j z = f (l.getD j d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]

/-! ## 3. Row facts -/

section Row
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))] [Fact (ringChar (ZMod P)).Prime]
  [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}

/-- The exec atom walk at a generic record (present case). -/
noncomputable abbrev awE (χe : CoinsE) (D : J8Data P Rg fuel s f r) :=
  Nock.V1J8.Gen.walkGenRowsBE (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) (chalsAJ8ZE χe 0)
    (chalsAJ8ZE χe 1) (Nock.V1J8.Gen.hdl D.acs) (ComplJ8Data.rIAP P D.acs)
    Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8.certB D.acs
    ((walkRows D.acs D.preads).map GenPortJ9AHWalkBfs.wrowOf) (krW D.acs D.preads)

variable (χe : CoinsE) (D : J8Data P Rg fuel s f r)

/-- The exec row data list. -/
noncomputable abbrev dsE : List WalkD :=
  dsL (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) (Nock.V1J8.Gen.hdl D.acs) (ComplJ8Data.rIAP P D.acs)
    D.acs ((walkRows D.acs D.preads).map GenPortJ9AHWalkBfs.wrowOf)

theorem nVOf_eq (hne : D.preads ≠ []) : nVOf D = (walkRows D.acs D.preads).length := by
  unfold nVOf; rw [if_neg hne]

theorem krVOf_eq (hne : D.preads ≠ []) : krVOf D = krW D.acs D.preads := by
  unfold krVOf; rw [if_neg hne]

theorem walkGenRowsBE_size (hne : D.preads ≠ []) : (awE χe D).1.size = nVOf D := by
  rw [nVOf_eq D hne]
  unfold awE walkGenRowsBE
  simp

/-- The `j`-th exec row. -/
noncomputable abbrev dW (j : ℕ) : WalkD :=
  dE χe D (wTrie D.acs D.preads j) j

theorem dW_w (j : ℕ) : (dW χe D j).w = GenPortJ9AHWalkBfs.wrowOf (wTrie D.acs D.preads j) :=
  dE_w χe D _ j

theorem wrowOf_getD (j : ℕ) (hj : j < (walkRows D.acs D.preads).length) (d : WRow) :
    ((walkRows D.acs D.preads).map GenPortJ9AHWalkBfs.wrowOf).getD j d =
      GenPortJ9AHWalkBfs.wrowOf (wTrie D.acs D.preads j) := by
  simp [wTrie, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]

theorem dsE_getD (j : ℕ) (hj : j < (walkRows D.acs D.preads).length) (z : WalkD) :
    (dsE χe D).getD j z = dW χe D j := by
  rw [dsL_getD _ _ _ _ _ _ _ j (by simpa using hj) z ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩,
    wrowOf_getD D j hj]

/-- The honest values of row `j`, at the frame coins. -/
noncomputable abbrev α0 : KC := toχ χe ⟨0, by decide⟩
noncomputable abbrev γ0 : KC := toχ χe ⟨1, by decide⟩

theorem vRow9_eq : vRow9 deltaF D (toχ χe) = fun k => rowW χe D k (α0 χe) (γ0 χe) := by
  funext k
  unfold vRow9 rowW
  rw [zA_eq]

noncomputable abbrev vH (j : ℕ) : WalkVals (ZMod P) KC (Quad (algebraMap (ZMod P) KC deltaF)) :=
  walkFill deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe)) (fun k => rowW χe D k (α0 χe) (γ0 χe)) j

theorem vValsC9_eq (i : Fin (nVOf D)) : vValsC9 deltaF D (toχ χe) i = vH χe D i := by
  show walkFill deltaF _ _ (vRow9 deltaF D (toχ χe)) i = _
  rw [vRow9_eq]

variable (hwA : ∀ u ∈ walkRows D.acs D.preads, u.label.node ∈ D.acs)
  (hsm : ∀ y ∈ D.acs, GenPortJ9AHAtomRow.Small y)
  (hcl : ∀ y ∈ D.acs, y.isCell = true)
include hwA hsm hcl

theorem fp_toQ (j : ℕ) (hj : j < (walkRows D.acs D.preads).length) (t : ℕ) (ht : t < 12) :
    K6.toQ (fpD (dW χe D j) t) = (vH χe D j).fpSlot t := by
  have hm := wTrie_mem D.acs D.preads hj
  interval_cases t
  · exact congrArg ComputeTable.FP.size (toQ_pE χe D _ j hwA hsm hm)
  · exact congrArg ComputeTable.FP.dyck (toQ_pE χe D _ j hwA hsm hm)
  · exact congrArg ComputeTable.FP.leaf (toQ_pE χe D _ j hwA hsm hm)
  · exact congrArg ComputeTable.FP.size (toQ_lE χe D _ j hwA hsm hm)
  · exact congrArg ComputeTable.FP.dyck (toQ_lE χe D _ j hwA hsm hm)
  · exact congrArg ComputeTable.FP.leaf (toQ_lE χe D _ j hwA hsm hm)
  · exact congrArg ComputeTable.FP.size (toQ_rE χe D _ j hwA hsm hm)
  · exact congrArg ComputeTable.FP.dyck (toQ_rE χe D _ j hwA hsm hm)
  · exact congrArg ComputeTable.FP.leaf (toQ_rE χe D _ j hwA hsm hm)
  · exact congrArg ComputeTable.FP.size (toQ_rootE χe D _ j hwA hsm hm)
  · exact congrArg ComputeTable.FP.dyck (toQ_rootE χe D _ j hwA hsm hm)
  · exact congrArg ComputeTable.FP.leaf (toQ_rootE χe D _ j hwA hsm hm)

theorem xInv_eq (j : ℕ) (hj : j < (walkRows D.acs D.preads).length) :
    K6.toQ (dW χe D j).xInv = (vH χe D j).xInv :=
  toQ_xInv χe D _ j hwA hsm (wTrie_mem D.acs D.preads hj) hcl (α0 χe) (γ0 χe) rfl

theorem pInvL_eq (j : ℕ) (hj : j < (walkRows D.acs D.preads).length) :
    K6.toQ (dW χe D j).pInvL = (vH χe D j).pInvL :=
  toQ_pInvL χe D _ j hwA hsm (wTrie_mem D.acs D.preads hj) (α0 χe) (γ0 χe) rfl

theorem pInvR_eq (j : ℕ) (hj : j < (walkRows D.acs D.preads).length) :
    K6.toQ (dW χe D j).pInvR = (vH χe D j).pInvR :=
  toQ_pInvR χe D _ j hwA hsm (wTrie_mem D.acs D.preads hj) (α0 χe) (γ0 χe) rfl

/-- The `𝕂` roles of the exec row equal the honest `wroleVal` of the filled row. -/
theorem wrole_eq (j : ℕ) (hj : j < (walkRows D.acs D.preads).length) (ln cnt acc : K3) (xa pa : K6)
    (hln : K3.toK ln = (vH χe D j).ln) (hcnt : K3.toK cnt = (vH χe D j).cnt)
    (hacc : K3.toK acc = (vH χe D j).acc)
    (hxa : K6.toQ xa = (vH χe D j).xAcc) (hpa : K6.toQ pa = (vH χe D j).pAcc)
    (ρ : ℕ) (hρ : ρ < 37) :
    wroleVal deltaF (vH χe D j) ρ = K3.toK (wroleD (dW χe D j) ln cnt acc xa pa ρ) := by
  have hio : ∀ k < 5, K6.toQ (ioD (dW χe D j) xa pa k) = (vH χe D j).ioSlot k := by
    intro k hk
    interval_cases k
    · exact xInv_eq χe D hwA hsm hcl j hj
    · exact pInvL_eq χe D hwA hsm hcl j hj
    · exact pInvR_eq χe D hwA hsm hcl j hj
    · exact hxa
    · exact hpa
  unfold wroleVal wroleD
  by_cases h1 : ρ < 24
  · rw [if_pos h1, if_pos h1]
    have hf := fp_toQ χe D hwA hsm hcl j hj (ρ / 2) (by omega)
    have hr := toK_reim _ _ hf
    split_ifs
    · exact hr.1.symm
    · exact hr.2.symm
  · rw [if_neg h1, if_neg h1]
    by_cases h24 : ρ = 24
    · subst h24; simpa using hln.symm
    by_cases h25 : ρ = 25
    · subst h25; simpa using hcnt.symm
    by_cases h26 : ρ = 26
    · subst h26; simpa using hacc.symm
    rw [if_neg h24, if_neg h25, if_neg h26, if_neg h24, if_neg h25, if_neg h26]
    have hr := toK_reim _ _ (hio ((ρ - 27) / 2) (by omega))
    split_ifs
    · exact hr.1.symm
    · exact hr.2.symm

/-- The honest handle role fill at orbit `o`. -/
noncomputable abbrev rolesH {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h) :
    WalkTraceH.Roles (nVOf D) (Quad (algebraMap (ZMod P) KC deltaF)) :=
  WalkTraceHQ.rolesF deltaF (krW D.acs D.preads) powerBasis3 (nV_pos D) (powN o (nVOf D)) o
    (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (pubsVOf9 deltaF powerBasis3 D o (toχ χe))
    (vCol9 deltaF powerBasis3 D (toχ χe)) (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D)

theorem hXi_eq (hne : D.preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf D))) (k : ℕ) (hk : k < nVOf D) :
    K6.toQ (dW χe D k).hXi = (rolesH χe D o).xi ⟨k, hk⟩ := by
  have hk' : k < (walkRows D.acs D.preads).length := by rw [← nVOf_eq D hne]; exact hk
  rw [toQ_hXi χe D _ k hwA hsm (wTrie_mem D.acs D.preads hk') hcl]
  simp only [rolesH, WalkTraceHQ.rolesF]
  rw [(aw_dRow_split9 deltaF powerBasis3 D o hinj (toχ χe) _ ⟨k, hk⟩).1]
  rw [vValsC9_eq]
  rfl

theorem hPLi_eq (hne : D.preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf D)))
    (k : ℕ) (hk : k < nVOf D) :
    K6.toQ (dW χe D k).hPLi = (rolesH χe D o).pl ⟨k, hk⟩ := by
  rw [toQ_hPLi χe D _ k]
  simp only [rolesH, WalkTraceHQ.rolesF]
  rw [(aw_dRow_split9 deltaF powerBasis3 D o hinj (toχ χe) _ ⟨k, hk⟩).2.1]
  rw [vValsC9_eq]
  rfl

theorem hPRi_eq (hne : D.preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf D)))
    (k : ℕ) (hk : k < nVOf D) :
    K6.toQ (dW χe D k).hPRi = (rolesH χe D o).pr ⟨k, hk⟩ := by
  rw [toQ_hPRi χe D _ k]
  simp only [rolesH, WalkTraceHQ.rolesF]
  rw [(aw_dRow_split9 deltaF powerBasis3 D o hinj (toχ χe) _ ⟨k, hk⟩).2.2]
  rw [vValsC9_eq]
  rfl

theorem cN_mL (k : ℕ) (hk : k < nVOf D) :
    WalkTraceH.cN k (vCol9 deltaF powerBasis3 D (toχ χe) WChip.mL) =
      (((wTrie D.acs D.preads k).label.mL : ℕ) : ZMod P) := by
  unfold WalkTraceH.cN; rw [dif_pos hk]; rfl

theorem cN_mR (k : ℕ) (hk : k < nVOf D) :
    WalkTraceH.cN k (vCol9 deltaF powerBasis3 D (toχ χe) WChip.mR) =
      (((wTrie D.acs D.preads k).label.mR : ℕ) : ZMod P) := by
  unfold WalkTraceH.cN; rw [dif_pos hk]; rfl

theorem hxaR (hne : D.preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf D)))
    (j : ℕ) (hj : j < nVOf D) (hxa : K6)
    (h1 : K6.toQ hxa = ∑ k ∈ Finset.range (j + 1), K6.toQ (dW χe D k).hXi) :
    K6.toQ hxa = (rolesH χe D o).xa ⟨j, hj⟩ := by
  rw [h1]
  simp only [rolesH, WalkTraceHQ.rolesF]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < nVOf D := by have := Finset.mem_range.mp hk; omega
  have := hXi_eq χe D hwA hsm hcl hne o hinj k hk'
  simp only [rolesH, WalkTraceHQ.rolesF] at this
  simp only [WalkTraceHQ.dN, dif_pos hk']
  exact this

theorem hpaR (hne : D.preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf D)))
    (j : ℕ) (hj : j < nVOf D) (hpa : K6)
    (h1 : K6.toQ hpa = ∑ k ∈ Finset.range (j + 1), K6.toQ (hPTermD (dW χe D k))) :
    K6.toQ hpa = (rolesH χe D o).pa ⟨j, hj⟩ := by
  rw [h1]
  simp only [rolesH, WalkTraceHQ.rolesF]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < nVOf D := by have := Finset.mem_range.mp hk; omega
  have eL := hPLi_eq χe D hwA hsm hcl hne o hinj k hk'
  have eR := hPRi_eq χe D hwA hsm hcl hne o hinj k hk'
  simp only [rolesH, WalkTraceHQ.rolesF] at eL eR
  have mL := cN_mL χe D hwA hsm hcl k hk'
  have mR := cN_mR χe D hwA hsm hcl k hk'
  unfold hPTermD
  rw [K6.toQ_add, K6.toQ_mul, K6.toQ_mul, toQ_lq, toQ_lq, eL, eR]
  simp only [WalkTraceHQ.dN, dif_pos hk', mL, mR, dW_w]
  rfl

theorem pAccEq (hne : D.preads ≠ []) (j : ℕ) (hj : j < nVOf D) (pa : K6)
    (h1 : K6.toQ pa = ∑ k ∈ Finset.range (j + 1), K6.toQ (pTermD (dW χe D k))) :
    K6.toQ pa = (vH χe D j).pAcc := by
  rw [h1]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < nVOf D := by have := Finset.mem_range.mp hk; omega
  have hk'' : k < (walkRows D.acs D.preads).length := by rw [← nVOf_eq D hne]; exact hk'
  unfold pTermD
  rw [K6.toQ_add, K6.toQ_mul, K6.toQ_mul, toQ_lq, toQ_lq,
    pInvL_eq χe D hwA hsm hcl k hk'', pInvR_eq χe D hwA hsm hcl k hk'', dW_w]
  rfl

theorem xAccEq (hne : D.preads ≠ []) (j : ℕ) (hj : j < nVOf D) (xa : K6)
    (h1 : K6.toQ xa = ∑ k ∈ Finset.range (j + 1), K6.toQ (dW χe D k).xInv) :
    K6.toQ xa = (vH χe D j).xAcc := by
  rw [h1]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < nVOf D := by have := Finset.mem_range.mp hk; omega
  have hk'' : k < (walkRows D.acs D.preads).length := by rw [← nVOf_eq D hne]; exact hk'
  exact xInv_eq χe D hwA hsm hcl k hk''

/-- **The core column lemma** at one row, with the accumulators abstract. -/
theorem col_core (hne : D.preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf D)))
    (j : ℕ) (hjN : j < nVOf D) (c : ℕ) (hc : c < 166)
    (q : ℕ) (hq : q = GenWalk.qH (krW D.acs D.preads) (Nock.Walk.foCol (walkRows D.acs D.preads)) (j + 1))
    (ln cnt acc : K3) (xa pa hxa hpa : K6)
    (hln : K3.toK ln = (vH χe D j).ln) (hcnt : K3.toK cnt = (vH χe D j).cnt)
    (hacc : K3.toK acc = (vH χe D j).acc)
    (hx : K6.toQ xa = ∑ k ∈ Finset.range (j + 1), K6.toQ (dW χe D k).xInv)
    (hp : K6.toQ pa = ∑ k ∈ Finset.range (j + 1), K6.toQ (pTermD (dW χe D k)))
    (hhx : K6.toQ hxa = ∑ k ∈ Finset.range (j + 1), K6.toQ (dW χe D k).hXi)
    (hhp : K6.toQ hpa = ∑ k ∈ Finset.range (j + 1), K6.toQ (hPTermD (dW χe D k))) :
    (if c = 24 ∧ (tlN' (dW χe D j).w.node).isCell then
        ((ComplJ8Data.ptrP P D.acs D.rows (dW χe D j).w.node : ℕ) : ZMod P)
      else walkColDB Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8.certB (Nock.V1J8.Gen.hdl D.acs)
        (walkRows D.acs D.preads).length (krW D.acs D.preads) q (dW χe D j) ln cnt acc xa pa hxa hpa c) =
      fullCol (nV_pos D)
        (WalkTraceHQ.colHQ deltaF (krW D.acs D.preads) powerBasis3 (vCol9 deltaF powerBasis3 D (toχ χe))
          (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D) (rolesH χe D o)) c ⟨j, hjN⟩ := by
  have hj : j < (walkRows D.acs D.preads).length := by rw [← nVOf_eq D hne]; exact hjN
  have hxs := xAccEq χe D hwA hsm hcl hne j hjN xa hx
  have hps := pAccEq χe D hwA hsm hcl hne j hjN pa hp
  have hj' : (dW χe D j).j = j := by
    show (dE χe D (wTrie D.acs D.preads j) j).j = j
    rw [walkDBE_j]; rfl
  by_cases h0 : c = 0
  · subst h0
    simp [walkColDB, walkColD, fullCol, hj', Nock.V1J8.Gen.flag]
  by_cases h1 : c = 1
  · subst h1
    have hnv := nVOf_eq D hne
    by_cases e : j + 1 = (walkRows D.acs D.preads).length
    · simp [walkColDB, walkColD, fullCol, hj', Nock.V1J8.Gen.flag, Fin.ext_iff, e] <;> omega
    · simp [walkColDB, walkColD, fullCol, hj', Nock.V1J8.Gen.flag, Fin.ext_iff, e] <;> omega
  simp only [fullCol, if_neg h0, if_neg h1]
  by_cases hb : c < 25
  · have hlo := walkColDBE_lo χe D _ j hwA hsm (wTrie_mem D.acs D.preads hj) hcl hne hjN rfl
      (walkRows D.acs D.preads).length (krW D.acs D.preads) q ln cnt acc xa pa hxa hpa c (by omega) hb
      (by rw [hq])
    rw [hlo]
    simp only [WalkTraceHQ.colHQ, extColF, WalkTraceH.walkTemplate_width]
    by_cases hb21 : c < 21
    · rw [if_pos hb21, if_pos hb21]
      simp only [ComplJ9BAWR.wColBR, walkCol, if_pos hb21, ComplJ9BAWR.wValsBR]
      rfl
    · rw [if_neg hb21, if_neg hb21, if_pos hb]
      have c21 : 21 ≤ c := by omega
      interval_cases c <;> simp [WalkTraceHQ.new]
  rw [if_neg (fun hh => hb (by omega))]
  simp only [WalkTraceHQ.colHQ, extColF, WalkTraceH.walkTemplate_width]
  rw [if_neg (show ¬ c < 21 by omega), if_neg hb]
  by_cases hr : c < 136
  · rw [if_pos (show c < 132 + (25 - 21) by omega)]
    rw [walkColDB_role _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) hr]
    simp only [ComplJ9BAWR.wColBR, walkCol, if_neg (show ¬ (c - (25 - 21) < 21) by omega),
      ComplJ9BAWR.wValsBR]
    have e1 : c - (25 - 21) - 21 = c - 25 := by omega
    simp only [e1]
    have hV : walkFill deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe))
        (ComplJ9BAWR.wRowsBR deltaF (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (encA deltaF (toχ χe)) D.acs (rIA D)
          D.preads) j = vH χe D j := by
      have e2 := congrFun (vVals9_eq deltaF D (toχ χe)) ⟨j, hjN⟩
      rw [vValsC9_eq] at e2
      exact e2
    rw [hV]
    have hρ : (c - 25) / 3 < 37 := by omega
    have hw := wrole_eq χe D hwA hsm hcl j hj ln cnt acc xa pa hln hcnt hacc hxs hps _ hρ
    rw [hw]
    show _ = coordN powerBasis3 _ (c - 25)
    rw [coordN_toK']
  · rw [if_neg (show ¬ c < 132 + (25 - 21) by omega)]
    rw [walkColDB_hand _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    simp only [WalkTraceHQ.new]
    rw [if_neg (show c ≠ 21 by omega), if_neg (show c ≠ 22 by omega), if_neg (show c ≠ 23 by omega),
      if_neg (show c ≠ 24 by omega), if_pos (show 136 ≤ c ∧ c < 166 from ⟨by omega, hc⟩)]
    have R0 := toK_reim _ _ (hXi_eq χe D hwA hsm hcl hne o hinj j hjN)
    have R1 := toK_reim _ _ (hPLi_eq χe D hwA hsm hcl hne o hinj j hjN)
    have R2 := toK_reim _ _ (hPRi_eq χe D hwA hsm hcl hne o hinj j hjN)
    have R3 := toK_reim _ _ (hxaR χe D hwA hsm hcl hne o hinj j hjN hxa hhx)
    have R4 := toK_reim _ _ (hpaR χe D hwA hsm hcl hne o hinj j hjN hpa hhp)
    generalize ht : (c - 136) / 3 = t
    have ht10 : t < 10 := by omega
    interval_cases t
    · simp [hsD, WalkTraceHQ.roleVal]
      exact (coordN_toK' _ _).symm.trans (congrArg (coordN powerBasis3 · (c - 136)) R0.1)
    · simp [hsD, WalkTraceHQ.roleVal]
      exact (coordN_toK' _ _).symm.trans (congrArg (coordN powerBasis3 · (c - 136)) R0.2)
    · simp [hsD, WalkTraceHQ.roleVal]
      exact (coordN_toK' _ _).symm.trans (congrArg (coordN powerBasis3 · (c - 136)) R1.1)
    · simp [hsD, WalkTraceHQ.roleVal]
      exact (coordN_toK' _ _).symm.trans (congrArg (coordN powerBasis3 · (c - 136)) R1.2)
    · simp [hsD, WalkTraceHQ.roleVal]
      exact (coordN_toK' _ _).symm.trans (congrArg (coordN powerBasis3 · (c - 136)) R2.1)
    · simp [hsD, WalkTraceHQ.roleVal]
      exact (coordN_toK' _ _).symm.trans (congrArg (coordN powerBasis3 · (c - 136)) R2.2)
    · simp [hsD, WalkTraceHQ.roleVal]
      exact (coordN_toK' _ _).symm.trans (congrArg (coordN powerBasis3 · (c - 136)) R3.1)
    · simp [hsD, WalkTraceHQ.roleVal]
      exact (coordN_toK' _ _).symm.trans (congrArg (coordN powerBasis3 · (c - 136)) R3.2)
    · simp [hsD, WalkTraceHQ.roleVal]
      exact (coordN_toK' _ _).symm.trans (congrArg (coordN powerBasis3 · (c - 136)) R4.1)
    · simp [hsD, WalkTraceHQ.roleVal]
      exact (coordN_toK' _ _).symm.trans (congrArg (coordN powerBasis3 · (c - 136)) R4.2)

omit hwA hsm hcl in
theorem dsE_length : (dsE χe D).length = (walkRows D.acs D.preads).length := by
  simp [dsE, dsL]

theorem scan_sum (hne : D.preads ≠ []) (f : WalkD → K6) (j : ℕ) (hj : j < (walkRows D.acs D.preads).length) :
    K6.toQ ((scanK6 ((dsE χe D).map f)).getD j 0) =
      ∑ k ∈ Finset.range (j + 1), K6.toQ (f (dW χe D k)) := by
  have hl := dsE_length χe D
  rw [GenPortJ9AHCell.toQ_scanK6_getD' _ _ (by simpa [hl] using hj)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < (walkRows D.acs D.preads).length := by have := Finset.mem_range.mp hk; omega
  rw [getD_map_lt f _ k (by simpa [hl] using hk') (dW χe D 0) 0, dsE_getD χe D k hk']

theorem hcur_ok (hne : D.preads ≠ []) :
    ((dsE χe D).map (curD (chalsAJ8ZE χe 1))).length = (walkRows D.acs D.preads).length ∧
    ∀ i < (walkRows D.acs D.preads).length,
      K3.toK (((dsE χe D).map (curD (chalsAJ8ZE χe 1))).getD i 0) =
        Nock.Walk.curCol (fun t => ComplJ9BAWR.wNodeValR deltaF (GlobalCarryRecognizer.enc (ComplJ8Of.zA deltaF (toχ χe)))
          (ComplJ8Data.rIAP P D.acs) (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe) 1) t)
          (walkRows D.acs D.preads) (i + 1) := by
  have hl := dsE_length χe D
  refine ⟨by simp [hl], fun i hi => ?_⟩
  rw [getD_map_lt _ _ i (by simpa [hl] using hi) (dW χe D 0) 0, dsE_getD χe D i hi]
  have := toK_curD_chals χe D (wTrie D.acs D.preads i) i hwA hsm (wTrie_mem D.acs D.preads hi) hcl
  refine this.trans ?_
  simp [Nock.Walk.curCol, wTrie, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- **The executable atom-walk table's column `c < 166` at row `i` is the honest J-9 atom walk's.** -/
theorem walkGenRowsBE_cols (hne : D.preads ≠ []) {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (powN o (nVOf D))) (i : Fin (nVOf D)) (c : ℕ) (hc : c < 166) :
    ((awE χe D).1.getD i #[]).getD c 0 =
      fullCol (nV_pos D)
        (WalkTraceHQ.colHQ deltaF (krVOf D) powerBasis3 (vCol9 deltaF powerBasis3 D (toχ χe))
          (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D)
          (WalkTraceHQ.rolesF deltaF (krVOf D) powerBasis3 (nV_pos D) (powN o (nVOf D)) o
            (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe)) (pubsVOf9 deltaF powerBasis3 D o (toχ χe))
            (vCol9 deltaF powerBasis3 D (toχ χe)) (kLV9 D) (vLV9 D) (kRV9 D) (vRV9 D))) c i := by
  have hjN := i.2
  have hj : (i : ℕ) < (walkRows D.acs D.preads).length := by rw [← nVOf_eq D hne]; exact hjN
  have hN : (i : ℕ) < ((walkRows D.acs D.preads).map GenPortJ9AHWalkBfs.wrowOf).length := by simpa using hj
  rw [krVOf_eq D hne]
  rw [walkGenRowsBE_getD _ _ _ _ _ _ _ _ _ _ _ _ _ hN hc (dW χe D i) (dsE_getD χe D i hj _).symm]
  rw [List.length_map]
  obtain ⟨hl1, hl2⟩ := hcur_ok χe D hwA hsm hcl hne
  obtain ⟨l1, l2, l3⟩ := GenPortJ9AHWalkAcc.walkLCA_eq D.acs D.preads
    (fun t => ComplJ9BAWR.wNodeValR deltaF (GlobalCarryRecognizer.enc (ComplJ8Of.zA deltaF (toχ χe)))
      (ComplJ8Data.rIAP P D.acs) (ChalsAZJ8.chalsAJ8Z deltaF (toχ χe) 1) t)
    (chalsAJ8ZE χe 0) ((dsE χe D).map (curD (chalsAJ8ZE χe 1))) ⟨hl1, hl2⟩ i hj
    ((lcaL (ComplJ8Data.ptrP P D.acs D.rows) (coOfA χe) (yE χe) (chalsAJ8ZE χe 0) (chalsAJ8ZE χe 1)
      (Nock.V1J8.Gen.hdl D.acs) (ComplJ8Data.rIAP P D.acs) D.acs
      ((walkRows D.acs D.preads).map GenPortJ9AHWalkBfs.wrowOf) (krW D.acs D.preads)).getD i (0, 0, 0)) rfl
  rw [toK_chalsA] at l1 l2 l3
  exact col_core χe D hwA hsm hcl hne o hinj i hjN c hc _
    (GenPortJ9AHWalkAcc.q_eq D.acs D.preads i hj) _ _ _ _ _ _ _
    l1 l2 l3
    (scan_sum χe D hwA hsm hcl hne (fun d => d.xInv) i hj) (scan_sum χe D hwA hsm hcl hne pTermD i hj)
    (scan_sum χe D hwA hsm hcl hne (fun d => d.hXi) i hj) (scan_sum χe D hwA hsm hcl hne hPTermD i hj)

end Row

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW

open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms wrowOf_eq
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms dsL_getD
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms walkGenRowsBE_getD
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms walkColDB_role
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms walkColDB_hand
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms walkGenRowsBE_size
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms dsE_getD
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms wrole_eq
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms hXi_eq
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms hxaR
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms hpaR
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms pAccEq
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms xAccEq
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms col_core
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms scan_sum
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms hcur_ok
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHAW in
#print axioms walkGenRowsBE_cols
