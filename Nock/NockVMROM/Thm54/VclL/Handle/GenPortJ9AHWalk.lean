/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHWalk.lean

  Reuses `dW`, `toQ_*`, `walkColD_base`, `walkColDB_*`, `toK_curD_frame`,
  `q_eq`, `childSums_eq` and `walkLCA_eq`.

  Extra hypothesis: `hwroot` (every walk row's ROOT is a cell of `D.cells` or an atom), needed for
  `ridx = cells.idxOf root` (`walkDB_ridx`).  Same shape as `hwcell`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRow
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkAcc

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalk

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.GenWalk
open Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalkRow
open Nock.NockVMROM.Thm54.StrictExtension (StrictOrbitDomain)

/-! ## 1. Scans (copied from `GenPortJ9AChips`, which imports `AcceptsJ9A`) -/

theorem scanK6_eq (l : List K6) : Gen.scanK6 l = (List.scanl (· + ·) 0 l).tail := by
  have key : ∀ (l : List K6) (a : K6) (pre : List K6),
      (l.foldl (fun (st : List K6 × K6) x => (st.1 ++ [st.2 + x], st.2 + x)) (pre, a)).1 =
        pre ++ (List.scanl (· + ·) a l).tail := by
    intro l
    induction l with
    | nil => intro a pre; simp
    | cons x l ih =>
      intro a pre
      rw [List.foldl_cons, ih, List.scanl_cons, List.tail_cons]
      cases l <;> simp [List.scanl]
  unfold Gen.scanK6
  rw [key]; simp

theorem toQ_scanl_getD : ∀ (l : List K6) (a : K6) (i : ℕ), i < l.length →
    K6.toQ ((List.scanl (· + ·) a l).getD (i + 1) 0) =
      K6.toQ a + ∑ j ∈ Finset.range (i + 1), K6.toQ (l.getD j 0)
  | [], a, i, h => by simp at h
  | x :: t, a, 0, _ => by
    rw [List.scanl_cons, List.getD_cons_succ]
    cases t <;> simp [List.scanl_cons, K6.toQ_add]
  | x :: t, a, j + 1, h => by
    have ih := toQ_scanl_getD t (a + x) j (by simpa using h)
    rw [List.scanl_cons, List.getD_cons_succ, ih, K6.toQ_add]
    rw [Finset.sum_range_succ' _ (j + 1)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    abel

theorem toQ_scanK6_getD (l : List K6) (i : ℕ) (hi : i < l.length) :
    K6.toQ ((Gen.scanK6 l).getD i 0) = ∑ j ∈ Finset.range (i + 1), K6.toQ (l.getD j 0) := by
  rw [scanK6_eq]
  have := toQ_scanl_getD l 0 i hi
  rw [K6.toQ_zero, zero_add] at this
  rw [← this]
  have e : ∀ L : List K6, L.tail.getD i 0 = L.getD (i + 1) 0 := by
    intro L; cases L <;> simp
  rw [e]

theorem getD_map_lt {α β : Type} (f : α → β) (l : List α) (j : ℕ) (hj : j < l.length) (d : α) (z : β) :
    (l.map f).getD j z = f (l.getD j d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]

/-! ## 2. The exec table's cell access -/

/-- The executable row data list of `walkGenRowsB`. -/
def dsL (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun) (ws : List WRow) : List WalkD :=
  (ws.zipIdx 0).map fun (w, j) => walkDB k y H rI cs w j

/-- The executable `(ln, cnt, acc)` list. -/
def lcaL (k : Co) (y : K6) (α γ : K3) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun) (ws : List WRow)
    (kr : ℕ) : List (K3 × K3 × K3) :=
  walkLCA α kr (ws.map foW) (childSums α kr (ws.map foW) ((dsL k y H rI cs ws).map (curD γ)).toArray)
    ((dsL k y H rI cs ws).map (curD γ))

theorem dsL_getD (k : Co) (y : K6) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cs : List Noun) (ws : List WRow) (j : ℕ)
    (hj : j < ws.length) (z : WalkD) (d : WRow) :
    (dsL k y H rI cs ws).getD j z = walkDB k y H rI cs (ws.getD j d) j := by
  unfold dsL
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hj]

theorem walkGenRowsB_getD (k : Co) (y : K6) (α γ : K3) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cert : ℕ → ℕ → ℕ)
    (cs : List Noun) (ws : List WRow) (kr : ℕ) (i c : ℕ) (hi : i < ws.length) (hc : c < 166) :
    ((walkGenRowsB k y α γ H rI cert cs ws kr).1.getD i #[]).getD c 0 =
      walkColDB cert H ws.length kr (kr + (scanN (ws.map foW)).getD i 0 - (i + 1))
        ((dsL k y H rI cs ws).getD i
          (walkDB k y H rI cs (ws.getD i ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩) i))
        ((lcaL k y α γ H rI cs ws kr).getD i (0, 0, 0)).1
        ((lcaL k y α γ H rI cs ws kr).getD i (0, 0, 0)).2.1
        ((lcaL k y α γ H rI cs ws kr).getD i (0, 0, 0)).2.2
        ((scanK6 ((dsL k y H rI cs ws).map (·.xInv))).getD i 0)
        ((scanK6 ((dsL k y H rI cs ws).map pTermD)).getD i 0)
        ((scanK6 ((dsL k y H rI cs ws).map (·.hXi))).getD i 0)
        ((scanK6 ((dsL k y H rI cs ws).map hPTermD)).getD i 0) c := by
  unfold walkGenRowsB
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  simp only [Array.getElem?_ofFn]
  rw [dif_pos hc]
  rfl

/-! ## 3. Row facts -/

section Row
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))] [Fact (ringChar (ZMod P)).Prime]
  [Algebra (ZMod (ringChar (ZMod P))) KC]
  {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
  (χe : CoinsE) (D : ComplJ8Data.J8Data P Rg fuel s f r)

theorem wrowOf_getD (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) (d : WRow) :
    ((walkRows D.cells D.reads).map wrowOf).getD j d = wrowOf (wTrie D.cells D.reads j) := by
  simp [wTrie, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]

theorem dsL_dW (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) (z : WalkD) (d : WRow) :
    (dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells ((walkRows D.cells D.reads).map wrowOf)).getD j z =
      dW χe D.H D.cells D.reads j := by
  rw [dsL_getD _ _ _ _ _ _ j (by simpa using hj) z d, wrowOf_getD D j hj]

theorem fp_toQ (j : ℕ) (α γ : KC) (t : ℕ) (ht : t < 12) :
    K6.toQ (fpD (dW χe D.H D.cells D.reads j) t) = (rowW χe D.cells D.reads j α γ).fpSlot t := by
  interval_cases t
  · exact congrArg ComputeTable.FP.size (toQ_wpE χe D.H D.cells D.reads j)
  · exact congrArg ComputeTable.FP.dyck (toQ_wpE χe D.H D.cells D.reads j)
  · exact congrArg ComputeTable.FP.leaf (toQ_wpE χe D.H D.cells D.reads j)
  · exact congrArg ComputeTable.FP.size (toQ_wlE χe D.H D.cells D.reads j)
  · exact congrArg ComputeTable.FP.dyck (toQ_wlE χe D.H D.cells D.reads j)
  · exact congrArg ComputeTable.FP.leaf (toQ_wlE χe D.H D.cells D.reads j)
  · exact congrArg ComputeTable.FP.size (toQ_wrE χe D.H D.cells D.reads j)
  · exact congrArg ComputeTable.FP.dyck (toQ_wrE χe D.H D.cells D.reads j)
  · exact congrArg ComputeTable.FP.leaf (toQ_wrE χe D.H D.cells D.reads j)
  · exact congrArg ComputeTable.FP.size (toQ_rootE χe D.H D.cells D.reads j)
  · exact congrArg ComputeTable.FP.dyck (toQ_rootE χe D.H D.cells D.reads j)
  · exact congrArg ComputeTable.FP.leaf (toQ_rootE χe D.H D.cells D.reads j)

/-- The honest values of walk row `j` at the frame coins (the filled row). -/
noncomputable abbrev vH (j : ℕ) : WalkVals (ZMod P) KC (Quad (algebraMap (ZMod P) KC deltaF)) :=
  walkFill deltaF (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe))
    (ComplJ8Enc.wRowsBE deltaF (VerJ8.chalsMJ8 deltaF (toχ χe)) (ComplJ8Of.encR deltaF (toχ χe)) D.cells D.reads) j

variable (hcs : ∀ c ∈ D.cells, c.isCell = true)
  (hwcell : ∀ u ∈ walkRows D.cells D.reads, u.label.node ∈ D.cells)
  (hwroot : ∀ u ∈ walkRows D.cells D.reads, u.label.root ∈ D.cells ∨ u.label.root.isCell = false)
include hcs hwcell hwroot

theorem hnodeK (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) :
    (wTrie D.cells D.reads j).label.node ∈ D.cells ∨ (wTrie D.cells D.reads j).label.node.isCell = false :=
  Or.inl (hwcell _ (wTrie_mem D.cells D.reads hj))

theorem hrootK (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) :
    (wTrie D.cells D.reads j).label.root ∈ D.cells ∨ (wTrie D.cells D.reads j).label.root.isCell = false :=
  hwroot _ (wTrie_mem D.cells D.reads hj)

/-- The `𝕂` roles of the exec row equal the honest `wroleVal` of the filled row. -/
theorem wrole_eq (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) (ln cnt acc : K3) (xa pa : K6)
    (hln : K3.toK ln = (vH χe D j).ln) (hcnt : K3.toK cnt = (vH χe D j).cnt) (hacc : K3.toK acc = (vH χe D j).acc)
    (hxa : K6.toQ xa = (vH χe D j).xAcc) (hpa : K6.toQ pa = (vH χe D j).pAcc)
    (ρ : ℕ) (hρ : ρ < 37) :
    wroleVal deltaF (vH χe D j) ρ = K3.toK (wroleD (dW χe D.H D.cells D.reads j) ln cnt acc xa pa ρ) := by
  have hm := hnodeK D hcs hwcell hwroot j hj
  have hmr := hrootK D hcs hwcell hwroot j hj
  have hio : ∀ k < 5, K6.toQ (ioD (dW χe D.H D.cells D.reads j) xa pa k) = (vH χe D j).ioSlot k := by
    intro k hk
    interval_cases k
    · exact toQ_xInv χe D.H D.cells D.reads j hcs _ _ hm
    · exact toQ_pInvL χe D.H D.cells D.reads j hcs _ _ hmr
    · exact toQ_pInvR χe D.H D.cells D.reads j hcs _ _ hmr
    · exact hxa
    · exact hpa
  unfold wroleVal wroleD
  by_cases h1 : ρ < 24
  · rw [if_pos h1, if_pos h1]
    have hf := fp_toQ χe D j (VerJ8.chalsMJ8 deltaF (toχ χe) 0) (VerJ8.chalsMJ8 deltaF (toχ χe) 1) (ρ / 2) (by omega)
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

omit hcs hwcell hwroot in
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

omit hcs hwcell hwroot in
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

/-- The honest walk column function at the frame coins. -/
noncomputable abbrev wcolH : ℕ → Fin (walkRows D.cells D.reads).length → ZMod P :=
  ComplJ8Enc.wColBE deltaF powerBasis3 (VerJ8.chalsMJ8 deltaF (toχ χe)) (ComplJ8Of.encR deltaF (toχ χe))
    (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe)) D.cells D.reads

/-- The honest handle role fill at orbit `o`. -/
noncomputable abbrev rolesH {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h) :
    WalkTraceH.Roles (walkRows D.cells D.reads).length (Quad (algebraMap (ZMod P) KC deltaF)) :=
  WalkTraceHQ.rolesF deltaF (krW D.cells D.reads) powerBasis3 (ComplJ8Of.walk_pos D.cells D.reads)
    (ComplJ8Of.powN o _) o (VerJ8.chalsMJ8 deltaF (toχ χe)) (ComplJ8Of.pubsWOf deltaF powerBasis3 D o (toχ χe))
    (wcolH χe D) (ComplJ8Of.kLW D) (ComplJ8Of.vLW D) (ComplJ8Of.kRW D) (ComplJ8Of.vRW D)

theorem hXi_eq {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows D.cells D.reads).length))
    (k : ℕ) (hk : k < (walkRows D.cells D.reads).length) :
    K6.toQ (dW χe D.H D.cells D.reads k).hXi = (rolesH χe D o).xi ⟨k, hk⟩ := by
  rw [toQ_hXi χe D.H D.cells D.reads k hcs (hnodeK D hcs hwcell hwroot k hk)]
  simp only [rolesH, WalkTraceHQ.rolesF]
  rw [(ComplJ8Of.walk_dRow_split deltaF powerBasis3 D o hinj (toχ χe) _ ⟨k, hk⟩).1]
  rfl

theorem hPLi_eq {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows D.cells D.reads).length))
    (k : ℕ) (hk : k < (walkRows D.cells D.reads).length) :
    K6.toQ (dW χe D.H D.cells D.reads k).hPLi = (rolesH χe D o).pl ⟨k, hk⟩ := by
  rw [toQ_hPLi χe D.H D.cells D.reads k hcs (hrootK D hcs hwcell hwroot k hk)]
  simp only [rolesH, WalkTraceHQ.rolesF]
  rw [(ComplJ8Of.walk_dRow_split deltaF powerBasis3 D o hinj (toχ χe) _ ⟨k, hk⟩).2.1]
  rfl

theorem hPRi_eq {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows D.cells D.reads).length))
    (k : ℕ) (hk : k < (walkRows D.cells D.reads).length) :
    K6.toQ (dW χe D.H D.cells D.reads k).hPRi = (rolesH χe D o).pr ⟨k, hk⟩ := by
  rw [toQ_hPRi χe D.H D.cells D.reads k hcs (hrootK D hcs hwcell hwroot k hk)]
  simp only [rolesH, WalkTraceHQ.rolesF]
  rw [(ComplJ8Of.walk_dRow_split deltaF powerBasis3 D o hinj (toχ χe) _ ⟨k, hk⟩).2.2]
  rfl

theorem cN_mL (k : ℕ) (hk : k < (walkRows D.cells D.reads).length) :
    WalkTraceH.cN k (wcolH χe D WChip.mL) = (((wTrie D.cells D.reads k).label.mL : ℕ) : ZMod P) := by
  unfold WalkTraceH.cN; rw [dif_pos hk]; rfl

theorem cN_mR (k : ℕ) (hk : k < (walkRows D.cells D.reads).length) :
    WalkTraceH.cN k (wcolH χe D WChip.mR) = (((wTrie D.cells D.reads k).label.mR : ℕ) : ZMod P) := by
  unfold WalkTraceH.cN; rw [dif_pos hk]; rfl

theorem hxaR {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows D.cells D.reads).length))
    (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) (hxa : K6)
    (h1 : K6.toQ hxa = ∑ k ∈ Finset.range (j + 1), K6.toQ (dW χe D.H D.cells D.reads k).hXi) :
    K6.toQ hxa = (rolesH χe D o).xa ⟨j, hj⟩ := by
  rw [h1]
  simp only [rolesH, WalkTraceHQ.rolesF]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < (walkRows D.cells D.reads).length := by have := Finset.mem_range.mp hk; omega
  have := hXi_eq χe D hcs hwcell hwroot o hinj k hk'
  simp only [rolesH, WalkTraceHQ.rolesF] at this
  simp only [WalkTraceHQ.dN, dif_pos hk']
  exact this

theorem hpaR {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows D.cells D.reads).length))
    (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) (hpa : K6)
    (h1 : K6.toQ hpa = ∑ k ∈ Finset.range (j + 1), K6.toQ (hPTermD (dW χe D.H D.cells D.reads k))) :
    K6.toQ hpa = (rolesH χe D o).pa ⟨j, hj⟩ := by
  rw [h1]
  simp only [rolesH, WalkTraceHQ.rolesF]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < (walkRows D.cells D.reads).length := by have := Finset.mem_range.mp hk; omega
  have eL := hPLi_eq χe D hcs hwcell hwroot o hinj k hk'
  have eR := hPRi_eq χe D hcs hwcell hwroot o hinj k hk'
  simp only [rolesH, WalkTraceHQ.rolesF] at eL eR
  have mL := cN_mL χe D hcs hwcell hwroot k hk'
  have mR := cN_mR χe D hcs hwcell hwroot k hk'
  unfold hPTermD
  rw [K6.toQ_add, K6.toQ_mul, K6.toQ_mul, FillMem.toQ_lq, FillMem.toQ_lq, eL, eR]
  simp only [WalkTraceHQ.dN, dif_pos hk', mL, mR]
  rfl

theorem pAccEq (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) (pa : K6)
    (h1 : K6.toQ pa = ∑ k ∈ Finset.range (j + 1), K6.toQ (pTermD (dW χe D.H D.cells D.reads k))) :
    K6.toQ pa = (vH χe D j).pAcc := by
  rw [h1]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < (walkRows D.cells D.reads).length := by have := Finset.mem_range.mp hk; omega
  unfold pTermD
  rw [K6.toQ_add, K6.toQ_mul, K6.toQ_mul, FillMem.toQ_lq, FillMem.toQ_lq,
    toQ_pInvL χe D.H D.cells D.reads k hcs _ _ (hrootK D hcs hwcell hwroot k hk'),
    toQ_pInvR χe D.H D.cells D.reads k hcs _ _ (hrootK D hcs hwcell hwroot k hk')]
  rfl

theorem xAccEq (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) (xa : K6)
    (h1 : K6.toQ xa = ∑ k ∈ Finset.range (j + 1), K6.toQ (dW χe D.H D.cells D.reads k).xInv) :
    K6.toQ xa = (vH χe D j).xAcc := by
  rw [h1]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < (walkRows D.cells D.reads).length := by have := Finset.mem_range.mp hk; omega
  exact toQ_xInv χe D.H D.cells D.reads k hcs _ _ (hnodeK D hcs hwcell hwroot k hk')

/-- **The core column lemma** at one row, with the accumulators abstract. -/
theorem col_core {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows D.cells D.reads).length))
    (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) (c : ℕ) (hc : c < 166)
    (q : ℕ) (hq : q = GenWalk.qH (krW D.cells D.reads) (Nock.Walk.foCol (walkRows D.cells D.reads)) (j + 1))
    (ln cnt acc : K3) (xa pa hxa hpa : K6)
    (hln : K3.toK ln = (vH χe D j).ln) (hcnt : K3.toK cnt = (vH χe D j).cnt)
    (hacc : K3.toK acc = (vH χe D j).acc)
    (hx : K6.toQ xa = ∑ k ∈ Finset.range (j + 1), K6.toQ (dW χe D.H D.cells D.reads k).xInv)
    (hp : K6.toQ pa = ∑ k ∈ Finset.range (j + 1), K6.toQ (pTermD (dW χe D.H D.cells D.reads k)))
    (hhx : K6.toQ hxa = ∑ k ∈ Finset.range (j + 1), K6.toQ (dW χe D.H D.cells D.reads k).hXi)
    (hhp : K6.toQ hpa = ∑ k ∈ Finset.range (j + 1), K6.toQ (hPTermD (dW χe D.H D.cells D.reads k))) :
    walkColDB HonestK8.certB8 D.H (walkRows D.cells D.reads).length (krW D.cells D.reads) q
        (dW χe D.H D.cells D.reads j) ln cnt acc xa pa hxa hpa c =
      fullCol (ComplJ8Of.walk_pos D.cells D.reads)
        (HonestK8.certUp
          (ComplJ8Enc.wColHQBE deltaF powerBasis3 (ComplJ8Of.walk_pos D.cells D.reads)
            (ComplJ8Of.powN o _) o (VerJ8.chalsMJ8 deltaF (toχ χe))
            (ComplJ8Of.pubsWOf deltaF powerBasis3 D o (toχ χe)) (ComplJ8Of.encR deltaF (toχ χe))
            (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe)) D.cells D.reads
            (ComplJ8Of.kLW D) (ComplJ8Of.vLW D) (ComplJ8Of.kRW D) (ComplJ8Of.vRW D))
          (ComplJ8Walk.lenB D.cells D.reads)) c ⟨j, hj⟩ := by
  have hm := hnodeK D hcs hwcell hwroot j hj
  have hmr := hrootK D hcs hwcell hwroot j hj
  have hxs := xAccEq χe D hcs hwcell hwroot j hj xa hx
  have hps := pAccEq χe D hcs hwcell hwroot j hj pa hp
  by_cases h0 : c = 0
  · subst h0
    simp [walkColDB, walkColD, fullCol, dW, walkDB, flag]
  by_cases h1 : c = 1
  · subst h1
    by_cases e : j + 1 = (walkRows D.cells D.reads).length
    · have e' : j = (walkRows D.cells D.reads).length - 1 := by omega
      simp [walkColDB, walkColD, fullCol, dW, walkDB, flag, Fin.ext_iff, e, e'] <;> omega
    · have e' : j ≠ (walkRows D.cells D.reads).length - 1 := by omega
      simp [walkColDB, walkColD, fullCol, dW, walkDB, flag, Fin.ext_iff, e, e'] <;> omega
  simp only [fullCol, if_neg h0, if_neg h1, HonestK8.certUp]
  by_cases hcert : 14 ≤ c ∧ c < 21
  · rw [if_pos hcert, walkColDB_cert _ _ _ _ _ _ _ _ _ _ _ _ _ hcert]
    rfl
  rw [if_neg hcert]
  simp only [ComplJ8Enc.wColHQBE, WalkTraceHQ.colHQ, extColF, WalkTraceH.walkTemplate_width]
  by_cases hb : c < 21
  · rw [if_pos hb]
    simp only [ComplJ8Enc.wColBE, walkCol, if_pos hb]
    have c2 : 2 ≤ c ∧ c < 14 := by omega
    by_cases hc2 : c = 2
    · subst hc2
      simp [walkColDB, walkColD, WalkVals.base, WalkVals.named, flag, dW, walkDB, decide_eq_true_eq]
      by_cases hp : j < krW D.cells D.reads <;> simp [hp]
    by_cases hc12 : c = 12
    · subst hc12
      simp [walkColDB, walkColD, WalkVals.base, WalkVals.named, hq]
      rfl
    by_cases hc13 : c = 13
    · subst hc13
      simp [walkColDB, walkColD, WalkVals.base, WalkVals.named, hq]
      rfl
    have c3 : 3 ≤ c ∧ c < 12 := by omega
    rw [walkColD_base χe D.H D.cells D.reads j hcs HonestK8.certB8 _ _ q ln cnt acc xa pa hxa hpa
      (VerJ8.chalsMJ8 deltaF (toχ χe) 0) (VerJ8.chalsMJ8 deltaF (toχ χe) 1) c c3 hm hmr]
    obtain ⟨c31, c32⟩ := c3
    interval_cases c <;>
      first
      | rfl
      | (simp [baseColV, WalkVals.base, WalkVals.named]; done)
      | (simp [baseColV, WalkVals.base, WalkVals.named]; rfl)
  rw [if_neg hb]
  by_cases hk : c < 25
  · rw [if_pos hk]
    obtain ⟨e21, e22, e23, e24⟩ := walkColDB_handle χe D.H D.cells D.reads j hcs HonestK8.certB8
      (walkRows D.cells D.reads).length (krW D.cells D.reads) q ln cnt acc xa pa hxa hpa hm
    have c21 : 21 ≤ c := by omega
    interval_cases c
    · simpa [WalkTraceHQ.new, ComplJ8Of.kLW, ComplJ8Of.wNode] using e21
    · simpa [WalkTraceHQ.new, ComplJ8Of.vLW, ComplJ8Of.wNode] using e22
    · simpa [WalkTraceHQ.new, ComplJ8Of.kRW, ComplJ8Of.wNode] using e23
    · simpa [WalkTraceHQ.new, ComplJ8Of.vRW, ComplJ8Of.wNode] using e24
  rw [if_neg hk]
  by_cases hr : c < 136
  · rw [if_pos (show c < 132 + (25 - 21) by omega)]
    rw [walkColDB_role _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) hr]
    simp only [ComplJ8Enc.wColBE, walkCol, if_neg (show ¬ (c - (25 - 21) < 21) by omega)]
    have e1 : c - (25 - 21) - 21 = c - 25 := by omega
    simp only [e1]
    rw [wrole_eq χe D hcs hwcell hwroot j hj ln cnt acc xa pa hln hcnt hacc hxs hps ((c - 25) / 3) (by omega),
      coord_K]
  · rw [if_neg (show ¬ c < 132 + (25 - 21) by omega)]
    rw [walkColDB_hand _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    simp only [WalkTraceHQ.new, if_neg (show c ≠ 21 by omega), if_neg (show c ≠ 22 by omega),
      if_neg (show c ≠ 23 by omega), if_neg (show c ≠ 24 by omega),
      if_pos (show 136 ≤ c ∧ c < 166 from ⟨by omega, hc⟩)]
    have hxi := hXi_eq χe D hcs hwcell hwroot o hinj j hj
    have hpl := hPLi_eq χe D hcs hwcell hwroot o hinj j hj
    have hpr := hPRi_eq χe D hcs hwcell hwroot o hinj j hj
    have hxaR' := hxaR χe D hcs hwcell hwroot o hinj j hj hxa hhx
    have hpaR' := hpaR χe D hcs hwcell hwroot o hinj j hj hpa hhp
    have hs : ∀ t < 10, WalkTraceHQ.roleVal deltaF (rolesH χe D o) t ⟨j, hj⟩ =
        K3.toK (if t % 2 = 0 then (hsD (dW χe D.H D.cells D.reads j) hxa hpa (t / 2)).re
          else (hsD (dW χe D.H D.cells D.reads j) hxa hpa (t / 2)).im) := by
      intro t ht
      interval_cases t
      · exact (toK_reim _ _ hxi).1.symm
      · exact (toK_reim _ _ hxi).2.symm
      · exact (toK_reim _ _ hpl).1.symm
      · exact (toK_reim _ _ hpl).2.symm
      · exact (toK_reim _ _ hpr).1.symm
      · exact (toK_reim _ _ hpr).2.symm
      · exact (toK_reim _ _ hxaR').1.symm
      · exact (toK_reim _ _ hxaR').2.symm
      · exact (toK_reim _ _ hpaR').1.symm
      · exact (toK_reim _ _ hpaR').2.symm
    rw [hs ((c - 136) / 3) (by omega), coordN_toK]

theorem scan_sum (f : WalkD → K6) (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) :
    K6.toQ ((Gen.scanK6 ((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
        ((walkRows D.cells D.reads).map wrowOf)).map f)).getD j 0) =
      ∑ k ∈ Finset.range (j + 1), K6.toQ (f (dW χe D.H D.cells D.reads k)) := by
  have hl : (dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
      ((walkRows D.cells D.reads).map wrowOf)).length = (walkRows D.cells D.reads).length := by
    simp [dsL]
  rw [toQ_scanK6_getD _ _ (by simpa [hl] using hj)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < (walkRows D.cells D.reads).length := by have := Finset.mem_range.mp hk; omega
  rw [getD_map_lt f _ k (by simpa [hl] using hk') (dW χe D.H D.cells D.reads 0) 0,
    dsL_dW χe D k hk' _ ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩]

theorem hcur_ok (j : ℕ) (hj : j < (walkRows D.cells D.reads).length) :
    ((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells ((walkRows D.cells D.reads).map wrowOf)).map
        (curD (chalsMJ8E χe 1))).length = (walkRows D.cells D.reads).length ∧
    ∀ i < (walkRows D.cells D.reads).length,
      K3.toK (((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
          ((walkRows D.cells D.reads).map wrowOf)).map (curD (chalsMJ8E χe 1))).getD i 0) =
        Nock.Walk.curCol (ComplJ8Enc.wNodeValE deltaF (ComplJ8Of.encR deltaF (toχ χe)) D.cells
          (VerJ8.chalsMJ8 deltaF (toχ χe) 1)) (walkRows D.cells D.reads) (i + 1) := by
  have hl : (dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells
      ((walkRows D.cells D.reads).map wrowOf)).length = (walkRows D.cells D.reads).length := by
    simp [dsL]
  refine ⟨by simp [hl], fun i hi => ?_⟩
  rw [getD_map_lt _ _ i (by simpa [hl] using hi) (dW χe D.H D.cells D.reads 0) 0,
    dsL_dW χe D i hi _ ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩,
    toK_curD_frame χe D.H D.cells D.reads i hcs (hrootK D hcs hwcell hwroot i hi)]
  simp [Nock.Walk.curCol, wTrie, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

end Row

section Main
variable [Fact (¬ IsSquare (algebraMap (ZMod P) KC deltaF))] [Fact (ringChar (ZMod P)).Prime]
  [Algebra (ZMod (ringChar (ZMod P))) KC]

/-- **The executable walk table's column `c < 166` at row `i` is the honest J-8 walk's.** -/
theorem walkGenRowsB_cols (χe : CoinsE) {Rg : Nock.Jet.VerifiedRegistry} {fuel : ℕ} {s f r : Noun}
    (D : ComplJ8Data.J8Data P Rg fuel s f r)
    (hcs : ∀ c ∈ D.cells, c.isCell = true)
    (hwcell : ∀ u ∈ walkRows D.cells D.reads, u.label.node ∈ D.cells)
    (hwroot : ∀ u ∈ walkRows D.cells D.reads, u.label.root ∈ D.cells ∨ u.label.root.isCell = false)
    (hall : ∀ x ∈ D.reads, VclL.isPathAx x.2 = true) (hwalk : ComplJ8Walk.WalkDepthOK D.reads)
    {h : ℕ} (o : StrictOrbitDomain (ZMod P) 3 h)
    (hinj : Function.Injective (ComplJ8Of.powN o (walkRows D.cells D.reads).length))
    (i : Fin (walkRows D.cells D.reads).length) (c : ℕ) (hc : c < 166) :
    ((Nock.V1J8.Gen.walkGenRowsB (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) D.H
        (Nock.V1J8.Gen.idxN D.cells) HonestK8.certB8 D.cells ((walkRows D.cells D.reads).map wrowOf)
        (krW D.cells D.reads)).1.getD i #[]).getD c 0 =
      fullCol (ComplJ8Of.walk_pos D.cells D.reads)
        (HonestK8.certUp
          (ComplJ8Enc.wColHQBE deltaF powerBasis3 (ComplJ8Of.walk_pos D.cells D.reads)
            (ComplJ8Of.powN o _) o (VerJ8.chalsMJ8 deltaF (toχ χe))
            (ComplJ8Of.pubsWOf deltaF powerBasis3 D o (toχ χe)) (ComplJ8Of.encR deltaF (toχ χe))
            (ComplJ8Of.γV deltaF (toχ χe)) (ComplJ8Of.ρV deltaF (toχ χe)) D.cells D.reads
            (ComplJ8Of.kLW D) (ComplJ8Of.vLW D) (ComplJ8Of.kRW D) (ComplJ8Of.vRW D))
          (ComplJ8Walk.lenB D.cells D.reads)) c i := by
  have hj := i.2
  have hN : (i : ℕ) < ((walkRows D.cells D.reads).map wrowOf).length := by simpa using hj
  rw [walkGenRowsB_getD _ _ _ _ _ _ _ _ _ _ _ _ hN hc]
  rw [List.length_map, dsL_dW χe D i hj _ ⟨.atom 0, .atom 0, 0, 0, false, false, 0, 0⟩]
  obtain ⟨hl1, hl2⟩ := hcur_ok χe D hcs hwcell hwroot i hj
  obtain ⟨l1, l2, l3⟩ := GenPortJ9AHWalkAcc.walkLCA_eq D.cells D.reads
    (ComplJ8Enc.wNodeValE deltaF (ComplJ8Of.encR deltaF (toχ χe)) D.cells (VerJ8.chalsMJ8 deltaF (toχ χe) 1))
    (chalsMJ8E χe 0)
    ((dsL (coOf χe) (yE χe) D.H (idxN D.cells) D.cells ((walkRows D.cells D.reads).map wrowOf)).map
      (curD (chalsMJ8E χe 1))) ⟨hl1, hl2⟩ i hj
    ((lcaL (coOf χe) (yE χe) (chalsMJ8E χe 0) (chalsMJ8E χe 1) D.H (idxN D.cells) D.cells
      ((walkRows D.cells D.reads).map wrowOf) (krW D.cells D.reads)).getD i (0, 0, 0)) rfl
  rw [toK_chals] at l1 l2 l3
  exact col_core χe D hcs hwcell hwroot o hinj i hj c hc _
    (GenPortJ9AHWalkAcc.q_eq D.cells D.reads i hj) _ _ _ _ _ _ _
    l1 l2 l3
    (scan_sum χe D hcs hwcell hwroot (fun d => d.xInv) i hj) (scan_sum χe D hcs hwcell hwroot pTermD i hj)
    (scan_sum χe D hcs hwcell hwroot (fun d => d.hXi) i hj) (scan_sum χe D hcs hwcell hwroot hPTermD i hj)

end Main

#print axioms scanK6_eq
#print axioms toQ_scanK6_getD
#print axioms dsL_getD
#print axioms walkGenRowsB_getD
#print axioms dsL_dW
#print axioms fp_toQ
#print axioms wrole_eq
#print axioms walkColDB_role
#print axioms walkColDB_hand
#print axioms hXi_eq
#print axioms hPLi_eq
#print axioms hPRi_eq
#print axioms hxaR
#print axioms hpaR
#print axioms pAccEq
#print axioms xAccEq
#print axioms col_core
#print axioms scan_sum
#print axioms hcur_ok
#print axioms walkGenRowsB_cols

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHWalk
