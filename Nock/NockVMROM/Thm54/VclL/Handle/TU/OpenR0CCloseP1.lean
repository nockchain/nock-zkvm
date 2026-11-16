/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/OpenR0CCloseP1.lean

 **Trace uniqueness on the P1 fragment: closing the open hypotheses of `OpenR0CP1.r0C_of_twins`.**

 * §1 `hdef`: every `actH` handle of every compute row denotes. The tree `rowBridge` uses (the goal's tree,
 relabelled by the first occurrence of each label); `defined_treeXI` gives every node's subject and every real
 node's result; `e_all` extends the result to the chain nodes (a chain child carries its parent's result);
 `actH_def_row` reads the remaining handles off the row semantics, and the `s10L` row's `f_tth` off the pair
 path record (`OpenR0CP1.ftth_s10L`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.CellUniqP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CCloseP1

open Nock Nock.Reified Nock.Edit Nock.Walk
open Nock.Edit.GenX (P1Frag genX)
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemIJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TU.TwinRowSemIJ8 (relabX)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.RowBridgeP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CP1
open Nock.NockVMROM.Thm54 (P8PublicClaim)
open Nock.Jet (Registry)

noncomputable section

/-! ## 1. `hdef` -/

section Def
variable {p : ℕ} [Fact p.Prime] {L : Type} (rw : L → RowVSX) {D : HX → Option Noun} {R : Registry}

/-- **Every node's result denotes**, once the root's does: a real child's result by `defined_treeXI`, a chain
child (`s10` position `2`, `s10L` position `0`) carries its parent's result. -/
theorem e_all (hD : DenOKX p D) : ∀ t : NTree L, RowsOKXI rw p D R t →
    (∀ u, InTree t u → D (rw u.label).s ≠ none ∧ ((rw u.label).st.isChain = false → D (rw u.label).e ≠ none)) →
    D (rw t.label).e ≠ none → ∀ u, InTree t u → D (rw u.label).e ≠ none
  | .node l cs, h, hdef, he => by
    have hroles := h.roles rw hD (InTree.here (NTree.node l cs))
    have hlink : cs.map (fun c => (rw c.label).trip) = kidsX (rw l) := h.link _ (InTree.here (NTree.node l cs))
    have hkid : ∀ c ∈ cs, D (rw c.label).e ≠ none := by
      intro c hc
      have hcu : InTree (NTree.node l cs) c := InTree.sub (by simpa [NTree.children] using hc) (InTree.here _)
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
      have hi' : i < (((NTree.node l cs).children).map fun c => rw c.label).length := by
        simpa [NTree.children] using hi
      have hr : (rw (cs[i]'hi).label).st.isChain = chainPosX (rw l).st i := by
        have := hroles i hi'
        simpa [NTree.children, NTree.label] using this
      cases hcp : chainPosX (rw l).st i
      · rw [hcp] at hr
        exact (hdef _ hcu).2 hr
      · have hlen : i < (kidsX (rw l)).length := by rw [← hlink]; simpa using hi
        have htrip : (rw (cs[i]'hi).label).trip = (kidsX (rw l))[i]'hlen := by
          have := List.getElem_of_eq hlink (by simpa using hi)
          simpa using this
        have heq : (rw (cs[i]'hi).label).e = (rw l).e := by
          have h2 := congrArg (fun x : TripX => x.2.2) htrip
          simp only [RowVSX.trip] at h2
          rw [h2]
          revert hlen
          generalize hS : (rw l).st = S at hcp
          rcases i with _ | _ | _ | i <;> cases S <;> simp [chainPosX] at hcp <;>
            intro hlen <;> simp [kidsX, hS]
        rw [heq]; exact he
    have ih : ∀ c ∈ cs, ∀ u, InTree c u → D (rw u.label).e ≠ none := fun c hc =>
      e_all hD c (h.sub rw (by simpa [NTree.children] using hc))
        (fun u hu => hdef u (InTree.sub (by simpa [NTree.children] using hc) hu)) (hkid c hc)
    intro u hu
    cases hu with
    | here => exact he
    | sub hc hu' => exact ih _ hc u hu'

/-- **The `actH` handles of one row denote**, from the row semantics, the subject and result, the child
triples' subjects and results, and (on `s10L`) the pair record's child `f_tth`. -/
theorem actH_def_row (hD : DenOKX p D) {env : Env (ZMod p)} {st : StateX}
    (hsem : RowSemX0 p D R (rowOfX env st))
    (hs : D (hdV env xS) ≠ none) (he : D (hdV env xE) ≠ none)
    (hk : ∀ k ∈ kidsX (rowOfX env st), D k.1 ≠ none ∧ D k.2.2 ≠ none)
    (hft : st = .s10L → D (hdV env xFtth) ≠ none) :
    ∀ h ∈ actH st, D (hdV env h) ≠ none := by
  intro h hh
  cases st <;> simp only [actH, List.mem_cons, List.not_mem_nil, or_false] at hh <;>
    simp only [RowSemX0, rowOfX] at hsem
  · -- s0
    obtain ⟨c1, -⟩ := hsem
    have n1 := cell3_ne c1
    rcases hh with rfl | rfl | rfl | rfl
    · exact hs
    · exact n1.1
    · exact he
    · exact n1.2.2
  · -- s7
    obtain ⟨c1, -, c2, hes⟩ := hsem
    have n1 := cell3_ne c1
    have n2 := cell3_ne c2
    have k0 := hk (hdV env xSf2, hdV env xFtt, hdV env xSf1) (by simp [kidsX, rowOfX])
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs
    · exact n1.1
    · exact he
    · rw [← hes]; exact he
    · simpa using k0.1
    · exact n1.2.2
    · exact n2.2.1
    · exact n2.2.2
  · -- cons
    obtain ⟨c1, -, c2⟩ := hsem
    have n1 := cell3_ne c1
    have n2 := cell3_ne c2
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs
    · exact n1.1
    · exact he
    · exact n2.2.1
    · exact n2.2.2
    · exact n1.2.1
    · exact n1.2.2
  · -- s10
    obtain ⟨c1, -, c2, c3, -⟩ := hsem
    have n1 := cell3_ne c1
    have n2 := cell3_ne c2
    have n3 := cell3_ne c3
    have k0 := hk (hdV env xS, hdV env xFttt, hdV env xSf1) (by simp [kidsX, rowOfX])
    have k1 := hk (hdV env xS, hdV env xFtt, hdV env xSf2) (by simp [kidsX, rowOfX])
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hs
    · exact n1.1
    · exact he
    · simpa using k0.2
    · simpa using k1.2
    · exact n1.2.2
    · exact n2.2.1
    · exact n2.2.2
    · exact n3.2.1
    · exact n3.2.2
  · -- s10L
    obtain ⟨a, hfa, -⟩ := hsem
    rcases hh with rfl | rfl | rfl | rfl
    · exact hs
    · rw [hfa, hD.atom]; simp
    · exact he
    · exact hft rfl
  · -- s10T
    rcases hh with rfl | rfl | rfl
    · exact hs
    · rw [hsem, hD.atom]; simp
    · exact he

end Def

section Bridge
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
variable {n : ℕ} {E : ℕ → Env (ZMod p)} {st : ℕ → StateX} {D : HX → Option Noun} {R : Registry}
  {comb : ℕ → Noun}

/-- **`hdef` from the bridge's inputs**: every `actH` handle of every compute row denotes. -/
theorem hdef_of_bridge [CharP K p] (hp : 2 ^ 63 + 1 < p) (hD : DenOKX p D) (hn : 1 ≤ n)
    (A : RowsAccXI n E st D R comb) (hG : ForestReconGoal (stVS K) (lblOf (rowsWX E st)) 1 n)
    (x : P8PublicClaim) (hs : D (hdV (E 0) xS) = some x.subject) (hf : D (hdV (E 0) xF) = some x.formula)
    (hfrag : P1Frag x.formula) :
    ∀ j < n, ∀ h ∈ actH (st j), D (hdV (E j) h) ≠ none := by
  classical
  have hp17 : 17 < p := by omega
  obtain ⟨t, hlab, hroot, hrow, hlink⟩ := goal_tree (K := K) hn hG
  obtain ⟨hlen, hlbl⟩ := bfs_at hlab
  have node : ∀ j (hj : j < (bfsForest [t]).length), InTree t ((bfsForest [t])[j]'hj) := by
    intro j hj
    obtain ⟨c, hc, hcu⟩ := (mem_bfsForest [t] _).mp (List.getElem_mem hj)
    rw [List.mem_singleton] at hc; subst hc; exact hcu
  have semI : ∀ i, 1 ≤ i → i ≤ n →
      RowSemX0I p D R (rowOfX (E (i - 1)) (st (i - 1))) ∧ KidKinds (rowOfX (E (i - 1)) (st (i - 1))) := by
    intro i hi1 hin
    have hj : i - 1 < (bfsForest [t]).length := by omega
    have hui := hlbl (i - 1) hj
    rw [show i - 1 + 1 = i by omega] at hui
    exact rowSemXI_of_chip hD (by omega) (A.base _ (by omega)) (st (i - 1)) (A.oh _ (by omega))
      (A.served _ (by omega)) (fun hs => halving_of_treeI hp A hrow hlink (node _ hj) hui hs rfl)
  have spec : ∀ i, 1 ≤ i → i ≤ n → ∃ k, 1 ≤ k ∧ k ≤ n ∧ lblOf (rowsWX E st) i = lblOf (rowsWX E st) k ∧
      relabX n E st (lblOf (rowsWX E st) i) = rowOfX (E (k - 1)) (st (k - 1)) := fun i hi1 hin => by
    have h : ∃ k, 1 ≤ k ∧ k ≤ n ∧ lblOf (rowsWX E st) i = lblOf (rowsWX E st) k := ⟨i, hi1, hin, rfl⟩
    exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2.1, (Nat.find_spec h).2.2,
      by simp only [relabX, dif_pos h]⟩
  have rw_spec : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ n ∧ u.label = lblOf (rowsWX E st) i ∧
      relabX n E st u.label = rowOfX (E (i - 1)) (st (i - 1)) := by
    intro u hu
    obtain ⟨i, hi1, hin, hui⟩ := hrow u hu
    obtain ⟨k, hk1, hkn, hik, hrk⟩ := spec i hi1 hin
    exact ⟨k, hk1, hkn, hui.trans hik, by rw [hui]; exact hrk⟩
  have hok : RowsOKXI (relabX n E st) p D R t := by
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · obtain ⟨i, hi1, hin, -, hrw⟩ := rw_spec u hu
      rw [hrw]; exact semI i hi1 hin
    · obtain ⟨i, hi1, hin, hui, hrw⟩ := rw_spec u hu
      have hm : u.children.map (fun c => (relabX n E st c.label).trip) =
          u.children.map (fun c => c.label.2.trip) :=
        List.map_congr_left fun c hc => by
          obtain ⟨j, -, -, hcj, hrwc⟩ := rw_spec c (inTree_trans hu (InTree.sub hc (InTree.here _)))
          rw [hrwc, hcj]
          simp only [lblOf, rowsWX, rowW_trip]
      rw [hm, hlink u hu, hrw, hui]
      simp only [lblOf, rowsWX]
      by_cases hs : st (i - 1) = .s10L
      · have hH := halving_of_treeI hp A hrow hlink hu hui hs
        have hO := A.oh (i - 1) (by omega)
        rw [hs] at hO ⊢
        exact kidsX_rowW_of_halving (A.base _ (by omega)) hO hH
      · rw [rowW_of_ne _ hs]
  -- the root
  obtain ⟨k0, hk01, hk0n, h1k, hr0⟩ := spec 1 le_rfl hn
  have hroot' : relabX n E st t.label = rowOfX (E (k0 - 1)) (st (k0 - 1)) := by rw [hroot]; exact hr0
  obtain ⟨-, hS0, hF0, -, -⟩ :=
    agree_of_lbl (E := E) (st := st) hD (semI 1 le_rfl hn).1 (semI k0 hk01 hk0n).1 h1k
  simp only [Nat.sub_self] at hS0 hF0
  have hsR : D (relabX n E st t.label).s = some x.subject := by
    rw [hroot']; show D (hdV _ xS) = _; rw [← hS0]; exact hs
  have hfR : D (relabX n E st t.label).f = some x.formula := by
    rw [hroot']; show D (hdV _ xF) = _; rw [← hF0]; exact hf
  have hsR' : D (relabX n E st t.label).s ≠ none := by rw [hsR]; exact Option.some_ne_none _
  have hdefT := defined_treeXI (relabX n E st) hD t hok hsR'
  have hrc : (relabX n E st t.label).st.isChain = false := by
    cases hc : (relabX n E st t.label).st.isChain
    · rfl
    · exfalso
      have hsem0 := (hok.sem t (InTree.here _)).1.1 (preRow_triv
        (by intro h; rw [h] at hc; exact absurd hc (by decide))
        (by intro h; rw [h] at hc; exact absurd hc (by decide))
        (by intro h; rw [h] at hc; exact absurd hc (by decide)))
      have hk := (chain_iff_kind hD hsem0).1 hc
      have hat : D (relabX n E st t.label).f = some (.atom (relabX n E st t.label).f.2) := by
        rw [show (relabX n E st t.label).f = (0, (relabX n E st t.label).f.2) from Prod.ext hk rfl]
        exact hD.atom _
      rw [hfR] at hat
      generalize x.formula = F at hfrag hat
      cases hfrag <;> cases hat
  have heT := e_all (relabX n E st) hD t hok hdefT ((hdefT t (InTree.here _)).2 hrc)
  -- row `j`
  intro j hj h hh
  have hjt : j < (bfsForest [t]).length := by omega
  have hu := node j hjt
  have hui := hlbl j hjt
  obtain ⟨k, hk1, hkn, hjk, hrk⟩ := spec (j + 1) (by omega) (by omega)
  have ag := agree_of_lbl (E := E) (st := st) hD (semI (j + 1) (by omega) (by omega)).1
    (semI k hk1 hkn).1 hjk
  simp only [Nat.add_sub_cancel] at ag
  obtain ⟨hst, hS, hF, hE, hfull⟩ := ag
  have hrel : relabX n E st ((bfsForest [t])[j]'hjt).label = rowOfX (E (k - 1)) (st (k - 1)) := by
    rw [hui]; exact hrk
  have hlinku := hok.link _ hu
  rw [hrel] at hlinku
  have hkx : kidsX (rowOfX (E j) (st j)) = kidsX (rowOfX (E (k - 1)) (st (k - 1))) :=
    kidsX_congr hst hS hF hE hfull
  rw [← hkx] at hlinku
  have hkd : ∀ kk ∈ kidsX (rowOfX (E j) (st j)), D kk.1 ≠ none ∧ D kk.2.2 ≠ none := by
    rw [← hlinku]
    intro kk hkk
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hkk
    have hcu : InTree t c := inTree_trans hu (InTree.sub hc (InTree.here _))
    exact ⟨(hdefT c hcu).1, heT c hcu⟩
  have hsj : D (hdV (E j) xS) ≠ none := by
    rw [hS]; have := (hdefT _ hu).1; rw [hrel] at this; exact this
  have hej : D (hdV (E j) xE) ≠ none := by
    rw [hE]; have := heT _ hu; rw [hrel] at this; exact this
  have hsI := (semI (j + 1) (by omega) (by omega)).1
  simp only [Nat.add_sub_cancel] at hsI
  by_cases h4 : st j = .s4
  · rw [h4] at hh; simp [actH] at hh
  by_cases h5 : st j = .s5
  · rw [h5] at hh; simp [actH] at hh
  by_cases h11 : st j = .s11j
  · rw [h11] at hh; simp [actH] at hh
  have hsem := sem0 hsI h4 h5 h11
  have hft : st j = .s10L → D (hdV (E j) xFtth) ≠ none := by
    intro h10
    have hO : OneHotAt (E j) sS10L := by
      have := (A.oh j hj : OneHotAt (E j) (stIdx (st j))); rw [h10] at this; exact this
    rw [h10] at hsem
    obtain ⟨S, C, -, hC, -⟩ := ftth_s10L hp17 hD (A.base j hj) hO (A.served j hj) hsem
    rw [hC]; exact Option.some_ne_none _
  exact actH_def_row hD hsem hsj hej hkd hft h hh

end Bridge

/-! ## 2. `r0C_closed` -/

section Close
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

/-- **`O.r0C` and `O.claim` from two accepting transcripts**, with `hAx`, `hdef` and `hU` discharged. Two
transcripts at the canonical layout `Pb = canonPb hpG sz c` and one coin vector `χ`, each meeting the hypotheses of
`TwinLinkJ8A.hsoundJ8XUA_ex` with the atom reader pinned to the producer's `rA = rAT b Pb tr`
(`LinkJ8A.linkXUA_of_R5`), the canonical conjuncts `hC`, `hC'` (`canonC`), `hM` (`canonM`, first trace) and the atom
pads `hA`, `hA'`, with equal round-0 cell columns (`hr0M`, the field `OpenP1.r0M`), the claim formula in the
fragment and a terminating generated run: the round-0 compute columns agree at every row node, and the cell claim
serials agree. -/
theorem r0C_closed [CharP K p] [CharP 𝕂′ p] {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1}
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
    (hr0M : ∀ j : Fin 242, (j : ℕ) < 134 → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i))
    (hfrag : P1Frag c.formula) {fuel : ℕ} {tg : NTree GenX.SkelX} {res : Noun}
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
    have ht0 := CellUniqP1.b0_eq_of_r0M δ b _ (chalsMJ8 δ χ) M.pubsC (chalsMJ8 δ χ) M'.pubsC hr0M
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
      rw [hext', ← ht0] at h2
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

end Close

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CCloseP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CCloseP1.e_all
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CCloseP1.actH_def_row
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CCloseP1.hdef_of_bridge
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.OpenR0CCloseP1.r0C_closed
