/-
  Nock/NockVMROM/Thm54/TraceGen/GenSkeletonVcomp.lean

  Every node of a `genComputeSkeleton` tree satisfies `Vcomp` on its
  `stampOfAcc` render (`ComputeRowAccepted`'s third conjunct).  OP7/OP8
  subformula slots follow AIR `evalV` (`sf1` = consumer, `sf2` = helper).
  Autocons `headCell` (`f_h.dyck ≠ 0`) is an extra hypothesis: NPR cell
  Dyck can vanish at a finite-field seed.  OP5 `tis` vs `eqOp` agrees
  when the compared operands at that node do not collide.  OP3 cell-test
  agrees when that node's call result is not a size-`z` cell.  Both
  extra hypotheses are tree-local (inhabitable on a generated tree that
  never uses OP3 and whose OP5 operands are small atoms).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonBind
import Nock.NockVMROM.Thm54.TraceGen.BFSAssign
import Nock.NockVMROM.Thm54.P8Census

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open ComputeTable

variable {K : Type} [Field K]

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

/-! ## Encoding helpers -/

theorem encC_atom_fp (z : K) (k : ℕ) :
    encC z (.atom k) = FP.atomFP z (k : K) := by
  rw [encC_eq, GlobalCarryRecognizer.enc_atom]

theorem encC_atom_size_dyck (z : K) (k : ℕ) :
    (encC z (.atom k)).size = z ∧ (encC z (.atom k)).dyck = 0 := by
  simp [encC_atom_fp, FP.atomFP]

theorem encC_atom_leaf (z : K) (k : ℕ) :
    (encC z (.atom k)).leaf = (k : K) := by
  simp [encC_atom_fp, FP.atomFP]

theorem encC_lus_atom (z : K) (n : ℕ) :
    encC z (.atom (n + 1)) = FP.inc z (encC z (.atom n)) := by
  simp [encC_atom_fp, FP.inc, FP.atomFP, Nat.cast_succ]

theorem lus_eq_some {n r : Noun} (h : Noun.lus n = some r) :
    ∃ k, n = .atom k ∧ r = .atom (k + 1) := by
  cases n with
  | atom k =>
      simp [Noun.lus] at h
      exact ⟨k, rfl, h.symm⟩
  | cell _ _ =>
      simp [Noun.lus] at h

theorem encC_wut_atom (z : K) (k : ℕ) :
    encC z (Noun.wut (.atom k)) =
      FP.atomFP z (FP.qm z (encC z (.atom k))) := by
  simp [Noun.wut, encC_atom_fp, FP.qm, FP.atomFP]

theorem encC_wut_cell (z : K) (x y : Noun)
    (hsz : (encC z (.cell x y)).size ≠ z) :
    encC z (Noun.wut (.cell x y)) =
      FP.atomFP z (FP.qm z (encC z (.cell x y))) := by
  simp only [Noun.wut, encC_atom_fp, FP.qm]
  rw [if_neg hsz]
  simp

theorem encC_tis (z : K) (a b : Noun)
    (h : a = b ∨ encC z a ≠ encC z b) :
    encC z (Noun.tis a b) =
      FP.atomFP z (FP.eqOp (encC z a) (encC z b)) := by
  cases h with
  | inl heq =>
      subst heq
      simp [Noun.tis, FP.eqOp, encC_atom_fp]
  | inr hne =>
      have hab : a ≠ b := fun heq => hne (heq ▸ rfl)
      exact encC_tis_of_enc_ne z a b hab hne

theorem encC_cell_atom_dyck (z : K) (hz : z ≠ 0) (k : ℕ) (y : Noun) :
    (encC z (.cell (.atom k) y)).dyck =
      z * (1 + z * (encC z y).dyck) := by
  have hsz : (encC z (.atom k)).size = z := (encC_atom_size_dyck z k).1
  have hdy : (encC z (.atom k)).dyck = 0 := (encC_atom_size_dyck z k).2
  rw [encC_eq, GlobalCarryRecognizer.enc_cons hz]
  simp only [FP.cons]
  rw [← encC_eq (n := .atom k), ← encC_eq (n := y), hsz, hdy]
  rw [mul_zero, zero_add]
  have hz' : z * z * z⁻¹ = z := by
    rw [mul_assoc, mul_inv_cancel₀ hz, mul_one]
  rw [hz']
  ring

theorem encC_cell_atom_atom_dyck (z : K) (hz : z ≠ 0) (a b : ℕ) :
    (encC z (.cell (.atom a) (.atom b))).dyck = z := by
  have h := encC_cell_atom_dyck z hz a (.atom b)
  have hdy : (encC z (.atom b)).dyck = 0 := (encC_atom_size_dyck z b).2
  rw [hdy] at h
  simpa using h

theorem encC_cell_atom_atom_dyck_ne (z : K) (hz : z ≠ 0) (a b : ℕ) :
    (encC z (.cell (.atom a) (.atom b))).dyck ≠ 0 := by
  rw [encC_cell_atom_atom_dyck z hz a b]
  exact hz

/-! ## Assigned-stamp `Vcomp` on an explicit `skelNode` -/

theorem vcomp_render_cons (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject leftF rightF leftR rightR : Noun)
    (reqs : List (ServiceReq K))
    (hhead : (encC z leftF).dyck ≠ 0) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelCons subject leftF rightF leftR rightR) reqs)
        with stamp := stampOfAcc State.cons acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelCons subject leftF rightF leftR rightR) reqs)
      with stamp := stampOfAcc State.cons acc}
  have hstate : g.skel.state = State.cons := by simp [g, skelNode, genSkelCons]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelCons, stampOfAcc_lnPrevExponent]
  refine renderNode_cons_Vcomp_of_assigned z α g leftF rightF leftR rightR
    hz hstate ?hform ?heval hhead hstamp
  · simp [g, skelNode, genSkelCons]
  · simp [g, skelNode, genSkelCons]

theorem vcomp_render_op0 (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject result : Noun) (ax : ℕ) (reqs : List (ServiceReq K)) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelOp0 subject (.cell (.atom 0) (.atom ax))
          (.atom 0) (.atom ax) result ax) reqs)
        with stamp := stampOfAcc State.s0 acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelOp0 subject (.cell (.atom 0) (.atom ax))
        (.atom 0) (.atom ax) result ax) reqs)
      with stamp := stampOfAcc State.s0 acc}
  have hstate : g.skel.state = State.s0 := by simp [g, skelNode, genSkelOp0]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelOp0, stampOfAcc_lnPrevExponent]
  refine renderNode_op0_Vcomp_of_assigned z α g hz hstate ?hform hstamp
  simp [g, skelNode, genSkelOp0, P8Census.skeletonMemoryAxis,
    Nock.Framework.recordCount]

theorem vcomp_render_op1 (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject result : Noun) (reqs : List (ServiceReq K)) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelOp1 subject (.cell (.atom 1) result) result (.atom 1))
          reqs)
        with stamp := stampOfAcc State.s1 acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelOp1 subject (.cell (.atom 1) result) result (.atom 1))
        reqs)
      with stamp := stampOfAcc State.s1 acc}
  have hstate : g.skel.state = State.s1 := by simp [g, skelNode, genSkelOp1]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelOp1, stampOfAcc_lnPrevExponent]
  refine renderNode_op1_Vcomp_of_assigned z α g hz hstate ?hform hstamp
  simp [g, skelNode, genSkelOp1]

theorem vcomp_render_op4 (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject tail callResult result : Noun) (reqs : List (ServiceReq K))
    (hlus : Noun.lus callResult = some result) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelOp4 subject (.cell (.atom 4) tail) (.atom 4) tail
          subject tail callResult result) reqs)
        with stamp := stampOfAcc State.s4 acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelOp4 subject (.cell (.atom 4) tail) (.atom 4) tail
        subject tail callResult result) reqs)
      with stamp := stampOfAcc State.s4 acc}
  obtain ⟨k, hcall, hres⟩ := lus_eq_some hlus
  subst callResult result
  have hstate : g.skel.state = State.s4 := by simp [g, skelNode, genSkelOp4]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelOp4, stampOfAcc_lnPrevExponent]
  refine renderNode_op4_Vcomp_of_assigned z α g hz hstate ?hform ?hsf1s
    ?hsf1e ?heval hstamp
  · simp [g, skelNode, genSkelOp4, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp4, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp only [g, skelNode, genSkelOp4, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
    exact encC_atom_size_dyck z k
  · simp only [g, skelNode, genSkelOp4, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
    exact encC_lus_atom z k

theorem vcomp_render_op5 (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject b c sf1 sf2 : Noun) (reqs : List (ServiceReq K))
    (hncol : sf1 = sf2 ∨ encC z sf1 ≠ encC z sf2) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelOp5 subject (.cell (.atom 5) (.cell b c)) (.atom 5)
          (.cell b c) b c sf1 sf2 (Noun.tis sf1 sf2)) reqs)
        with stamp := stampOfAcc State.s5 acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelOp5 subject (.cell (.atom 5) (.cell b c)) (.atom 5)
        (.cell b c) b c sf1 sf2 (Noun.tis sf1 sf2)) reqs)
      with stamp := stampOfAcc State.s5 acc}
  have hstate : g.skel.state = State.s5 := by simp [g, skelNode, genSkelOp5]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelOp5, stampOfAcc_lnPrevExponent]
  refine renderNode_op5_Vcomp_of_assigned z α g hz hstate ?hform ?hsf1s
    ?hsf2s ?heval hstamp
  · simp [g, skelNode, genSkelOp5, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp5, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp5, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp5, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
    exact encC_tis z sf1 sf2 hncol

theorem vcomp_render_op6_zero (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject b c d result : Noun) (reqs : List (ServiceReq K)) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelOp6 subject (.cell (.atom 6) (.cell b (.cell c d)))
          (.atom 6) (.cell b (.cell c d)) b (.cell c d) c d (.atom 0)
          c result) reqs)
        with stamp := stampOfAcc State.s6 acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelOp6 subject (.cell (.atom 6) (.cell b (.cell c d)))
        (.atom 6) (.cell b (.cell c d)) b (.cell c d) c d (.atom 0)
        c result) reqs)
      with stamp := stampOfAcc State.s6 acc}
  have hstate : g.skel.state = State.s6 := by simp [g, skelNode, genSkelOp6]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelOp6, stampOfAcc_lnPrevExponent]
  refine renderNode_op6_Vcomp_of_assigned z α g c d hz hstate ?hform ?hsf1s
    ?hsf2s ?hsf1f ?heval ?hsf2e hstamp
  · simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · refine Or.inl ⟨?_, ?_⟩
    · have hr : P8Census.skeletonSubformula g.skel 1 .result = .atom 0 := by
        simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
          ComputeTable.fanoutComp]
      rw [hr]; simpa using encC_atom_leaf z 0
    · simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
        ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · have hr : P8Census.skeletonSubformula g.skel 1 .result = .atom 0 := by
      simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
        ComputeTable.fanoutComp]
    refine ⟨?_, ?_, Or.inl ?_⟩
    · rw [hr]; exact (encC_atom_size_dyck z 0).1
    · rw [hr]; exact (encC_atom_size_dyck z 0).2
    · rw [hr]; simpa using encC_atom_leaf z 0

theorem vcomp_render_op6_one (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject b c d result : Noun) (reqs : List (ServiceReq K)) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelOp6 subject (.cell (.atom 6) (.cell b (.cell c d)))
          (.atom 6) (.cell b (.cell c d)) b (.cell c d) c d (.atom 1)
          d result) reqs)
        with stamp := stampOfAcc State.s6 acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelOp6 subject (.cell (.atom 6) (.cell b (.cell c d)))
        (.atom 6) (.cell b (.cell c d)) b (.cell c d) c d (.atom 1)
        d result) reqs)
      with stamp := stampOfAcc State.s6 acc}
  have hstate : g.skel.state = State.s6 := by simp [g, skelNode, genSkelOp6]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelOp6, stampOfAcc_lnPrevExponent]
  refine renderNode_op6_Vcomp_of_assigned z α g c d hz hstate ?hform ?hsf1s
    ?hsf2s ?hsf1f ?heval ?hsf2e hstamp
  · simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · refine Or.inr ⟨?_, ?_⟩
    · have hr : P8Census.skeletonSubformula g.skel 1 .result = .atom 1 := by
        simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
          ComputeTable.fanoutComp]
      rw [hr]; simpa using encC_atom_leaf z 1
    · simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
        ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · have hr : P8Census.skeletonSubformula g.skel 1 .result = .atom 1 := by
      simp [g, skelNode, genSkelOp6, P8Census.skeletonSubformula,
        ComputeTable.fanoutComp]
    refine ⟨?_, ?_, Or.inr ?_⟩
    · rw [hr]; exact (encC_atom_size_dyck z 1).1
    · rw [hr]; exact (encC_atom_size_dyck z 1).2
    · rw [hr]; simpa using encC_atom_leaf z 1

theorem vcomp_render_op7 (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject b c sb result : Noun) (reqs : List (ServiceReq K)) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelOp7 subject (.cell (.atom 7) (.cell b c)) (.atom 7)
          (.cell b c) b c sb result) reqs)
        with stamp := stampOfAcc State.s7 acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelOp7 subject (.cell (.atom 7) (.cell b c)) (.atom 7)
        (.cell b c) b c sb result) reqs)
      with stamp := stampOfAcc State.s7 acc}
  have hstate : g.skel.state = State.s7 := by simp [g, skelNode, genSkelOp7]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelOp7, stampOfAcc_lnPrevExponent]
  refine renderNode_op7_Vcomp_of_assigned z α g hz hstate ?hform ?hsf1s
    ?hsf2s ?heval hstamp
  · simp [g, skelNode, genSkelOp7, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp7, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp7, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp7, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]

theorem vcomp_render_op8 (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject b c sb result : Noun) (reqs : List (ServiceReq K)) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelOp8 subject (.cell (.atom 8) (.cell b c)) (.atom 8)
          (.cell b c) b c sb result) reqs)
        with stamp := stampOfAcc State.s8 acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelOp8 subject (.cell (.atom 8) (.cell b c)) (.atom 8)
        (.cell b c) b c sb result) reqs)
      with stamp := stampOfAcc State.s8 acc}
  have hstate : g.skel.state = State.s8 := by simp [g, skelNode, genSkelOp8]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelOp8, stampOfAcc_lnPrevExponent]
  refine renderNode_op8_Vcomp_of_assigned z α g hz hstate ?hform ?hsf1s
    ?hsf2s ?heval hstamp
  · simp [g, skelNode, genSkelOp8, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp8, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp8, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp8, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]

theorem vcomp_render_op9 (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject c core arm result : Noun) (ax : ℕ) (reqs : List (ServiceReq K)) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelOp9 subject (.cell (.atom 9) (.cell (.atom ax) c))
          (.atom 9) (.cell (.atom ax) c) (.atom ax) c core arm result ax) reqs)
        with stamp := stampOfAcc State.s9 acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelOp9 subject (.cell (.atom 9) (.cell (.atom ax) c))
        (.atom 9) (.cell (.atom ax) c) (.atom ax) c core arm result ax) reqs)
      with stamp := stampOfAcc State.s9 acc}
  have hstate : g.skel.state = State.s9 := by simp [g, skelNode, genSkelOp9]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelOp9, stampOfAcc_lnPrevExponent]
  refine renderNode_op9_Vcomp_of_assigned z α g hz hstate ?hform ?hsf1s
    ?hsf2s ?heval hstamp
  · simp [g, skelNode, genSkelOp9, P8Census.skeletonSubformula,
      P8Census.skeletonMemoryAxis, ComputeTable.fanoutComp,
      Nock.Framework.recordCount]
  · simp [g, skelNode, genSkelOp9, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp9, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp9, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]

theorem vcomp_render_op2 (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject b c sf1 sf2 result : Noun) (reqs : List (ServiceReq K)) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelOp2 subject (.cell (.atom 2) (.cell b c)) (.atom 2)
          (.cell b c) b c sf1 sf2 result) reqs)
        with stamp := stampOfAcc State.s2 acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelOp2 subject (.cell (.atom 2) (.cell b c)) (.atom 2)
        (.cell b c) b c sf1 sf2 result) reqs)
      with stamp := stampOfAcc State.s2 acc}
  have hstate : g.skel.state = State.s2 := by simp [g, skelNode, genSkelOp2]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelOp2, stampOfAcc_lnPrevExponent]
  refine renderNode_op2_Vcomp_of_assigned z α g hz hstate ?hform ?hsf1s
    ?hsf2s ?hsf3s ?hsf3f ?heval hstamp
  · simp [g, skelNode, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp2, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]

theorem vcomp_render_op3 (z α : K) (hz : z ≠ 0) (acc : ℕ)
    (subject tail callResult : Noun) (reqs : List (ServiceReq K))
    (hwut : encC z (Noun.wut callResult) =
      FP.atomFP z (FP.qm z (encC z callResult))) :
    let g : GenComputeRow K :=
      {(skelNode (genSkelOp3 subject (.cell (.atom 3) tail) (.atom 3) tail
          subject tail callResult (Noun.wut callResult)) reqs)
        with stamp := stampOfAcc State.s3 acc}
    Vcomp (renderNode z α g).row.2.1
      (renderNode z α g).row.2.2.1 (renderNode z α g).row.2.2.2 := by
  let g : GenComputeRow K :=
    {(skelNode (genSkelOp3 subject (.cell (.atom 3) tail) (.atom 3) tail
        subject tail callResult (Noun.wut callResult)) reqs)
      with stamp := stampOfAcc State.s3 acc}
  have hstate : g.skel.state = State.s3 := by simp [g, skelNode, genSkelOp3]
  have hstamp : g.stamp = stampOfAcc g.skel.state g.stamp.lnPrevExponent := by
    simp [g, skelNode, genSkelOp3, stampOfAcc_lnPrevExponent]
  refine renderNode_op3_Vcomp_of_assigned z α g hz hstate ?hform ?hsf1s
    ?heval hstamp
  · simp [g, skelNode, genSkelOp3, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simp [g, skelNode, genSkelOp3, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp]
  · simpa [g, skelNode, genSkelOp3, P8Census.skeletonSubformula,
      ComputeTable.fanoutComp] using hwut

set_option maxHeartbeats 8000000

/-! ## Generated trees satisfy `Vcomp` under `stampOfAcc` -/

/-- OP5 NPR non-collision on the two compared operand nouns. -/
def op5ResultsAgree (z : K) (s : ComputeRowSkeleton) : Prop :=
  P8Census.skeletonSubformula s 0 TripleSlot.result =
      P8Census.skeletonSubformula s 1 TripleSlot.result ∨
    encC z (P8Census.skeletonSubformula s 0 TripleSlot.result) ≠
      encC z (P8Census.skeletonSubformula s 1 TripleSlot.result)

/-- OP3 cell-test size window on the recursive call's result. -/
def op3CallSizeOk (z : K) (s : ComputeRowSkeleton) : Prop :=
  match P8Census.skeletonSubformula s 0 TripleSlot.result with
  | .atom _ => True
  | .cell x y => (encC z (.cell x y)).size ≠ z

/-- Restrict a state-gated node hypothesis to a child tree. -/
theorem inTreeState_restrict {st : State} {P : ComputeRowSkeleton → Prop}
    {t c : NTree (GenComputeRow K)}
    (h : ∀ v, InTree t v → v.label.skel.state = st → P v.label.skel)
    (hc : c ∈ t.children) :
    ∀ v, InTree c v → v.label.skel.state = st → P v.label.skel :=
  fun v hv hs => h v (InTree.sub hc hv) hs

/-- Restrict a cons-head Dyck hypothesis to a child tree. -/
theorem consHeadDyck_sub {z : K} {t c : NTree (GenComputeRow K)}
    (hdyck : ∀ v, InTree t v → v.label.skel.state = State.cons →
      (encC z (formulaHead v.label.skel.formula)).dyck ≠ 0)
    (hc : c ∈ t.children) :
    ∀ v, InTree c v → v.label.skel.state = State.cons →
      (encC z (formulaHead v.label.skel.formula)).dyck ≠ 0 :=
  fun v hv hs => hdyck v (InTree.sub hc hv) hs

/-- Restrict an OP5 non-collision hypothesis to a child tree. -/
theorem op5Agree_sub {z : K} {t c : NTree (GenComputeRow K)}
    (hncol : ∀ v, InTree t v → v.label.skel.state = State.s5 →
      op5ResultsAgree z v.label.skel)
    (hc : c ∈ t.children) :
    ∀ v, InTree c v → v.label.skel.state = State.s5 →
      op5ResultsAgree z v.label.skel :=
  fun v hv hs => hncol v (InTree.sub hc hv) hs

/-- Restrict an OP3 cell-size hypothesis to a child tree. -/
theorem op3Size_sub {z : K} {t c : NTree (GenComputeRow K)}
    (hsz : ∀ v, InTree t v → v.label.skel.state = State.s3 →
      op3CallSizeOk z v.label.skel)
    (hc : c ∈ t.children) :
    ∀ v, InTree c v → v.label.skel.state = State.s3 →
      op3CallSizeOk z v.label.skel :=
  fun v hv hs => hsz v (InTree.sub hc hv) hs

theorem genSkelOp5_results (subject formula head fTail fTh fTt sf1 sf2 result : Noun) :
    P8Census.skeletonSubformula
        (genSkelOp5 subject formula head fTail fTh fTt sf1 sf2 result) 0
        TripleSlot.result = sf1 ∧
      P8Census.skeletonSubformula
        (genSkelOp5 subject formula head fTail fTh fTt sf1 sf2 result) 1
        TripleSlot.result = sf2 := by
  constructor <;>
    simp [P8Census.skeletonSubformula, genSkelOp5, ComputeTable.fanoutComp]

theorem op3CallSizeOk_cell {z : K} {s : ComputeRowSkeleton} {x y : Noun}
    (h : op3CallSizeOk z s)
    (hr : P8Census.skeletonSubformula s 0 TripleSlot.result = .cell x y) :
    (encC z (.cell x y)).size ≠ z := by
  unfold op3CallSizeOk at h
  rw [hr] at h
  exact h

/-- Every node of a successfully generated compute tree satisfies `Vcomp` at
    `stampOfAcc`.  `hdyck` is autocons `headCell`; `hncol` is OP5 NPR
    non-collision on the compared operands -/
theorem genComputeSkeleton_inTree_Vcomp
    (z α : K) (hz : z ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hdyck : ∀ v, InTree t v → v.label.skel.state = State.cons →
      (encC z (formulaHead v.label.skel.formula)).dyck ≠ 0)
    (hncol : ∀ v, InTree t v → v.label.skel.state = State.s5 →
      op5ResultsAgree z v.label.skel)
    (hsz : ∀ v, InTree t v → v.label.skel.state = State.s3 →
      op3CallSizeOk z v.label.skel)
    (u : NTree (GenComputeRow K)) (hu : InTree t u) (acc : ℕ) :
    Vcomp (renderNode z α
        {(u.label) with stamp := stampOfAcc u.label.skel.state acc}).row.2.1
      (renderNode z α
        {(u.label) with stamp := stampOfAcc u.label.skel.state acc}).row.2.2.1
      (renderNode z α
        {(u.label) with stamp := stampOfAcc u.label.skel.state acc}).row.2.2.2 := by
  induction fuel generalizing subject formula t result u acc with
  | zero =>
    simp [genComputeSkeleton] at h
  | succ n ih =>
    cases formula with
    | atom _ =>
      simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error _ =>
          simp [genComputeSkeleton, hL] at h
        | ok pL =>
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hL, hR] at h
          | ok pR =>
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨rfl, rfl⟩ := h
            cases hu with
            | here =>
              have hhead : (encC z (.cell lh lt)).dyck ≠ 0 :=
                hdyck _ (InTree.here _) (by simp [skelNode, genSkelCons])
              simpa [skelNode, genSkelCons] using
                vcomp_render_cons z α hz acc subject (.cell lh lt) tl pL.2 pR.2 _
                  hhead
            | sub hs hu' =>
              simp [NTree.children] at hs
              rcases hs with rfl | rfl
              · exact ih hL (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
              · exact ih hR (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        · -- OP_0
          cases tl with
          | cell _ _ =>
            simp [genComputeSkeleton] at h
          | atom ax =>
            cases hslot : Noun.slot ax subject with
            | none =>
              simp [genComputeSkeleton, hslot] at h
            | some slotR =>
              simp [genComputeSkeleton, hslot] at h
              obtain ⟨rfl, rfl⟩ := h
              cases hu with
              | here =>
                simpa [skelNode, genSkelOp0] using
                  vcomp_render_op0 z α hz acc subject slotR ax _
              | sub hs _ =>
                simp [NTree.children] at hs
        · -- OP_1
          simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hu with
          | here =>
            simpa [skelNode, genSkelOp1] using
              vcomp_render_op1 z α hz acc subject tl _
          | sub hs _ =>
            simp [NTree.children] at hs
        · -- OP_2
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                cases hM : genComputeSkeleton (K := K) n pB.2 pC.2 with
                | error _ =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pM =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  obtain ⟨rfl, rfl⟩ := h
                  cases hu with
                  | here =>
                    simpa [skelNode, genSkelOp2] using
                      vcomp_render_op2 z α hz acc subject b c pB.2 pC.2 pM.2 _
                  | sub hs hu' =>
                    simp [NTree.children] at hs
                    rcases hs with rfl | rfl | rfl
                    · exact ih hB (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
                    · exact ih hC (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
                    · exact ih hM (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
        · -- OP_3
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            cases hu with
            | here =>
              have hwut : encC z (Noun.wut p.2) =
                  FP.atomFP z (FP.qm z (encC z p.2)) := by
                cases hp : p.2 with
                | atom k =>
                    exact encC_wut_atom z k
                | cell x y =>
                    exact encC_wut_cell z x y <|
                      op3CallSizeOk_cell
                        (hsz _ (InTree.here _) (by simp [skelNode, genSkelOp3]))
                        (by
                          simp [skelNode, genSkelOp3, P8Census.skeletonSubformula,
                            ComputeTable.fanoutComp, hp])
              simpa [skelNode, genSkelOp3] using
                vcomp_render_op3 z α hz acc subject tl p.2 _ hwut
            | sub hs hu' =>
              simp [NTree.children] at hs
              cases hs
              exact ih hcall (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
        · -- OP_4
          cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ =>
            simp [genComputeSkeleton, hcall] at h
          | ok p =>
            cases hlus : Noun.lus p.2 with
            | none =>
              simp [genComputeSkeleton, hcall, hlus] at h
            | some lusR =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              cases hu with
              | here =>
                simpa [skelNode, genSkelOp4] using
                  vcomp_render_op4 z α hz acc subject tl p.2 lusR _ hlus
              | sub hs hu' =>
                simp [NTree.children] at hs
                cases hs
                exact ih hcall (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
        · -- OP_5
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  have hp : pB.2 = pC.2 ∨ encC z pB.2 ≠ encC z pC.2 := by
                    have hagr := hncol _ (InTree.here _)
                      (by simp [skelNode, genSkelOp5])
                    simpa [op5ResultsAgree, skelNode, genSkelOp5,
                      P8Census.skeletonSubformula, ComputeTable.fanoutComp]
                      using hagr
                  simpa [skelNode, genSkelOp5] using
                    vcomp_render_op5 z α hz acc subject b c pB.2 pC.2 _ hp
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
                  · exact ih hC (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
        · -- OP_6
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ =>
              simp [genComputeSkeleton] at h
            | cell c d =>
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ =>
                simp [genComputeSkeleton, hcond] at h
              | ok pCond =>
                cases hval : pCond.2 with
                | cell _ _ =>
                  simp [genComputeSkeleton, hcond, hval] at h
                | atom condv =>
                  cases condv with
                  | zero =>
                    cases htaken : genComputeSkeleton (K := K) n subject c with
                    | error _ =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                    | ok pTaken =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                      obtain ⟨rfl, rfl⟩ := h
                      cases hu with
                      | here =>
                        simpa [skelNode, genSkelOp6] using
                          vcomp_render_op6_zero z α hz acc subject b c d pTaken.2 _
                      | sub hs hu' =>
                        simp [NTree.children] at hs
                        rcases hs with rfl | rfl
                        · exact ih hcond (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
                        · exact ih htaken (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
                  | succ condv =>
                    cases condv with
                    | zero =>
                      cases htaken : genComputeSkeleton (K := K) n subject d with
                      | error _ =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                      | ok pTaken =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                        obtain ⟨rfl, rfl⟩ := h
                        cases hu with
                        | here =>
                          simpa [skelNode, genSkelOp6] using
                            vcomp_render_op6_one z α hz acc subject b c d pTaken.2 _
                        | sub hs hu' =>
                          simp [NTree.children] at hs
                          rcases hs with rfl | rfl
                          · exact ih hcond (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
                          · exact ih htaken (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
                    | succ _ =>
                      simp [genComputeSkeleton, hcond, hval] at h
        · -- OP_7
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n pB.2 c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  simpa [skelNode, genSkelOp7] using
                    vcomp_render_op7 z α hz acc subject b c pB.2 pC.2 _
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
                  · exact ih hC (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
        · -- OP_8
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ =>
              simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n (.cell pB.2 subject) c with
              | error _ =>
                simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  simpa [skelNode, genSkelOp8] using
                    vcomp_render_op8 z α hz acc subject b c pB.2 pC.2 _
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
                  · exact ih hC (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
        · -- OP_9
          cases tl with
          | atom _ =>
            simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ =>
              simp [genComputeSkeleton] at h
            | atom ax =>
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ =>
                simp [genComputeSkeleton, hcore] at h
              | ok pCore =>
                cases hslot : Noun.slot ax pCore.2 with
                | none =>
                  simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pCore.2 arm with
                  | error _ =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pInv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    obtain ⟨rfl, rfl⟩ := h
                    cases hu with
                    | here =>
                      simpa [skelNode, genSkelOp9] using
                        vcomp_render_op9 z α hz acc subject c pCore.2 arm
                          pInv.2 ax _
                    | sub hs hu' =>
                      simp [NTree.children] at hs
                      rcases hs with rfl | rfl
                      · exact ih hcore (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
                      · exact ih hinv (consHeadDyck_sub hdyck (by simp [NTree.children])) (op5Agree_sub hncol (by simp [NTree.children])) (op3Size_sub hsz (by simp [NTree.children])) _ hu' acc
        · -- OP_10 notROM
          simp [genComputeSkeleton] at h
        · -- OP_11 notROM
          simp [genComputeSkeleton] at h
        · -- ≥ 12 malformed
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

theorem genComputeSkeleton_bfs_Vcomp
    (z α : K) (hz : z ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hdyck : ∀ v, InTree t v → v.label.skel.state = State.cons →
      (encC z (formulaHead v.label.skel.formula)).dyck ≠ 0)
    (hncol : ∀ v, InTree t v → v.label.skel.state = State.s5 →
      op5ResultsAgree z v.label.skel)
    (hsz : ∀ v, InTree t v → v.label.skel.state = State.s3 →
      op3CallSizeOk z v.label.skel)
    {n : NTree (GenComputeRow K)}
    (hn : n ∈ bfsForest [t]) (acc : ℕ) :
    Vcomp (renderNode z α
        {(n.label) with stamp := stampOfAcc n.label.skel.state acc}).row.2.1
      (renderNode z α
        {(n.label) with stamp := stampOfAcc n.label.skel.state acc}).row.2.2.1
      (renderNode z α
        {(n.label) with stamp := stampOfAcc n.label.skel.state acc}).row.2.2.2 := by
  have hin : InTree t n := by
    have := (mem_bfsForest [t] n).mp hn
    obtain ⟨c, hc, hct⟩ := this
    simp at hc
    subst c
    exact hct
  exact genComputeSkeleton_inTree_Vcomp z α hz h hdyck hncol hsz n hin acc

theorem genComputeSkeleton_bfsLabelAt_Vcomp
    (z α : K) (hz : z ≠ 0)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hdyck : ∀ v, InTree t v → v.label.skel.state = State.cons →
      (encC z (formulaHead v.label.skel.formula)).dyck ≠ 0)
    (hncol : ∀ v, InTree t v → v.label.skel.state = State.s5 →
      op5ResultsAgree z v.label.skel)
    (hsz : ∀ v, InTree t v → v.label.skel.state = State.s3 →
      op3CallSizeOk z v.label.skel)
    {i : ℕ} (hi : i ∈ List.range' 1 (bfsForest [t]).length) :
    Vcomp (renderNode z α (bfsLabelAt t i)).row.2.1
      (renderNode z α (bfsLabelAt t i)).row.2.2.1
      (renderNode z α (bfsLabelAt t i)).row.2.2.2 := by
  have hi' := lt_bfsRows_of_mem_range' hi
  have hlen : i - 1 < (bfsForest [t]).length := by
    simpa [bfsRows_length] using hi'
  have hmem : (bfsForest [t])[i - 1] ∈ bfsForest [t] := List.getElem_mem hlen
  have hlbl : (bfsForest [t])[i - 1].label = (bfsRows t)[i - 1] := by
    simp [bfsRows]
  rw [bfsLabelAt_eq t i hi']
  simpa [hlbl] using
    genComputeSkeleton_bfs_Vcomp z α hz h hdyck hncol hsz hmem
      (accAt t (i - 1))

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.vcomp_render_op1
#print axioms Nock.NockVMROM.Thm54.TraceGen.vcomp_render_op7
#print axioms Nock.NockVMROM.Thm54.TraceGen.encC_cell_atom_atom_dyck_ne
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_bfsLabelAt_Vcomp
