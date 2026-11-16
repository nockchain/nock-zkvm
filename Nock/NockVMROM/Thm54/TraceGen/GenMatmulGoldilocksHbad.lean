/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulGoldilocksHbad.lean

  Generated census pairs are diagonal or
  `.s5`/`.s6` off-diag (`GenGenericOffdiag`).  Matmul OP5 operands are atoms
  (equal, or `{0,1}`); OP6 branches are `op0 6` vs a slam whose leaf count
  differs.  `hwrap` is generated `Noun.lus` plus `BoundedBy 65537`.

  Completeness, not a new bound summand.  No Galois
  `decide`.  Do not claim `orderOf seedZ = 2^32 → hbad`.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericOffdiag
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksSeed
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulLeafBound
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSeed
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenSubISAWindow

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.P8Census
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

/-! ## Combined generated-tree predicate (off-diag `SepSeed` + OP4 `lus`) -/

def RowOffdiagSep (z : K) (g : GenComputeRow K) : Prop :=
  (g.skel.state = .s5 →
    GlobalCarryRecognizer.SepSeed z
      (skeletonSubformula g.skel 0 TripleSlot.result)
      (skeletonSubformula g.skel 1 TripleSlot.result)) ∧
  (g.skel.state = .s6 →
    GlobalCarryRecognizer.SepSeed z
      (skeletonDec g.skel .f_tth) (skeletonDec g.skel .f_ttt))

def TraceSep (z : K) (t : NTree (GenComputeRow K)) : Prop :=
  (∀ v, InTree t v → RowOffdiagSep z v.label) ∧
  (∀ v, InTree t v → v.label.skel.state = .s4 →
    Noun.lus (skeletonSubformula v.label.skel 0 TripleSlot.result)
      = some v.label.skel.evaluation)

theorem traceSep_of_children {z : K} {lab : GenComputeRow K}
    {cs : List (NTree (GenComputeRow K))}
    (hoff : RowOffdiagSep z lab)
    (hwrap : lab.skel.state = .s4 →
      Noun.lus (skeletonSubformula lab.skel 0 TripleSlot.result)
        = some lab.skel.evaluation)
    (hcs : ∀ c ∈ cs, TraceSep z c) :
    TraceSep z (.node lab cs) := by
  constructor
  · intro v hv
    cases hv with
    | here => exact hoff
    | sub hs hu => exact (hcs _ hs).1 _ hu
  · intro v hv hs4
    cases hv with
    | here => exact hwrap hs4
    | sub hs hu => exact (hcs _ hs).2 _ hu hs4

theorem traceSep_leaf {z : K} {lab : GenComputeRow K}
    (hoff : RowOffdiagSep z lab)
    (hwrap : lab.skel.state = .s4 →
      Noun.lus (skeletonSubformula lab.skel 0 TripleSlot.result)
        = some lab.skel.evaluation) :
    TraceSep z (.node lab []) :=
  traceSep_of_children hoff hwrap (fun _ hc => by simp [NTree.children] at hc)

theorem rowOffdiag_vacuous {z : K} {g : GenComputeRow K}
    (hne5 : g.skel.state ≠ .s5) (hne6 : g.skel.state ≠ .s6) :
    RowOffdiagSep z g :=
  ⟨fun h => absurd h hne5, fun h => absurd h hne6⟩

theorem wrap_vacuous {g : GenComputeRow K} (hne : g.skel.state ≠ .s4) :
    g.skel.state = .s4 →
      Noun.lus (skeletonSubformula g.skel 0 TripleSlot.result)
        = some g.skel.evaluation :=
  fun h => absurd h hne

/-! ## Per-opcode combinators -/

theorem traceSep_gen_op0 {z : K} {n : ℕ} {s : Noun} {ax : ℕ} {r : Noun}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (hslot : Noun.slot ax s = some r)
    (h : genComputeSkeleton (K := K) (n + 1) s (op0 ax) = .ok (t, res)) :
    TraceSep z t := by
  have h' := gen_op0 (K := K) n hslot
  rw [(gen_ok_unique h h').1]
  refine traceSep_leaf ?_ ?_
  · exact rowOffdiag_vacuous (by simp [skelNode, genSkelOp0])
      (by simp [skelNode, genSkelOp0])
  · exact wrap_vacuous (by simp [skelNode, genSkelOp0])

theorem traceSep_gen_op1 {z : K} {n : ℕ} {s : Noun} {k : ℕ}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) s (op1 k) = .ok (t, res)) :
    TraceSep z t := by
  have h' := gen_op1 (K := K) n s k
  rw [(gen_ok_unique h h').1]
  refine traceSep_leaf ?_ ?_
  · exact rowOffdiag_vacuous (by simp [skelNode, genSkelOp1])
      (by simp [skelNode, genSkelOp1])
  · exact wrap_vacuous (by simp [skelNode, genSkelOp1])

theorem traceSep_gen_quote {z : K} {n : ℕ} {s result : Noun}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) s (quote result) = .ok (t, res)) :
    TraceSep z t := by
  have h' := gen_quote (K := K) n s result
  rw [(gen_ok_unique h h').1]
  refine traceSep_leaf ?_ ?_
  · exact rowOffdiag_vacuous (by simp [skelNode, genSkelOp1])
      (by simp [skelNode, genSkelOp1])
  · exact wrap_vacuous (by simp [skelNode, genSkelOp1])

theorem traceSep_gen_op4 {z : K} {n : ℕ} {s tail callResult result : Noun}
    {callTree t : NTree (GenComputeRow K)} {res : Noun}
    (hcall : genComputeSkeleton (K := K) n s tail = .ok (callTree, callResult))
    (hinc : Noun.lus callResult = some result)
    (h : genComputeSkeleton (K := K) (n + 1) s (op4 tail) = .ok (t, res))
    (ih : TraceSep z callTree) :
    TraceSep z t := by
  have h' := gen_op4 (K := K) n hcall hinc
  rw [(gen_ok_unique h h').1]
  refine traceSep_of_children ?_ ?_ ?_
  · exact rowOffdiag_vacuous (by simp [skelNode, genSkelOp4])
      (by simp [skelNode, genSkelOp4])
  · intro _
    simpa [skelNode, genSkelOp4, skeletonSubformula, ComputeTable.fanoutComp]
      using hinc
  · intro c hc
    simp [NTree.children] at hc
    subst c
    exact ih

theorem traceSep_gen_op5 {z : K} {n : ℕ} {s b c sf1 sf2 : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n s c = .ok (cTree, sf2))
    (h : genComputeSkeleton (K := K) (n + 1) s (op5 b c) = .ok (t, res))
    (ihb : TraceSep z bTree) (ihc : TraceSep z cTree)
    (hsep : GlobalCarryRecognizer.SepSeed z sf1 sf2) :
    TraceSep z t := by
  have h' := gen_op5 (K := K) n hb hc
  rw [(gen_ok_unique h h').1]
  refine traceSep_of_children ?_ ?_ ?_
  · constructor
    · intro _
      have hr := genSkelOp5_results s (op5 b c) (.atom 5) (.cell b c) b c sf1 sf2
        (Noun.tis sf1 sf2)
      simpa [skelNode, hr.1, hr.2] using hsep
    · intro hs6
      simp [skelNode, genSkelOp5] at hs6
  · exact wrap_vacuous (by simp [skelNode, genSkelOp5])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihc

theorem traceSep_gen_op6_zero {z : K} {n : ℕ} {s b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (condTree, .atom 0))
    (hc : genComputeSkeleton (K := K) n s c = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op6 b c d) = .ok (t, res))
    (ihb : TraceSep z condTree) (ihc : TraceSep z takenTree)
    (hsep : GlobalCarryRecognizer.SepSeed z c d) :
    TraceSep z t := by
  have h' := gen_op6_zero (K := K) n (d := d) hb hc
  rw [(gen_ok_unique h h').1]
  refine traceSep_of_children ?_ ?_ ?_
  · constructor
    · intro hs5
      simp [skelNode, genSkelOp6] at hs5
    · intro _
      simpa [skelNode, genSkelOp6, skeletonDec, SemanticStrategy.decActive]
        using hsep
  · exact wrap_vacuous (by simp [skelNode, genSkelOp6])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihc

theorem traceSep_gen_op6_one {z : K} {n : ℕ} {s b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (condTree, .atom 1))
    (hd : genComputeSkeleton (K := K) n s d = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op6 b c d) = .ok (t, res))
    (ihb : TraceSep z condTree) (ihd : TraceSep z takenTree)
    (hsep : GlobalCarryRecognizer.SepSeed z c d) :
    TraceSep z t := by
  have h' := gen_op6_one (K := K) n (c := c) hb hd
  rw [(gen_ok_unique h h').1]
  refine traceSep_of_children ?_ ?_ ?_
  · constructor
    · intro hs5
      simp [skelNode, genSkelOp6] at hs5
    · intro _
      simpa [skelNode, genSkelOp6, skeletonDec, SemanticStrategy.decActive]
        using hsep
  · exact wrap_vacuous (by simp [skelNode, genSkelOp6])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihd

theorem traceSep_gen_op7 {z : K} {n : ℕ} {s b c sb result : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n sb c = .ok (cTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op7 b c) = .ok (t, res))
    (ihb : TraceSep z bTree) (ihc : TraceSep z cTree) :
    TraceSep z t := by
  have h' := gen_op7 (K := K) n hb hc
  rw [(gen_ok_unique h h').1]
  refine traceSep_of_children ?_ ?_ ?_
  · exact rowOffdiag_vacuous (by simp [skelNode, genSkelOp7])
      (by simp [skelNode, genSkelOp7])
  · exact wrap_vacuous (by simp [skelNode, genSkelOp7])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihb
    · exact ihc

theorem traceSep_gen_cons {z : K} {n : ℕ}
    {s leftHead leftTail tail lRes rRes : Noun}
    {lTree rTree t : NTree (GenComputeRow K)} {res : Noun}
    (hl : genComputeSkeleton (K := K) n s (.cell leftHead leftTail) =
      .ok (lTree, lRes))
    (hr : genComputeSkeleton (K := K) n s tail = .ok (rTree, rRes))
    (h : genComputeSkeleton (K := K) (n + 1) s
      (.cell (.cell leftHead leftTail) tail) = .ok (t, res))
    (ihl : TraceSep z lTree) (ihr : TraceSep z rTree) :
    TraceSep z t := by
  have h' := gen_cons (K := K) n hl hr
  rw [(gen_ok_unique h h').1]
  refine traceSep_of_children ?_ ?_ ?_
  · exact rowOffdiag_vacuous (by simp [skelNode, genSkelCons])
      (by simp [skelNode, genSkelCons])
  · exact wrap_vacuous (by simp [skelNode, genSkelCons])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihl
    · exact ihr

theorem traceSep_gen_invokeAxis {z : K} {n : ℕ}
    {s core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree t : NTree (GenComputeRow K)} {res : Noun}
    (hcore : genComputeSkeleton (K := K) (n + 2) s (op0 1) =
      .ok (coreTree, core))
    (hslotA : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) (n + 2) core arm =
      .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 3) s (invokeAxis axis) = .ok (t, res))
    (ihc : TraceSep z coreTree) (iha : TraceSep z invokeTree) :
    TraceSep z t := by
  have h' := gen_invokeAxis (K := K) n hcore hslotA harm
  rw [(gen_ok_unique h h').1]
  refine traceSep_of_children ?_ ?_ ?_
  · exact rowOffdiag_vacuous (by simp [skelNode, genSkelOp9])
      (by simp [skelNode, genSkelOp9])
  · exact wrap_vacuous (by simp [skelNode, genSkelOp9])
  · intro ch hch
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihc
    · exact iha

theorem traceSep_gen_slam {z : K} {n : ℕ} {axis : ℕ}
    {s bHead bTail sampleF battery sample arm result : Noun}
    {battTree sampTree invokeTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) (n + 3) s (.cell bHead bTail) =
      .ok (battTree, battery))
    (hs : genComputeSkeleton (K := K) (n + 3) s sampleF =
      .ok (sampTree, sample))
    (hslot : Noun.slot axis (.cell battery sample) = some arm)
    (harm : genComputeSkeleton (K := K) (n + 3) (.cell battery sample) arm =
      .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 5) s
      (slam (.cell bHead bTail) sampleF axis) = .ok (t, res))
    (ihb : TraceSep z battTree) (ihs : TraceSep z sampTree)
    (iha : TraceSep z invokeTree) :
    TraceSep z t := by
  have hpair := gen_cons (K := K) (n + 3) (lTree := battTree) (rTree := sampTree) hb hs
  have hcore := gen_op0 (K := K) (n + 2) (slot_1 (.cell battery sample))
  have hax := gen_invokeAxis (K := K) (n + 1) hcore hslot harm
  have hop := gen_op7 (K := K) (n + 4) hpair hax
  have huniq := gen_ok_unique h (by simpa [slam] using hop)
  rw [huniq.1]
  exact traceSep_gen_op7 (z := z) hpair hax hop
    (traceSep_gen_cons (z := z) hb hs hpair ihb ihs)
    (traceSep_gen_invokeAxis (z := z) hcore hslot harm hax
      (traceSep_gen_op0 (z := z) (slot_1 (.cell battery sample)) hcore) iha)

/-! ## Leaf-count `SepSeed` for the two OP6 pairs -/

theorem slam_addNewSample_leaves :
    (slam (op0 2) addNewSample 2).leaves = 15 := by
  rw [slam_leaves, op0_leaves, addNewSample_leaves]

theorem slam_macNewSample_leaves :
    (slam (op0 2) macNewSample 4).leaves = 27 := by
  rw [slam_leaves, op0_leaves, macNewSample_leaves]

theorem sepSeed_addArm_branches (z : K) (hz : z ≠ 0)
    (hord : ¬ orderOf z ∣ (13 : ℕ)) :
    GlobalCarryRecognizer.SepSeed z (op0 6) (slam (op0 2) addNewSample 2) := by
  refine sepSeed_of_leaves_ne z hz ?_ ?_
  · rw [op0_leaves, slam_addNewSample_leaves]; decide
  · simp [leafGap, op0_leaves, slam_addNewSample_leaves]
    exact hord

theorem sepSeed_macArm_branches (z : K) (hz : z ≠ 0)
    (hord : ¬ orderOf z ∣ (25 : ℕ)) :
    GlobalCarryRecognizer.SepSeed z (op0 6) (slam (op0 2) macNewSample 4) := by
  refine sepSeed_of_leaves_ne z hz ?_ ?_
  · rw [op0_leaves, slam_macNewSample_leaves]; decide
  · simp [leafGap, op0_leaves, slam_macNewSample_leaves]
    exact hord

theorem sepSeed_atom_pair (z : K) {a b : ℕ}
    (ha : a < ringChar K) (hb : b < ringChar K) :
    GlobalCarryRecognizer.SepSeed z (.atom a) (.atom b) := by
  rcases eq_or_ne a b with rfl | hne
  · exact sepSeed_self z _
  · exact sepSeed_atoms_of_bounded z ha hb le_rfl hne

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.P8Census
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

set_option maxHeartbeats 40000000

theorem seedZ_not_dvd_13 : ¬ orderOf seedZ ∣ (13 : ℕ) := by
  rw [seedZ_order]
  exact (by decide : ¬ 2 ^ 32 ∣ 13)

theorem seedZ_not_dvd_25 : ¬ orderOf seedZ ∣ (25 : ℕ) := by
  rw [seedZ_order]
  exact (by decide : ¬ 2 ^ 32 ∣ 25)

theorem sepSeed_addArm_seed :
    GlobalCarryRecognizer.SepSeed seedZ (op0 6) (slam (op0 2) addNewSample 2) :=
  sepSeed_addArm_branches seedZ seedZ_ne_zero seedZ_not_dvd_13

theorem sepSeed_macArm_seed :
    GlobalCarryRecognizer.SepSeed seedZ (op0 6) (slam (op0 2) macNewSample 4) :=
  sepSeed_macArm_branches seedZ seedZ_ne_zero seedZ_not_dvd_25

theorem ringChar_gt_two : (2 : ℕ) < ringChar K := by
  rw [ringChar_K]
  simp only [Field.p]; norm_num

theorem sepSeed_atoms01 :
    GlobalCarryRecognizer.SepSeed seedZ (.atom 0) (.atom 1) :=
  sepSeed_atom_pair seedZ
    (lt_trans (by decide : (0 : ℕ) < 2) ringChar_gt_two)
    (lt_trans (by decide : (1 : ℕ) < 2) ringChar_gt_two)

/-! ## Arm spine (same constructors as `seedOK_*`, no Dyck hyps) -/

theorem traceSep_addArm_done (n : ℕ) (acc m : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (addCore acc m m) addArm =
      .ok (t, acc)) :
    TraceSep seedZ t := by
  have h14 := gen_op0 (K := K) (n + 3) (addCore_slot14 acc m m)
  have h15 := gen_op0 (K := K) (n + 3) (addCore_slot15 acc m m)
  have h5eq := gen_op5 (K := K) (n + 4) h14 h15
  have ih5 := traceSep_gen_op5 (z := seedZ) h14 h15 h5eq
    (traceSep_gen_op0 (z := seedZ) (addCore_slot14 acc m m) h14)
    (traceSep_gen_op0 (z := seedZ) (addCore_slot15 acc m m) h15)
    (sepSeed_self seedZ m)
  rw [tis_self m] at h5eq
  have hthen := gen_op0 (K := K) (n + 4) (addCore_slot6 acc m m)
  have hop6 := gen_op6_zero (K := K) (n + 5)
    (d := slam (op0 2) addNewSample 2) h5eq hthen
  have huniq := gen_ok_unique h (by simpa [addArm] using hop6)
  rw [huniq.1]
  exact traceSep_gen_op6_zero (z := seedZ) h5eq hthen hop6
    (by simpa [tis_self m] using ih5)
    (traceSep_gen_op0 (z := seedZ) (addCore_slot6 acc m m) hthen)
    sepSeed_addArm_seed

theorem traceSep_addNewSample (n acc i m : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 5)
      (addCore (.atom acc) (.atom i) (.atom m)) addNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom (i + 1)) (.atom m)))) :
    TraceSep seedZ t := by
  have h6 := gen_op0 (K := K) (n + 2)
    (addCore_slot6 (.atom acc) (.atom i) (.atom m))
  have h14 := gen_op0 (K := K) (n + 1)
    (addCore_slot14 (.atom acc) (.atom i) (.atom m))
  have h15 := gen_op0 (K := K) (n + 2)
    (addCore_slot15 (.atom acc) (.atom i) (.atom m))
  have hincA := gen_op4 (K := K) (n + 3) h6 (lus_nat acc)
  have hincI := gen_op4 (K := K) (n + 2) h14 (lus_nat i)
  have hinner := gen_cons (K := K) (n + 3) hincI h15
  have houter := gen_cons (K := K) (n + 4) hincA hinner
  have huniq := gen_ok_unique h houter
  rw [huniq.1]
  exact traceSep_gen_cons (z := seedZ) hincA hinner houter
    (traceSep_gen_op4 (z := seedZ) h6 (lus_nat acc) hincA
      (traceSep_gen_op0 (z := seedZ)
        (addCore_slot6 (.atom acc) (.atom i) (.atom m)) h6))
    (traceSep_gen_cons (z := seedZ) hincI h15 hinner
      (traceSep_gen_op4 (z := seedZ) h14 (lus_nat i) hincI
        (traceSep_gen_op0 (z := seedZ)
          (addCore_slot14 (.atom acc) (.atom i) (.atom m)) h14))
      (traceSep_gen_op0 (z := seedZ)
        (addCore_slot15 (.atom acc) (.atom i) (.atom m)) h15))

theorem traceSep_addArm_one (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 16)
      (addCore (.atom acc) (.atom 0) (.atom 1)) addArm =
      .ok (t, .atom (acc + 1))) :
    TraceSep seedZ t := by
  have h14 := gen_op0 (K := K) (n + 13)
    (addCore_slot14 (.atom acc) (.atom 0) (.atom 1))
  have h15 := gen_op0 (K := K) (n + 13)
    (addCore_slot15 (.atom acc) (.atom 0) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 14) h14 h15
  have ihcond := traceSep_gen_op5 (z := seedZ) h14 h15 hcond
    (traceSep_gen_op0 (z := seedZ)
      (addCore_slot14 (.atom acc) (.atom 0) (.atom 1)) h14)
    (traceSep_gen_op0 (z := seedZ)
      (addCore_slot15 (.atom acc) (.atom 0) (.atom 1)) h15)
    sepSeed_atoms01
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_addNewSample (K := K) (n + 8) acc 0 1
  have ihns := traceSep_addNewSample (n + 8) acc 0 1 hns
  have hbatt := gen_op0 (K := K) (n + 12)
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
  obtain ⟨doneTree, hdone⟩ :=
    gen_addArm_done (K := K) (n + 7) (.atom (acc + 1)) (.atom 1)
  have ihdone := traceSep_addArm_done (n + 7) (.atom (acc + 1)) (.atom 1) hdone
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 10) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1)) hdone
  have ihslam := traceSep_gen_slam (z := seedZ) hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1)) hdone hslam
    (traceSep_gen_op0 (z := seedZ)
      (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hbatt)
    ihns ihdone
  have hop6 := gen_op6_one (K := K) (n + 15) (c := op0 6) hcond hslam
  have huniq := gen_ok_unique h (by simpa [addArm, slam, op0] using hop6)
  rw [huniq.1]
  exact traceSep_gen_op6_one (z := seedZ) hcond hslam hop6
    (by simpa [htis] using ihcond) ihslam sepSeed_addArm_seed

theorem traceSep_macArm_done (n : ℕ) (acc k m : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (macCoreAt acc k k m) macArm =
      .ok (t, acc)) :
    TraceSep seedZ t := by
  have h14 := gen_op0 (K := K) (n + 3) (macCoreAt_slot14 acc k k m)
  have h30 := gen_op0 (K := K) (n + 3) (macCoreAt_slot30 acc k k m)
  have h5eq := gen_op5 (K := K) (n + 4) h14 h30
  have ih5 := traceSep_gen_op5 (z := seedZ) h14 h30 h5eq
    (traceSep_gen_op0 (z := seedZ) (macCoreAt_slot14 acc k k m) h14)
    (traceSep_gen_op0 (z := seedZ) (macCoreAt_slot30 acc k k m) h30)
    (sepSeed_self seedZ k)
  rw [tis_self k] at h5eq
  have hthen := gen_op0 (K := K) (n + 4) (macCoreAt_slot6 acc k k m)
  have hop6 := gen_op6_zero (K := K) (n + 5)
    (d := slam (op0 2) macNewSample 4) h5eq hthen
  have huniq := gen_ok_unique h (by simpa [macArm] using hop6)
  rw [huniq.1]
  exact traceSep_gen_op6_zero (z := seedZ) h5eq hthen hop6
    (by simpa [tis_self k] using ih5)
    (traceSep_gen_op0 (z := seedZ) (macCoreAt_slot6 acc k k m) hthen)
    sepSeed_macArm_seed

theorem traceSep_addFromMac_m0 (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 12)
      (macCore (.atom acc) (.atom 1) (.atom 0)) addFromMac = .ok (t, .atom acc)) :
    TraceSep seedZ t := by
  have h5 := gen_op0 (K := K) (n + 9)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hacc := gen_op0 (K := K) (n + 8)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hz := gen_op1 (K := K) (n + 7)
    (macCore (.atom acc) (.atom 1) (.atom 0)) 0
  have hm := gen_op0 (K := K) (n + 7)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinner := gen_cons (K := K) (n + 8) hz hm
  have hsmpl := gen_cons (K := K) (n + 9) hacc hinner
  obtain ⟨doneTree, hdone⟩ := gen_addArm_done (K := K) (n + 4) (.atom acc) (.atom 0)
  have ihdone := traceSep_addArm_done (n + 4) (.atom acc) (.atom 0) hdone
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 7) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 0)) hdone
  have huniq := gen_ok_unique h (by simpa [addFromMac, slam, op0, op1, macCore] using hslam)
  rw [huniq.1]
  exact traceSep_gen_slam (z := seedZ) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 0)) hdone hslam
    (traceSep_gen_op0 (z := seedZ)
      (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h5)
    (traceSep_gen_cons (z := seedZ) hacc hinner hsmpl
      (traceSep_gen_op0 (z := seedZ)
        (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hacc)
      (traceSep_gen_cons (z := seedZ) hz hm hinner
        (traceSep_gen_op1 (z := seedZ) hz)
        (traceSep_gen_op0 (z := seedZ)
          (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hm)))
    ihdone

theorem traceSep_addFromMac_m1 (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 21)
      (macCore (.atom acc) (.atom 1) (.atom 1)) addFromMac =
      .ok (t, .atom (acc + 1))) :
    TraceSep seedZ t := by
  have h5 := gen_op0 (K := K) (n + 18)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have haccS := gen_op0 (K := K) (n + 17)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hz := gen_op1 (K := K) (n + 16)
    (macCore (.atom acc) (.atom 1) (.atom 1)) 0
  have hm := gen_op0 (K := K) (n + 16)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinner := gen_cons (K := K) (n + 17) hz hm
  have hsmpl := gen_cons (K := K) (n + 18) haccS hinner
  obtain ⟨doneTree, hdone⟩ := gen_addArm_one (K := K) (n + 3) acc
  have ihdone := traceSep_addArm_one (n + 3) acc hdone
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hdone
  have huniq := gen_ok_unique h (by simpa [addFromMac, slam, op0, op1, macCore] using hslam)
  rw [huniq.1]
  exact traceSep_gen_slam (z := seedZ) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hdone hslam
    (traceSep_gen_op0 (z := seedZ)
      (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h5)
    (traceSep_gen_cons (z := seedZ) haccS hinner hsmpl
      (traceSep_gen_op0 (z := seedZ)
        (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) haccS)
      (traceSep_gen_cons (z := seedZ) hz hm hinner
        (traceSep_gen_op1 (z := seedZ) hz)
        (traceSep_gen_op0 (z := seedZ)
          (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hm)))
    ihdone

theorem traceSep_macNewSample_m1 (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 23)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom 1) (.cell (.atom 1) (.atom 1))))) :
    TraceSep seedZ t := by
  obtain ⟨addT, hadd⟩ := gen_addFromMac_m1 (K := K) (n + 1) acc
  have ihadd := traceSep_addFromMac_m1 (n + 1) acc hadd
  have h14 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hinc := gen_op4 (K := K) (n + 20) h14 (lus_nat 0)
  have hn := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hm := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hnm := gen_cons (K := K) (n + 20) hn hm
  have hrest := gen_cons (K := K) (n + 21) hinc hnm
  have hadd' :
      genComputeSkeleton (K := K) (n + 22)
        (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 1))
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2))) = .ok (addT, .atom (acc + 1)) := by
    simpa [addFromMac, slam, op7, op0, op1, invokeAxis, macCore] using hadd
  have hcell := gen_cons (K := K) (n + 22) hadd' hrest
  have ihcell := traceSep_gen_cons (z := seedZ) hadd' hrest hcell ihadd
    (traceSep_gen_cons (z := seedZ) hinc hnm hrest
      (traceSep_gen_op4 (z := seedZ) h14 (lus_nat 0) hinc
        (traceSep_gen_op0 (z := seedZ)
          (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h14))
      (traceSep_gen_cons (z := seedZ) hn hm hnm
        (traceSep_gen_op0 (z := seedZ)
          (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hn)
        (traceSep_gen_op0 (z := seedZ)
          (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hm)))
  have hnamed :=
    show genComputeSkeleton (K := K) (n + 23)
        (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample = _ from by
      simpa [macNewSample, addFromMac, slam, op7, op4, op0, op1, invokeAxis,
        macCore] using hcell
  have huniq := gen_ok_unique h hnamed
  rw [huniq.1]
  exact ihcell

theorem traceSep_macNewSample_m0 (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 14)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample =
      .ok (t, .cell (.atom acc) (.cell (.atom 1) (.cell (.atom 1) (.atom 0))))) :
    TraceSep seedZ t := by
  obtain ⟨addT, hadd⟩ := gen_addFromMac_m0 (K := K) (n + 1) acc
  have ihadd := traceSep_addFromMac_m0 (n + 1) acc hadd
  have h14 := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hinc := gen_op4 (K := K) (n + 11) h14 (lus_nat 0)
  have hn := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hm := gen_op0 (K := K) (n + 10)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hnm := gen_cons (K := K) (n + 11) hn hm
  have hrest := gen_cons (K := K) (n + 12) hinc hnm
  have hadd' :
      genComputeSkeleton (K := K) (n + 13)
        (macCoreAt (.atom acc) (.atom 0) (.atom 1) (.atom 0))
        (.cell (.atom 7)
          (.cell (.cell (op0 5)
            (.cell (op0 6) (.cell (op1 0) (op0 31))))
            (invokeAxis 2))) = .ok (addT, .atom acc) := by
    simpa [addFromMac, slam, op7, op0, op1, invokeAxis, macCore] using hadd
  have hcell := gen_cons (K := K) (n + 13) hadd' hrest
  have ihcell := traceSep_gen_cons (z := seedZ) hadd' hrest hcell ihadd
    (traceSep_gen_cons (z := seedZ) hinc hnm hrest
      (traceSep_gen_op4 (z := seedZ) h14 (lus_nat 0) hinc
        (traceSep_gen_op0 (z := seedZ)
          (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h14))
      (traceSep_gen_cons (z := seedZ) hn hm hnm
        (traceSep_gen_op0 (z := seedZ)
          (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hn)
        (traceSep_gen_op0 (z := seedZ)
          (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hm)))
  have hnamed :=
    show genComputeSkeleton (K := K) (n + 14)
        (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample = _ from by
      simpa [macNewSample, addFromMac, slam, op7, op4, op0, op1, invokeAxis,
        macCore] using hcell
  have huniq := gen_ok_unique h hnamed
  rw [huniq.1]
  exact ihcell

theorem traceSep_macArm_zero (n : ℕ) (acc m : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (macCore acc (.atom 0) m) macArm =
      .ok (t, acc)) :
    TraceSep seedZ t :=
  traceSep_macArm_done n acc (.atom 0) m (by simpa [macCore] using h)

theorem traceSep_macArm_one_m0 (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = .ok (t, .atom acc)) :
    TraceSep seedZ t := by
  have h14 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have h30 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hcond := gen_op5 (K := K) (n + 20) h14 h30
  have ihcond := traceSep_gen_op5 (z := seedZ) h14 h30 hcond
    (traceSep_gen_op0 (z := seedZ)
      (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h14)
    (traceSep_gen_op0 (z := seedZ)
      (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h30)
    sepSeed_atoms01
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_macNewSample_m0 (K := K) (n + 5) acc
  have ihns := traceSep_macNewSample_m0 (n + 5) acc hns
  have hbatt := gen_op0 (K := K) (n + 18)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  obtain ⟨doneTree, hdone⟩ :=
    gen_macArm_done (K := K) (n + 13) (.atom acc) (.atom 1) (.atom 0)
  have ihdone := traceSep_macArm_done (n + 13)
    (.atom acc) (.atom 1) (.atom 0) hdone
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16)
    (axis := 4) (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0)) hdone
  have ihslam := traceSep_gen_slam (z := seedZ) hbatt hns
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0)) hdone hslam
    (traceSep_gen_op0 (z := seedZ)
      (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hbatt)
    ihns ihdone
  have hop6 := gen_op6_one (K := K) (n + 21) (c := op0 6) hcond hslam
  have huniq := gen_ok_unique h
    (by simpa [macArm, slam, op0, macNewSample, macCore] using hop6)
  rw [huniq.1]
  exact traceSep_gen_op6_one (z := seedZ) hcond hslam hop6
    (by simpa [htis] using ihcond) ihslam sepSeed_macArm_seed

theorem traceSep_macArm_one_m1 (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      .ok (t, .atom (acc + 1))) :
    TraceSep seedZ t := by
  have h14 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have h30 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 29) h14 h30
  have ihcond := traceSep_gen_op5 (z := seedZ) h14 h30 hcond
    (traceSep_gen_op0 (z := seedZ)
      (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h14)
    (traceSep_gen_op0 (z := seedZ)
      (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h30)
    sepSeed_atoms01
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_macNewSample_m1 (K := K) (n + 5) acc
  have ihns := traceSep_macNewSample_m1 (n + 5) acc hns
  have hbatt := gen_op0 (K := K) (n + 27)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  obtain ⟨doneTree, hdone⟩ :=
    gen_macArm_done (K := K) (n + 22) (.atom (acc + 1)) (.atom 1) (.atom 1)
  have ihdone := traceSep_macArm_done (n + 22)
    (.atom (acc + 1)) (.atom 1) (.atom 1) hdone
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 25)
    (axis := 4) (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) hdone
  have ihslam := traceSep_gen_slam (z := seedZ) hbatt hns
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) hdone hslam
    (traceSep_gen_op0 (z := seedZ)
      (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hbatt)
    ihns ihdone
  have hop6 := gen_op6_one (K := K) (n + 30) (c := op0 6) hcond hslam
  have huniq := gen_ok_unique h
    (by simpa [macArm, slam, op0, macNewSample, macCore] using hop6)
  rw [huniq.1]
  exact traceSep_gen_op6_one (z := seedZ) hcond hslam hop6
    (by simpa [htis] using ihcond) ihslam sepSeed_macArm_seed

theorem traceSep_gen_macSampleF {n : ℕ}
    {s aH aT nH nT mF acc k m : Noun}
    {aTree nTree mTree t : NTree (GenComputeRow K)} {res : Noun}
    (ha : genComputeSkeleton (K := K) (n + 2) s (.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n s (.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n s mF = .ok (mTree, m))
    (h : genComputeSkeleton (K := K) (n + 3) s
      (.cell (.cell aH aT) (.cell (op1 0) (.cell (.cell nH nT) mF))) =
      .ok (t, res))
    (iha : TraceSep seedZ aTree) (ihn : TraceSep seedZ nTree)
    (ihm : TraceSep seedZ mTree) :
    TraceSep seedZ t := by
  have hnm := gen_cons (K := K) n hn hm
  have hz := gen_op1 (K := K) n s 0
  have hinner := gen_cons (K := K) (n + 1) hz hnm
  have houter := gen_cons (K := K) (n + 2) ha hinner
  have huniq := gen_ok_unique h houter
  rw [huniq.1]
  exact traceSep_gen_cons (z := seedZ) ha hinner houter iha
    (traceSep_gen_cons (z := seedZ) hz hnm hinner (traceSep_gen_op1 (z := seedZ) hz)
      (traceSep_gen_cons (z := seedZ) hn hm hnm ihn ihm))

theorem traceSep_gen_invokeMac {n : ℕ}
    {s aH aT nH nT mF acc k m result : Noun}
    {aTree nTree mTree armTree t : NTree (GenComputeRow K)} {res : Noun}
    (ha : genComputeSkeleton (K := K) (n + 2) s (.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n s (.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n s mF = .ok (mTree, m))
    (harm : genComputeSkeleton (K := K) (n + 3) (macCore acc k m) macArm =
      .ok (armTree, result))
    (h : genComputeSkeleton (K := K) (n + 5) s
      (invokeMac (.cell aH aT) (.cell nH nT) mF) = .ok (t, res))
    (iha : TraceSep seedZ aTree) (ihn : TraceSep seedZ nTree)
    (ihm : TraceSep seedZ mTree) (ihaArm : TraceSep seedZ armTree) :
    TraceSep seedZ t := by
  have hqB := gen_quote (K := K) (n + 2) s mmBattery
  obtain ⟨sfTree, hsf⟩ := gen_macSampleF (K := K) n ha hn hm
  have ihsf := traceSep_gen_macSampleF ha hn hm hsf iha ihn ihm
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) n (axis := 4)
    (bHead := .atom 1) (bTail := mmBattery) hqB hsf
    (macCoreAt_slot4 acc (.atom 0) k m) harm
  have huniq := gen_ok_unique h
    (by simpa [invokeMac, slam, quote, macCore, macCoreAt] using hslam)
  rw [huniq.1]
  exact traceSep_gen_slam (z := seedZ) hqB hsf
    (macCoreAt_slot4 acc (.atom 0) k m) harm hslam
    (traceSep_gen_quote (z := seedZ) hqB) ihsf ihaArm

theorem traceSep_mmC00 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC00 =
      .ok (t, .atom 2)) :
    TraceSep seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA⟩ := gen_macArm_one_m1 (K := K) (n + 20) 0
  have ihInnerArm := traceSep_macArm_one_m1 (n + 20) 0 innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 12) ha0 a00 b00 innerA
  have ihInner := traceSep_gen_invokeMac ha0 a00 b00 innerA hinner
    (traceSep_gen_op1 (z := seedZ) ha0)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot8 a00)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot12 b00)
    ihInnerArm
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 1
  have ihOuterArm := traceSep_macArm_one_m1 (n + 23) 1 outerA
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 14)
    hinner' a01 b10 outerA
  have hh := h
  simp only [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact traceSep_gen_invokeMac hinner' a01 b10 outerA houter
    ihInner
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot9 a01)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot14 b10)
    ihOuterArm

theorem traceSep_mmC01 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC01 =
      .ok (t, .atom 1)) :
    TraceSep seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA⟩ := gen_macArm_one_m0 (K := K) (n + 29) 0
  have ihInnerArm := traceSep_macArm_one_m0 (n + 29) 0 innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 13) ha0 a00 b01 innerA
  have ihInner := traceSep_gen_invokeMac ha0 a00 b01 innerA hinner
    (traceSep_gen_op1 (z := seedZ) ha0)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot8 a00)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot13 b01)
    ihInnerArm
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := traceSep_macArm_one_m1 (n + 23) 0 outerA
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 15)
    hinner' a01 b11 outerA
  have hh := h
  simp only [mmC01, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact traceSep_gen_invokeMac hinner' a01 b11 outerA houter
    ihInner
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot9 a01)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot15 b11)
    ihOuterArm

theorem traceSep_mmC10 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC10 =
      .ok (t, .atom 1)) :
    TraceSep seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA⟩ := gen_macArm_zero (K := K) (n + 45) (.atom 0) (.atom 1)
  have ihInnerArm := traceSep_macArm_zero (n + 45) (.atom 0) (.atom 1) innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 12) ha0 a10 b00 innerA
  have ihInner := traceSep_gen_invokeMac ha0 a10 b00 innerA hinner
    (traceSep_gen_op1 (z := seedZ) ha0)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot10 a10)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot12 b00)
    ihInnerArm
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := traceSep_macArm_one_m1 (n + 23) 0 outerA
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 14)
    hinner' a11 b10 outerA
  have hh := h
  simp only [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact traceSep_gen_invokeMac hinner' a11 b10 outerA houter
    ihInner
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot11 a11)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot14 b10)
    ihOuterArm

theorem traceSep_mmC11 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC11 =
      .ok (t, .atom 1)) :
    TraceSep seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA⟩ := gen_macArm_zero (K := K) (n + 45) (.atom 0) (.atom 0)
  have ihInnerArm := traceSep_macArm_zero (n + 45) (.atom 0) (.atom 0) innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 13) ha0 a10 b01 innerA
  have ihInner := traceSep_gen_invokeMac ha0 a10 b01 innerA hinner
    (traceSep_gen_op1 (z := seedZ) ha0)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot10 a10)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot13 b01)
    ihInnerArm
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := traceSep_macArm_one_m1 (n + 23) 0 outerA
  have hinner' := hinner
  simp only [invokeMac, slam, op7, quote, op1] at hinner'
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 15)
    hinner' a11 b11 outerA
  have hh := h
  simp only [mmC11, mac2, invokeMac, slam, op7, quote, op1, op0] at hh
  have huniq := gen_ok_unique hh houter
  rw [huniq.1]
  exact traceSep_gen_invokeMac hinner' a11 b11 outerA houter
    ihInner
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot11 a11)
    (traceSep_gen_op0 (z := seedZ) mmSubject_slot15 b11)
    ihOuterArm

theorem traceSep_mm {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) 64 mmSubject mmFormula = .ok (t, mmC)) :
    TraceSep seedZ t := by
  obtain ⟨t00, h00⟩ := gen_mmC00 (K := K) 6
  obtain ⟨t01, h01⟩ := gen_mmC01 (K := K) 6
  obtain ⟨t10, h10⟩ := gen_mmC10 (K := K) 6
  obtain ⟨t11, h11⟩ := gen_mmC11 (K := K) 6
  have ih00 := traceSep_mmC00 6 h00
  have ih01 := traceSep_mmC01 6 h01
  have ih10 := traceSep_mmC10 6 h10
  have ih11 := traceSep_mmC11 6 h11
  have h00c := h00
  simp only [mmC00, mac2, invokeMac, slam, op7, quote, op1] at h00c
  have h01c := h01
  simp only [mmC01, mac2, invokeMac, slam, op7, quote, op1] at h01c
  have h10c := h10
  simp only [mmC10, mac2, invokeMac, slam, op7, quote, op1] at h10c
  have h11c := h11
  simp only [mmC11, mac2, invokeMac, slam, op7, quote, op1] at h11c
  have hL := gen_cons (K := K) 62 h00c h01c
  have hR := gen_cons (K := K) 62 h10c h11c
  have hop := gen_cons (K := K) 63 hL hR
  have hh := h
  simp only [mmFormula, mmC00, mmC01, mmC10, mmC11, mac2, invokeMac, slam, op7,
    quote, op1, op0] at hh
  have huniq := gen_ok_unique hh hop
  rw [huniq.1]
  exact traceSep_gen_cons (z := seedZ) hL hR hop
    (traceSep_gen_cons (z := seedZ) h00c h01c hL ih00 ih01)
    (traceSep_gen_cons (z := seedZ) h10c h11c hR ih10 ih11)

theorem mmTree_traceSep : TraceSep seedZ (mmTree (K := K)) :=
  traceSep_mm (mmTree_gen (K := K))

/-! ## Transport to AIR `bfsRows` and `mm_hbad` -/

theorem mm_hoff5 :
    ∀ g ∈ bfsRows (airReorder (mmTree (K := K))),
      g.skel.state = .s5 →
        GlobalCarryRecognizer.SepSeed seedZ
          (skeletonSubformula g.skel 0 TripleSlot.result)
          (skeletonSubformula g.skel 1 TripleSlot.result) := by
  refine (forall_bfsRows_iff (airReorder (mmTree (K := K)))).mpr ?_
  intro u hu hs5
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label (mmTree (K := K)) u hu
  have hrow := mmTree_traceSep.1 u0 hu0
  simpa [hl] using hrow.1 (by simpa [hl] using hs5)

theorem mm_hoff6 :
    ∀ g ∈ bfsRows (airReorder (mmTree (K := K))),
      g.skel.state = .s6 →
        GlobalCarryRecognizer.SepSeed seedZ
          (skeletonDec g.skel .f_tth) (skeletonDec g.skel .f_ttt) := by
  refine (forall_bfsRows_iff (airReorder (mmTree (K := K)))).mpr ?_
  intro u hu hs6
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label (mmTree (K := K)) u hu
  have hrow := mmTree_traceSep.1 u0 hu0
  simpa [hl] using hrow.2 (by simpa [hl] using hs6)

theorem mm_hwrap :
    ∀ g ∈ bfsRows (airReorder (mmTree (K := K))),
      g.skel.state = .s4 →
        OpcodeSemantics.incMod (ringChar K)
          (skeletonSubformula g.skel 0 TripleSlot.result)
          = g.skel.evaluation := by
  refine (forall_bfsRows_iff (airReorder (mmTree (K := K)))).mpr ?_
  intro u hu hs4
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label (mmTree (K := K)) u hu
  have hlus : Noun.lus (skeletonSubformula u.label.skel 0 TripleSlot.result)
      = some u.label.skel.evaluation := by
    have h := mmTree_traceSep.2 u0 hu0 (by simpa [hl] using hs4)
    simpa [hl] using h
  have hbnd : u.label.skel.BoundedBy 65537 := by
    have h := mmTreeAir_inTree_bounded (K := K) u hu
    exact h.1
  have hr : FieldEmbedding.BoundedBy 65537 u.label.skel.evaluation := hbnd.2.2.1
  have hle : (65537 : ℕ) ≤ ringChar K := by
    rw [ringChar_K]
    simp only [Field.p]; norm_num
  exact incMod_eq_of_lus hlus hr hle

variable [Fintype K] [DecidableEq K]

theorem mm_hbad (hΛ : 1 ≤ (568 : ℕ)) :
    seedZ ∉ (genSkeletonP8Census (K := K) hΛ
      (mmTree_gen (K := K)) mm_traceConfined
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ)
        (mmTree (K := K)))).census.badSeeds :=
  notMem_badSeeds_of_offdiag_sep (mmTree_gen (K := K)) hΛ
    mm_traceConfined _ mm_hwrap seedZ mm_hoff5 mm_hoff6

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks

#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.mm_hbad
#print axioms Nock.NockVMROM.Thm54.TraceGen.sepSeed_of_leaves_ne
#print axioms Nock.NockVMROM.Thm54.TraceGen.generated_comparisons_self_or_offdiag
#print axioms Nock.NockVMROM.Thm54.TraceGen.notMem_badSeeds_of_offdiag_sep


