/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulSize.lean

  Exact compute-tree node count for the generated 2×2 matmul program.
  The four fused-MAC branches plus three autocons wrappers total 401
  nodes (`mmTree_size`), independent of the table field.  Used by the
  `ExactConfig` orbit-prefix (`compRows = 401 ≤ 2^16`).

  Memory-forest counts live in `GenMatmulConfig`: they need the assigned
  request nouns, not just compute fan-out.

  `Gen.lean` is not edited.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmul
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonFanout
import Nock.NockVMROM.Thm54.TraceGen.GenTierASize
import Nock.NockVMROM.Thm54.TraceGen.GenTierAData
import Nock.NockVMROM.Thm54.ExactTraversal

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open ComputeTable

variable {K : Type} [Field K]

/-! ## Relabeling preserves size (`mapNTree_size` is in `GenTierASize`) -/

theorem renderRows_size (z α : K) (t : NTree (GenComputeRow K)) :
    (renderRows z α t).size = t.size := by
  rw [renderRows_eq_mapNTree, mapNTree_size]

theorem bfsAssign_size (t : NTree (GenComputeRow K)) :
    (bfsAssign t).size = t.size := by
  have hlen : (bfsForest [bfsAssign t]).length = (bfsForest [t]).length := by
    rw [bfsForest_bfsAssign, List.length_map, List.length_range']
  have hL : (bfsForest [bfsAssign t]).length = (bfsAssign t).size := by
    simp [bfsForest_length, totalSize]
  have hR : (bfsForest [t]).length = t.size := by
    simp [bfsForest_length, totalSize]
  omega

/-! ## Unique tree of a successful `genComputeSkeleton` -/

theorem gen_ok_unique {fuel : ℕ} {s f : Noun}
    {t t' : NTree (GenComputeRow K)} {r r' : Noun}
    (h : genComputeSkeleton (K := K) fuel s f = .ok (t, r))
    (h' : genComputeSkeleton (K := K) fuel s f = .ok (t', r')) :
    t = t' ∧ r = r' := by
  rw [h] at h'
  injection h' with hp
  exact Prod.mk.inj hp

theorem gen_ok_size {fuel : ℕ} {s f : Noun}
    {t t' : NTree (GenComputeRow K)} {r r' : Noun} {n : ℕ}
    (h : genComputeSkeleton (K := K) fuel s f = .ok (t, r))
    (h' : genComputeSkeleton (K := K) fuel s f = .ok (t', r'))
    (hsz : t'.size = n) :
    t.size = n := by
  rw [(gen_ok_unique h h').1, hsz]

theorem size_node_nil {α} (l : α) : (NTree.node l []).size = 1 := by
  simp [NTree.size]

theorem size_node_one {α} (l : α) (t : NTree α) :
    (NTree.node l [t]).size = 1 + t.size := by
  simp [NTree.size]

theorem size_node_two {α} (l : α) (a b : NTree α) :
    (NTree.node l [a, b]).size = 1 + a.size + b.size := by
  simp [NTree.size]
  omega

/-! ## Size of the named constructors -/

theorem gen_op1_size (n : ℕ) (subject : Noun) (k : ℕ)
    {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) subject (op1 k) = .ok (t, r)) :
    t.size = 1 :=
  gen_ok_size h (gen_op1 (K := K) n subject k) (size_node_nil _)

theorem gen_quote_size (n : ℕ) (subject result : Noun)
    {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) subject (quote result) = .ok (t, r)) :
    t.size = 1 :=
  gen_ok_size h (gen_quote (K := K) n subject result) (size_node_nil _)

theorem gen_op0_size (n : ℕ) {subject : Noun} {axis : ℕ} {result : Noun}
    (hs : Noun.slot axis subject = some result)
    {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) subject (op0 axis) = .ok (t, r)) :
    t.size = 1 :=
  gen_ok_size h (gen_op0 (K := K) n hs) (size_node_nil _)

theorem gen_op4_size (n : ℕ) {subject tail callResult result : Noun}
    {callTree t : NTree (GenComputeRow K)} {r : Noun}
    (hc : genComputeSkeleton (K := K) n subject tail = .ok (callTree, callResult))
    (hinc : Noun.lus callResult = some result)
    (h : genComputeSkeleton (K := K) (n + 1) subject (op4 tail) = .ok (t, r)) :
    t.size = 1 + callTree.size :=
  gen_ok_size h (gen_op4 (K := K) n hc hinc) (size_node_one _ _)

theorem gen_op5_size (n : ℕ) {subject b c sf1 sf2 : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n subject c = .ok (cTree, sf2))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op5 b c) = .ok (t, r)) :
    t.size = 1 + bTree.size + cTree.size :=
  gen_ok_size h (gen_op5 (K := K) n hb hc) (size_node_two _ _ _)

theorem gen_op6_zero_size (n : ℕ) {subject b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (condTree, .atom 0))
    (hc : genComputeSkeleton (K := K) n subject c = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op6 b c d) = .ok (t, r)) :
    t.size = 1 + condTree.size + takenTree.size :=
  gen_ok_size h (gen_op6_zero (K := K) n hb hc) (size_node_two _ _ _)

theorem gen_op6_one_size (n : ℕ) {subject b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (condTree, .atom 1))
    (hd : genComputeSkeleton (K := K) n subject d = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op6 b c d) = .ok (t, r)) :
    t.size = 1 + condTree.size + takenTree.size :=
  gen_ok_size h (gen_op6_one (K := K) n hb hd) (size_node_two _ _ _)

theorem gen_op7_size (n : ℕ) {subject b c sb result : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) n subject b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n sb c = .ok (cTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject (op7 b c) = .ok (t, r)) :
    t.size = 1 + bTree.size + cTree.size :=
  gen_ok_size h (gen_op7 (K := K) n hb hc) (size_node_two _ _ _)

theorem gen_op9_size (n : ℕ) {subject c core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree t : NTree (GenComputeRow K)} {r : Noun}
    (hc : genComputeSkeleton (K := K) n subject c = .ok (coreTree, core))
    (hslot : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) n core arm = .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) subject
      (.cell (.atom 9) (.cell (.atom axis) c)) = .ok (t, r)) :
    t.size = 1 + coreTree.size + invokeTree.size :=
  gen_ok_size h (gen_op9 (K := K) n hc hslot harm) (size_node_two _ _ _)

theorem gen_cons_size (n : ℕ)
    {subject leftHead leftTail tail lRes rRes : Noun}
    {lTree rTree t : NTree (GenComputeRow K)} {r : Noun}
    (hl : genComputeSkeleton (K := K) n subject (.cell leftHead leftTail) =
      .ok (lTree, lRes))
    (hr : genComputeSkeleton (K := K) n subject tail = .ok (rTree, rRes))
    (h : genComputeSkeleton (K := K) (n + 1) subject
      (.cell (.cell leftHead leftTail) tail) = .ok (t, r)) :
    t.size = 1 + lTree.size + rTree.size :=
  gen_ok_size h (gen_cons (K := K) n hl hr) (size_node_two _ _ _)

theorem gen_invokeAxis_size (n : ℕ) {subject core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree t : NTree (GenComputeRow K)} {r : Noun}
    (hcore : genComputeSkeleton (K := K) (n + 2) subject (op0 1) =
      .ok (coreTree, core))
    (hslotA : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) (n + 2) core arm = .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 3) subject (invokeAxis axis) = .ok (t, r)) :
    t.size = 1 + coreTree.size + invokeTree.size :=
  gen_ok_size h (gen_invokeAxis (K := K) n hcore hslotA harm) (size_node_two _ _ _)

theorem gen_slam_size (n : ℕ) {axis : ℕ}
    {subject bHead bTail sampleF battery sample arm result : Noun}
    {battTree sampTree invokeTree t : NTree (GenComputeRow K)} {r : Noun}
    (hb : genComputeSkeleton (K := K) (n + 3) subject (.cell bHead bTail) =
      .ok (battTree, battery))
    (hs : genComputeSkeleton (K := K) (n + 3) subject sampleF =
      .ok (sampTree, sample))
    (hslot : Noun.slot axis (.cell battery sample) = some arm)
    (harm : genComputeSkeleton (K := K) (n + 3) (.cell battery sample) arm =
      .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 5) subject
        (slam (.cell bHead bTail) sampleF axis) = .ok (t, r)) :
    t.size = 4 + battTree.size + sampTree.size + invokeTree.size := by
  have hpair :=
    gen_cons (K := K) (n + 3) (lTree := battTree) (rTree := sampTree) hb hs
  have hcore :=
    gen_op0 (K := K) (n + 2) (slot_1 (.cell battery sample))
  have hax := gen_invokeAxis (K := K) (n + 1) hcore hslot harm
  simp only [slam] at h
  have h7 := gen_op7_size (K := K) (n + 4) hpair hax h
  have hp := gen_cons_size (K := K) (n + 3) hb hs hpair
  have hx := gen_invokeAxis_size (K := K) (n + 1) hcore hslot harm hax
  have hc0 := gen_op0_size (K := K) (n + 2) (slot_1 (.cell battery sample)) hcore
  omega

/-! ## Add-arm and MAC-arm sizes -/

theorem gen_addArm_done_size (n : ℕ) (acc m : Noun) :
    ∃ t, genComputeSkeleton (K := K) (n + 6) (addCore acc m m) addArm =
      .ok (t, acc) ∧ t.size = 5 := by
  have h14 := gen_op0 (K := K) (n + 3) (addCore_slot14 acc m m)
  have h15 := gen_op0 (K := K) (n + 3) (addCore_slot15 acc m m)
  have hcond := gen_op5 (K := K) (n + 4) h14 h15
  rw [tis_self m] at hcond
  have hthen := gen_op0 (K := K) (n + 4) (addCore_slot6 acc m m)
  have hop := gen_op6_zero (K := K) (n + 5)
    (d := slam (op0 2) addNewSample 2) hcond hthen
  refine ⟨_, by simpa [addArm] using hop, ?_⟩
  have h6 := gen_op6_zero_size (K := K) (n + 5) hcond hthen
    (by simpa [addArm] using hop)
  have hc := gen_op5_size (K := K) (n + 4) h14 h15 hcond
  have hs14 := gen_op0_size (K := K) (n + 3) (addCore_slot14 acc m m) h14
  have hs15 := gen_op0_size (K := K) (n + 3) (addCore_slot15 acc m m) h15
  have hs6 := gen_op0_size (K := K) (n + 4) (addCore_slot6 acc m m) hthen
  omega

theorem gen_addNewSample_size (n acc i m : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 5)
      (addCore (.atom acc) (.atom i) (.atom m)) addNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom (i + 1)) (.atom m))) ∧
      t.size = 7 := by
  have h6 := gen_op0 (K := K) (n + 2) (addCore_slot6 (.atom acc) (.atom i) (.atom m))
  have h14 := gen_op0 (K := K) (n + 1) (addCore_slot14 (.atom acc) (.atom i) (.atom m))
  have h15 := gen_op0 (K := K) (n + 2) (addCore_slot15 (.atom acc) (.atom i) (.atom m))
  have hincA := gen_op4 (K := K) (n + 3) h6 (lus_nat acc)
  have hincI := gen_op4 (K := K) (n + 2) h14 (lus_nat i)
  have hinner := gen_cons (K := K) (n + 3) hincI h15
  have houter := gen_cons (K := K) (n + 4) hincA hinner
  refine ⟨_, houter, ?_⟩
  have ho := gen_cons_size (K := K) (n + 4) hincA hinner houter
  have hi := gen_cons_size (K := K) (n + 3) hincI h15 hinner
  have hA := gen_op4_size (K := K) (n + 3) h6 (lus_nat acc) hincA
  have hI := gen_op4_size (K := K) (n + 2) h14 (lus_nat i) hincI
  have hs6 := gen_op0_size (K := K) (n + 2)
    (addCore_slot6 (.atom acc) (.atom i) (.atom m)) h6
  have hs14 := gen_op0_size (K := K) (n + 1)
    (addCore_slot14 (.atom acc) (.atom i) (.atom m)) h14
  have hs15 := gen_op0_size (K := K) (n + 2)
    (addCore_slot15 (.atom acc) (.atom i) (.atom m)) h15
  omega

theorem gen_addArm_one_size (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 16)
      (addCore (.atom acc) (.atom 0) (.atom 1)) addArm =
      .ok (t, .atom (acc + 1)) ∧ t.size = 21 := by
  have h14 := gen_op0 (K := K) (n + 13)
    (addCore_slot14 (.atom acc) (.atom 0) (.atom 1))
  have h15 := gen_op0 (K := K) (n + 13)
    (addCore_slot15 (.atom acc) (.atom 0) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 14) h14 h15
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns, hns_sz⟩ := gen_addNewSample_size (K := K) (n + 8) acc 0 1
  have hbatt := gen_op0 (K := K) (n + 12)
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
  obtain ⟨doneTree, hdone, hdone_sz⟩ :=
    gen_addArm_done_size (K := K) (n + 7) (.atom (acc + 1)) (.atom 1)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 10) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1)) hdone
  have hop6 := gen_op6_one (K := K) (n + 15) (c := op0 6) hcond hslam
  refine ⟨_, by simpa [addArm, slam, op0] using hop6, ?_⟩
  have h6 := gen_op6_one_size (K := K) (n + 15) hcond hslam
    (by simpa [addArm, slam, op0] using hop6)
  have hc := gen_op5_size (K := K) (n + 14) h14 h15 hcond
  have hs14 := gen_op0_size (K := K) (n + 13)
    (addCore_slot14 (.atom acc) (.atom 0) (.atom 1)) h14
  have hs15 := gen_op0_size (K := K) (n + 13)
    (addCore_slot15 (.atom acc) (.atom 0) (.atom 1)) h15
  have hss := gen_slam_size (K := K) (n + 10) hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1)) hdone hslam
  have hbatt_sz := gen_op0_size (K := K) (n + 12)
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hbatt
  omega

theorem gen_macArm_done_size (n : ℕ) (acc k m : Noun) :
    ∃ t, genComputeSkeleton (K := K) (n + 6) (macCoreAt acc k k m) macArm =
      .ok (t, acc) ∧ t.size = 5 := by
  have h14 := gen_op0 (K := K) (n + 3) (macCoreAt_slot14 acc k k m)
  have h30 := gen_op0 (K := K) (n + 3) (macCoreAt_slot30 acc k k m)
  have hcond := gen_op5 (K := K) (n + 4) h14 h30
  rw [tis_self k] at hcond
  have hthen := gen_op0 (K := K) (n + 4) (macCoreAt_slot6 acc k k m)
  have hop := gen_op6_zero (K := K) (n + 5)
    (d := slam (op0 2) macNewSample 4) hcond hthen
  refine ⟨_, by simpa [macArm] using hop, ?_⟩
  have h6 := gen_op6_zero_size (K := K) (n + 5) hcond hthen
    (by simpa [macArm] using hop)
  have hc := gen_op5_size (K := K) (n + 4) h14 h30 hcond
  have hs14 := gen_op0_size (K := K) (n + 3) (macCoreAt_slot14 acc k k m) h14
  have hs30 := gen_op0_size (K := K) (n + 3) (macCoreAt_slot30 acc k k m) h30
  have hs6 := gen_op0_size (K := K) (n + 4) (macCoreAt_slot6 acc k k m) hthen
  omega

theorem gen_macArm_zero_size (n : ℕ) (acc m : Noun) :
    ∃ t, genComputeSkeleton (K := K) (n + 6) (macCore acc (.atom 0) m) macArm =
      .ok (t, acc) ∧ t.size = 5 :=
  gen_macArm_done_size n acc (.atom 0) m

theorem gen_macSampleF_size (n : ℕ)
    {subject aH aT nH nT mF acc k m : Noun}
    {aTree nTree mTree t : NTree (GenComputeRow K)} {r : Noun}
    (ha : genComputeSkeleton (K := K) (n + 2) subject (.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n subject (.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n subject mF = .ok (mTree, m))
    (h : genComputeSkeleton (K := K) (n + 3) subject
      (.cell (.cell aH aT) (.cell (op1 0) (.cell (.cell nH nT) mF))) = .ok (t, r)) :
    t.size = 4 + aTree.size + nTree.size + mTree.size := by
  have hnm := gen_cons (K := K) n hn hm
  have hz := gen_op1 (K := K) n subject 0
  have hinner := gen_cons (K := K) (n + 1) hz hnm
  have ho := gen_cons_size (K := K) (n + 2) ha hinner h
  have hi := gen_cons_size (K := K) (n + 1) hz hnm hinner
  have hnm_sz := gen_cons_size (K := K) n hn hm hnm
  have hz_sz := gen_op1_size (K := K) n subject 0 hz
  omega

theorem gen_invokeMac_size (n : ℕ)
    {subject aH aT nH nT mF acc k m result : Noun}
    {aTree nTree mTree armTree t : NTree (GenComputeRow K)} {r : Noun}
    (ha : genComputeSkeleton (K := K) (n + 2) subject (.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n subject (.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n subject mF = .ok (mTree, m))
    (harm : genComputeSkeleton (K := K) (n + 3) (macCore acc k m) macArm =
      .ok (armTree, result))
    (h : genComputeSkeleton (K := K) (n + 5) subject
        (invokeMac (.cell aH aT) (.cell nH nT) mF) = .ok (t, r)) :
    t.size = 9 + aTree.size + nTree.size + mTree.size + armTree.size := by
  have hqB := gen_quote (K := K) (n + 2) subject mmBattery
  obtain ⟨sfTree, hsf⟩ := gen_macSampleF (K := K) n ha hn hm
  simp only [invokeMac, slam, quote] at h
  have hss := gen_slam_size (K := K) n hqB hsf
    (macCoreAt_slot4 acc (.atom 0) k m) harm h
  have hq_sz := gen_quote_size (K := K) (n + 2) subject mmBattery hqB
  have hsf_sz := gen_macSampleF_size (K := K) n ha hn hm hsf
  omega

theorem gen_addFromMac_m0_size (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 12)
      (macCore (.atom acc) (.atom 1) (.atom 0)) addFromMac = .ok (t, .atom acc) ∧
      t.size = 15 := by
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
  obtain ⟨doneTree, hdone, hdone_sz⟩ :=
    gen_addArm_done_size (K := K) (n + 4) (.atom acc) (.atom 0)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 7) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 0)) hdone
  refine ⟨_, by simpa [addFromMac, slam, op0, op1, macCore] using hslam, ?_⟩
  have hss := gen_slam_size (K := K) (n + 7) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 0)) hdone
    (by simpa [addFromMac, slam, op0, op1, macCore] using hslam)
  have hs5 := gen_op0_size (K := K) (n + 9)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h5
  have hsmpl_sz := gen_cons_size (K := K) (n + 9) hacc hinner hsmpl
  have hinner_sz := gen_cons_size (K := K) (n + 8) hz hm hinner
  have hsacc := gen_op0_size (K := K) (n + 8)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hacc
  have hsz := gen_op1_size (K := K) (n + 7)
    (macCore (.atom acc) (.atom 1) (.atom 0)) 0 hz
  have hsm := gen_op0_size (K := K) (n + 7)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hm
  omega

theorem gen_addFromMac_m1_size (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 21)
      (macCore (.atom acc) (.atom 1) (.atom 1)) addFromMac =
      .ok (t, .atom (acc + 1)) ∧ t.size = 31 := by
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
  obtain ⟨doneTree, hdone, hdone_sz⟩ := gen_addArm_one_size (K := K) (n + 3) acc
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hdone
  refine ⟨_, by simpa [addFromMac, slam, op0, op1, macCore] using hslam, ?_⟩
  have hss := gen_slam_size (K := K) (n + 16) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hdone
    (by simpa [addFromMac, slam, op0, op1, macCore] using hslam)
  have hs5 := gen_op0_size (K := K) (n + 18)
    (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h5
  have hsmpl_sz := gen_cons_size (K := K) (n + 18) haccS hinner hsmpl
  have hinner_sz := gen_cons_size (K := K) (n + 17) hz hm hinner
  have hsacc := gen_op0_size (K := K) (n + 17)
    (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) haccS
  have hsz := gen_op1_size (K := K) (n + 16)
    (macCore (.atom acc) (.atom 1) (.atom 1)) 0 hz
  have hsm := gen_op0_size (K := K) (n + 16)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hm
  omega

theorem gen_macNewSample_m0_size (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 14)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample =
      .ok (t, .cell (.atom acc) (.cell (.atom 1) (.cell (.atom 1) (.atom 0)))) ∧
      t.size = 22 := by
  obtain ⟨addT, hadd, hadd_sz⟩ := gen_addFromMac_m0_size (K := K) (n + 1) acc
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
  obtain ⟨t, ht⟩ := gen_macNewSample_m0 (K := K) n acc
  refine ⟨t, ht, ?_⟩
  simp only [macNewSample, macCore, addFromMac, slam, op7, op0, op1, invokeAxis] at ht
  refine gen_ok_size (n := 22) ht hcell ?_
  have ho := gen_cons_size (K := K) (n + 13) hadd' hrest hcell
  have hr := gen_cons_size (K := K) (n + 12) hinc hnm hrest
  have hnm_sz := gen_cons_size (K := K) (n + 11) hn hm hnm
  have hinc_sz := gen_op4_size (K := K) (n + 11) h14 (lus_nat 0) hinc
  have hs14 := gen_op0_size (K := K) (n + 10)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h14
  have hsn := gen_op0_size (K := K) (n + 10)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hn
  have hsm := gen_op0_size (K := K) (n + 10)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hm
  omega

theorem gen_macArm_one_m0_size (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = .ok (t, .atom acc) ∧
      t.size = 36 := by
  have h14 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have h30 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hcond := gen_op5 (K := K) (n + 20) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns, hns_sz⟩ := gen_macNewSample_m0_size (K := K) (n + 5) acc
  have hbatt := gen_op0 (K := K) (n + 18)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  obtain ⟨doneTree, hdone, hdone_sz⟩ :=
    gen_macArm_done_size (K := K) (n + 13) (.atom acc) (.atom 1) (.atom 0)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16) (axis := 4)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0)) hdone
  have hop6 := gen_op6_one (K := K) (n + 21) (c := op0 6) hcond hslam
  refine ⟨_, by simpa [macArm, slam, op0, macNewSample, macCore] using hop6, ?_⟩
  have h6 := gen_op6_one_size (K := K) (n + 21) hcond hslam
    (by simpa [macArm, slam, op0, macNewSample, macCore] using hop6)
  have hc := gen_op5_size (K := K) (n + 20) h14 h30 hcond
  have hs14 := gen_op0_size (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h14
  have hs30 := gen_op0_size (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h30
  have hss := gen_slam_size (K := K) (n + 16) hbatt hns
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0)) hdone hslam
  have hbatt_sz := gen_op0_size (K := K) (n + 18)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hbatt
  omega

theorem gen_macNewSample_m1_size (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 23)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom 1) (.cell (.atom 1) (.atom 1)))) ∧
      t.size = 38 := by
  obtain ⟨addT, hadd, hadd_sz⟩ := gen_addFromMac_m1_size (K := K) (n + 1) acc
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
  obtain ⟨t, ht⟩ := gen_macNewSample_m1 (K := K) n acc
  refine ⟨t, ht, ?_⟩
  simp only [macNewSample, macCore, addFromMac, slam, op7, op0, op1, invokeAxis] at ht
  refine gen_ok_size (n := 38) ht hcell ?_
  have ho := gen_cons_size (K := K) (n + 22) hadd' hrest hcell
  have hr := gen_cons_size (K := K) (n + 21) hinc hnm hrest
  have hnm_sz := gen_cons_size (K := K) (n + 20) hn hm hnm
  have hinc_sz := gen_op4_size (K := K) (n + 20) h14 (lus_nat 0) hinc
  have hs14 := gen_op0_size (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h14
  have hsn := gen_op0_size (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hn
  have hsm := gen_op0_size (K := K) (n + 19)
    (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hm
  omega

theorem gen_macArm_one_m1_size (n acc : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      .ok (t, .atom (acc + 1)) ∧ t.size = 52 := by
  have h14 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have h30 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 29) h14 h30
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns, hns_sz⟩ := gen_macNewSample_m1_size (K := K) (n + 5) acc
  have hbatt := gen_op0 (K := K) (n + 27)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  obtain ⟨doneTree, hdone, hdone_sz⟩ :=
    gen_macArm_done_size (K := K) (n + 22) (.atom (acc + 1)) (.atom 1) (.atom 1)
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 25) (axis := 4)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) hdone
  have hop6 := gen_op6_one (K := K) (n + 30) (c := op0 6) hcond hslam
  refine ⟨_, by simpa [macArm, slam, op0, macNewSample, macCore] using hop6, ?_⟩
  have h6 := gen_op6_one_size (K := K) (n + 30) hcond hslam
    (by simpa [macArm, slam, op0, macNewSample, macCore] using hop6)
  have hc := gen_op5_size (K := K) (n + 29) h14 h30 hcond
  have hs14 := gen_op0_size (K := K) (n + 28)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h14
  have hs30 := gen_op0_size (K := K) (n + 28)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h30
  have hss := gen_slam_size (K := K) (n + 25) hbatt hns
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) hdone hslam
  have hbatt_sz := gen_op0_size (K := K) (n + 27)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hbatt
  omega

/-! ## 2×2 matmul sizes -/

theorem gen_mmC00_size (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC00 =
      .ok (t, .atom 2) ∧ t.size = 127 := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA, inner_sz⟩ := gen_macArm_one_m1_size (K := K) (n + 20) 0
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 12) ha0 a00 b00 innerA
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA, outer_sz⟩ := gen_macArm_one_m1_size (K := K) (n + 23) 1
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a01 b10 outerA
  obtain ⟨t, ht⟩ := gen_mmC00 (K := K) n
  refine ⟨t, ht, ?_⟩
  simp only [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0] at ht
  refine gen_ok_size (n := 127) ht (by simpa [invokeMac, slam, op7, quote, op1, op0]
    using houter) ?_
  have hout := gen_invokeMac_size (K := K) (n + 51) (by
      simpa [invokeMac, slam, op7, quote, op1] using hinner) a01 b10 outerA
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using houter)
  have hin := gen_invokeMac_size (K := K) (n + 48) ha0 a00 b00 innerA hinner
  have ha0s := gen_op1_size (K := K) (n + 49) mmSubject 0 ha0
  have a00s := gen_op0_size (K := K) (n + 47) mmSubject_slot8 a00
  have b00s := gen_op0_size (K := K) (n + 47) mmSubject_slot12 b00
  have a01s := gen_op0_size (K := K) (n + 50) mmSubject_slot9 a01
  have b10s := gen_op0_size (K := K) (n + 50) mmSubject_slot14 b10
  omega

theorem gen_mmC01_size (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC01 =
      .ok (t, .atom 1) ∧ t.size = 111 := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA, inner_sz⟩ := gen_macArm_one_m0_size (K := K) (n + 29) 0
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 13) ha0 a00 b01 innerA
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA, outer_sz⟩ := gen_macArm_one_m1_size (K := K) (n + 23) 0
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 8)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 9) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a01 b11 outerA
  obtain ⟨t, ht⟩ := gen_mmC01 (K := K) n
  refine ⟨t, ht, ?_⟩
  simp only [mmC01, mac2, invokeMac, slam, op7, quote, op1, op0] at ht
  refine gen_ok_size (n := 111) ht (by simpa [invokeMac, slam, op7, quote, op1, op0]
    using houter) ?_
  have hout := gen_invokeMac_size (K := K) (n + 51) (by
      simpa [invokeMac, slam, op7, quote, op1] using hinner) a01 b11 outerA
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using houter)
  have hin := gen_invokeMac_size (K := K) (n + 48) ha0 a00 b01 innerA hinner
  have ha0s := gen_op1_size (K := K) (n + 49) mmSubject 0 ha0
  have a00s := gen_op0_size (K := K) (n + 47) mmSubject_slot8 a00
  have b01s := gen_op0_size (K := K) (n + 47) mmSubject_slot13 b01
  have a01s := gen_op0_size (K := K) (n + 50) mmSubject_slot9 a01
  have b11s := gen_op0_size (K := K) (n + 50) mmSubject_slot15 b11
  omega

theorem gen_mmC10_size (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC10 =
      .ok (t, .atom 1) ∧ t.size = 80 := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA, inner_sz⟩ := gen_macArm_zero_size (K := K) (n + 45) (.atom 0) (.atom 1)
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 12) ha0 a10 b00 innerA
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA, outer_sz⟩ := gen_macArm_one_m1_size (K := K) (n + 23) 0
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 12)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 14)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a11 b10 outerA
  obtain ⟨t, ht⟩ := gen_mmC10 (K := K) n
  refine ⟨t, ht, ?_⟩
  simp only [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0] at ht
  refine gen_ok_size (n := 80) ht (by simpa [invokeMac, slam, op7, quote, op1, op0]
    using houter) ?_
  have hout := gen_invokeMac_size (K := K) (n + 51) (by
      simpa [invokeMac, slam, op7, quote, op1] using hinner) a11 b10 outerA
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using houter)
  have hin := gen_invokeMac_size (K := K) (n + 48) ha0 a10 b00 innerA hinner
  have ha0s := gen_op1_size (K := K) (n + 49) mmSubject 0 ha0
  have a10s := gen_op0_size (K := K) (n + 47) mmSubject_slot10 a10
  have b00s := gen_op0_size (K := K) (n + 47) mmSubject_slot12 b00
  have a11s := gen_op0_size (K := K) (n + 50) mmSubject_slot11 a11
  have b10s := gen_op0_size (K := K) (n + 50) mmSubject_slot14 b10
  omega

theorem gen_mmC11_size (n : ℕ) :
    ∃ t, genComputeSkeleton (K := K) (n + 56) mmSubject mmC11 =
      .ok (t, .atom 1) ∧ t.size = 80 := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA, inner_sz⟩ := gen_macArm_zero_size (K := K) (n + 45) (.atom 0) (.atom 0)
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 13) ha0 a10 b01 innerA
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA, outer_sz⟩ := gen_macArm_one_m1_size (K := K) (n + 23) 0
  obtain ⟨houterT, _, _, houter, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 51)
    (aH := .atom 7)
    (aT := .cell (.cell (quote mmBattery)
        (.cell (op1 0) (.cell (op1 0)
          (.cell (.cell (.atom 0) (.atom 10)) (op0 13)))))
      (invokeAxis 4))
    (nH := .atom 0) (nT := .atom 11) (mF := op0 15)
    (by simpa [invokeMac, slam, op7, quote, op1] using hinner) a11 b11 outerA
  obtain ⟨t, ht⟩ := gen_mmC11 (K := K) n
  refine ⟨t, ht, ?_⟩
  simp only [mmC11, mac2, invokeMac, slam, op7, quote, op1, op0] at ht
  refine gen_ok_size (n := 80) ht (by simpa [invokeMac, slam, op7, quote, op1, op0]
    using houter) ?_
  have hout := gen_invokeMac_size (K := K) (n + 51) (by
      simpa [invokeMac, slam, op7, quote, op1] using hinner) a11 b11 outerA
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using houter)
  have hin := gen_invokeMac_size (K := K) (n + 48) ha0 a10 b01 innerA hinner
  have ha0s := gen_op1_size (K := K) (n + 49) mmSubject 0 ha0
  have a10s := gen_op0_size (K := K) (n + 47) mmSubject_slot10 a10
  have b01s := gen_op0_size (K := K) (n + 47) mmSubject_slot13 b01
  have a11s := gen_op0_size (K := K) (n + 50) mmSubject_slot11 a11
  have b11s := gen_op0_size (K := K) (n + 50) mmSubject_slot15 b11
  omega

theorem mmTree_size : (mmTree (K := K)).size = 401 := by
  obtain ⟨t00, h00, s00⟩ := gen_mmC00_size (K := K) 6
  obtain ⟨t01, h01, s01⟩ := gen_mmC01_size (K := K) 6
  obtain ⟨t10, h10, s10⟩ := gen_mmC10_size (K := K) 6
  obtain ⟨t11, h11, s11⟩ := gen_mmC11_size (K := K) 6
  have h00c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 8) (op0 12))
              (.cell (op1 0) (.cell (op0 9) (op0 14)))))
            (invokeAxis 4))) = .ok (t00, .atom 2) := by
    simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1] using h00
  have h01c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 8) (op0 13))
              (.cell (op1 0) (.cell (op0 9) (op0 15)))))
            (invokeAxis 4))) = .ok (t01, .atom 1) := by
    simpa [mmC01, mac2, invokeMac, slam, op7, quote, op1] using h01
  have h10c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 10) (op0 12))
              (.cell (op1 0) (.cell (op0 11) (op0 14)))))
            (invokeAxis 4))) = .ok (t10, .atom 1) := by
    simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1] using h10
  have h11c :
      genComputeSkeleton (K := K) 62 mmSubject
        (.cell (.atom 7)
          (.cell (.cell (quote mmBattery)
            (.cell (invokeMac (op1 0) (op0 10) (op0 13))
              (.cell (op1 0) (.cell (op0 11) (op0 15)))))
            (invokeAxis 4))) = .ok (t11, .atom 1) := by
    simpa [mmC11, mac2, invokeMac, slam, op7, quote, op1] using h11
  have hL := gen_cons (K := K) 62 h00c h01c
  have hR := gen_cons (K := K) 62 h10c h11c
  have hop := gen_cons (K := K) 63 hL hR
  have ht := mmTree_gen (K := K)
  simp only [mmFormula, mmC00, mmC01, mmC10, mmC11, mac2, invokeMac, slam, op7,
    quote, op1, op0] at ht
  refine gen_ok_size (n := 401) ht hop ?_
  have hsL := gen_cons_size (K := K) 62 h00c h01c hL
  have hsR := gen_cons_size (K := K) 62 h10c h11c hR
  have hsO := gen_cons_size (K := K) 63 hL hR hop
  omega

theorem mmComputeTree_size (z α : K) :
    (mapNTree GenComputeRow.row (renderRows z α (bfsAssign (mmTree (K := K))))).size =
      401 := by
  rw [mapNTree_size, renderRows_size, bfsAssign_size, mmTree_size]

#print axioms mmTree_size
#print axioms mmComputeTree_size

end Nock.NockVMROM.Thm54.TraceGen
