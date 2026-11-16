/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulSeed.lean

  Discharge the three `computeRowsAccepted_of_seed` InTree hypotheses
  for the assigned matmul tree by transporting `SeedOK` along the named
  `gen_*` constructors (no OP3, no opcode-2 formula).  Source-noun
  `AllCellDyckNe` supplies autocons `formulaHead` Dyck; OP5 windows are
  either identical operands or `{0,1}` atoms.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulHyps
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonVcomp

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open ComputeTable

variable {K : Type} [Field K]

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

/-- OP5 operands are equal or a pair of atoms, so `c = 1` separates unequal
    encodings on the leaf coordinate. -/
def op5C1Ready (s : ComputeRowSkeleton) : Prop :=
  let u := P8Census.skeletonSubformula s 0 TripleSlot.result
  let v := P8Census.skeletonSubformula s 1 TripleSlot.result
  u = v ∨ ∃ a b : ℕ, u = .atom a ∧ v = .atom b

/-- Combined NPR seed window on one generated compute tree -/
def SeedOK (z : K) (t : NTree (GenComputeRow K)) : Prop :=
  ∀ v, InTree t v →
    v.label.skel.state ≠ State.s3 ∧
      (v.label.skel.state = State.cons →
        (encC z (formulaHead v.label.skel.formula)).dyck ≠ 0) ∧
      (v.label.skel.state = State.s5 → op5ResultsAgree z v.label.skel) ∧
      (v.label.skel.state = State.s5 → op5C1Ready v.label.skel)

theorem seedOK_of_children {z : K} {lab : GenComputeRow K}
    {cs : List (NTree (GenComputeRow K))}
    (hroot_ne : lab.skel.state ≠ State.s3)
    (hroot_cons : lab.skel.state = State.cons →
      (encC z (formulaHead lab.skel.formula)).dyck ≠ 0)
    (hroot_s5 : lab.skel.state = State.s5 → op5ResultsAgree z lab.skel)
    (hroot_c1 : lab.skel.state = State.s5 → op5C1Ready lab.skel)
    (hcs : ∀ c ∈ cs, SeedOK z c) :
    SeedOK z (.node lab cs) := by
  intro v hv
  cases hv with
  | here => exact ⟨hroot_ne, hroot_cons, hroot_s5, hroot_c1⟩
  | sub hs hu => exact hcs _ hs _ hu

theorem seedOK_leaf {z : K} {lab : GenComputeRow K}
    (hroot_ne : lab.skel.state ≠ State.s3)
    (hroot_cons : lab.skel.state = State.cons →
      (encC z (formulaHead lab.skel.formula)).dyck ≠ 0)
    (hroot_s5 : lab.skel.state = State.s5 → op5ResultsAgree z lab.skel)
    (hroot_c1 : lab.skel.state = State.s5 → op5C1Ready lab.skel) :
    SeedOK z (.node lab []) :=
  seedOK_of_children hroot_ne hroot_cons hroot_s5 hroot_c1
    (fun _ hc => by simp [NTree.children] at hc)

theorem seedOK_gen_op0 {z : K} {n : ℕ} {s : Noun} {ax : ℕ} {r : Noun}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (hslot : Noun.slot ax s = some r)
    (h : genComputeSkeleton (K := K) (n + 1) s (op0 ax) = .ok (t, res)) :
    SeedOK z t := by
  have h' := gen_op0 (K := K) n hslot
  rw [(gen_ok_unique h h').1]
  refine seedOK_leaf ?_ ?_ ?_ ?_
  · simp [skelNode, genSkelOp0]
  · simp [skelNode, genSkelOp0]
  · simp [skelNode, genSkelOp0]
  · simp [skelNode, genSkelOp0]

theorem seedOK_gen_op1 {z : K} {n : ℕ} {s : Noun} {k : ℕ}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) s (op1 k) = .ok (t, res)) :
    SeedOK z t := by
  have h' := gen_op1 (K := K) n s k
  rw [(gen_ok_unique h h').1]
  refine seedOK_leaf ?_ ?_ ?_ ?_
  · simp [skelNode, genSkelOp1]
  · simp [skelNode, genSkelOp1]
  · simp [skelNode, genSkelOp1]
  · simp [skelNode, genSkelOp1]

theorem seedOK_gen_quote {z : K} {n : ℕ} {s result : Noun}
    {t : NTree (GenComputeRow K)} {res : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) s (quote result) = .ok (t, res)) :
    SeedOK z t := by
  have h' := gen_quote (K := K) n s result
  rw [(gen_ok_unique h h').1]
  refine seedOK_leaf ?_ ?_ ?_ ?_
  · simp [skelNode, genSkelOp1]
  · simp [skelNode, genSkelOp1]
  · simp [skelNode, genSkelOp1]
  · simp [skelNode, genSkelOp1]

theorem seedOK_gen_op4 {z : K} {n : ℕ} {s tail callResult result : Noun}
    {callTree t : NTree (GenComputeRow K)} {res : Noun}
    (hcall : genComputeSkeleton (K := K) n s tail = .ok (callTree, callResult))
    (hinc : Noun.lus callResult = some result)
    (h : genComputeSkeleton (K := K) (n + 1) s (op4 tail) = .ok (t, res))
    (ih : SeedOK z callTree) :
    SeedOK z t := by
  have h' := gen_op4 (K := K) n hcall hinc
  rw [(gen_ok_unique h h').1]
  refine seedOK_of_children ?_ ?_ ?_ ?_ ?_
  · simp [skelNode, genSkelOp4]
  · simp [skelNode, genSkelOp4]
  · simp [skelNode, genSkelOp4]
  · simp [skelNode, genSkelOp4]
  · intro c hc v hv
    simp [NTree.children] at hc
    subst c
    exact ih v hv

theorem seedOK_gen_op5 {z : K} {n : ℕ} {s b c sf1 sf2 : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sf1))
    (hc : genComputeSkeleton (K := K) n s c = .ok (cTree, sf2))
    (h : genComputeSkeleton (K := K) (n + 1) s (op5 b c) = .ok (t, res))
    (ihb : SeedOK z bTree) (ihc : SeedOK z cTree)
    (hag : sf1 = sf2 ∨ encC z sf1 ≠ encC z sf2)
    (hc1 : sf1 = sf2 ∨ ∃ a b : ℕ, sf1 = .atom a ∧ sf2 = .atom b) :
    SeedOK z t := by
  have h' := gen_op5 (K := K) n hb hc
  rw [(gen_ok_unique h h').1]
  refine seedOK_of_children ?_ ?_ ?_ ?_ ?_
  · simp [skelNode, genSkelOp5]
  · simp [skelNode, genSkelOp5]
  · intro _
    have hr := genSkelOp5_results s (op5 b c) (.atom 5) (.cell b c) b c sf1 sf2
      (Noun.tis sf1 sf2)
    simpa [skelNode, op5ResultsAgree, hr.1, hr.2] using hag
  · intro _
    have hr := genSkelOp5_results s (op5 b c) (.atom 5) (.cell b c) b c sf1 sf2
      (Noun.tis sf1 sf2)
    simpa [skelNode, op5C1Ready, hr.1, hr.2] using hc1
  · intro ch hc v hv
    simp [NTree.children] at hc
    rcases hc with rfl | rfl
    · exact ihb v hv
    · exact ihc v hv

theorem seedOK_gen_op6_zero {z : K} {n : ℕ} {s b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (condTree, .atom 0))
    (hc : genComputeSkeleton (K := K) n s c = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op6 b c d) = .ok (t, res))
    (ihb : SeedOK z condTree) (ihc : SeedOK z takenTree) :
    SeedOK z t := by
  have h' := gen_op6_zero (K := K) n (d := d) hb hc
  rw [(gen_ok_unique h h').1]
  refine seedOK_of_children ?_ ?_ ?_ ?_ ?_
  · simp [skelNode, genSkelOp6]
  · simp [skelNode, genSkelOp6]
  · simp [skelNode, genSkelOp6]
  · simp [skelNode, genSkelOp6]
  · intro ch hc v hv
    simp [NTree.children] at hc
    rcases hc with rfl | rfl
    · exact ihb v hv
    · exact ihc v hv

theorem seedOK_gen_op6_one {z : K} {n : ℕ} {s b c d result : Noun}
    {condTree takenTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (condTree, .atom 1))
    (hd : genComputeSkeleton (K := K) n s d = .ok (takenTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op6 b c d) = .ok (t, res))
    (ihb : SeedOK z condTree) (ihd : SeedOK z takenTree) :
    SeedOK z t := by
  have h' := gen_op6_one (K := K) n (c := c) hb hd
  rw [(gen_ok_unique h h').1]
  refine seedOK_of_children ?_ ?_ ?_ ?_ ?_
  · simp [skelNode, genSkelOp6]
  · simp [skelNode, genSkelOp6]
  · simp [skelNode, genSkelOp6]
  · simp [skelNode, genSkelOp6]
  · intro ch hc v hv
    simp [NTree.children] at hc
    rcases hc with rfl | rfl
    · exact ihb v hv
    · exact ihd v hv

theorem seedOK_gen_op7 {z : K} {n : ℕ} {s b c sb result : Noun}
    {bTree cTree t : NTree (GenComputeRow K)} {res : Noun}
    (hb : genComputeSkeleton (K := K) n s b = .ok (bTree, sb))
    (hc : genComputeSkeleton (K := K) n sb c = .ok (cTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s (op7 b c) = .ok (t, res))
    (ihb : SeedOK z bTree) (ihc : SeedOK z cTree) :
    SeedOK z t := by
  have h' := gen_op7 (K := K) n hb hc
  rw [(gen_ok_unique h h').1]
  refine seedOK_of_children ?_ ?_ ?_ ?_ ?_
  · simp [skelNode, genSkelOp7]
  · simp [skelNode, genSkelOp7]
  · simp [skelNode, genSkelOp7]
  · simp [skelNode, genSkelOp7]
  · intro ch hc v hv
    simp [NTree.children] at hc
    rcases hc with rfl | rfl
    · exact ihb v hv
    · exact ihc v hv

theorem seedOK_gen_op9 {z : K} {n : ℕ} {s c core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree t : NTree (GenComputeRow K)} {res : Noun}
    (hc : genComputeSkeleton (K := K) n s c = .ok (coreTree, core))
    (hslot : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) n core arm = .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 1) s
      (.cell (.atom 9) (.cell (.atom axis) c)) = .ok (t, res))
    (ihc : SeedOK z coreTree) (iha : SeedOK z invokeTree) :
    SeedOK z t := by
  have h' := gen_op9 (K := K) n hc hslot harm
  rw [(gen_ok_unique h h').1]
  refine seedOK_of_children ?_ ?_ ?_ ?_ ?_
  · simp [skelNode, genSkelOp9]
  · simp [skelNode, genSkelOp9]
  · simp [skelNode, genSkelOp9]
  · simp [skelNode, genSkelOp9]
  · intro ch hch v hv
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihc v hv
    · exact iha v hv

theorem seedOK_gen_cons {z : K} {n : ℕ}
    {s leftHead leftTail tail lRes rRes : Noun}
    {lTree rTree t : NTree (GenComputeRow K)} {res : Noun}
    (hl : genComputeSkeleton (K := K) n s (.cell leftHead leftTail) =
      .ok (lTree, lRes))
    (hr : genComputeSkeleton (K := K) n s tail = .ok (rTree, rRes))
    (h : genComputeSkeleton (K := K) (n + 1) s
      (.cell (.cell leftHead leftTail) tail) = .ok (t, res))
    (ihl : SeedOK z lTree) (ihr : SeedOK z rTree)
    (hdy : (encC z (.cell leftHead leftTail)).dyck ≠ 0) :
    SeedOK z t := by
  have h' := gen_cons (K := K) n hl hr
  rw [(gen_ok_unique h h').1]
  refine seedOK_of_children ?_ ?_ ?_ ?_ ?_
  · simp [skelNode, genSkelCons]
  · intro _
    simpa [skelNode, genSkelCons, formulaHead]
  · simp [skelNode, genSkelCons]
  · simp [skelNode, genSkelCons]
  · intro ch hc v hv
    simp [NTree.children] at hc
    rcases hc with rfl | rfl
    · exact ihl v hv
    · exact ihr v hv

theorem seedOK_gen_invokeAxis {z : K} {n : ℕ}
    {s core arm result : Noun} {axis : ℕ}
    {coreTree invokeTree t : NTree (GenComputeRow K)} {res : Noun}
    (hcore : genComputeSkeleton (K := K) (n + 2) s (op0 1) =
      .ok (coreTree, core))
    (hslotA : Noun.slot axis core = some arm)
    (harm : genComputeSkeleton (K := K) (n + 2) core arm =
      .ok (invokeTree, result))
    (h : genComputeSkeleton (K := K) (n + 3) s (invokeAxis axis) = .ok (t, res))
    (ihc : SeedOK z coreTree) (iha : SeedOK z invokeTree) :
    SeedOK z t := by
  have h' := gen_invokeAxis (K := K) n hcore hslotA harm
  rw [(gen_ok_unique h h').1]
  refine seedOK_of_children ?_ ?_ ?_ ?_ ?_
  · simp [skelNode, genSkelOp9]
  · simp [skelNode, genSkelOp9]
  · simp [skelNode, genSkelOp9]
  · simp [skelNode, genSkelOp9]
  · intro ch hch v hv
    simp [NTree.children] at hch
    rcases hch with rfl | rfl
    · exact ihc v hv
    · exact iha v hv

theorem seedOK_addArm_done (z : K) (n : ℕ) (acc m : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (addCore acc m m) addArm =
      .ok (t, acc)) :
    SeedOK z t := by
  have h14 := gen_op0 (K := K) (n + 3) (addCore_slot14 acc m m)
  have h15 := gen_op0 (K := K) (n + 3) (addCore_slot15 acc m m)
  have h5eq := gen_op5 (K := K) (n + 4) h14 h15
  have ih5 := seedOK_gen_op5 (z := z) h14 h15 h5eq
    (seedOK_gen_op0 (z := z) (addCore_slot14 acc m m) h14)
    (seedOK_gen_op0 (z := z) (addCore_slot15 acc m m) h15)
    (Or.inl rfl) (Or.inl rfl)
  rw [tis_self m] at h5eq
  have hthen := gen_op0 (K := K) (n + 4) (addCore_slot6 acc m m)
  have hop6 := gen_op6_zero (K := K) (n + 5)
    (d := slam (op0 2) addNewSample 2) h5eq hthen
  have huniq := gen_ok_unique h (by simpa [addArm] using hop6)
  rw [huniq.1]
  exact seedOK_gen_op6_zero (z := z) h5eq hthen hop6 (by convert ih5; simp [tis_self m])
    (seedOK_gen_op0 (z := z) (addCore_slot6 acc m m) hthen)

theorem seedOK_addNewSample (z : K) (n acc i m : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 5)
      (addCore (.atom acc) (.atom i) (.atom m)) addNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom (i + 1)) (.atom m))))
    (hdyA : (encC z (op4 (op0 6))).dyck ≠ 0)
    (hdyI : (encC z (op4 (op0 14))).dyck ≠ 0) :
    SeedOK z t := by
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
  exact seedOK_gen_cons (z := z) hincA hinner houter
    (seedOK_gen_op4 (z := z) h6 (lus_nat acc) hincA
      (seedOK_gen_op0 (z := z) (addCore_slot6 (.atom acc) (.atom i) (.atom m)) h6))
    (seedOK_gen_cons (z := z) hincI h15 hinner
      (seedOK_gen_op4 (z := z) h14 (lus_nat i) hincI
        (seedOK_gen_op0 (z := z) (addCore_slot14 (.atom acc) (.atom i) (.atom m)) h14))
      (seedOK_gen_op0 (z := z) (addCore_slot15 (.atom acc) (.atom i) (.atom m)) h15)
      hdyI)
    hdyA

theorem seedOK_gen_slam {z : K} {n : ℕ} {axis : ℕ}
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
    (ihb : SeedOK z battTree) (ihs : SeedOK z sampTree)
    (iha : SeedOK z invokeTree)
    (hdy : (encC z (.cell bHead bTail)).dyck ≠ 0) :
    SeedOK z t := by
  have hpair := gen_cons (K := K) (n + 3) (lTree := battTree) (rTree := sampTree) hb hs
  have hcore := gen_op0 (K := K) (n + 2) (slot_1 (.cell battery sample))
  have hax := gen_invokeAxis (K := K) (n + 1) hcore hslot harm
  have hop := gen_op7 (K := K) (n + 4) hpair hax
  have huniq := gen_ok_unique h (by simpa [slam] using hop)
  rw [huniq.1]
  exact seedOK_gen_op7 (z := z) hpair hax hop
    (seedOK_gen_cons (z := z) hb hs hpair ihb ihs hdy)
    (seedOK_gen_invokeAxis (z := z) hcore hslot harm hax
      (seedOK_gen_op0 (z := z) (slot_1 (.cell battery sample)) hcore) iha)

theorem seedOK_addArm_one (z : K) (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 16)
      (addCore (.atom acc) (.atom 0) (.atom 1)) addArm =
      .ok (t, .atom (acc + 1)))
    (hdyA : (encC z (op4 (op0 6))).dyck ≠ 0)
    (hdyI : (encC z (op4 (op0 14))).dyck ≠ 0)
    (hdyBatt : (encC z (op0 2)).dyck ≠ 0)
    (hag01 : encC z (.atom 0) ≠ encC z (.atom 1)) :
    SeedOK z t := by
  have h14 := gen_op0 (K := K) (n + 13)
    (addCore_slot14 (.atom acc) (.atom 0) (.atom 1))
  have h15 := gen_op0 (K := K) (n + 13)
    (addCore_slot15 (.atom acc) (.atom 0) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 14) h14 h15
  have ihcond := seedOK_gen_op5 (z := z) h14 h15 hcond
    (seedOK_gen_op0 (z := z) (addCore_slot14 (.atom acc) (.atom 0) (.atom 1)) h14)
    (seedOK_gen_op0 (z := z) (addCore_slot15 (.atom acc) (.atom 0) (.atom 1)) h15)
    (Or.inr hag01) (Or.inr ⟨0, 1, rfl, rfl⟩)
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_addNewSample (K := K) (n + 8) acc 0 1
  have ihns := seedOK_addNewSample (z := z) (n + 8) acc 0 1 hns hdyA hdyI
  have hbatt := gen_op0 (K := K) (n + 12)
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1))
  obtain ⟨doneTree, hdone⟩ :=
    gen_addArm_done (K := K) (n + 7) (.atom (acc + 1)) (.atom 1)
  have ihdone := seedOK_addArm_done (z := z) (n + 7) (.atom (acc + 1)) (.atom 1) hdone
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 10) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1)) hdone
  have ihslam := seedOK_gen_slam (z := z) hbatt hns
    (addCore_slot2 (.atom (acc + 1)) (.atom 1) (.atom 1)) hdone hslam
    (seedOK_gen_op0 (z := z) (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hbatt)
    ihns ihdone hdyBatt
  have hop6 := gen_op6_one (K := K) (n + 15) (c := op0 6) hcond hslam
  have huniq := gen_ok_unique h (by simpa [addArm, slam, op0] using hop6)
  rw [huniq.1]
  exact seedOK_gen_op6_one (z := z) hcond hslam hop6
    (by convert ihcond; simp [htis]) ihslam

theorem seedOK_macArm_done (z : K) (n : ℕ) (acc k m : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (macCoreAt acc k k m) macArm =
      .ok (t, acc)) :
    SeedOK z t := by
  have h14 := gen_op0 (K := K) (n + 3) (macCoreAt_slot14 acc k k m)
  have h30 := gen_op0 (K := K) (n + 3) (macCoreAt_slot30 acc k k m)
  have h5eq := gen_op5 (K := K) (n + 4) h14 h30
  have ih5 := seedOK_gen_op5 (z := z) h14 h30 h5eq
    (seedOK_gen_op0 (z := z) (macCoreAt_slot14 acc k k m) h14)
    (seedOK_gen_op0 (z := z) (macCoreAt_slot30 acc k k m) h30)
    (Or.inl rfl) (Or.inl rfl)
  rw [tis_self k] at h5eq
  have hthen := gen_op0 (K := K) (n + 4) (macCoreAt_slot6 acc k k m)
  have hop6 := gen_op6_zero (K := K) (n + 5)
    (d := slam (op0 2) macNewSample 4) h5eq hthen
  have huniq := gen_ok_unique h (by simpa [macArm] using hop6)
  rw [huniq.1]
  exact seedOK_gen_op6_zero (z := z) h5eq hthen hop6 (by convert ih5; simp [tis_self k])
    (seedOK_gen_op0 (z := z) (macCoreAt_slot6 acc k k m) hthen)

theorem seedOK_gen_macSampleF {z : K} {n : ℕ}
    {s aH aT nH nT mF acc k m : Noun}
    {aTree nTree mTree t : NTree (GenComputeRow K)} {res : Noun}
    (ha : genComputeSkeleton (K := K) (n + 2) s (.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n s (.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n s mF = .ok (mTree, m))
    (h : genComputeSkeleton (K := K) (n + 3) s
      (.cell (.cell aH aT) (.cell (op1 0) (.cell (.cell nH nT) mF))) =
      .ok (t, res))
    (iha : SeedOK z aTree) (ihn : SeedOK z nTree) (ihm : SeedOK z mTree)
    (hdyA : (encC z (.cell aH aT)).dyck ≠ 0)
    (hdyN : (encC z (.cell nH nT)).dyck ≠ 0)
    (hdyZ : (encC z (op1 0)).dyck ≠ 0) :
    SeedOK z t := by
  have hnm := gen_cons (K := K) n hn hm
  have hz := gen_op1 (K := K) n s 0
  have hinner := gen_cons (K := K) (n + 1) hz hnm
  have houter := gen_cons (K := K) (n + 2) ha hinner
  have huniq := gen_ok_unique h houter
  rw [huniq.1]
  exact seedOK_gen_cons (z := z) ha hinner houter iha
    (seedOK_gen_cons (z := z) hz hnm hinner (seedOK_gen_op1 (z := z) hz)
      (seedOK_gen_cons (z := z) hn hm hnm ihn ihm hdyN) hdyZ)
    hdyA

theorem seedOK_addFromMac_m0 (z : K) (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 12)
      (macCore (.atom acc) (.atom 1) (.atom 0)) addFromMac = .ok (t, .atom acc))
    (hdy5 : (encC z (op0 5)).dyck ≠ 0)
    (hdy6 : (encC z (op0 6)).dyck ≠ 0)
    (hdyZ : (encC z (op1 0)).dyck ≠ 0) :
    SeedOK z t := by
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
  have ihdone := seedOK_addArm_done (z := z) (n + 4) (.atom acc) (.atom 0) hdone
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 7) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 0)) hdone
  have huniq := gen_ok_unique h (by simpa [addFromMac, slam, op0, op1, macCore] using hslam)
  rw [huniq.1]
  exact seedOK_gen_slam (z := z) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 0)) hdone hslam
    (seedOK_gen_op0 (z := z) (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h5)
    (seedOK_gen_cons (z := z) hacc hinner hsmpl
      (seedOK_gen_op0 (z := z) (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hacc)
      (seedOK_gen_cons (z := z) hz hm hinner (seedOK_gen_op1 (z := z) hz)
        (seedOK_gen_op0 (z := z) (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hm)
        hdyZ)
      hdy6)
    ihdone hdy5

theorem seedOK_addFromMac_m1 (z : K) (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 21)
      (macCore (.atom acc) (.atom 1) (.atom 1)) addFromMac =
      .ok (t, .atom (acc + 1)))
    (hdy5 : (encC z (op0 5)).dyck ≠ 0)
    (hdy6 : (encC z (op0 6)).dyck ≠ 0)
    (hdyZ : (encC z (op1 0)).dyck ≠ 0)
    (hdyA : (encC z (op4 (op0 6))).dyck ≠ 0)
    (hdyI : (encC z (op4 (op0 14))).dyck ≠ 0)
    (hdyBatt : (encC z (op0 2)).dyck ≠ 0)
    (hag01 : encC z (.atom 0) ≠ encC z (.atom 1)) :
    SeedOK z t := by
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
  have ihdone := seedOK_addArm_one (z := z) (n + 3) acc hdone hdyA hdyI hdyBatt hag01
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16) (axis := 2)
    (bHead := .atom 0) (bTail := .atom 5) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hdone
  have huniq := gen_ok_unique h (by simpa [addFromMac, slam, op0, op1, macCore] using hslam)
  rw [huniq.1]
  exact seedOK_gen_slam (z := z) h5 hsmpl
    (addCore_slot2 (.atom acc) (.atom 0) (.atom 1)) hdone hslam
    (seedOK_gen_op0 (z := z) (macCoreAt_slot5 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h5)
    (seedOK_gen_cons (z := z) haccS hinner hsmpl
      (seedOK_gen_op0 (z := z) (macCoreAt_slot6 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) haccS)
      (seedOK_gen_cons (z := z) hz hm hinner (seedOK_gen_op1 (z := z) hz)
        (seedOK_gen_op0 (z := z) (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hm)
        hdyZ)
      hdy6)
    ihdone hdy5

theorem seedOK_macNewSample_m1 (z : K) (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 23)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample =
      .ok (t, .cell (.atom (acc + 1)) (.cell (.atom 1) (.cell (.atom 1) (.atom 1)))))
    (hdy5 : (encC z (op0 5)).dyck ≠ 0)
    (hdy6 : (encC z (op0 6)).dyck ≠ 0)
    (hdyZ : (encC z (op1 0)).dyck ≠ 0)
    (hdyA : (encC z (op4 (op0 6))).dyck ≠ 0)
    (hdyI : (encC z (op4 (op0 14))).dyck ≠ 0)
    (hdyBatt : (encC z (op0 2)).dyck ≠ 0)
    (hag01 : encC z (.atom 0) ≠ encC z (.atom 1))
    (hdyAdd : (encC z addFromMac).dyck ≠ 0)
    (hdyN : (encC z (op0 30)).dyck ≠ 0) :
    SeedOK z t := by
  obtain ⟨addT, hadd⟩ := gen_addFromMac_m1 (K := K) (n + 1) acc
  have ihadd := seedOK_addFromMac_m1 (z := z) (n + 1) acc hadd
    hdy5 hdy6 hdyZ hdyA hdyI hdyBatt hag01
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
  have ihcell := seedOK_gen_cons (z := z) hadd' hrest hcell ihadd
    (seedOK_gen_cons (z := z) hinc hnm hrest
      (seedOK_gen_op4 (z := z) h14 (lus_nat 0) hinc
        (seedOK_gen_op0 (z := z)
          (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h14))
      (seedOK_gen_cons (z := z) hn hm hnm
        (seedOK_gen_op0 (z := z)
          (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hn)
        (seedOK_gen_op0 (z := z)
          (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hm)
        hdyN)
      hdyI)
    (by simpa [addFromMac, slam, op7, op0, op1, invokeAxis] using hdyAdd)
  have hnamed :=
    show genComputeSkeleton (K := K) (n + 23)
        (macCore (.atom acc) (.atom 1) (.atom 1)) macNewSample = _ from by
      simpa [macNewSample, addFromMac, slam, op7, op4, op0, op1, invokeAxis,
        macCore] using hcell
  have huniq := gen_ok_unique h hnamed
  rw [huniq.1]
  exact ihcell

theorem seedOK_macNewSample_m0 (z : K) (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 14)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample =
      .ok (t, .cell (.atom acc) (.cell (.atom 1) (.cell (.atom 1) (.atom 0)))))
    (hdy5 : (encC z (op0 5)).dyck ≠ 0)
    (hdy6 : (encC z (op0 6)).dyck ≠ 0)
    (hdyZ : (encC z (op1 0)).dyck ≠ 0)
    (hdyI : (encC z (op4 (op0 14))).dyck ≠ 0)
    (hdyAdd : (encC z addFromMac).dyck ≠ 0)
    (hdyN : (encC z (op0 30)).dyck ≠ 0) :
    SeedOK z t := by
  obtain ⟨addT, hadd⟩ := gen_addFromMac_m0 (K := K) (n + 1) acc
  have ihadd := seedOK_addFromMac_m0 (z := z) (n + 1) acc hadd hdy5 hdy6 hdyZ
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
  have ihcell := seedOK_gen_cons (z := z) hadd' hrest hcell ihadd
    (seedOK_gen_cons (z := z) hinc hnm hrest
      (seedOK_gen_op4 (z := z) h14 (lus_nat 0) hinc
        (seedOK_gen_op0 (z := z)
          (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h14))
      (seedOK_gen_cons (z := z) hn hm hnm
        (seedOK_gen_op0 (z := z)
          (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hn)
        (seedOK_gen_op0 (z := z)
          (macCoreAt_slot31 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hm)
        hdyN)
      hdyI)
    (by simpa [addFromMac, slam, op7, op0, op1, invokeAxis] using hdyAdd)
  have hnamed :=
    show genComputeSkeleton (K := K) (n + 14)
        (macCore (.atom acc) (.atom 1) (.atom 0)) macNewSample = _ from by
      simpa [macNewSample, addFromMac, slam, op7, op4, op0, op1, invokeAxis,
        macCore] using hcell
  have huniq := gen_ok_unique h hnamed
  rw [huniq.1]
  exact ihcell

theorem seedOK_macArm_zero (z : K) (n : ℕ) (acc m : Noun)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 6) (macCore acc (.atom 0) m) macArm =
      .ok (t, acc)) :
    SeedOK z t :=
  seedOK_macArm_done z n acc (.atom 0) m (by simpa [macCore] using h)

theorem seedOK_macArm_one_m0 (z : K) (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = .ok (t, .atom acc))
    (hdy5 : (encC z (op0 5)).dyck ≠ 0)
    (hdy6 : (encC z (op0 6)).dyck ≠ 0)
    (hdyZ : (encC z (op1 0)).dyck ≠ 0)
    (hdyI : (encC z (op4 (op0 14))).dyck ≠ 0)
    (hdyBatt : (encC z (op0 2)).dyck ≠ 0)
    (hag01 : encC z (.atom 0) ≠ encC z (.atom 1))
    (hdyAdd : (encC z addFromMac).dyck ≠ 0)
    (hdyN : (encC z (op0 30)).dyck ≠ 0) :
    SeedOK z t := by
  have h14 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have h30 := gen_op0 (K := K) (n + 19)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  have hcond := gen_op5 (K := K) (n + 20) h14 h30
  have ihcond := seedOK_gen_op5 (z := z) h14 h30 hcond
    (seedOK_gen_op0 (z := z)
      (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h14)
    (seedOK_gen_op0 (z := z)
      (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) h30)
    (Or.inr hag01) (Or.inr ⟨0, 1, rfl, rfl⟩)
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_macNewSample_m0 (K := K) (n + 5) acc
  have ihns := seedOK_macNewSample_m0 (z := z) (n + 5) acc hns
    hdy5 hdy6 hdyZ hdyI hdyAdd hdyN
  have hbatt := gen_op0 (K := K) (n + 18)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0))
  obtain ⟨doneTree, hdone⟩ :=
    gen_macArm_done (K := K) (n + 13) (.atom acc) (.atom 1) (.atom 0)
  have ihdone := seedOK_macArm_done (z := z) (n + 13)
    (.atom acc) (.atom 1) (.atom 0) hdone
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 16)
    (axis := 4) (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0)) hdone
  have ihslam := seedOK_gen_slam (z := z) hbatt hns
    (macCoreAt_slot4 (.atom acc) (.atom 1) (.atom 1) (.atom 0)) hdone hslam
    (seedOK_gen_op0 (z := z)
      (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 0)) hbatt)
    ihns ihdone hdyBatt
  have hop6 := gen_op6_one (K := K) (n + 21) (c := op0 6) hcond hslam
  have huniq := gen_ok_unique h
    (by simpa [macArm, slam, op0, macNewSample, macCore] using hop6)
  rw [huniq.1]
  exact seedOK_gen_op6_one (z := z) hcond hslam hop6
    (by convert ihcond; simp [htis]) ihslam

theorem seedOK_macArm_one_m1 (z : K) (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      .ok (t, .atom (acc + 1)))
    (hdy5 : (encC z (op0 5)).dyck ≠ 0)
    (hdy6 : (encC z (op0 6)).dyck ≠ 0)
    (hdyZ : (encC z (op1 0)).dyck ≠ 0)
    (hdyA : (encC z (op4 (op0 6))).dyck ≠ 0)
    (hdyI : (encC z (op4 (op0 14))).dyck ≠ 0)
    (hdyBatt : (encC z (op0 2)).dyck ≠ 0)
    (hag01 : encC z (.atom 0) ≠ encC z (.atom 1))
    (hdyAdd : (encC z addFromMac).dyck ≠ 0)
    (hdyN : (encC z (op0 30)).dyck ≠ 0) :
    SeedOK z t := by
  have h14 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have h30 := gen_op0 (K := K) (n + 28)
    (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  have hcond := gen_op5 (K := K) (n + 29) h14 h30
  have ihcond := seedOK_gen_op5 (z := z) h14 h30 hcond
    (seedOK_gen_op0 (z := z)
      (macCoreAt_slot14 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h14)
    (seedOK_gen_op0 (z := z)
      (macCoreAt_slot30 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) h30)
    (Or.inr hag01) (Or.inr ⟨0, 1, rfl, rfl⟩)
  have htis : Noun.tis (.atom 0) (.atom 1) = .atom 1 := tis_atom_ne (by decide)
  rw [htis] at hcond
  obtain ⟨nsTree, hns⟩ := gen_macNewSample_m1 (K := K) (n + 5) acc
  have ihns := seedOK_macNewSample_m1 (z := z) (n + 5) acc hns
    hdy5 hdy6 hdyZ hdyA hdyI hdyBatt hag01 hdyAdd hdyN
  have hbatt := gen_op0 (K := K) (n + 27)
    (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1))
  obtain ⟨doneTree, hdone⟩ :=
    gen_macArm_done (K := K) (n + 22) (.atom (acc + 1)) (.atom 1) (.atom 1)
  have ihdone := seedOK_macArm_done (z := z) (n + 22)
    (.atom (acc + 1)) (.atom 1) (.atom 1) hdone
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) (n + 25)
    (axis := 4) (bHead := .atom 0) (bTail := .atom 2) hbatt hns
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) hdone
  have ihslam := seedOK_gen_slam (z := z) hbatt hns
    (macCoreAt_slot4 (.atom (acc + 1)) (.atom 1) (.atom 1) (.atom 1)) hdone hslam
    (seedOK_gen_op0 (z := z)
      (macCoreAt_slot2 (.atom acc) (.atom 0) (.atom 1) (.atom 1)) hbatt)
    ihns ihdone hdyBatt
  have hop6 := gen_op6_one (K := K) (n + 30) (c := op0 6) hcond hslam
  have huniq := gen_ok_unique h
    (by simpa [macArm, slam, op0, macNewSample, macCore] using hop6)
  rw [huniq.1]
  exact seedOK_gen_op6_one (z := z) hcond hslam hop6
    (by convert ihcond; simp [htis]) ihslam

theorem seedOK_gen_invokeMac {z : K} {n : ℕ}
    {s aH aT nH nT mF acc k m result : Noun}
    {aTree nTree mTree armTree t : NTree (GenComputeRow K)} {res : Noun}
    (ha : genComputeSkeleton (K := K) (n + 2) s (.cell aH aT) = .ok (aTree, acc))
    (hn : genComputeSkeleton (K := K) n s (.cell nH nT) = .ok (nTree, k))
    (hm : genComputeSkeleton (K := K) n s mF = .ok (mTree, m))
    (harm : genComputeSkeleton (K := K) (n + 3) (macCore acc k m) macArm =
      .ok (armTree, result))
    (h : genComputeSkeleton (K := K) (n + 5) s
      (invokeMac (.cell aH aT) (.cell nH nT) mF) = .ok (t, res))
    (iha : SeedOK z aTree) (ihn : SeedOK z nTree) (ihm : SeedOK z mTree)
    (ihaArm : SeedOK z armTree)
    (hdyA : (encC z (.cell aH aT)).dyck ≠ 0)
    (hdyN : (encC z (.cell nH nT)).dyck ≠ 0)
    (hdyZ : (encC z (op1 0)).dyck ≠ 0)
    (hdyQ : (encC z (quote mmBattery)).dyck ≠ 0) :
    SeedOK z t := by
  have hqB := gen_quote (K := K) (n + 2) s mmBattery
  obtain ⟨sfTree, hsf⟩ := gen_macSampleF (K := K) n ha hn hm
  have ihsf := seedOK_gen_macSampleF (z := z) ha hn hm hsf iha ihn ihm hdyA hdyN hdyZ
  obtain ⟨slamTree, _, _, hslam, _, _, _, _, _⟩ := gen_slam (K := K) n (axis := 4)
    (bHead := .atom 1) (bTail := mmBattery) hqB hsf
    (macCoreAt_slot4 acc (.atom 0) k m) harm
  have huniq := gen_ok_unique h
    (by simpa [invokeMac, slam, quote, macCore, macCoreAt] using hslam)
  rw [huniq.1]
  exact seedOK_gen_slam (z := z) hqB hsf
    (macCoreAt_slot4 acc (.atom 0) k m) harm hslam
    (seedOK_gen_quote (z := z) hqB) ihsf ihaArm hdyQ

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54.TraceGen

set_option maxHeartbeats 40000000

theorem one_add_seedZ_sq_ne : 1 + seedZ ^ 2 ≠ 0 := by
  intro h
  have hF : (1 + (8 : F) ^ 2) = 0 :=
    φ_injective (by simpa [seedZ, map_add, map_one, map_pow] using h)
  exact (by decide : (1 + (8 : F) ^ 2) ≠ 0) hF

theorem op4_op0_dyck (ax : ℕ) :
    (encC seedZ (op4 (op0 ax))).dyck ≠ 0 := by
  rw [op4, op0]
  have h := encC_cell_atom_dyck seedZ seedZ_ne_zero 4
    (.cell (.atom 0) (.atom ax))
  rw [h, encC_cell_atom_atom_dyck seedZ seedZ_ne_zero 0 ax]
  exact mul_ne_zero seedZ_ne_zero (by simpa [pow_two] using one_add_seedZ_sq_ne)

theorem op0_2_dyck : (encC seedZ (op0 2)).dyck ≠ 0 :=
  encC_cell_atom_atom_dyck_ne seedZ seedZ_ne_zero 0 2

theorem op0_dyck (ax : ℕ) : (encC seedZ (op0 ax)).dyck ≠ 0 :=
  encC_cell_atom_atom_dyck_ne seedZ seedZ_ne_zero 0 ax

theorem op1_0_dyck : (encC seedZ (op1 0)).dyck ≠ 0 :=
  encC_cell_atom_atom_dyck_ne seedZ seedZ_ne_zero 1 0

theorem addFromMac_dyck : (encC seedZ addFromMac).dyck ≠ 0 :=
  (allCellDyckNe_algebraMap φ_injective addFromMac_allCellDyckNe_base).1

theorem quote_mmBattery_dyck : (encC seedZ (quote mmBattery)).dyck ≠ 0 :=
  (allCellDyckNe_algebraMap φ_injective quote_mmBattery_allCellDyckNe_base).1

theorem encC_zero_ne_one :
    encC seedZ (.atom 0) ≠ encC seedZ (.atom 1) :=
  encC_atom_ne seedZ 0 1 (by simp [Nat.cast_zero, Nat.cast_one])

theorem seedOK_addArm_one_seed (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 16)
      (addCore (.atom acc) (.atom 0) (.atom 1)) addArm =
      .ok (t, .atom (acc + 1))) :
    SeedOK seedZ t :=
  seedOK_addArm_one seedZ n acc h
    (op4_op0_dyck 6) (op4_op0_dyck 14) op0_2_dyck encC_zero_ne_one

theorem seedOK_macArm_one_m0_seed (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 22)
      (macCore (.atom acc) (.atom 1) (.atom 0)) macArm = .ok (t, .atom acc)) :
    SeedOK seedZ t :=
  seedOK_macArm_one_m0 seedZ n acc h
    (op0_dyck 5) (op0_dyck 6) op1_0_dyck (op4_op0_dyck 14)
    op0_2_dyck encC_zero_ne_one addFromMac_dyck (op0_dyck 30)

theorem seedOK_macArm_one_m1_seed (n acc : ℕ)
    {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 31)
      (macCore (.atom acc) (.atom 1) (.atom 1)) macArm =
      .ok (t, .atom (acc + 1))) :
    SeedOK seedZ t :=
  seedOK_macArm_one_m1 seedZ n acc h
    (op0_dyck 5) (op0_dyck 6) op1_0_dyck (op4_op0_dyck 6) (op4_op0_dyck 14)
    op0_2_dyck encC_zero_ne_one addFromMac_dyck (op0_dyck 30)

theorem cell_op1_0_dyck :
    (encC seedZ (.cell (.atom 1) (.atom 0))).dyck ≠ 0 := by
  simpa [op1] using op1_0_dyck

theorem cell_op0_dyck (ax : ℕ) :
    (encC seedZ (.cell (.atom 0) (.atom ax))).dyck ≠ 0 := by
  simpa [op0] using op0_dyck ax

theorem mmC01_allCellDyckNe : AllCellDyckNe seedZ mmC01 :=
  allCellDyckNe_algebraMap φ_injective mmC01_allCellDyckNe_base
theorem mmC10_allCellDyckNe : AllCellDyckNe seedZ mmC10 :=
  allCellDyckNe_algebraMap φ_injective mmC10_allCellDyckNe_base
theorem mmC11_allCellDyckNe : AllCellDyckNe seedZ mmC11 :=
  allCellDyckNe_algebraMap φ_injective mmC11_allCellDyckNe_base

/-- Acc-formula of the outer MAC is the inner `invokeMac` -/
theorem mac2_inner_all {accF nF mF nF' mF' : Noun}
    (h : AllCellDyckNe seedZ (mac2 accF nF mF nF' mF')) :
    AllCellDyckNe seedZ (invokeMac accF nF mF) := by
  have hcell : AllCellDyckNe seedZ
      (.cell (.atom 7)
        (.cell (.cell (quote mmBattery)
          (.cell (invokeMac accF nF mF)
            (.cell (op1 0) (.cell nF' mF'))))
          (invokeAxis 4))) := by
    simpa [mac2, invokeMac, slam, op7, quote, op1] using h
  exact allCellDyckNe_left (allCellDyckNe_right (allCellDyckNe_left
    (allCellDyckNe_right hcell)))

theorem invokeMac_dyck (accF nF mF : Noun)
    (h : AllCellDyckNe seedZ (invokeMac accF nF mF)) :
    (encC seedZ (invokeMac accF nF mF)).dyck ≠ 0 := by
  simpa [invokeMac, slam, op7] using
    allCellDyckNe_cell (by simpa [invokeMac, slam, op7] using h)

theorem mmC00_inner_dyck :
    (encC seedZ (invokeMac (op1 0) (op0 8) (op0 12))).dyck ≠ 0 :=
  invokeMac_dyck _ _ _ (mac2_inner_all (by simpa [mmC00] using mmC00_allCellDyckNe))
theorem mmC01_inner_dyck :
    (encC seedZ (invokeMac (op1 0) (op0 8) (op0 13))).dyck ≠ 0 :=
  invokeMac_dyck _ _ _ (mac2_inner_all (by simpa [mmC01] using mmC01_allCellDyckNe))
theorem mmC10_inner_dyck :
    (encC seedZ (invokeMac (op1 0) (op0 10) (op0 12))).dyck ≠ 0 :=
  invokeMac_dyck _ _ _ (mac2_inner_all (by simpa [mmC10] using mmC10_allCellDyckNe))
theorem mmC11_inner_dyck :
    (encC seedZ (invokeMac (op1 0) (op0 10) (op0 13))).dyck ≠ 0 :=
  invokeMac_dyck _ _ _ (mac2_inner_all (by simpa [mmC11] using mmC11_allCellDyckNe))

theorem mmC00_dyck : (encC seedZ mmC00).dyck ≠ 0 := mmC00_allCellDyckNe.1
theorem mmC01_dyck : (encC seedZ mmC01).dyck ≠ 0 := mmC01_allCellDyckNe.1
theorem mmC10_dyck : (encC seedZ mmC10).dyck ≠ 0 := mmC10_allCellDyckNe.1
theorem mmC11_dyck : (encC seedZ mmC11).dyck ≠ 0 := mmC11_allCellDyckNe.1

theorem mmFormula_left_dyck :
    (encC seedZ (.cell mmC00 mmC01)).dyck ≠ 0 :=
  allCellDyckNe_cell (allCellDyckNe_left mmFormula_allCellDyckNe)
theorem mmFormula_right_dyck :
    (encC seedZ (.cell mmC10 mmC11)).dyck ≠ 0 :=
  allCellDyckNe_cell (allCellDyckNe_right mmFormula_allCellDyckNe)

theorem seedOK_mmC00 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC00 =
      .ok (t, .atom 2)) :
    SeedOK seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA⟩ := gen_macArm_one_m1 (K := K) (n + 20) 0
  have ihInnerArm := seedOK_macArm_one_m1_seed (n + 20) 0 innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 12) ha0 a00 b00 innerA
  have ihInner := seedOK_gen_invokeMac (z := seedZ) ha0 a00 b00 innerA hinner
    (seedOK_gen_op1 (z := seedZ) ha0)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot8 a00)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot12 b00)
    ihInnerArm cell_op1_0_dyck (cell_op0_dyck 8) op1_0_dyck quote_mmBattery_dyck
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 1
  have ihOuterArm := seedOK_macArm_one_m1_seed (n + 23) 1 outerA
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
  exact seedOK_gen_invokeMac (z := seedZ) hinner' a01 b10 outerA houter
    ihInner
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot9 a01)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot14 b10)
    ihOuterArm
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using mmC00_inner_dyck)
    (cell_op0_dyck 9) op1_0_dyck quote_mmBattery_dyck

theorem seedOK_mmC01 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC01 =
      .ok (t, .atom 1)) :
    SeedOK seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a00 := gen_op0 (K := K) (n + 47) mmSubject_slot8
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA⟩ := gen_macArm_one_m0 (K := K) (n + 29) 0
  have ihInnerArm := seedOK_macArm_one_m0_seed (n + 29) 0 innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 8)
    (mF := op0 13) ha0 a00 b01 innerA
  have ihInner := seedOK_gen_invokeMac (z := seedZ) ha0 a00 b01 innerA hinner
    (seedOK_gen_op1 (z := seedZ) ha0)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot8 a00)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot13 b01)
    ihInnerArm cell_op1_0_dyck (cell_op0_dyck 8) op1_0_dyck quote_mmBattery_dyck
  have a01 := gen_op0 (K := K) (n + 50) mmSubject_slot9
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := seedOK_macArm_one_m1_seed (n + 23) 0 outerA
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
  exact seedOK_gen_invokeMac (z := seedZ) hinner' a01 b11 outerA houter
    ihInner
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot9 a01)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot15 b11)
    ihOuterArm
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using mmC01_inner_dyck)
    (cell_op0_dyck 9) op1_0_dyck quote_mmBattery_dyck

theorem seedOK_mmC10 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC10 =
      .ok (t, .atom 1)) :
    SeedOK seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b00 := gen_op0 (K := K) (n + 47) mmSubject_slot12
  obtain ⟨innerArm, innerA⟩ := gen_macArm_zero (K := K) (n + 45) (.atom 0) (.atom 1)
  have ihInnerArm := seedOK_macArm_zero seedZ (n + 45) (.atom 0) (.atom 1) innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 12) ha0 a10 b00 innerA
  have ihInner := seedOK_gen_invokeMac (z := seedZ) ha0 a10 b00 innerA hinner
    (seedOK_gen_op1 (z := seedZ) ha0)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot10 a10)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot12 b00)
    ihInnerArm cell_op1_0_dyck (cell_op0_dyck 10) op1_0_dyck quote_mmBattery_dyck
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b10 := gen_op0 (K := K) (n + 50) mmSubject_slot14
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := seedOK_macArm_one_m1_seed (n + 23) 0 outerA
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
  exact seedOK_gen_invokeMac (z := seedZ) hinner' a11 b10 outerA houter
    ihInner
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot11 a11)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot14 b10)
    ihOuterArm
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using mmC10_inner_dyck)
    (cell_op0_dyck 11) op1_0_dyck quote_mmBattery_dyck

theorem seedOK_mmC11 (n : ℕ) {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) (n + 56) mmSubject mmC11 =
      .ok (t, .atom 1)) :
    SeedOK seedZ t := by
  have ha0 := gen_op1 (K := K) (n + 49) mmSubject 0
  have a10 := gen_op0 (K := K) (n + 47) mmSubject_slot10
  have b01 := gen_op0 (K := K) (n + 47) mmSubject_slot13
  obtain ⟨innerArm, innerA⟩ := gen_macArm_zero (K := K) (n + 45) (.atom 0) (.atom 0)
  have ihInnerArm := seedOK_macArm_zero seedZ (n + 45) (.atom 0) (.atom 0) innerA
  obtain ⟨hinnerT, _, _, hinner, _, _, _, _⟩ := gen_invokeMac (K := K) (n + 48)
    (aH := .atom 1) (aT := .atom 0) (nH := .atom 0) (nT := .atom 10)
    (mF := op0 13) ha0 a10 b01 innerA
  have ihInner := seedOK_gen_invokeMac (z := seedZ) ha0 a10 b01 innerA hinner
    (seedOK_gen_op1 (z := seedZ) ha0)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot10 a10)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot13 b01)
    ihInnerArm cell_op1_0_dyck (cell_op0_dyck 10) op1_0_dyck quote_mmBattery_dyck
  have a11 := gen_op0 (K := K) (n + 50) mmSubject_slot11
  have b11 := gen_op0 (K := K) (n + 50) mmSubject_slot15
  obtain ⟨outerArm, outerA⟩ := gen_macArm_one_m1 (K := K) (n + 23) 0
  have ihOuterArm := seedOK_macArm_one_m1_seed (n + 23) 0 outerA
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
  exact seedOK_gen_invokeMac (z := seedZ) hinner' a11 b11 outerA houter
    ihInner
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot11 a11)
    (seedOK_gen_op0 (z := seedZ) mmSubject_slot15 b11)
    ihOuterArm
    (by simpa [invokeMac, slam, op7, quote, op1, op0] using mmC11_inner_dyck)
    (cell_op0_dyck 11) op1_0_dyck quote_mmBattery_dyck

theorem seedOK_mm {t : NTree (GenComputeRow K)}
    (h : genComputeSkeleton (K := K) 64 mmSubject mmFormula = .ok (t, mmC)) :
    SeedOK seedZ t := by
  obtain ⟨t00, h00⟩ := gen_mmC00 (K := K) 6
  obtain ⟨t01, h01⟩ := gen_mmC01 (K := K) 6
  obtain ⟨t10, h10⟩ := gen_mmC10 (K := K) 6
  obtain ⟨t11, h11⟩ := gen_mmC11 (K := K) 6
  have ih00 := seedOK_mmC00 6 h00
  have ih01 := seedOK_mmC01 6 h01
  have ih10 := seedOK_mmC10 6 h10
  have ih11 := seedOK_mmC11 6 h11
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
  exact seedOK_gen_cons (z := seedZ) hL hR hop
    (seedOK_gen_cons (z := seedZ) h00c h01c hL ih00 ih01
      (by simpa [mmC00, mac2, invokeMac, slam, op7, quote, op1, op0] using mmC00_dyck))
    (seedOK_gen_cons (z := seedZ) h10c h11c hR ih10 ih11
      (by simpa [mmC10, mac2, invokeMac, slam, op7, quote, op1, op0] using mmC10_dyck))
    (by simpa [mmC00, mmC01, mac2, invokeMac, slam, op7, quote, op1, op0]
      using mmFormula_left_dyck)

theorem mmTree_seedOK : SeedOK seedZ (mmTree (K := K)) :=
  seedOK_mm (mmTree_gen (K := K))

/-- Autocons emission always stores the axis-3 tail request. -/
theorem gen_ok_cons_request {n : ℕ} {s lh lt tail : Noun}
    {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) (n + 1) s (.cell (.cell lh lt) tail) =
      .ok (t, r)) :
    t.label.requests = [⟨.cell (.cell lh lt) tail, tail, 3, 0⟩] := by
  revert h
  simp only [genComputeSkeleton]
  cases genComputeSkeleton (K := K) n s (.cell lh lt) with
  | error _ =>
    intro h; cases h
  | ok pL =>
    cases genComputeSkeleton (K := K) n s tail with
    | error _ =>
      intro h; cases h
    | ok pR =>
      intro h
      injection h with hp
      injection hp with ht _
      subst t
      simp [skelNode]

/-- Root cons of the four MAC branches issues one axis-3 tail request. -/
theorem mmTree_root_request_shape :
    ∃ hd tl, (mmTree (K := K)).label.requests =
      [⟨.cell hd tl, tl, 3, 0⟩] := by
  have h := mmTree_gen (K := K)
  simp only [mmFormula] at h
  exact ⟨.cell mmC00 mmC01, .cell mmC10 mmC11, gen_ok_cons_request (n := 63) h⟩

theorem mm_computeRowsAccepted :
    (exec seedZ alphaA).ComputeRowsAccepted :=
  computeRowsAccepted_of_seed seedZ alphaA seedZ_ne_zero
    (fun v hv hcons => (mmTree_seedOK v hv).2.1 hcons)
    (fun v hv hs5 => (mmTree_seedOK v hv).2.2.1 hs5)
    (fun v hv hs3 => op3CallSizeOk_of_not_s3 (mmTree_seedOK v hv).1 hs3)

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.seedOK_addArm_done
#print axioms Nock.NockVMROM.Thm54.TraceGen.seedOK_macArm_one_m1
#print axioms Nock.NockVMROM.Thm54.TraceGen.seedOK_gen_invokeMac
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.seedOK_mmC00
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mmTree_seedOK
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mmTree_root_request_shape
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.mm_computeRowsAccepted
