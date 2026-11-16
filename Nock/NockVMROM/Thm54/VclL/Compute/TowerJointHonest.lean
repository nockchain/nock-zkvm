import Nock.NockVMROM.Thm54.VclL.Compute.TowerCompFamilyT
import Nock.NockVMROM.Thm54.VclL.Compute.TowerLookupHonest
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemHonest
import Nock.NockVMROM.Thm54.VclL.Chips.MemSoundnessVCL
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMem

/-!
# The joint compute-memory honest datum

From ONE generator run (`HC : HonestVCLT`) the
memory datum `jointMem HC hf : HonestVCL` with the SAME `V` and `d := demT HC.t` (the demand of the run).
`honestV_eq` is `rfl`; `honestReq_eq` is `req_zero` at index 0 and `honestReqCF_eq_req` at 1, 2 with `hslot`
PROVED from the run (`demT_slot`: `genComputeSkeleton_tree_requests_wf` through `airReorder` and the BFS
labelling) and `vReqs = []` (`rfl`).  The memory-side numeric facts of `HonestVCL` (`JointMemFacts`) are about
the verifier datum and the run's demand, not about the compute trace, and are taken as a Prop-structure.
No `hdeep` is used.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.VclL.Chips Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

noncomputable section

section Joint
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] [Fintype F] (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))]
  {hT hP hC : ℕ}

/-- SHD-A merge: a row's slot-kind keys (export or path) are among its slot keys. -/
theorem rowKeysAt_sub {L : Type} [Field L] (acc : AccVCL) (g : GenComputeRow L) {r : Noun × ℕ}
    (hr : r ∈ rowKeysAt acc g) : r ∈ rowSlotKeys g := by
  simp only [rowKeysAt, List.mem_filterMap, List.mem_filter] at hr
  obtain ⟨j, -, hj⟩ := hr
  exact List.mem_of_getElem? hj

/-- SHD-A merge: every key of the run's demand (export reads or path reads) is a slot key of a
generated row. -/
theorem demT_key_mem {L : Type} [Field L] {t : NTree (GenComputeRow L)} {r : Noun × ℕ}
    (hr : r ∈ (demandOfRowsD ((List.range' 1 (Walk.bfsForest [airReorder t]).length).map
      (bfsLabelAt (airReorder t)))).reads ∨
      r ∈ (demandOfRowsD ((List.range' 1 (Walk.bfsForest [airReorder t]).length).map
      (bfsLabelAt (airReorder t)))).preads) :
    ∃ g ∈ (List.range' 1 (Walk.bfsForest [airReorder t]).length).map (bfsLabelAt (airReorder t)),
      r ∈ rowSlotKeys g := by
  simp only [demandOfRowsD, List.mem_flatMap] at hr
  rcases hr with ⟨g, hg, h⟩ | ⟨g, hg, h⟩
  · exact ⟨g, hg, rowKeysAt_sub _ g h⟩
  · exact ⟨g, hg, rowKeysAt_sub _ g h⟩

/-- **`hslot`, from the run**: every request of every generated row has a defined `Noun.slot`
(the generator's `OP_0`/`OP_9` arms fire only when it succeeds; every other arm emits axis 2 / 3 on a cell).
SHD-A merge: stated over the path-kind reads `pathReads (demT t).preads`. -/
theorem demT_slot_of_gen {fuel : ℕ} {S Fm R : Noun}
    {t : NTree (GenComputeRow (Quad (algebraMap F K δF)))}
    (hgen : genComputeSkeleton (K := Quad (algebraMap F K δF)) fuel S Fm = .ok (t, R)) :
    ∀ r ∈ pathReads (demT t).preads, (Noun.slot r.2 r.1).isSome := by
  intro r hr
  have hwf : treeRequestsWF (airReorder t) :=
    treeRequestsWF_airReorder (genComputeSkeleton_tree_requests_wf hgen)
  unfold pathReads at hr
  rw [List.mem_dedup, List.mem_filter] at hr
  obtain ⟨g, hg, hrg⟩ := demT_key_mem (t := t) (Or.inr hr.1)
  simp only [List.mem_map] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hi' := lt_bfsRows_of_mem_range' (t := airReorder t) hi
  simp only [rowSlotKeys, List.mem_map] at hrg
  obtain ⟨req, hreq, rfl⟩ := hrg
  rw [bfsLabelAt_requests _ i hi'] at hreq
  have hlen : i - 1 < (bfsForest [airReorder t]).length := by
    rwa [← bfsRows_length]
  have hnode : (bfsForest [airReorder t])[i - 1] ∈ bfsForest [airReorder t] := List.getElem_mem _
  have hin : InTree (airReorder t) (bfsForest [airReorder t])[i - 1] := by
    rcases (mem_bfsForest [airReorder t] _).mp hnode with ⟨c, hc, hIn⟩
    simp only [List.mem_singleton] at hc
    subst c
    exact hIn
  have hreq' : req ∈ (bfsForest [airReorder t])[i - 1].label.requests := by
    have : (bfsRows (airReorder t))[i - 1] = (bfsForest [airReorder t])[i - 1].label := by
      simp [bfsRows]
    simpa [this] using hreq
  have := (hwf _ hin req hreq').2
  simp [this]

theorem demT_slot (HC : HonestVCLT F K δF hC (ChipRAP.shapeV hT hP)) :
    ∀ r ∈ pathReads (demT HC.t).preads, (Noun.slot r.2 r.1).isSome :=
  demT_slot_of_gen δF HC.hgen

variable (hT hP hC) in
/-- **The memory-side facts of `HonestVCL`** at the run's verifier datum and demand (about `V` and the demand;
none concerns the compute trace). -/
structure JointMemFacts (HC : HonestVCLT F K δF hC (ChipRAP.shapeV hT hP)) : Prop where
  hF : GeneratedField.PrimeFieldElems F
  hq : 2 ^ 63 < ringChar F
  hrows : ∀ t, HC.V.memRows t + 1 < ringChar F
  hadj : ∀ t, HC.V.AdjacentM t
  hinj : ∀ t, Function.Injective (HC.V.memNodes t)
  hrank : ∀ n ∈ (demT HC.t).cells, rankOf n < 2 ^ 110
  h62 : ∀ r ∈ pathReads (demT HC.t).preads, depthOf r.2 ≤ 62
  hC0 : HC.V.memRows (tC hT hP) = (demT HC.t).cells.length
  hP0 : HC.V.memRows (tP hT hP) =
    (pathTableP δF (0 : Quad (algebraMap F K δF)) (demT HC.t).cells (demT HC.t).preads).length

/-- **The joint builder**: the memory honest datum of the SAME run (`V := HC.V`, `d := demT HC.t`). -/
def jointMem (HC : HonestVCLT F K δF hC (ChipRAP.shapeV hT hP)) (hf : JointMemFacts δF hT hP hC HC) :
    HonestVCL (K := K) δF hT hP hC where
  V := HC.V
  d := demT HC.t
  hF := hf.hF
  hq := hf.hq
  hrows := hf.hrows
  hadj := hf.hadj
  hinj := hf.hinj
  hrank := hf.hrank
  h62 := hf.h62
  hC0 := hf.hC0
  hP0 := hf.hP0

/-- **`honestV_eq`**: the two honest verifier data are the same. -/
theorem jointMem_honestV (HC : HonestVCLT F K δF hC (ChipRAP.shapeV hT hP)) (hf : JointMemFacts δF hT hP hC HC) :
    (compSoundnessVCLT F K hC (ChipRAP.shapeV hT hP) δF).honestV HC =
      (memSoundnessVCL (K := K) δF hT hP (hC := hC) (C := tableVCLT hC)).honestV (jointMem δF HC hf) := rfl

/-- **`honestReq_eq`**: the two honest request vectors agree at every coin vector and accumulator. -/
theorem jointMem_honestReq (HC : HonestVCLT F K δF hC (ChipRAP.shapeV hT hP)) (hf : JointMemFacts δF hT hP hC HC) :
    (compSoundnessVCLT F K hC (ChipRAP.shapeV hT hP) δF).honestReq HC =
      (memSoundnessVCL (K := K) δF hT hP (hC := hC) (C := tableVCLT hC)).honestReq (jointMem δF HC hf) := by
  funext χ a
  show reqT HC.t χ a = (jointMem δF HC hf).req χ a
  rw [honestReqCF_eq_req (jointMem δF HC hf) χ (demT_slot δF HC) rfl a]
  rfl

end Joint

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
