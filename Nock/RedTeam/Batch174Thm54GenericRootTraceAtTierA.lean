/-
  Nock/RedTeam/Batch174Thm54GenericRootTraceAtTierA.lean

  **Instantiation check for the generic `RootTrace` builder**.

  `GenServedRootTrace.rootTraceOfRecordTree` builds `RootTrace cfg exec i` for a one-record forest
  root at an ARBITRARY axis, from the generic descent bundle.  A generic theorem is not done until a
  live configuration's own obligation is re-derived from it, so this batch

  1. rebuilds `DotConfig769`'s forest root 1 — the object `DotConfig769.rootTrace1` inhabits by hand
     — from the generic builder, with the type checked by the elaborator;
  2. exhibits the read/verify exponent computation at axis `5` and axis `7`, i.e. OUTSIDE the
     `{2, 3}` window in which `GenTierAMemoryTrace`'s walk theory was proved.  That is the
     non-vacuity witness for the generalization: the axis-2/axis-3 lemmas cannot state it.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedRootTrace
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMemoryTrace

namespace Nock.RedTeam.Batch174

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.TraceGen
  (axisMTree mappedRecordTree servedGen encC genAnnotatedRecordTree
   axisTopBit axisRest axisPath_three readExps_recordTree verifyExps_recordTree
   genAnnotatedRecordTree_servedGen rootTraceOfRecordTree axisPath_cons
   dotBranchPair dotThenFormula dotFormula dotParentTail dotCondFormula
   rootTraceOfChainedPair genAnnotatedChainedTree chain32Root
   genAnnotatedChainedTree_axis3_axis2_eq genAnnotatedDescentCont
   servedGen_descentCont GenMemoryRow)
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769

noncomputable section

/-! ## 1. `axisPath` really is the builder's top-bit descent -/

theorem b174_axisPath_five : axisPath 5 = [false, true] := by
  rw [axisPath_cons (by norm_num)]
  · rw [show axisTopBit 5 = false from by decide,
      show axisRest 5 = 3 from by decide, axisPath_three]

theorem b174_axisPath_seven : axisPath 7 = [true, true] := by
  rw [axisPath_cons (by norm_num)]
  · rw [show axisTopBit 7 = true from by decide,
      show axisRest 7 = 3 from by decide, axisPath_three]

/-- The paper's own round trip at an axis the fixture never uses. -/
theorem b174_pathAxis_five : pathAxis (axisPath 5) = 5 :=
  pathAxis_axisPath 5 (by norm_num)

/-! ## 2. Non-vacuity: the record tree at axes outside `{2, 3}`

`GenTierAMemoryTrace.readExps_recordTree_axis2` / `_axis3` cannot state either of these. -/

/-- A concrete depth-2 subject: `slot 5` is the head of the tail. -/
def b174Subject : Noun :=
  .cell (.cell (.atom 1) (.atom 2)) (.cell (.atom 3) (.atom 4))

theorem b174_slot_five : Noun.slot 5 b174Subject = some (.atom 2) := by
  simp [b174Subject, Noun.slot]

theorem b174_slot_seven : Noun.slot 7 b174Subject = some (.atom 4) := by
  simp [b174Subject, Noun.slot]

theorem b174_readExps_axis5 (e : ℕ) :
    readExps (axisMTree alphaA
        (mappedRecordTree (encC seedZ) seedZ alphaA formRDefault b174Subject (.atom 2) 5 e)) =
      [timestampExp alphaA (alphaA ^ e)] :=
  readExps_recordTree (cfg := cfg seedZ alphaA) (exec := execThreadedA seedZ alphaA)
    (encC seedZ) seedZ alphaA b174Subject (.atom 2) 5 e b174_slot_five rfl

theorem b174_verifyExps_axis5 (e : ℕ) :
    verifyExps (axisMTree alphaA
        (mappedRecordTree (encC seedZ) seedZ alphaA formRDefault b174Subject (.atom 2) 5 e)) =
      [timestampExp alphaA (alphaA ^ e)] :=
  verifyExps_recordTree (cfg := cfg seedZ alphaA) (exec := execThreadedA seedZ alphaA)
    (encC seedZ) seedZ alphaA b174Subject (.atom 2) 5 e b174_slot_five rfl

theorem b174_readExps_axis7 (e : ℕ) :
    readExps (axisMTree alphaA
        (mappedRecordTree (encC seedZ) seedZ alphaA formRDefault b174Subject (.atom 4) 7 e)) =
      [timestampExp alphaA (alphaA ^ e)] :=
  readExps_recordTree (cfg := cfg seedZ alphaA) (exec := execThreadedA seedZ alphaA)
    (encC seedZ) seedZ alphaA b174Subject (.atom 4) 7 e b174_slot_seven rfl

theorem b174_servedGen_axis5 (e : ℕ) :
    servedGen [genAnnotatedRecordTree (encC seedZ) seedZ alphaA formRDefault b174Subject (.atom 2) 5 e] =
      [⟨encC seedZ b174Subject, encC seedZ (.atom 2), (5 : K), alphaA ^ e⟩] :=
  genAnnotatedRecordTree_servedGen _ _ _ _ _ _ _

/-! ## 3. `DotConfig769`'s own forest root 1, rebuilt from the generic builder -/

theorem b174_slot_two : Noun.slot 2 dotBranchPair = some dotThenFormula := by
  simp [dotBranchPair, Noun.slot]

theorem b174_axis_at_one :
    exactAxisTree (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 1)
      = axisMTree (cfg seedZ alphaA).challenges.α
          (mappedRecordTree (encC seedZ) seedZ (cfg seedZ alphaA).challenges.α formRDefault
            dotBranchPair dotThenFormula 2 3) := by
  rw [axis_at (memIdx 1)]
  simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
  rfl

theorem b174_served_at_one :
    rootResponseRecords (execThreadedA seedZ alphaA) (memIdx 1)
      = servedGen [genAnnotatedRecordTree (encC seedZ) seedZ
          (cfg seedZ alphaA).challenges.α formRDefault dotBranchPair dotThenFormula 2 3] := by
  rw [served_at (memIdx 1)]
  simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
  rfl

/-- **The generic builder inhabits `DotConfig769`'s own root-1 obligation.** -/
def b174_rootTrace1 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 1) :=
  rootTraceOfRecordTree (encC seedZ) seedZ dotBranchPair dotThenFormula 2 3
    service3 rfl rfl rfl (service_hexp _ _ _ _ _ _) rfl b174_slot_two
    b174_axis_at_one b174_served_at_one

/-- Same type as the hand-built one, checked by the elaborator. -/
theorem b174_type_matches :
    (b174_rootTrace1 : RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 1))
      = b174_rootTrace1 := rfl

/-- Both carry the same single service, so the generic route reproduces the fixture's data. -/
theorem b174_services_agree :
    b174_rootTrace1.services = rootTrace1.services := rfl

theorem b174_subject_agrees :
    b174_rootTrace1.subject = rootTrace1.subject := rfl

/-! ## 4. The chained pair: `DotConfig769`'s forest root 0, rebuilt generically -/

/-- The continuation descent transports `servedGen` at an axis the fixture never uses. -/
theorem b174_descentCont_servedGen_axis5
    (c : NTree (GenMemoryRow K)) (contCell : MemoryTable.Cell K)
    (contState : MemoryTable.MState) :
    ∀ u ∈ (genAnnotatedDescentCont (encC seedZ) seedZ formRDefault [c] contCell contState
        b174Subject 5).1,
      servedGen [u] = servedGen [c] :=
  servedGen_descentCont (encC seedZ) seedZ c contCell contState 5 b174Subject

theorem b174_slot_three_formula :
    Noun.slot 3 dotFormula = some dotParentTail := by
  simp [dotFormula, Noun.slot]

theorem b174_slot_two_tail :
    Noun.slot 2 dotParentTail = some dotCondFormula := by
  simp [dotParentTail, Noun.slot]

theorem b174_chain_gen :
    genAnnotatedChainedTree (encC seedZ) seedZ (cfg seedZ alphaA).challenges.α formRDefault
        [⟨dotFormula, dotParentTail, 3, 1⟩, ⟨dotParentTail, dotCondFormula, 2, 2⟩]
      = some (chain32Root (lmb := formRDefault) (encC seedZ) seedZ alphaA
          (.atom 6) dotCondFormula dotBranchPair 1 2) :=
  genAnnotatedChainedTree_axis3_axis2_eq (lmb := formRDefault) (encC seedZ) seedZ alphaA
    (.atom 6) dotCondFormula dotBranchPair 1 2

theorem b174_axis_at_zero :
    exactAxisTree (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 0)
      = axisMTree (cfg seedZ alphaA).challenges.α
          (mapNTree GenMemoryRow.row (chain32Root (lmb := formRDefault) (encC seedZ) seedZ alphaA
            (.atom 6) dotCondFormula dotBranchPair 1 2)) := by
  rw [axis_at (memIdx 0)]
  simp only [forestTrees, memIdx, List.getElem_cons_zero]
  rfl

theorem b174_served_at_zero :
    rootResponseRecords (execThreadedA seedZ alphaA) (memIdx 0)
      = servedGen [chain32Root (lmb := formRDefault) (encC seedZ) seedZ alphaA
          (.atom 6) dotCondFormula dotBranchPair 1 2] := by
  rw [served_at (memIdx 0)]
  simp only [forestTrees, memIdx, List.getElem_cons_zero]

/-- **The generic chained builder inhabits `DotConfig769`'s own root-0 obligation.** -/
def b174_rootTrace0 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 0) :=
  rootTraceOfChainedPair (encC seedZ) seedZ
    ⟨dotFormula, dotParentTail, 3, 1⟩ ⟨dotParentTail, dotCondFormula, 2, 2⟩
    _ b174_chain_gen rfl service1 service2
    rfl rfl rfl (service_hexp _ _ _ _ _ _) rfl
    rfl rfl rfl (service_hexp _ _ _ _ _ _) rfl
    b174_slot_three_formula b174_slot_two_tail
    (timestampExp_ne (by decide) (by decide) (by decide))
    b174_axis_at_zero b174_served_at_zero

theorem b174_chain_services_agree :
    b174_rootTrace0.services = rootTrace0.services := rfl

theorem b174_chain_subject_agrees :
    b174_rootTrace0.subject = rootTrace0.subject := rfl

end

#print axioms b174_axisPath_five
#print axioms b174_pathAxis_five
#print axioms b174_readExps_axis5
#print axioms b174_verifyExps_axis5
#print axioms b174_readExps_axis7
#print axioms b174_servedGen_axis5
#print axioms b174_rootTrace1
#print axioms b174_services_agree
#print axioms b174_subject_agrees
#print axioms b174_descentCont_servedGen_axis5
#print axioms b174_rootTrace0
#print axioms b174_chain_services_agree
#print axioms b174_chain_subject_agrees

end Nock.RedTeam.Batch174
