/-
  Nock/NockVMROM/Thm54/TraceGen/GenTierAMemoryTrace.lean

  Generic `ServiceWalk` on the annotated noun-walk / axis-2 / axis-3 record
  trees the generator emits, then the same-execution `ExactServedMemoryTrace`
  on AIR-ordered `DotConfig769`.

  The walk is noun-indexed: halt at atoms, decompose at cells, and a single
  `read`/`verify` pair at each served record.

  They were
  moved because three independent sessions read this file's name as a scope claim and treated
  them as Tier A-only. Names and statements are unchanged and the
  namespace is the same, so uses here resolve exactly as before.

  What *is* Tier A-specific in this file, and stays: the `serviceWalk_recordTree_axis2` / `_axis3`
  lemmas carry `haxis : s.axis = 2` / `= 3`, the `mappedChain32` /
  `chain32*` block is the fixture's chained tree, and the `DotConfig769` namespace at the end is
  the AIR-ordered carrier.

  -- the paper
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericRowFacts
import Nock.NockVMROM.Thm54.TraceGen.GenTierASemanticData
import Nock.NockVMROM.Thm54.TraceGen.GenTierATopology
import Nock.NockVMROM.Thm54.BoundSemanticTrace
import Nock.NockVMROM.Thm54.ServedMemoryTrace
import Nock.NockVMROM.Thm54.AxisSoundness
import Nock.NockVMROM.Thm54.MonolithicRowLayout

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.TraceGen

variable {K : Type} [Field K]

-- Form R `λ` (generic lemmas; 28th λ-fix).
variable {lmb : K}

/-! ## Mapped annotated trees -- the paper -/

noncomputable def mappedNounWalk (E : Noun → ComputeTable.FP K) (z lmb : K) (n : Noun) :
    NTree (MState × DTmem K) :=
  mapNTree GenMemoryRow.row (genAnnotatedNounWalk E z lmb n).1

theorem mappedNounWalk_atom (E : Noun → ComputeTable.FP K) (z : K) (a : ℕ) :
    mappedNounWalk E z lmb (.atom a) =
      .node (MState.halt, (memInputs z, op9HaltPub E a)) [] := by
  simp [mappedNounWalk, genAnnotatedNounWalk, mapNTree, gMemRow9, memHaltSkel]

theorem axisMTree_nounWalk_atom (E : Noun → ComputeTable.FP K) (z α : K) (a : ℕ) :
    axisMTree α (mappedNounWalk E z lmb (.atom a)) = .halt := by
  rw [mappedNounWalk_atom, axisMTree, ofNTree_halt]
  rfl

theorem mappedNounWalk_cell (E : Noun → ComputeTable.FP K) (z : K) (h t : Noun) :
    mappedNounWalk E z lmb (.cell h t) =
      .node (MState.decompose,
          (memInputs z,
            annotatedDecPub E (.cell h t) h t
              (genAnnotatedNounWalk E z lmb h).2 (genAnnotatedNounWalk E z lmb t).2
              (nounWalkRootState h) (nounWalkRootState t) 0 0 lmb))
        [mappedNounWalk E z lmb h, mappedNounWalk E z lmb t] := by
  simp [mappedNounWalk, genAnnotatedNounWalk, mapNTree, gMemRow9, memDecomposeSkel]

theorem axisMTree_nounWalk_cell (E : Noun → ComputeTable.FP K) (z α : K)
    (h t : Noun) :
    axisMTree α (mappedNounWalk E z lmb (.cell h t)) =
      .decompose (axisMTree α (mappedNounWalk E z lmb h))
        (axisMTree α (mappedNounWalk E z lmb t)) := by
  rw [mappedNounWalk_cell, axisMTree, ofNTree_decompose]
  rfl

theorem readCount_nounWalk (E : Noun → ComputeTable.FP K) (z α : K) (e : ℕ) :
    ∀ n, readCount e (axisMTree α (mappedNounWalk E z lmb n)) = 0
  | .atom a => by simp [axisMTree_nounWalk_atom]
  | .cell h t => by
      simp [axisMTree_nounWalk_cell, readCount,
        readCount_nounWalk E z α e h, readCount_nounWalk E z α e t]

theorem verifyCount_nounWalk (E : Noun → ComputeTable.FP K) (z α : K) (e : ℕ) :
    ∀ n, verifyCount e (axisMTree α (mappedNounWalk E z lmb n)) = 0
  | .atom a => by simp [axisMTree_nounWalk_atom]
  | .cell h t => by
      simp [axisMTree_nounWalk_cell, verifyCount,
        verifyCount_nounWalk E z α e h, verifyCount_nounWalk E z α e t]

variable {F : Type} [Field F] [Algebra F K]

theorem serviceWalk_nounWalk {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (services : List (Service cfg exec))
    (E : Noun → ComputeTable.FP K) (z : K) :
    ∀ n, ServiceWalk services n
      (axisMTree cfg.challenges.α (mappedNounWalk E z lmb n))
  | .atom a => by
      rw [axisMTree_nounWalk_atom]
      exact ServiceWalk.halt
  | .cell h t => by
      rw [axisMTree_nounWalk_cell]
      exact ServiceWalk.decompose
        (serviceWalk_nounWalk services E z h)
        (serviceWalk_nounWalk services E z t)

/-! ## Axis-3 record tree: read / decompose / walk-head / verify-tail -- the paper -/

theorem axisPath_two : axisPath 2 = [false] := by
  rw [axisPath_of_two_le (by norm_num)]
  simp [axisPath_of_lt_two]

theorem axisPath_three : axisPath 3 = [true] := by
  rw [axisPath_of_two_le (by norm_num)]
  simp [axisPath_of_lt_two]

theorem mappedRecordTree_axis3 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    mappedRecordTree E z α lmb (.cell hd tl) tl 3 e =
      .node (MState.read_root,
          (memInputs z,
            annotatedReadPub E (.cell hd tl) tl 3 (α ^ e)
              (genAnnotatedDescent E z lmb (.cell hd tl) tl 3 (α ^ e) e
                (.cell hd tl) 3).2 0 0 lmb))
        ((genAnnotatedDescent E z lmb (.cell hd tl) tl 3 (α ^ e) e
          (.cell hd tl) 3).1.map (mapNTree GenMemoryRow.row)) := by
  simp [mappedRecordTree, genAnnotatedRecordTree, mapNTree, gMemRow9, memReadSkelAx]

theorem mappedVerify_eq (E : Noun → ComputeTable.FP K) (z : K)
    (root child : Noun) (ax : ℕ) (ts : K) (e : ℕ) :
    mapNTree GenMemoryRow.row (genAnnotatedVerify E z lmb root child ax ts e).1 =
      .node (MState.verify_child,
          (memInputs z,
            annotatedVerifyPub E root child ax ts
              (genAnnotatedNounWalk E z lmb child).2 0 0 lmb))
        [mappedNounWalk E z lmb child] := by
  simp [genAnnotatedVerify, mapNTree, gMemRow9, memVerifySkelAx, mappedNounWalk]

theorem axisMTree_verify (E : Noun → ComputeTable.FP K) (z α : K)
    (root child : Noun) (ax : ℕ) (ts : K) (e : ℕ) :
    axisMTree α (mapNTree GenMemoryRow.row
        (genAnnotatedVerify E z lmb root child ax ts e).1) =
      .verify (timestampExp α ts) (ax : K)
        (axisMTree α (mappedNounWalk E z lmb child)) := by
  rw [mappedVerify_eq, axisMTree, ofNTree_verify]
  rfl

theorem mappedRecordTree_axis3_children (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    (genAnnotatedDescent E z lmb (.cell hd tl) tl 3 (α ^ e) e (.cell hd tl) 3).1.map
        (mapNTree GenMemoryRow.row) =
      [.node (MState.decompose,
          (memInputs z,
            annotatedDecPub E (.cell hd tl) hd tl
              (genAnnotatedNounWalk E z lmb hd).2
              (genAnnotatedVerify E z lmb (.cell hd tl) tl 3 (α ^ e) e).2
              (nounWalkRootState hd) (descentRootState 1) 0 0 lmb))
        [mappedNounWalk E z lmb hd,
          mapNTree GenMemoryRow.row
            (genAnnotatedVerify E z lmb (.cell hd tl) tl 3 (α ^ e) e).1]] := by
  rw [genAnnotatedDescent_axis3]
  simp [mapNTree, gMemRow9, memDecomposeSkel, mappedNounWalk]

theorem axisMTree_recordTree_axis3 (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    axisMTree α (mappedRecordTree E z α lmb (.cell hd tl) tl 3 e) =
      .read (timestampExp α (α ^ e))
        (.decompose (axisMTree α (mappedNounWalk E z lmb hd))
          (.verify (timestampExp α (α ^ e)) (3 : K)
            (axisMTree α (mappedNounWalk E z lmb tl)))) := by
  rw [mappedRecordTree_axis3, mappedRecordTree_axis3_children, axisMTree,
    ofNTree_read]
  refine congrArg₂ MTree.read ?_ ?_
  · simp [timestampExpAt, annotatedReadPub]
  · rw [ofNTree_decompose]
    refine congrArg₂ MTree.decompose rfl ?_
    simpa [axisMTree] using
      axisMTree_verify E z α (.cell hd tl) tl 3 (α ^ e) e

theorem mappedRecordTree_axis2 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    mappedRecordTree E z α lmb (.cell hd tl) hd 2 e =
      .node (MState.read_root,
          (memInputs z,
            annotatedReadPub E (.cell hd tl) hd 2 (α ^ e)
              (genAnnotatedDescent E z lmb (.cell hd tl) hd 2 (α ^ e) e
                (.cell hd tl) 2).2 0 0 lmb))
        ((genAnnotatedDescent E z lmb (.cell hd tl) hd 2 (α ^ e) e
          (.cell hd tl) 2).1.map (mapNTree GenMemoryRow.row)) := by
  simp [mappedRecordTree, genAnnotatedRecordTree, mapNTree, gMemRow9, memReadSkelAx]

theorem mappedRecordTree_axis2_children (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    (genAnnotatedDescent E z lmb (.cell hd tl) hd 2 (α ^ e) e (.cell hd tl) 2).1.map
        (mapNTree GenMemoryRow.row) =
      [.node (MState.decompose,
          (memInputs z,
            annotatedDecPub E (.cell hd tl) hd tl
              (genAnnotatedVerify E z lmb (.cell hd tl) hd 2 (α ^ e) e).2
              (genAnnotatedNounWalk E z lmb tl).2
              (descentRootState 1) (nounWalkRootState tl) 0 0 lmb))
        [mapNTree GenMemoryRow.row
            (genAnnotatedVerify E z lmb (.cell hd tl) hd 2 (α ^ e) e).1,
          mappedNounWalk E z lmb tl]] := by
  rw [genAnnotatedDescent_axis2]
  simp [mapNTree, gMemRow9, memDecomposeSkel, mappedNounWalk]

theorem axisMTree_recordTree_axis2 (E : Noun → ComputeTable.FP K)
    (z α : K) (hd tl : Noun) (e : ℕ) :
    axisMTree α (mappedRecordTree E z α lmb (.cell hd tl) hd 2 e) =
      .read (timestampExp α (α ^ e))
        (.decompose
          (.verify (timestampExp α (α ^ e)) (2 : K)
            (axisMTree α (mappedNounWalk E z lmb hd)))
          (axisMTree α (mappedNounWalk E z lmb tl))) := by
  rw [mappedRecordTree_axis2, mappedRecordTree_axis2_children, axisMTree,
    ofNTree_read]
  refine congrArg₂ MTree.read ?_ ?_
  · simp [timestampExpAt, annotatedReadPub]
  · rw [ofNTree_decompose]
    refine congrArg₂ MTree.decompose ?_ rfl
    simpa [axisMTree] using
      axisMTree_verify E z α (.cell hd tl) hd 2 (α ^ e) e

theorem serviceWalk_recordTree_axis3 {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    (services : List (Service cfg exec)) (s : Service cfg exec)
    (E : Noun → ComputeTable.FP K) (z : K) (hd tl : Noun) (e : ℕ)
    (hs : s ∈ services) (hroot : s.root = .cell hd tl)
    (hchild : s.child = tl) (haxis : s.axis = 3)
    (hexp : s.exponent = timestampExp cfg.challenges.α (cfg.challenges.α ^ e)) :
    ServiceWalk services (.cell hd tl)
      (axisMTree cfg.challenges.α
        (mappedRecordTree E z cfg.challenges.α lmb (.cell hd tl) tl 3 e)) := by
  rw [axisMTree_recordTree_axis3]
  refine ServiceWalk.read s hs hexp hroot ?_ ?_
  · rw [haxis, axisPath_three]
    refine VerifyRoute.right (readCount_nounWalk E z _ _ hd)
      (verifyCount_nounWalk E z _ _ hd) ?_
    refine VerifyRoute.here hchild.symm ?_
      (readCount_nounWalk E z _ _ tl) (verifyCount_nounWalk E z _ _ tl)
    exact (congrArg (fun n : ℕ => (n : K)) haxis).symm.trans
      s.realization.axis_realizes.symm
  · exact ServiceWalk.decompose (serviceWalk_nounWalk services E z hd)
      (ServiceWalk.verify (serviceWalk_nounWalk services E z tl))

theorem serviceWalk_recordTree_axis2 {cfg : ExactConfig F K}
    {exec : ExactExecution cfg}
    (services : List (Service cfg exec)) (s : Service cfg exec)
    (E : Noun → ComputeTable.FP K) (z : K) (hd tl : Noun) (e : ℕ)
    (hs : s ∈ services) (hroot : s.root = .cell hd tl)
    (hchild : s.child = hd) (haxis : s.axis = 2)
    (hexp : s.exponent = timestampExp cfg.challenges.α (cfg.challenges.α ^ e)) :
    ServiceWalk services (.cell hd tl)
      (axisMTree cfg.challenges.α
        (mappedRecordTree E z cfg.challenges.α lmb (.cell hd tl) hd 2 e)) := by
  rw [axisMTree_recordTree_axis2]
  refine ServiceWalk.read s hs hexp hroot ?_ ?_
  · rw [haxis, axisPath_two]
    refine VerifyRoute.left ?_
      (readCount_nounWalk E z _ _ tl) (verifyCount_nounWalk E z _ _ tl)
    refine VerifyRoute.here hchild.symm ?_
      (readCount_nounWalk E z _ _ hd) (verifyCount_nounWalk E z _ _ hd)
    exact (congrArg (fun n : ℕ => (n : K)) haxis).symm.trans
      s.realization.axis_realizes.symm
  · exact ServiceWalk.decompose
      (ServiceWalk.verify (serviceWalk_nounWalk services E z hd))
      (serviceWalk_nounWalk services E z tl)

theorem mapped_gMemRow9 (sk : SemanticStrategy.MemoryRowSkeleton) (e : ℕ) (z : K)
    (pub : MemoryTable.Pub K) (ch : List (NTree (GenMemoryRow K))) :
    mapNTree GenMemoryRow.row (.node (gMemRow9 sk e z pub) ch) =
      .node (sk.state, (memInputs z, pub))
        (ch.map (mapNTree GenMemoryRow.row)) := by
  simp [mapNTree, gMemRow9]

/-! ## Chained axis-3 then axis-2 trees -- the paper -/

noncomputable def mappedChain32 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) : NTree (MState × DTmem K) :=
  mapNTree GenMemoryRow.row (chain32Root (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)

theorem mapped_chain32InnerDec (E : Noun → ComputeTable.FP K) (z α : K)
    (hd2 tl2 : Noun) (e2 : ℕ) :
    mapNTree GenMemoryRow.row (chain32InnerDec (lmb := lmb) E z α hd2 tl2 e2) =
      .node (MState.decompose, (memInputs z, chain32InnerDecPub (lmb := lmb) E z α hd2 tl2 e2))
        [mapNTree GenMemoryRow.row
            (genAnnotatedVerify E z lmb (.cell hd2 tl2) hd2 2 (α ^ e2) e2).1,
          mappedNounWalk E z lmb tl2] := by
  simp [chain32InnerDec, mapped_gMemRow9, memDecomposeSkel, mappedNounWalk]

theorem axisMTree_chain32InnerDec (E : Noun → ComputeTable.FP K) (z α : K)
    (hd2 tl2 : Noun) (e2 : ℕ) :
    axisMTree α (mapNTree GenMemoryRow.row (chain32InnerDec (lmb := lmb) E z α hd2 tl2 e2)) =
      .decompose
        (.verify (timestampExp α (α ^ e2)) (2 : K)
          (axisMTree α (mappedNounWalk E z lmb hd2)))
        (axisMTree α (mappedNounWalk E z lmb tl2)) := by
  rw [mapped_chain32InnerDec, axisMTree_decompose_node]
  refine congrArg₂ MTree.decompose ?_ rfl
  simpa [axisMTree] using
    axisMTree_verify E z α (.cell hd2 tl2) hd2 2 (α ^ e2) e2

theorem mapped_chain32InnerVerify (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    mapNTree GenMemoryRow.row (chain32InnerVerify (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) =
      .node (MState.verify_child,
          (memInputs z, chain32InnerVerifyPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2))
        [mapNTree GenMemoryRow.row (chain32InnerDec (lmb := lmb) E z α hd2 tl2 e2)] := by
  simp [chain32InnerVerify, mapped_gMemRow9, memVerifySkelAx]

theorem axisMTree_chain32InnerVerify (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    axisMTree α (mapNTree GenMemoryRow.row
        (chain32InnerVerify (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)) =
      .verify (timestampExp α (α ^ e1)) (3 : K)
        (axisMTree α (mapNTree GenMemoryRow.row
          (chain32InnerDec (lmb := lmb) E z α hd2 tl2 e2))) := by
  rw [mapped_chain32InnerVerify, axisMTree_verify_node]
  simp [chain32InnerVerifyPub, annotatedVerifyPub]

theorem mapped_chain32InnerRead (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    mapNTree GenMemoryRow.row (chain32InnerRead (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) =
      .node (MState.read_root,
          (memInputs z, chain32InnerReadPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2))
        [mapNTree GenMemoryRow.row
          (chain32InnerVerify (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)] := by
  simp [chain32InnerRead, mapped_gMemRow9, memReadSkelAx]

theorem axisMTree_chain32InnerRead (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    axisMTree α (mapNTree GenMemoryRow.row
        (chain32InnerRead (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)) =
      .read (timestampExp α (α ^ e2))
        (axisMTree α (mapNTree GenMemoryRow.row
          (chain32InnerVerify (lmb := lmb) E z α hd1 hd2 tl2 e1 e2))) := by
  rw [mapped_chain32InnerRead, axisMTree_read_node]
  simp [chain32InnerReadPub, annotatedReadPub]

theorem mapped_chain32OuterDec (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    mapNTree GenMemoryRow.row (chain32OuterDec (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) =
      .node (MState.decompose,
          (memInputs z, chain32OuterDecPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2))
        [mappedNounWalk E z lmb hd1,
          mapNTree GenMemoryRow.row
            (chain32InnerRead (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)] := by
  simp [chain32OuterDec, mapped_gMemRow9, memDecomposeSkel, mappedNounWalk]

theorem axisMTree_chain32OuterDec (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    axisMTree α (mapNTree GenMemoryRow.row
        (chain32OuterDec (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)) =
      .decompose (axisMTree α (mappedNounWalk E z lmb hd1))
        (axisMTree α (mapNTree GenMemoryRow.row
          (chain32InnerRead (lmb := lmb) E z α hd1 hd2 tl2 e1 e2))) := by
  rw [mapped_chain32OuterDec, axisMTree_decompose_node]

theorem mapped_chain32Root (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    mappedChain32 (lmb := lmb) E z α hd1 hd2 tl2 e1 e2 =
      .node (MState.read_root,
          (memInputs z, chain32RootPub (lmb := lmb) E z α hd1 hd2 tl2 e1 e2))
        [mapNTree GenMemoryRow.row
          (chain32OuterDec (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)] := by
  simp [mappedChain32, chain32Root, mapped_gMemRow9, memReadSkelAx]

theorem axisMTree_chain32 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    axisMTree α (mappedChain32 (lmb := lmb) E z α hd1 hd2 tl2 e1 e2) =
      .read (timestampExp α (α ^ e1))
        (.decompose (axisMTree α (mappedNounWalk E z lmb hd1))
          (.read (timestampExp α (α ^ e2))
            (.verify (timestampExp α (α ^ e1)) (3 : K)
              (.decompose
                (.verify (timestampExp α (α ^ e2)) (2 : K)
                  (axisMTree α (mappedNounWalk E z lmb hd2)))
                (axisMTree α (mappedNounWalk E z lmb tl2)))))) := by
  rw [mapped_chain32Root, axisMTree_read_node]
  simp only [chain32RootPub, annotatedReadPub]
  refine congrArg (MTree.read _) ?_
  rw [axisMTree_chain32OuterDec, axisMTree_chain32InnerRead,
    axisMTree_chain32InnerVerify, axisMTree_chain32InnerDec]

theorem serviceWalk_chain32 {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (services : List (Service cfg exec))
    (s1 s2 : Service cfg exec)
    (E : Noun → ComputeTable.FP K) (z : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ)
    (hs1 : s1 ∈ services) (hs2 : s2 ∈ services)
    (hroot1 : s1.root = .cell hd1 (.cell hd2 tl2))
    (hchild1 : s1.child = .cell hd2 tl2) (haxis1 : s1.axis = 3)
    (hexp1 : s1.exponent = timestampExp cfg.challenges.α (cfg.challenges.α ^ e1))
    (hroot2 : s2.root = .cell hd2 tl2)
    (hchild2 : s2.child = hd2) (haxis2 : s2.axis = 2)
    (hexp2 : s2.exponent = timestampExp cfg.challenges.α (cfg.challenges.α ^ e2))
    (hne : timestampExp cfg.challenges.α (cfg.challenges.α ^ e1) ≠
        timestampExp cfg.challenges.α (cfg.challenges.α ^ e2)) :
    ServiceWalk services (.cell hd1 (.cell hd2 tl2))
      (axisMTree cfg.challenges.α
        (mappedChain32 (lmb := lmb) E z cfg.challenges.α hd1 hd2 tl2 e1 e2)) := by
  rw [axisMTree_chain32]
  refine ServiceWalk.read s1 hs1 hexp1 hroot1 ?_ ?_
  · rw [haxis1, axisPath_three]
    refine VerifyRoute.right (readCount_nounWalk E z _ _ hd1)
      (verifyCount_nounWalk E z _ _ hd1) ?_
    refine VerifyRoute.read_other hne.symm ?_
    refine VerifyRoute.here hchild1.symm ?_ ?_ ?_
    · exact (congrArg (fun n : ℕ => (n : K)) haxis1).symm.trans
        s1.realization.axis_realizes.symm
    · simp [readCount, readCount_nounWalk]
    · simp [verifyCount, verifyCount_nounWalk, hne.symm]
  · refine ServiceWalk.decompose (serviceWalk_nounWalk services E z hd1) ?_
    refine ServiceWalk.read s2 hs2 hexp2 hroot2 ?_ ?_
    · rw [haxis2, axisPath_two]
      refine VerifyRoute.verify_other hne ?_
      refine VerifyRoute.left ?_
        (readCount_nounWalk E z _ _ tl2) (verifyCount_nounWalk E z _ _ tl2)
      refine VerifyRoute.here hchild2.symm ?_
        (readCount_nounWalk E z _ _ hd2) (verifyCount_nounWalk E z _ _ hd2)
      exact (congrArg (fun n : ℕ => (n : K)) haxis2).symm.trans
        s2.realization.axis_realizes.symm
    · exact ServiceWalk.verify
        (ServiceWalk.decompose
          (ServiceWalk.verify (serviceWalk_nounWalk services E z hd2))
          (serviceWalk_nounWalk services E z tl2))

theorem readExps_nounWalk (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ n, readExps (axisMTree α (mappedNounWalk E z lmb n)) = []
  | .atom a => by simp [axisMTree_nounWalk_atom, readExps]
  | .cell h t => by
      simp [axisMTree_nounWalk_cell, readExps,
        readExps_nounWalk E z α h, readExps_nounWalk E z α t]

theorem verifyExps_nounWalk (E : Noun → ComputeTable.FP K) (z α : K) :
    ∀ n, verifyExps (axisMTree α (mappedNounWalk E z lmb n)) = []
  | .atom a => by simp [axisMTree_nounWalk_atom, verifyExps]
  | .cell h t => by
      simp [axisMTree_nounWalk_cell, verifyExps,
        verifyExps_nounWalk E z α h, verifyExps_nounWalk E z α t]

theorem readExps_chain32 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    readExps (axisMTree α (mappedChain32 (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)) =
      [timestampExp α (α ^ e1), timestampExp α (α ^ e2)] := by
  rw [axisMTree_chain32]
  simp [readExps, readExps_nounWalk]

theorem verifyExps_chain32 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    verifyExps (axisMTree α (mappedChain32 (lmb := lmb) E z α hd1 hd2 tl2 e1 e2)) =
      [timestampExp α (α ^ e1), timestampExp α (α ^ e2)] := by
  rw [axisMTree_chain32]
  simp [verifyExps, verifyExps_nounWalk]

theorem readExps_recordTree_axis3 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    readExps (axisMTree α (mappedRecordTree E z α lmb (.cell hd tl) tl 3 e)) =
      [timestampExp α (α ^ e)] := by
  rw [axisMTree_recordTree_axis3]
  simp [readExps, readExps_nounWalk]

theorem verifyExps_recordTree_axis3 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    verifyExps (axisMTree α (mappedRecordTree E z α lmb (.cell hd tl) tl 3 e)) =
      [timestampExp α (α ^ e)] := by
  rw [axisMTree_recordTree_axis3]
  simp [verifyExps, verifyExps_nounWalk]

theorem readExps_recordTree_axis2 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    readExps (axisMTree α (mappedRecordTree E z α lmb (.cell hd tl) hd 2 e)) =
      [timestampExp α (α ^ e)] := by
  rw [axisMTree_recordTree_axis2]
  simp [readExps, readExps_nounWalk]

theorem verifyExps_recordTree_axis2 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd tl : Noun) (e : ℕ) :
    verifyExps (axisMTree α (mappedRecordTree E z α lmb (.cell hd tl) hd 2 e)) =
      [timestampExp α (α ^ e)] := by
  rw [axisMTree_recordTree_axis2]
  simp [verifyExps, verifyExps_nounWalk]

/-! ## Timestamp exponents and threading -- the paper -/

theorem timestampExp_pow_ne {α : K} {e1 e2 : ℕ} (hα : α ≠ 0)
    (h1 : e1 < orderOf α) (h2 : e2 < orderOf α) (hne : e1 ≠ e2) :
    timestampExp α (α ^ e1) ≠ timestampExp α (α ^ e2) := by
  intro heq
  have hc1 : TimestampClosedAt α (α ^ e1) := ⟨e1, rfl⟩
  have hc2 : TimestampClosedAt α (α ^ e2) := ⟨e2, rfl⟩
  have hpow : α ^ e1 = α ^ e2 := by
    rw [timestampExp_spec hc1, timestampExp_spec hc2, heq]
  have hdiv {a b : ℕ} (hle : a ≤ b) (_ha : a < orderOf α) (hb : b < orderOf α)
      (hne' : a ≠ b) (hp : α ^ a = α ^ b) : False := by
    have hmul : α ^ a * α ^ (b - a) = α ^ a := by
      rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hle, hp]
    have hone : α ^ (b - a) = 1 :=
      mul_left_cancel₀ (pow_ne_zero a hα) (by rw [hmul, mul_one])
    have hdvd : orderOf α ∣ b - a :=
      (orderOf_dvd_iff_pow_eq_one (x := α)).mpr hone
    have hlt : b - a < orderOf α := (Nat.sub_le b a).trans_lt hb
    have hpos : 0 < b - a := Nat.sub_pos_of_lt (lt_of_le_of_ne hle hne')
    exact Nat.not_dvd_of_pos_of_lt hpos hlt hdvd
  rcases le_total e1 e2 with hle | hle
  · exact hdiv hle h1 h2 hne hpow
  · exact hdiv hle h2 h1 hne.symm hpow.symm

theorem servedGen_threadGenForest (inp : MemoryTable.Inputs K) (acc : K)
    (forest : List (NTree (GenMemoryRow K))) :
    servedGen (threadGenForest inp acc forest) = servedGen forest := by
  rw [servedGen_eq_labels, threadGenForest_bfs_labels,
    threadGenRows_flatMap_responseRecords, servedGen_eq_labels]

theorem responseRecords_of_ne_read (pub : MemoryTable.Pub K)
    (_h : pub.st ≠ .read_root) (hver : pub.ver = false) :
    responseRecords pub = [] :=
  responseRecords_eq_nil_of_not_ver pub hver

theorem servedGen_skip_not_read (l : List (NTree (GenMemoryRow K))) (hl : l ≠ [])
    (h : ∀ t ∈ l, t.label.row.2.2.st ≠ .read_root)
    (hver : ∀ t ∈ l, t.label.row.2.2.ver = false) :
    servedGen l = servedGen (l.flatMap NTree.children) := by
  rw [servedGen_of_ne_nil l hl]
  have : l.flatMap (fun t => responseRecords t.label.row.2.2) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    obtain ⟨t, ht, hx'⟩ := List.mem_flatMap.mp hx
    rw [responseRecords_of_ne_read _ (h t ht) (hver t ht)] at hx'
    cases hx'
  rw [this, List.nil_append]

theorem servedGen_no_read (forest : List (NTree (GenMemoryRow K)))
    (h : forestFibre (.read_root : MemoryTable.MState) forest = 0)
    (hver : ∀ t ∈ bfsForest forest, t.label.row.2.2.ver = false) :
    servedGen forest = [] := by
  have hnil : ∀ t ∈ bfsForest forest, responseRecords t.label.row.2.2 = [] := by
    intro t ht
    exact responseRecords_eq_nil_of_not_ver _ (hver t ht)
  unfold servedGen
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  obtain ⟨t, ht, hx'⟩ := List.mem_flatMap.mp hx
  rw [hnil t ht] at hx'
  cases hx'

theorem servedGen_chain32 (E : Noun → ComputeTable.FP K) (z α : K)
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ) :
    servedGen [chain32Root (lmb := lmb) E z α hd1 hd2 tl2 e1 e2] =
      [⟨E (.cell hd1 (.cell hd2 tl2)), E (.cell hd2 tl2), (3 : K), α ^ e1⟩,
       ⟨E (.cell hd2 tl2), E hd2, (2 : K), α ^ e2⟩] := by
  have ht := genAnnotatedChainedTree_axis3_axis2_eq (lmb := lmb) E z α hd1 hd2 tl2 e1 e2
  obtain ⟨dec, walk, inner, hch, hdec, hdecver, hL2, hwalk, hwalkver, hwalkAll, hwalkf,
      hinr, hinrver, hmem, hf, hinnerChVer⟩ :=
    genAnnotatedChainedTree_axis3_axis2_shape E z α hd1 hd2 tl2 e1 e2 _ ht
  have hroot :
      (chain32Root (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).label.row.2.2.st = .read_root ∧
        (chain32Root (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).label.row.2.2.ver = true ∧
        (chain32Root (lmb := lmb) E z α hd1 hd2 tl2 e1 e2).label.row.2.2.mem =
          ⟨E (.cell hd1 (.cell hd2 tl2)), E (.cell hd2 tl2), (3 : K), α ^ e1⟩ := by
    simp [chain32Root, chain32RootPub, gMemRow9_st, gMemRow9_ver, gMemRow9_mem,
      annotatedReadPub_st, annotatedReadPub_ver, annotatedReadPub_mem]
  have hne :
      ([chain32Root (lmb := lmb) E z α hd1 hd2 tl2 e1 e2] : List _) ≠ [] :=
    List.cons_ne_nil _ _
  rw [servedGen_of_ne_nil _ hne]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append]
  rw [responseRecords_eq_singleton_of_read_root _ hroot.1 hroot.2.1, hroot.2.2, hch]
  have hdecne : ([dec] : List _) ≠ [] := List.cons_ne_nil _ _
  have hdec_not : ∀ t ∈ ([dec] : List _), t.label.row.2.2.st ≠ .read_root := by
    intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t; rw [hdec]; simp
  have hdec_ver : ∀ t ∈ ([dec] : List _), t.label.row.2.2.ver = false := by
    intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t; exact hdecver
  rw [servedGen_skip_not_read _ hdecne hdec_not hdec_ver]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hL2]
  have hL2ne : ([walk, inner] : List _) ≠ [] := List.cons_ne_nil _ _
  rw [servedGen_of_ne_nil _ hL2ne]
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [responseRecords_of_ne_read _ hwalk hwalkver, List.nil_append]
  rw [responseRecords_eq_singleton_of_read_root _ hinr hinrver, hmem]
  have hrest :
      forestFibre (.read_root : MemoryTable.MState)
        (walk.children ++ inner.children) = 0 := by
    have hwalkc : forestFibre (.read_root : MemoryTable.MState) walk.children = 0 := by
      cases walk with
      | node g cs =>
        have htf := (treeFibre_node (.read_root : MemoryTable.MState) g cs).symm.trans hwalkf
        exact (Nat.add_eq_zero.mp htf).2
    rw [forestFibre_append, hwalkc, hf]
  have hrestVer :
      ∀ t ∈ bfsForest (walk.children ++ inner.children),
        t.label.row.2.2.ver = false := by
    intro t ht
    obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp ht
    simp only [List.mem_append] at hc
    rcases hc with hC | hC
    · exact hwalkAll _ (InTree.sub hC hin)
    · exact hinnerChVer t ((mem_bfsForest _ _).mpr ⟨c, hC, hin⟩)
  simp [List.append_nil]
  rw [servedGen_no_read _ hrest hrestVer]

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.DotConfig769

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TraceGen

theorem alphaA_ne_zero : alphaA ≠ 0 := by
  intro h
  have : (4 : F) = 0 := φ_injective (by simpa [alphaA] using h)
  exact absurd this (by decide)

theorem timestampExp_ne {e1 e2 : ℕ}
    (h1 : e1 < 14) (h2 : e2 < 14) (hne : e1 ≠ e2) :
    timestampExp alphaA (alphaA ^ e1) ≠ timestampExp alphaA (alphaA ^ e2) :=
  timestampExp_pow_ne alphaA_ne_zero
    (h1.trans_le alphaA_order_ge_14) (h2.trans_le alphaA_order_ge_14) hne

theorem assignedForest_length :
    (assignedForest seedZ alphaA).length = 10 := by
  unfold assignedForest
  exact assigned_kMem seedZ alphaA

theorem memoryTreeAt_threaded (i : Fin (cfg seedZ alphaA).kMem) :
    (execThreadedA seedZ alphaA).memoryTreeAt i =
      mapNTree GenMemoryRow.row
        ((threadedForest seedZ alphaA)[(i : ℕ)]'(by
          rw [threaded_kMem]; exact i.isLt)) := by
  unfold ExactExecution.memoryTreeAt execThreadedA memoryForestThreaded
  simp [List.get_eq_getElem, List.getElem_map]

theorem exactAxisTree_assigned (i : Fin (cfg seedZ alphaA).kMem) :
    exactAxisTree (cfg seedZ alphaA) (execThreadedA seedZ alphaA) i =
      axisMTree alphaA (mapNTree GenMemoryRow.row
        ((assignedForest seedZ alphaA)[(i : ℕ)]'(by
          rw [assignedForest_length]; exact i.isLt))) := by
  rw [exactAxisTree, memoryTreeAt_threaded]
  change axisMTree (cfg seedZ alphaA).challenges.α _ = _
  simp only [cfg]
  unfold threadedForest
  exact axisMTree_threadGenForest (memInputs seedZ) 0 alphaA
    (assignedForest seedZ alphaA)
    (by rw [assignedForest_length]; exact i.isLt)

theorem recOf_mem (root child : Noun) (ax e : ℕ)
    (h : recOf seedZ alphaA root child ax e ∈
      (exec seedZ alphaA).rawRequests) :
    recOf seedZ alphaA root child ax e ∈
      (execThreadedA seedZ alphaA).rawRequests := by
  rwa [execThreadedA_rawRequests]

noncomputable def mkService (root child : Noun) (ax e : ℕ)
    (hslot : Noun.slot ax root = some child)
    (hmem : recOf seedZ alphaA root child ax e ∈
      (execThreadedA seedZ alphaA).rawRequests) :
    Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) where
  exponent := timestampExp alphaA (alphaA ^ e)
  record := recOf seedZ alphaA root child ax e
  root := root
  child := child
  axis := ax
  request_mem := hmem
  timestamp := timestampExp_spec ⟨e, rfl⟩
  realization :=
    { root_realizes := encC_eq seedZ root
      child_realizes := encC_eq seedZ child
      axis_realizes := rfl }
  served := hslot

theorem rawRequests_mem_of_eq {root child : Noun} {ax e : ℕ} :
    recOf seedZ alphaA root child ax e ∈
      [⟨encC seedZ dotFormula, encC seedZ dotParentTail, 3, alphaA ^ 1⟩,
       ⟨encC seedZ dotParentTail, encC seedZ dotCondFormula, 2, alphaA ^ 2⟩,
       ⟨encC seedZ dotBranchPair, encC seedZ dotThenFormula, 2, alphaA ^ 3⟩,
       ⟨encC seedZ dotThenFormula, encC seedZ dotThenTail, 3, alphaA ^ 4⟩,
       ⟨encC seedZ dotThenTail, encC seedZ dotOp2B, 2, alphaA ^ 5⟩,
       ⟨encC seedZ dotCondFormula, encC seedZ dotCondResult, 3, alphaA ^ 6⟩,
       ⟨encC seedZ dotOp2B, encC seedZ dotOp2Sf1, 3, alphaA ^ 7⟩,
       ⟨encC seedZ dotOp2C, encC seedZ dotOp2Sf2, 3, alphaA ^ 8⟩,
       ⟨encC seedZ dotOp9Formula, encC seedZ dotOp9Tail, 3, alphaA ^ 9⟩,
       ⟨encC seedZ dotOp9Tail, encC seedZ (.atom 2), 2, alphaA ^ 10⟩,
       ⟨encC seedZ dotCore, encC seedZ dotArm, 2, alphaA ^ 11⟩,
       ⟨encC seedZ dotCoreFormula, encC seedZ dotCore, 3, alphaA ^ 12⟩,
       ⟨encC seedZ dotArm, encC seedZ dotResult, 3, alphaA ^ 13⟩] →
    recOf seedZ alphaA root child ax e ∈
      (execThreadedA seedZ alphaA).rawRequests := by
  intro h
  rw [execThreadedA_rawRequests, rawRequests_eq]
  simpa [recOf] using h

noncomputable def service1 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotFormula dotParentTail 3 1
    (by simp [dotFormula, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service2 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotParentTail dotCondFormula 2 2
    (by simp [dotParentTail, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service3 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotBranchPair dotThenFormula 2 3
    (by simp [dotBranchPair, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service4 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotThenFormula dotThenTail 3 4
    (by simp [dotThenFormula, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service5 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotThenTail dotOp2B 2 5
    (by simp [dotThenTail, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service6 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotCondFormula dotCondResult 3 6
    (by simp [dotCondFormula, dotCondResult, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service7 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotOp2B dotOp2Sf1 3 7
    (by simp [dotOp2B, dotOp2Sf1, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service8 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotOp2C dotOp2Sf2 3 8
    (by simp [dotOp2C, dotOp2Sf2, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service9 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotOp9Formula dotOp9Tail 3 9
    (by simp [dotOp9Formula, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service10 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotOp9Tail (.atom 2) 2 10
    (by simp [dotOp9Tail, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service11 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotCore dotArm 2 11
    (by exact dot_slot)
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service12 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotCoreFormula dotCore 3 12
    (by simp [dotCoreFormula, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

noncomputable def service13 : Service (cfg seedZ alphaA) (execThreadedA seedZ alphaA) :=
  mkService dotArm dotResult 3 13
    (by simp [dotArm, dotElem0, dotResult, Noun.slot])
    (rawRequests_mem_of_eq (by simp [recOf]))

theorem kMem_eq : (cfg seedZ alphaA).kMem = 10 := by simp [cfg]

theorem cfg_alpha : (cfg seedZ alphaA).challenges.α = alphaA := rfl

def memIdx (n : ℕ) (hn : n < 10 := by decide) :
    Fin (cfg seedZ alphaA).kMem :=
  ⟨n, by simp only [cfg]; exact hn⟩

theorem assignedForest_get_lt {n : ℕ} (hn : n < 10) :
    n < (assignedForest seedZ alphaA).length := by
  rw [assignedForest_length]; exact hn

theorem fin_lt_ten (i : Fin (cfg seedZ alphaA).kMem) : (i : ℕ) < 10 := by
  have := i.isLt
  simp only [cfg] at this
  exact this

theorem chained_eq_chain32 (t : NTree (GenMemoryRow K))
    (hd1 hd2 tl2 : Noun) (e1 e2 : ℕ)
    (h : genAnnotatedChainedTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
      [⟨.cell hd1 (.cell hd2 tl2), .cell hd2 tl2, 3, e1⟩,
       ⟨.cell hd2 tl2, hd2, 2, e2⟩] = some t) :
    t = chain32Root (lmb := MemoryTable.formRDefault) (encC seedZ) seedZ alphaA hd1 hd2 tl2 e1 e2 := by
  have heq := genAnnotatedChainedTree_axis3_axis2_eq (lmb := MemoryTable.formRDefault)
    (encC seedZ) seedZ alphaA hd1 hd2 tl2 e1 e2
  have ht : some t = some (chain32Root (encC seedZ) seedZ alphaA hd1 hd2 tl2 e1 e2) :=
    h.symm.trans heq
  injection ht

noncomputable def forestTrees : List (NTree (GenMemoryRow K)) :=
  [chain32Root (lmb := MemoryTable.formRDefault) (encC seedZ) seedZ alphaA
    (.atom 6) dotCondFormula dotBranchPair 1 2,
   genAnnotatedRecordTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
    dotBranchPair dotThenFormula 2 3,
   chain32Root (lmb := MemoryTable.formRDefault) (encC seedZ) seedZ alphaA
    (.atom 2) dotOp2B dotOp2C 4 5,
   genAnnotatedRecordTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
    dotOp2B dotOp2Sf1 3 7,
   genAnnotatedRecordTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
    dotOp2C dotOp2Sf2 3 8,
   chain32Root (lmb := MemoryTable.formRDefault) (encC seedZ) seedZ alphaA
    (.atom 9) (.atom 2) dotCoreFormula 9 10,
   genAnnotatedRecordTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
    dotCore dotArm 2 11,
   genAnnotatedRecordTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
    dotCoreFormula dotCore 3 12,
   genAnnotatedRecordTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
    dotArm dotResult 3 13,
   genAnnotatedRecordTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
    dotCondFormula dotCondResult 3 6]

theorem assignedForest_trees : assignedForest seedZ alphaA = forestTrees := by
  obtain ⟨t12, t45, t910, hF, h12, h45, h910⟩ := assignedForest_eq seedZ alphaA
  have h12' : t12 = chain32Root (encC seedZ) seedZ alphaA
      (.atom 6) dotCondFormula dotBranchPair 1 2 :=
    chained_eq_chain32 t12 (.atom 6) dotCondFormula dotBranchPair 1 2
      (by simpa [dotFormula, dotParentTail] using h12)
  have h45' : t45 = chain32Root (encC seedZ) seedZ alphaA
      (.atom 2) dotOp2B dotOp2C 4 5 :=
    chained_eq_chain32 t45 (.atom 2) dotOp2B dotOp2C 4 5
      (by simpa [dotThenFormula, dotThenTail] using h45)
  have h910' : t910 = chain32Root (encC seedZ) seedZ alphaA
      (.atom 9) (.atom 2) dotCoreFormula 9 10 :=
    chained_eq_chain32 t910 (.atom 9) (.atom 2) dotCoreFormula 9 10
      (by simpa [dotOp9Formula, dotOp9Tail] using h910)
  unfold forestTrees
  rw [hF, h12', h45', h910']

theorem getElem_of_list_eq {α : Type*} {l₁ l₂ : List α} (h : l₁ = l₂)
    {n : ℕ} (h₁ : n < l₁.length) (h₂ : n < l₂.length) :
    l₁[n] = l₂[n] := by
  subst h
  rfl

theorem assignedAt_eq (n : ℕ) (hn : n < 10) :
    (assignedForest seedZ alphaA)[n]'(assignedForest_get_lt hn) =
      forestTrees[n]'(by simp [forestTrees]; exact hn) :=
  getElem_of_list_eq assignedForest_trees (assignedForest_get_lt hn)
    (by simp [forestTrees]; exact hn)

theorem assignedAt_zero :
    (assignedForest seedZ alphaA)[0]'(assignedForest_get_lt (by decide)) =
      chain32Root (lmb := MemoryTable.formRDefault) (encC seedZ) seedZ alphaA
        (.atom 6) dotCondFormula dotBranchPair 1 2 :=
  (assignedAt_eq 0 (by decide)).trans rfl

theorem rootResponseRecords_assigned (i : Fin (cfg seedZ alphaA).kMem) :
    rootResponseRecords (execThreadedA seedZ alphaA) i =
      servedGen [(assignedForest seedZ alphaA)[(i : ℕ)]'(assignedForest_get_lt (fin_lt_ten i))] := by
  unfold rootResponseRecords
  rw [memoryTreeAt_threaded]
  rw [servedGen_mapped_row]
  unfold threadedForest
  exact servedGen_thread_get (memInputs seedZ) 0 (assignedForest seedZ alphaA)
    (assignedForest_get_lt (fin_lt_ten i))

theorem exactAxis_mapped (i : Fin (cfg seedZ alphaA).kMem) :
    exactAxisTree (cfg seedZ alphaA) (execThreadedA seedZ alphaA) i =
      axisMTree alphaA (mapNTree GenMemoryRow.row
        ((assignedForest seedZ alphaA)[(i : ℕ)]'(assignedForest_get_lt (fin_lt_ten i)))) := by
  convert exactAxisTree_assigned i

theorem service_hexp (root child : Noun) (ax e : ℕ) hslot hmem :
    (mkService root child ax e hslot hmem).exponent =
      timestampExp (cfg seedZ alphaA).challenges.α
        ((cfg seedZ alphaA).challenges.α ^ e) :=
  rfl

theorem alphaA_pow_ne {e1 e2 : ℕ}
    (h1 : e1 < 14) (h2 : e2 < 14) (hne : e1 ≠ e2) :
    alphaA ^ e1 ≠ alphaA ^ e2 := by
  intro heq
  exact timestampExp_ne h1 h2 hne (congrArg (timestampExp alphaA) heq)

theorem served_at (i : Fin (cfg seedZ alphaA).kMem) :
    rootResponseRecords (execThreadedA seedZ alphaA) i =
      servedGen [forestTrees[(i : ℕ)]'(by
        simp [forestTrees]; exact fin_lt_ten i)] :=
  (rootResponseRecords_assigned i).trans
    (congrArg (fun t => servedGen [t]) (assignedAt_eq (i : ℕ) (fin_lt_ten i)))

theorem axis_at (i : Fin (cfg seedZ alphaA).kMem) :
    exactAxisTree (cfg seedZ alphaA) (execThreadedA seedZ alphaA) i =
      axisMTree alphaA (mapNTree GenMemoryRow.row
        (forestTrees[(i : ℕ)]'(by simp [forestTrees]; exact fin_lt_ten i))) :=
  (exactAxis_mapped i).trans
    (congrArg (fun t => axisMTree alphaA (mapNTree GenMemoryRow.row t))
      (assignedAt_eq (i : ℕ) (fin_lt_ten i)))

/-! ### Root 0: formula @3 then parentTail @2 (exps 1, 2) -/

noncomputable def rootTrace0 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 0) where
  subject := dotFormula
  services := [service1, service2]
  recordPartition := by
    rw [served_at]
    simp only [forestTrees, memIdx, List.getElem_cons_zero]
    rw [servedGen_chain32]
    simp [service1, service2, mkService, recOf, dotFormula, dotParentTail]
  readPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedChain32, service1, service2, mkService] using
      readExps_chain32 (encC seedZ) seedZ alphaA
        (.atom 6) dotCondFormula dotBranchPair 1 2
  verifyPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedChain32, service1, service2, mkService] using
      verifyExps_chain32 (encC seedZ) seedZ alphaA
        (.atom 6) dotCondFormula dotBranchPair 1 2
  traversal := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_zero]
    simpa [cfg_alpha, mappedChain32, dotFormula, dotParentTail] using
      (serviceWalk_chain32 [service1, service2] service1 service2
        (encC seedZ) seedZ (.atom 6) dotCondFormula dotBranchPair 1 2
        (by simp) (by simp)
        (by simp [service1, mkService, dotFormula, dotParentTail])
        (by simp [service1, mkService, dotParentTail]) rfl
        (service_hexp _ _ _ _ _ _)
        (by simp [service2, mkService, dotParentTail])
        (by simp [service2, mkService]) rfl
        (service_hexp _ _ _ _ _ _)
        (timestampExp_ne (by decide) (by decide) (by decide)))

/-! ### Remaining nine forest roots -- the paper -/

noncomputable def rootTrace1 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 1) where
  subject := dotBranchPair
  services := [service3]
  recordPartition := by
    rw [served_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [servedGen_recordTree]
    simp [service3, mkService, recOf]
  readPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service3, mkService, dotBranchPair] using
      readExps_recordTree_axis2 (encC seedZ) seedZ alphaA
        dotThenFormula dotElseFormula 3
  verifyPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service3, mkService, dotBranchPair] using
      verifyExps_recordTree_axis2 (encC seedZ) seedZ alphaA
        dotThenFormula dotElseFormula 3
  traversal := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa [cfg_alpha, mappedRecordTree, dotBranchPair] using
      (serviceWalk_recordTree_axis2 [service3] service3
        (encC seedZ) seedZ dotThenFormula dotElseFormula 3
        (by simp)
        (by simp [service3, mkService, dotBranchPair])
        (by simp [service3, mkService]) rfl
        (service_hexp _ _ _ _ _ _))

noncomputable def rootTrace2 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 2) where
  subject := dotThenFormula
  services := [service4, service5]
  recordPartition := by
    rw [served_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [servedGen_chain32]
    simp [service4, service5, mkService, recOf, dotThenFormula, dotThenTail]
  readPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedChain32, service4, service5, mkService] using
      readExps_chain32 (encC seedZ) seedZ alphaA
        (.atom 2) dotOp2B dotOp2C 4 5
  verifyPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedChain32, service4, service5, mkService] using
      verifyExps_chain32 (encC seedZ) seedZ alphaA
        (.atom 2) dotOp2B dotOp2C 4 5
  traversal := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa [cfg_alpha, mappedChain32, dotThenFormula, dotThenTail] using
      (serviceWalk_chain32 [service4, service5] service4 service5
        (encC seedZ) seedZ (.atom 2) dotOp2B dotOp2C 4 5
        (by simp) (by simp)
        (by simp [service4, mkService, dotThenFormula, dotThenTail])
        (by simp [service4, mkService, dotThenTail]) rfl
        (service_hexp _ _ _ _ _ _)
        (by simp [service5, mkService, dotThenTail])
        (by simp [service5, mkService]) rfl
        (service_hexp _ _ _ _ _ _)
        (timestampExp_ne (by decide) (by decide) (by decide)))

noncomputable def rootTrace3 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 3) where
  subject := dotOp2B
  services := [service7]
  recordPartition := by
    rw [served_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [servedGen_recordTree]
    simp [service7, mkService, recOf]
  readPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service7, mkService, dotOp2B, dotOp2Sf1] using
      readExps_recordTree_axis3 (encC seedZ) seedZ alphaA
        (.atom 1) dotOp2Sf1 7
  verifyPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service7, mkService, dotOp2B, dotOp2Sf1] using
      verifyExps_recordTree_axis3 (encC seedZ) seedZ alphaA
        (.atom 1) dotOp2Sf1 7
  traversal := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa [cfg_alpha, mappedRecordTree, dotOp2B, dotOp2Sf1] using
      (serviceWalk_recordTree_axis3 [service7] service7
        (encC seedZ) seedZ (.atom 1) dotOp2Sf1 7
        (by simp)
        (by simp [service7, mkService, dotOp2B, dotOp2Sf1])
        (by simp [service7, mkService, dotOp2Sf1]) rfl
        (service_hexp _ _ _ _ _ _))

noncomputable def rootTrace4 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 4) where
  subject := dotOp2C
  services := [service8]
  recordPartition := by
    rw [served_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [servedGen_recordTree]
    simp [service8, mkService, recOf]
  readPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service8, mkService, dotOp2C, dotOp2Sf2] using
      readExps_recordTree_axis3 (encC seedZ) seedZ alphaA
        (.atom 1) dotOp2Sf2 8
  verifyPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service8, mkService, dotOp2C, dotOp2Sf2] using
      verifyExps_recordTree_axis3 (encC seedZ) seedZ alphaA
        (.atom 1) dotOp2Sf2 8
  traversal := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa [cfg_alpha, mappedRecordTree, dotOp2C, dotOp2Sf2] using
      (serviceWalk_recordTree_axis3 [service8] service8
        (encC seedZ) seedZ (.atom 1) dotOp2Sf2 8
        (by simp)
        (by simp [service8, mkService, dotOp2C, dotOp2Sf2])
        (by simp [service8, mkService, dotOp2Sf2]) rfl
        (service_hexp _ _ _ _ _ _))

noncomputable def rootTrace5 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 5) where
  subject := dotOp9Formula
  services := [service9, service10]
  recordPartition := by
    rw [served_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [servedGen_chain32]
    simp [service9, service10, mkService, recOf, dotOp9Formula, dotOp9Tail]
  readPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedChain32, service9, service10, mkService] using
      readExps_chain32 (encC seedZ) seedZ alphaA
        (.atom 9) (.atom 2) dotCoreFormula 9 10
  verifyPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedChain32, service9, service10, mkService] using
      verifyExps_chain32 (encC seedZ) seedZ alphaA
        (.atom 9) (.atom 2) dotCoreFormula 9 10
  traversal := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa [cfg_alpha, mappedChain32, dotOp9Formula, dotOp9Tail] using
      (serviceWalk_chain32 [service9, service10] service9 service10
        (encC seedZ) seedZ (.atom 9) (.atom 2) dotCoreFormula 9 10
        (by simp) (by simp)
        (by simp [service9, mkService, dotOp9Formula, dotOp9Tail])
        (by simp [service9, mkService, dotOp9Tail]) rfl
        (service_hexp _ _ _ _ _ _)
        (by simp [service10, mkService, dotOp9Tail])
        (by simp [service10, mkService]) rfl
        (service_hexp _ _ _ _ _ _)
        (timestampExp_ne (by decide) (by decide) (by decide)))

noncomputable def rootTrace6 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 6) where
  subject := dotCore
  services := [service11]
  recordPartition := by
    rw [served_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [servedGen_recordTree]
    simp [service11, mkService, recOf]
  readPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service11, mkService, dotCore, dotArm] using
      readExps_recordTree_axis2 (encC seedZ) seedZ alphaA
        dotArm dotElem1 11
  verifyPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service11, mkService, dotCore, dotArm] using
      verifyExps_recordTree_axis2 (encC seedZ) seedZ alphaA
        dotArm dotElem1 11
  traversal := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa [cfg_alpha, mappedRecordTree, dotCore, dotArm] using
      (serviceWalk_recordTree_axis2 [service11] service11
        (encC seedZ) seedZ dotArm dotElem1 11
        (by simp)
        (by simp [service11, mkService, dotCore, dotArm])
        (by simp [service11, mkService, dotArm]) rfl
        (service_hexp _ _ _ _ _ _))

noncomputable def rootTrace7 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 7) where
  subject := dotCoreFormula
  services := [service12]
  recordPartition := by
    rw [served_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [servedGen_recordTree]
    simp [service12, mkService, recOf]
  readPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service12, mkService, dotCoreFormula] using
      readExps_recordTree_axis3 (encC seedZ) seedZ alphaA
        (.atom 1) dotCore 12
  verifyPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service12, mkService, dotCoreFormula] using
      verifyExps_recordTree_axis3 (encC seedZ) seedZ alphaA
        (.atom 1) dotCore 12
  traversal := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa [cfg_alpha, mappedRecordTree, dotCoreFormula] using
      (serviceWalk_recordTree_axis3 [service12] service12
        (encC seedZ) seedZ (.atom 1) dotCore 12
        (by simp)
        (by simp [service12, mkService, dotCoreFormula])
        (by simp [service12, mkService]) rfl
        (service_hexp _ _ _ _ _ _))

noncomputable def rootTrace8 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 8) where
  subject := dotArm
  services := [service13]
  recordPartition := by
    rw [served_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [servedGen_recordTree]
    simp [service13, mkService, recOf]
  readPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service13, mkService, dotArm, dotElem0, dotResult] using
      readExps_recordTree_axis3 (encC seedZ) seedZ alphaA
        (.atom 1) dotResult 13
  verifyPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service13, mkService, dotArm, dotElem0, dotResult] using
      verifyExps_recordTree_axis3 (encC seedZ) seedZ alphaA
        (.atom 1) dotResult 13
  traversal := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa [cfg_alpha, mappedRecordTree, dotArm, dotElem0, dotResult] using
      (serviceWalk_recordTree_axis3 [service13] service13
        (encC seedZ) seedZ (.atom 1) dotResult 13
        (by simp)
        (by simp [service13, mkService, dotArm, dotElem0]; rw [dotResult])
        (by simp [service13, mkService]) rfl
        (service_hexp _ _ _ _ _ _))

noncomputable def rootTrace9 :
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) (memIdx 9) where
  subject := dotCondFormula
  services := [service6]
  recordPartition := by
    rw [served_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [servedGen_recordTree]
    simp [service6, mkService, recOf]
  readPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service6, mkService, dotCondFormula, dotCondResult] using
      readExps_recordTree_axis3 (encC seedZ) seedZ alphaA
        (.atom 1) dotCondResult 6
  verifyPartition := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    refine List.Perm.of_eq ?_
    simpa [mappedRecordTree, service6, mkService, dotCondFormula, dotCondResult] using
      verifyExps_recordTree_axis3 (encC seedZ) seedZ alphaA
        (.atom 1) dotCondResult 6
  traversal := by
    rw [axis_at]
    simp only [forestTrees, memIdx, List.getElem_cons_succ, List.getElem_cons_zero]
    simpa [cfg_alpha, mappedRecordTree, dotCondFormula, dotCondResult] using
      (serviceWalk_recordTree_axis3 [service6] service6
        (encC seedZ) seedZ (.atom 1) dotCondResult 6
        (by simp)
        (by simp [service6, mkService, dotCondFormula]; rw [dotCondResult])
        (by simp [service6, mkService]) rfl
        (service_hexp _ _ _ _ _ _))

noncomputable def rootTraces : ∀ i : Fin (cfg seedZ alphaA).kMem,
    RootTrace (cfg seedZ alphaA) (execThreadedA seedZ alphaA) i
  | ⟨0, _⟩ => rootTrace0
  | ⟨1, _⟩ => rootTrace1
  | ⟨2, _⟩ => rootTrace2
  | ⟨3, _⟩ => rootTrace3
  | ⟨4, _⟩ => rootTrace4
  | ⟨5, _⟩ => rootTrace5
  | ⟨6, _⟩ => rootTrace6
  | ⟨7, _⟩ => rootTrace7
  | ⟨8, _⟩ => rootTrace8
  | ⟨9, _⟩ => rootTrace9
  | ⟨n + 10, h⟩ => absurd (show n + 10 < 10 by simp only [cfg] at h; exact h) (by omega)

theorem finRange_kMem :
    List.finRange (cfg seedZ alphaA).kMem =
      [⟨0, by simp [cfg]⟩, ⟨1, by simp [cfg]⟩, ⟨2, by simp [cfg]⟩,
       ⟨3, by simp [cfg]⟩, ⟨4, by simp [cfg]⟩, ⟨5, by simp [cfg]⟩,
       ⟨6, by simp [cfg]⟩, ⟨7, by simp [cfg]⟩, ⟨8, by simp [cfg]⟩,
       ⟨9, by simp [cfg]⟩] := by
  simp only [cfg]
  rfl

theorem mkService_ts (root child : Noun) (ax e : ℕ) hslot hmem :
    (cfg seedZ alphaA).challenges.α ^ (mkService root child ax e hslot hmem).exponent =
      alphaA ^ e := by
  change alphaA ^ timestampExp alphaA (alphaA ^ e) = alphaA ^ e
  exact (timestampExp_spec (α := (alphaA : K)) ⟨e, rfl⟩).symm

theorem forestTimestampPowers_eq :
    (List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers) =
      [alphaA ^ 1, alphaA ^ 2, alphaA ^ 3, alphaA ^ 4, alphaA ^ 5,
       alphaA ^ 7, alphaA ^ 8, alphaA ^ 9, alphaA ^ 10, alphaA ^ 11,
       alphaA ^ 12, alphaA ^ 13, alphaA ^ 6] := by
  rw [finRange_kMem]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, rootTraces]
  simp only [RootTrace.timestampPowers, RootTrace.exponents,
    rootTrace0, rootTrace1, rootTrace2, rootTrace3, rootTrace4,
    rootTrace5, rootTrace6, rootTrace7, rootTrace8, rootTrace9,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  simp only [service1, service2, service3, service4, service5, service6,
    service7, service8, service9, service10, service11, service12, service13]
  repeat rw [mkService_ts]
  rw [mkService_ts dotOp2B dotOp2Sf1 3 7 service7._proof_1 service7._proof_2,
    mkService_ts dotOp2C dotOp2Sf2 3 8 service8._proof_1 service8._proof_2,
    mkService_ts dotArm dotResult 3 13 service13._proof_1 service13._proof_2,
    mkService_ts dotCondFormula dotCondResult 3 6 service6._proof_1 service6._proof_2]

theorem pows_nodup (es : List ℕ)
    (hb : ∀ e ∈ es, e < 14) (hd : es.Nodup) :
    (es.map (fun e => alphaA ^ e)).Nodup := by
  induction es with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hd
    obtain ⟨ha, hl⟩ := hd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun e he => hb e (List.mem_cons_of_mem _ he)) hl⟩
    intro hmem
    obtain ⟨b, hb', heq⟩ := List.mem_map.mp hmem
    have hne : a ≠ b := fun h => ha (h ▸ hb')
    have ha' : a ∈ a :: l := List.mem_cons.mpr (Or.inl rfl)
    have hb'' : b ∈ a :: l := List.mem_cons.mpr (Or.inr hb')
    exact alphaA_pow_ne (hb a ha') (hb b hb'') hne heq.symm

theorem forestTimestampPowers_nodup :
    ((List.finRange (cfg seedZ alphaA).kMem).flatMap
      (fun i => (rootTraces i).timestampPowers)).Nodup := by
  rw [forestTimestampPowers_eq]
  refine pows_nodup [1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 6] ?_ (by decide)
  decide

theorem forestIndexRange_seed :
    IO.InRange (cfg seedZ alphaA).Ksz
      ((List.finRange (cfg seedZ alphaA).kMem).flatMap
        (fun i => (rootTraces i).timestampPowers)).length := by
  rw [forestTimestampPowers_eq]
  simp [IO.InRange, cfg]

theorem computeRow_state (i : Fin (cfg seedZ alphaA).compRows) :
    ((execThreaded seedZ alphaA).computeRowAt i).1 =
      (bfsLabelAt (dotTreeAir (K := K)) ((i : ℕ) + 1)).skel.state := by
  rw [computeRowAt_eq_threaded]
  exact renderNode_state seedZ alphaA _

theorem requiredServedLookups_zero (st : ComputeTable.State)
    (h0 : st ≠ .s0) (h9 : st ≠ .s9) :
    SemanticTrace.requiredServedLookups st = 0 := by
  cases st <;> simp [SemanticTrace.requiredServedLookups] at h0 h9 ⊢

theorem row_served_nil_of_state
    (i : Fin (cfg seedZ alphaA).compRows)
    (h : ((execThreaded seedZ alphaA).computeRowAt i).1 ≠ .s0 ∧
      ((execThreaded seedZ alphaA).computeRowAt i).1 ≠ .s9) :
    (rowData i).needs.served = [] := by
  have hlen := (rowData i).needs.served_count
  rw [requiredServedLookups_zero _ h.1 h.2] at hlen
  exact List.eq_nil_of_length_eq_zero hlen

def lookupTuple {z : K} (l : ServedNounLookup z) :
    ComputeTable.MemRec K × Noun × ℕ × Noun :=
  (l.record, l.root, l.axis, l.child)

theorem rowData_servedTuples (i : Fin (cfg seedZ alphaA).compRows) :
    (rowData i).needs.served.map lookupTuple =
      servedTuplesOf
        (skeletonRowAt (semanticSkeleton seedZ alphaA)
          (execThreaded seedZ alphaA) bindsAt_seed i)
        ((execThreaded seedZ alphaA).computeRowAt i).2.2.1 :=
  buildCoveredRow_servedTuples
    (skelAt_bounded i)
    (semanticSkeleton_operationalPremises _ (skelAt_mem i))
    (skeletonRowAt_binds (semanticSkeleton seedZ alphaA)
      (execThreaded seedZ alphaA) bindsAt_seed i)
    (row_comparison_faithful _ (skelAt_mem i))
    (row_comparison_leaves _ (skelAt_mem i))

theorem skelAt_five :
    skeletonRowAt (semanticSkeleton seedZ alphaA)
      (execThreaded seedZ alphaA) bindsAt_seed ⟨5, by simp [cfg]⟩ =
      dotOp9Skel := by
  have hlist := semanticSkeleton_computeRows seedZ alphaA
  have hlen :
      (computeSkeletonRows (semanticSkeleton seedZ alphaA)).length = 8 := by
    rw [hlist]; rfl
  have hlt : 5 < (computeSkeletonRows (semanticSkeleton seedZ alphaA)).length := by
    rw [hlen]; decide
  have hget : (computeSkeletonRows (semanticSkeleton seedZ alphaA))[5] =
      (dotOp9Tree (K := K)).label.skel := by
    have h := getElem_of_list_eq (n := 5) hlist hlt (by decide)
    rw [h]
    simp [List.getElem_cons_succ, List.getElem_cons_zero]
  simp [skeletonRowAt, List.get_eq_getElem]
  exact hget.trans rfl

theorem computeRowAt_five_mr3 :
    ((execThreaded seedZ alphaA).computeRowAt ⟨5, by simp [cfg]⟩).2.2.1.mr3 =
      recOf seedZ alphaA dotCore dotArm 2 11 := by
  rw [computeRowAt_eq_threaded]
  rw [renderNode_op9_row seedZ alphaA _ air_row_s9]
  rw [bfsLabelAt_air_skel6]
  simp only [renderOp9Row]
  rw [skeletonSubformula_dotOp9_core, skeletonSubformula_dotOp9_arm,
    skeletonMemoryAxis_dotOp9]
  simp [recOf, recExp_eq_getRecordExp]
  have h := liveRecordExps_air_named (K := K)
  simp [h]

theorem rowData_five_servedTuples :
    (rowData ⟨5, by simp [cfg]⟩).needs.served.map lookupTuple =
      [(recOf seedZ alphaA dotCore dotArm 2 11, dotCore, 2, dotArm)] := by
  rw [rowData_servedTuples, skelAt_five]
  have hs : (dotOp9Skel).state = .s9 := rfl
  simp [servedTuplesOf, lookupTuple, hs]
  rw [skeletonSubformula_dotOp9_core, skeletonSubformula_dotOp9_arm,
    skeletonMemoryAxis_dotOp9]
  simp [computeMemRec]
  rw [computeRowAt_five_mr3]

theorem computeRow_ne_s0_s9_of_ne_five
    (i : Fin (cfg seedZ alphaA).compRows) (hi : (i : ℕ) ≠ 5) :
    ((execThreaded seedZ alphaA).computeRowAt i).1 ≠ .s0 ∧
      ((execThreaded seedZ alphaA).computeRowAt i).1 ≠ .s9 := by
  have hst := computeRow_state i
  have hcfg : (cfg seedZ alphaA).compRows = 8 := by simp [cfg]
  have hi8 : (i : ℕ) < 8 := hcfg ▸ i.isLt
  constructor <;> (intro h; rw [hst] at h)
  · interval_cases (i : ℕ)
    · rw [air_row_s6] at h; cases h
    · rw [air_row_s2] at h; cases h
    · rw [air_row_s1_3] at h; cases h
    · rw [air_row_s1_4] at h; cases h
    · rw [air_row_s1_5] at h; cases h
    · exact hi rfl
    · rw [air_row_s1_7] at h; cases h
    · rw [air_row_s1_8] at h; cases h
  · interval_cases (i : ℕ)
    · rw [air_row_s6] at h; cases h
    · rw [air_row_s2] at h; cases h
    · rw [air_row_s1_3] at h; cases h
    · rw [air_row_s1_4] at h; cases h
    · rw [air_row_s1_5] at h; cases h
    · exact hi rfl
    · rw [air_row_s1_7] at h; cases h
    · rw [air_row_s1_8] at h; cases h

theorem row_served_nil_of_ne_five
    (i : Fin (cfg seedZ alphaA).compRows) (hi : (i : ℕ) ≠ 5) :
    (rowData i).needs.served = [] :=
  row_served_nil_of_state i (computeRow_ne_s0_s9_of_ne_five i hi)

noncomputable def memoryTrace
    (hfirst : ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.indicator = 0 ∧
      ((execThreaded seedZ alphaA).memoryPubAt ⟨0, (cfg seedZ alphaA).memRows_pos⟩).pt.counts = 0) :
    ExactServedMemoryTrace 769 Λ (cfg seedZ alphaA)
      (execThreaded seedZ alphaA) (semanticData hfirst) (execThreadedA seedZ alphaA) where
  roots := rootTraces
  timestampPowersNodup := forestTimestampPowers_nodup
  forestIndexRange := forestIndexRange_seed
  semanticCoverage := by
    intro row lookup hlookup
    have hmem : lookupTuple lookup ∈ (rowData row).needs.served.map lookupTuple :=
      List.mem_map.mpr ⟨lookup, hlookup, rfl⟩
    by_cases h5 : (row : ℕ) = 5
    · have hmap : (rowData row).needs.served.map lookupTuple =
          [(recOf seedZ alphaA dotCore dotArm 2 11, dotCore, 2, dotArm)] := by
        rw [show row = ⟨5, by simp [cfg]⟩ from Fin.ext h5]
        exact rowData_five_servedTuples
      rw [hmap] at hmem
      simp only [List.mem_singleton] at hmem
      refine ⟨memIdx 6, service11, ?_, ?_, ?_, ?_, ?_⟩
      · simp [memIdx, rootTraces, rootTrace6]
      · exact (congrArg Prod.fst hmem).symm
      · exact (congrArg (fun p => p.2.1) hmem).symm
      · exact (congrArg (fun p => p.2.2.2) hmem).symm
      · exact (congrArg (fun p => p.2.2.1) hmem).symm
    · rw [row_served_nil_of_ne_five row h5] at hmem
      simp at hmem

end Nock.NockVMROM.Thm54.TraceGen.DotConfig769

#print axioms Nock.NockVMROM.Thm54.TraceGen.serviceWalk_nounWalk
#print axioms Nock.NockVMROM.Thm54.TraceGen.serviceWalk_recordTree_axis3
#print axioms Nock.NockVMROM.Thm54.TraceGen.serviceWalk_recordTree_axis2
#print axioms Nock.NockVMROM.Thm54.TraceGen.serviceWalk_chain32
#print axioms Nock.NockVMROM.Thm54.TraceGen.timestampExp_pow_ne
#print axioms Nock.NockVMROM.Thm54.TraceGen.threadGenForest_map_memKey
#print axioms Nock.NockVMROM.Thm54.TraceGen.axisMTree_of_memKey
#print axioms Nock.NockVMROM.Thm54.TraceGen.servedGen_of_respKey
#print axioms Nock.NockVMROM.Thm54.TraceGen.servedGen_chain32
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.exactAxisTree_assigned
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.rootTrace0
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.rootTraces
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.forestTimestampPowers_nodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.computeRow_state
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.assignedForest_trees
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.rowData_five_servedTuples
#print axioms Nock.NockVMROM.Thm54.TraceGen.DotConfig769.memoryTrace

