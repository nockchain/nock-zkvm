/-
  Nock/NockVMROM/Thm54/TraceGen/ConsMemoryTrace.lean

  The same-execution served-memory
  trace of the BRANCHING slice `*[0 [[1 5] [1 6]]] = [5 6]`.

  The thirteen-row memory forest of `ConsConfig` services THREE committed records
  (`recCons`, `recL`, `recR`) through three nested `read_root`/`verify_child` pairs.  This module
  reifies that forest to its `MTree`, exhibits the three compute-side `Service`s, and assembles the
  single serviced root's `RootTrace`: the recursive noun-indexed `ServiceWalk` that pairs every
  `read_root` to its matching `verify_child` by FINGERPRINT VALUE — never by index
  (memoryless, positionless) — with the two exponent partitions carried as positionless `List.Perm`s.  The three distinct timestamps `α, α², α³` make the aggregate `z^i`
  multiset nodup, so the LogUp accumulator closes.

  The `RootTrace` and the aggregate timestamp facts here are self-contained: they consume no
  per-row AIR acceptance and no `ExactExecutionSemanticData`.  Assembling the full
  `ExactServedMemoryTrace` additionally needs the `ExactExecutionSemanticData` `language` (the
  still-open `ConsData` half); its `semanticCoverage` is then vacuous, because every `.cons`/`OP_1`
  row of this slice has an empty `needs.served` list (`ConsSemanticData`).
-/
import Nock.NockVMROM.Thm54.ServedMemoryTrace
import Nock.NockVMROM.Thm54.TraceGen.ConsConfig
import Nock.NockVMROM.Thm54.TraceGen.ConsSemanticData
import Nock.NockVMROM.Thm54.TraceGen.RowEncode

namespace Nock.NockVMROM.Thm54.TraceGen.ConsConfig

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.AxisBatching Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.TraceGen.ConsSkeleton

noncomputable section

/-! ## The three committed timestamps and their canonical exponents -/

theorem ts_recCons : recCons.ts = alphaA := rfl
theorem ts_recL : recL.ts = alphaA ^ 2 := rfl
theorem ts_recR : recR.ts = alphaA ^ 3 := rfl

theorem ts_closed_recCons : TimestampClosedAt cfg.challenges.α recCons.ts :=
  ⟨1, by rw [ts_recCons]; show alphaA = _; norm_num [cfg]⟩
theorem ts_closed_recL : TimestampClosedAt cfg.challenges.α recL.ts :=
  ⟨2, by rw [ts_recL]; rfl⟩
theorem ts_closed_recR : TimestampClosedAt cfg.challenges.α recR.ts :=
  ⟨3, by rw [ts_recR]; rfl⟩

/-- The `.cons` root request's canonical timestamp exponent. -/
def expCons : ℕ := timestampExp cfg.challenges.α recCons.ts
/-- The left `OP_1` child request's canonical timestamp exponent. -/
def expL : ℕ := timestampExp cfg.challenges.α recL.ts
/-- The right `OP_1` child request's canonical timestamp exponent. -/
def expR : ℕ := timestampExp cfg.challenges.α recR.ts

theorem ts_eq_recCons : recCons.ts = cfg.challenges.α ^ expCons :=
  timestampExp_spec ts_closed_recCons
theorem ts_eq_recL : recL.ts = cfg.challenges.α ^ expL :=
  timestampExp_spec ts_closed_recL
theorem ts_eq_recR : recR.ts = cfg.challenges.α ^ expR :=
  timestampExp_spec ts_closed_recR

/-! The three timestamps `α, α², α³` are pairwise distinct in `ZMod 97` (`α = 4`), so their
canonical exponents are pairwise distinct. -/

theorem alpha_pow_ne_12 : alphaA ≠ alphaA ^ 2 := by decide
theorem alpha_pow_ne_13 : alphaA ≠ alphaA ^ 3 := by decide
theorem alpha_pow_ne_23 : alphaA ^ 2 ≠ alphaA ^ 3 := by decide

theorem expCons_ne_expL : expCons ≠ expL := by
  intro h
  have heq : recCons.ts = recL.ts := by rw [ts_eq_recCons, ts_eq_recL, h]
  rw [ts_recCons, ts_recL] at heq
  exact alpha_pow_ne_12 heq
theorem expCons_ne_expR : expCons ≠ expR := by
  intro h
  have heq : recCons.ts = recR.ts := by rw [ts_eq_recCons, ts_eq_recR, h]
  rw [ts_recCons, ts_recR] at heq
  exact alpha_pow_ne_13 heq
theorem expL_ne_expR : expL ≠ expR := by
  intro h
  have heq : recL.ts = recR.ts := by rw [ts_eq_recL, ts_eq_recR, h]
  rw [ts_recL, ts_recR] at heq
  exact alpha_pow_ne_23 heq
theorem expL_ne_expCons : expL ≠ expCons := fun h => expCons_ne_expL h.symm
theorem expR_ne_expCons : expR ≠ expCons := fun h => expCons_ne_expR h.symm
theorem expR_ne_expL : expR ≠ expL := fun h => expL_ne_expR h.symm

/-! ## The reified memory `MTree` of the single serviced root -/

theorem memoryTreeAt_dummy :
    execA.memoryTreeAt ⟨0, by norm_num [cfg]⟩ = tDummyHaltA := rfl

theorem memoryTreeAt_root :
    execA.memoryTreeAt ⟨1, by norm_num [cfg]⟩ = rootTreeA := rfl

theorem axisPath_three : ServedMemoryTrace.axisPath 3 = [true] := by
  rw [ServedMemoryTrace.axisPath_of_two_le (by norm_num)]
  norm_num [ServedMemoryTrace.axisPath_of_lt_two]

set_option maxRecDepth 400000 in
theorem consAxisTree_eq :
    exactAxisTree cfg execA ⟨1, by norm_num [cfg]⟩ =
      MTree.read expCons
        (MTree.decompose
          (MTree.read expL
            (MTree.decompose MTree.halt
              (MTree.verify expL 3 MTree.halt)))
          (MTree.read expR
            (MTree.verify expCons 3
              (MTree.decompose MTree.halt
                (MTree.verify expR 3 MTree.halt))))) := by
  rw [exactAxisTree, memoryTreeAt_root]
  simp [rootTreeA, tDecFA, tReadLA, tReadRA, tDecLA, tVerifyFA, tHaltL1A, tVerifyLA, tDecRA,
    tHaltL5A,
    tHaltR1A, tVerifyRA, tHaltR6A, mOne, mTwo, mLeaf, lblOf,
    Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree, timestampExpAt,
    expCons, expL, expR, pReadFA, pDecFA, pReadLA, pReadRA, pDecLA, pVerifyFA, pHaltL1A, pVerifyLA,
    pDecRA, pHaltL5A, pHaltR1A, pVerifyRA, pHaltR6A,
    readPub, readPubA, decPub, decPubA, haltPub, haltPubA, verifyPub, verifyPubA, recCons, recL,
    recR]

/-! ## The three compute-side services -/

theorem rawRequests_eq :
    execA.rawRequests = [recCons, recL, recR] := by
  rw [ExactExecution.rawRequests_eq_computeRows, show execA.computeRows = exec.computeRows from rfl,
    computeRows_eq]
  simp [NockVM.activeRequestRecords, consRow, op1LRow, op1RRow, consPub, op1LPub, op1RPub,
    op1PubOf]

/-- The `.cons` root's service: opening the formula `[[1 5] [1 6]]` at axis `3` to `[1 6]`. -/
def serviceCons : Service cfg execA where
  exponent := expCons
  record := recCons
  root := formulaNoun
  child := rightFormula
  axis := 3
  request_mem := by rw [rawRequests_eq]; simp
  timestamp := ts_eq_recCons
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recCons] }
  served := by simp [formulaNoun, rightFormula, Noun.slot]

/-- The left `OP_1` child's service: opening `[1 5]` at axis `3` to `5`. -/
def serviceL : Service cfg execA where
  exponent := expL
  record := recL
  root := leftFormula
  child := leftResult
  axis := 3
  request_mem := by rw [rawRequests_eq]; simp
  timestamp := ts_eq_recL
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recL] }
  served := by simp [leftFormula, leftResult, Noun.slot]

/-- The right `OP_1` child's service: opening `[1 6]` at axis `3` to `6`. -/
def serviceR : Service cfg execA where
  exponent := expR
  record := recR
  root := rightFormula
  child := rightResult
  axis := 3
  request_mem := by rw [rawRequests_eq]; simp
  timestamp := ts_eq_recR
  realization :=
    { root_realizes := rfl
      child_realizes := rfl
      axis_realizes := by norm_num [recR] }
  served := by simp [rightFormula, rightResult, Noun.slot]

/-! ## The single serviced root's trace -/

theorem rootResponseRecords_eq :
    rootResponseRecords execA ⟨1, by norm_num [cfg]⟩ =
      [recCons, recL, recR] := by
  simp [rootResponseRecords, memoryTreeAt_root, rootTreeA, tDecFA, tReadLA, tReadRA, tDecLA,
    tVerifyFA,
    tHaltL1A, tVerifyLA, tDecRA, tHaltL5A, tHaltR1A, tVerifyRA, tHaltR6A, bfsForest,
    MemoryTable.responseRecords, lblOf, mOne, mTwo, mLeaf,
    pReadFA, pDecFA, pReadLA, pReadRA, pDecLA, pVerifyFA, pHaltL1A, pVerifyLA,
    pDecRA, pHaltL5A, pHaltR1A, pVerifyRA, pHaltR6A, readPub, readPubA, decPub, decPubA, haltPub,
    haltPubA, verifyPub, verifyPubA]

/-- The exact semantic service partition of the branching slice's single serviced root.

`recordPartition` is the literal `read_root` emission list; the two exponent partitions are the
paper's positionless LogUp permutations.  The `traversal` is the two-request pairing: `serviceCons`
is read at the root and verified deep in the right branch, `serviceL`/`serviceR` each read and
verified in their own branches — every pairing matched by fingerprint value, not by index. -/
def rootTrace : RootTrace cfg execA ⟨1, by norm_num [cfg]⟩ where
  subject := formulaNoun
  services := [serviceCons, serviceL, serviceR]
  recordPartition := by rw [rootResponseRecords_eq]; rfl
  readPartition := by
    rw [consAxisTree_eq]; simp [serviceCons, serviceL, serviceR, readExps]
  verifyPartition := by
    rw [consAxisTree_eq]
    simp only [verifyExps, serviceCons, serviceL, serviceR, List.map_cons,
      List.map_nil]
    exact List.Perm.swap expCons expL [expR]
  traversal := by
    rw [consAxisTree_eq]
    -- read serviceCons at the root formula noun
    refine ServiceWalk.read serviceCons (by simp) rfl rfl ?_ ?_
    · rw [show serviceCons.axis = 3 from rfl, axisPath_three]
      refine VerifyRoute.right (by simp [readCount]; exact expL_ne_expCons)
        (by simp [verifyCount]; exact expL_ne_expCons) ?_
      refine VerifyRoute.read_other expR_ne_expCons ?_
      exact VerifyRoute.here rfl rfl (by simp [readCount])
        (by simp [verifyCount]; exact expR_ne_expCons)
    · -- below: walk the decompose of the two child branches
      refine ServiceWalk.decompose ?_ ?_
      · -- left branch: read serviceL on leftFormula
        refine ServiceWalk.read serviceL (by simp) rfl rfl ?_ ?_
        · rw [show serviceL.axis = 3 from rfl, axisPath_three]
          refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
          exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])
        · exact ServiceWalk.decompose ServiceWalk.halt
            (ServiceWalk.verify ServiceWalk.halt)
      · -- right branch: read serviceR on rightFormula
        refine ServiceWalk.read serviceR (by simp) rfl rfl ?_ ?_
        · rw [show serviceR.axis = 3 from rfl, axisPath_three]
          refine VerifyRoute.verify_other expCons_ne_expR ?_
          refine VerifyRoute.right (by simp [readCount]) (by simp [verifyCount]) ?_
          exact VerifyRoute.here rfl rfl (by simp [readCount]) (by simp [verifyCount])
        · exact ServiceWalk.verify
            (ServiceWalk.decompose ServiceWalk.halt
              (ServiceWalk.verify ServiceWalk.halt))

theorem dummyAxisTree_eq :
    exactAxisTree cfg execA ⟨0, by norm_num [cfg]⟩ = MTree.halt := by
  rw [exactAxisTree, memoryTreeAt_dummy]
  simp [tDummyHaltA, mLeaf, lblOf, Nock.AxisBridge.ofNTree, Nock.AxisBridge.MemWalk.toMTree,
    timestampExpAt, pDummyHaltA, haltPub, haltPubA]

theorem dummyResponseRecords_eq :
    rootResponseRecords execA ⟨0, by norm_num [cfg]⟩ = [] := by
  simp [rootResponseRecords, memoryTreeAt_dummy, tDummyHaltA, mLeaf, bfsForest,
    MemoryTable.responseRecords, lblOf, pDummyHaltA, haltPub, haltPubA]

def dummyRootTrace : RootTrace cfg execA ⟨0, by norm_num [cfg]⟩ where
  subject := .atom 0
  services := []
  recordPartition := by rw [dummyResponseRecords_eq]; rfl
  readPartition := by rw [dummyAxisTree_eq]; simp [readExps]
  verifyPartition := by rw [dummyAxisTree_eq]; simp [verifyExps]
  traversal := by
    rw [dummyAxisTree_eq]
    exact ServiceWalk.halt

def rootTraces : ∀ i : Fin cfg.kMem, RootTrace cfg execA i
  | ⟨0, _⟩ => dummyRootTrace
  | ⟨1, _⟩ => rootTrace
  | ⟨n + 2, h⟩ => by
      simp only [cfg] at h
      omega

theorem rootTraces_dummy : rootTraces ⟨0, by norm_num [cfg]⟩ = dummyRootTrace := rfl
theorem rootTraces_root : rootTraces ⟨1, by norm_num [cfg]⟩ = rootTrace := rfl

theorem finRange_kMem :
    List.finRange cfg.kMem = [⟨0, by norm_num [cfg]⟩, ⟨1, by norm_num [cfg]⟩] := rfl

/-! ## The aggregate `z^i` timestamp multiset closes -/

theorem forestTimestampPowers_eq :
    (List.finRange cfg.kMem).flatMap (fun i => (rootTraces i).timestampPowers) =
      [alphaA, alphaA ^ 2, alphaA ^ 3] := by
  rw [finRange_kMem]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    rootTraces_dummy, rootTraces_root]
  simp only [RootTrace.timestampPowers, RootTrace.exponents, dummyRootTrace, rootTrace,
    List.map_cons, List.map_nil, List.append_nil, List.nil_append]
  rw [show (serviceCons.exponent : ℕ) = expCons from rfl,
    show (serviceL.exponent : ℕ) = expL from rfl,
    show (serviceR.exponent : ℕ) = expR from rfl,
    ← ts_eq_recCons, ← ts_eq_recL, ← ts_eq_recR, ts_recCons, ts_recL, ts_recR]

theorem forestTimestampPowers_nodup :
    ((List.finRange cfg.kMem).flatMap
      (fun i => (rootTraces i).timestampPowers)).Nodup := by
  rw [forestTimestampPowers_eq]
  have h12 := alpha_pow_ne_12
  have h13 := alpha_pow_ne_13
  have h23 := alpha_pow_ne_23
  simp [List.nodup_cons, h12, h13, h23]

/-- The whole forest's aggregate service-timestamp multiset lives in `[Ksz]`. -/
theorem forestIndexRange :
    IO.InRange cfg.Ksz
      ((List.finRange cfg.kMem).flatMap
        (fun i => (rootTraces i).timestampPowers)).length := by
  rw [forestTimestampPowers_eq]
  norm_num [IO.InRange, cfg]

/-! ## The executed trace is the row encode of the a-bearing view -/

theorem exec_encode : exec = execA.encodeMem :=
  RowEncode.eq_encodeMem_of rfl (by
    simp [exec, execA, tDummyHalt, tDummyHaltA, rootTree, rootTreeA, tDecF, tDecFA, tReadL,
      tReadLA, tReadR, tReadRA, tDecL, tDecLA, tVerifyF, tVerifyFA, tHaltL1, tHaltL1A, tVerifyL,
      tVerifyLA, tDecR, tDecRA, tHaltL5, tHaltL5A, tHaltR1, tHaltR1A, tVerifyR, tVerifyRA,
      tHaltR6, tHaltR6A, mOne, mTwo, mLeaf, mapNTree, lblOf, pDummyHalt, pDummyHaltA, pReadF,
      pReadFA, pDecF, pDecFA, pReadL, pReadLA, pReadR, pReadRA, pDecL, pDecLA, pVerifyF,
      pVerifyFA, pHaltL1, pHaltL1A, pVerifyL, pVerifyLA, pDecR, pDecRA, pHaltL5, pHaltL5A,
      pHaltR1, pHaltR1A, pVerifyR, pVerifyRA, pHaltR6, pHaltR6A, readPub, readPubA, verifyPub,
      verifyPubA, haltPub, haltPubA, decPub, decPubA])

end

end Nock.NockVMROM.Thm54.TraceGen.ConsConfig

#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.consAxisTree_eq
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.rootTrace
#print axioms Nock.NockVMROM.Thm54.TraceGen.ConsConfig.forestTimestampPowers_nodup
