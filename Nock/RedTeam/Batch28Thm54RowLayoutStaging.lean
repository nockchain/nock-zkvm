import Nock.NockVMROM.Thm54.MemoryMplus2L
import Nock.NockVMROM.Thm54.MultiRoundRAP
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
Nothing here is a prose verdict; every item is a compiled
statement about a concrete object.

1. **Non-vacuity of the `M + 2L` layout.**  A concrete five-row memory forest
   `read_root → decompose → (halt, verify_child → halt)` over `𝔽₁₇` with `M = 3`, `L = 1` on
   which `RowLayout.memory_rows_eq_M_add_two_mul_L_of_count_balance` fires with both `M` and `L`
   nonzero, together with the individual per-state counts.
2. **Compute `N` receipt** on the same execution.
3. **Co-residence receipt.**  A concrete finite-field IO witness (Packet C) accepted against the
   very records the `read_root` rows serve, with the selector-gated column over the same five
   memory rows reaching its terminal at row `M + 2L = 5`, stationary on the `verify_child` row.
   No appended `records + 1` phase is used.
4. **Staging receipts.**  The compute (`k = 2`, three sampled elements) and memory (`k = 1`, one
   sampled element) `StagedRAP` witnesses, their exact orbit order `e·2^h`, and the
   non-triviality of `constraints_respect_chronology`: a metadata-only `k = 2` staging with an
   empty chronology is *refuted*.
-/

namespace Nock.RedTeam.Batch28

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.RowLayout
open Nock.Framework.Thm54

noncomputable section

/-! ## A concrete configuration over `𝔽₁₇` -/

abbrev K17 := ZMod 17

instance b28_prime17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- `2` has exact multiplicative order `8 = 2³` in `𝔽₁₇`, so the five active memory rows fit in
the certified orbit. -/
theorem b28_omega_order : orderOf (2 : K17) = 8 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

def b28Orbit : OrbitDomain K17 where
  h := 3
  ω := 2
  βcoset := 1
  βcoset_ne_zero := by norm_num
  order_ω := by simpa using b28_omega_order

/-! ## One shared memory record -/

def recA : MemRec K17 where
  root := FP.atomFP 1 1
  child := FP.atomFP 1 2
  axis := 3
  ts := 4

theorem recA_ne_zero : recA ≠ (MemRec.zero : MemRec K17) := by
  intro h
  have hs := congrArg (fun r : MemRec K17 => r.root.size) h
  norm_num [recA, MemRec.zero, FP.atomFP] at hs

/-! ## The five-row memory forest -/

def mInp : MemoryTable.Inputs K17 := ⟨1, 0, 0⟩

def memPub (st : MState) (mem : MemRec K17) : MemoryTable.Pub K17 where
  st := st
  pt := Cell.zero
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := mem
  ipre := 0
  icur := 0

def readLabel : MState × MemoryTable.DTmem K17 :=
  (.read_root, (mInp, memPub .read_root recA))

def decompLabel : MState × MemoryTable.DTmem K17 :=
  (.decompose, (mInp, memPub .decompose MemRec.zero))

def haltLabel : MState × MemoryTable.DTmem K17 :=
  (.halt, (mInp, memPub .halt MemRec.zero))

def verifyLabel : MState × MemoryTable.DTmem K17 :=
  (.verify_child, (mInp, memPub .verify_child recA))

def haltTree : NTree (MState × MemoryTable.DTmem K17) := .node haltLabel []

def verifyTree : NTree (MState × MemoryTable.DTmem K17) := .node verifyLabel [haltTree]

def decompTree : NTree (MState × MemoryTable.DTmem K17) :=
  .node decompLabel [haltTree, verifyTree]

def memoryTree : NTree (MState × MemoryTable.DTmem K17) := .node readLabel [decompTree]

/-! ## The one-row compute tree -/

def cInp : ComputeTable.Inputs K17 := ⟨1, 1, 0, 0, 0⟩

def cPub : ComputeTable.Pub K17 where
  state := .s1
  s := 0
  f := 0
  e := 0
  sf1_s := 0
  sf1_f := 0
  sf1_e := 0
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 0
  ln := 1
  mr1 := recA
  mr2 := MemRec.zero
  mr3 := MemRec.zero

def cDec : ComputeTable.Dec K17 where
  f_h := 0
  f_t := 0
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

def cLabel : ComputeTable.State × ComputeTable.DTcomp K17 :=
  (.s1, (cInp, cPub, cDec))

def computeTree : NTree (ComputeTable.State × ComputeTable.DTcomp K17) := .node cLabel []

/-! ## The configuration and the execution -/

def b28Cfg : ExactConfig K17 K17 where
  challenges := { a := 0, b := 0, c := 0, α := 1, z := 1, β := 0, γ := 0, lam := MemoryTable.formRDefault }
  Ksz := 8
  kMem := 1
  orbit := b28Orbit
  orbit_h_pos := by norm_num [b28Orbit]
  compRows := 1
  memRows := 5
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by norm_num [b28Orbit]
  memRows_le := by norm_num [b28Orbit]
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => b28Orbit.orbitPoint i
  compNodes_spec := by intro i; rfl
  memNodes := fun i => b28Orbit.orbitPoint i
  memNodes_spec := by intro i; rfl

def b28Exec : ExactExecution b28Cfg where
  computeTree := computeTree
  memoryForest := [memoryTree]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, b28Cfg]
  memory_bfs_length := by
    norm_num [memoryTree, decompTree, verifyTree, haltTree, bfsForest, NTree.size, totalSize,
      b28Cfg]

/-- The BFS row lists really are the five memory rows and the one compute row. -/
theorem b28_rows :
    b28Exec.computeRows = [cLabel] ∧
      b28Exec.memoryRows = [readLabel, decompLabel, haltLabel, verifyLabel, haltLabel] := by
  constructor <;>
    norm_num [ExactExecution.computeRows, ExactExecution.memoryRows, b28Exec, computeTree,
      memoryTree, decompTree, verifyTree, haltTree, bfsForest, NTree.size, totalSize]

/-! ## 1. The `M + 2L` layout fires, with nonvacuous `M` and `L` -/

theorem b28_state_counts :
    memoryStateCount b28Exec .decompose = 1 ∧
      memoryStateCount b28Exec .halt = 2 ∧
      memoryStateCount b28Exec .read_root = 1 ∧
      memoryStateCount b28Exec .verify_child = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [memoryStateCount, fibreCount, b28_rows.2, readLabel, decompLabel, haltLabel,
      verifyLabel, memPub]

theorem b28_M : memoryM b28Exec = 3 := by
  simp [memoryM, b28_state_counts.1, b28_state_counts.2.1]

theorem b28_honest_ver :
    ∀ row ∈ b28Exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MState.read_root) := by
  simp [b28_rows.2, readLabel, decompLabel, haltLabel, verifyLabel, memPub]

theorem b28_L : memoryL b28Exec = 1 := by
  rw [← readRootCount_eq_L _ b28_honest_ver]
  exact b28_state_counts.2.2.1

/-- `M` and `L` are both nonzero: the layout receipt is not vacuous. -/
theorem b28_nonvacuous : 0 < memoryM b28Exec ∧ 0 < memoryL b28Exec := by
  rw [b28_M, b28_L]; exact ⟨by norm_num, by norm_num⟩

/-- The paper's record pairing holds: the `verify_child` row removes exactly the record the
`read_root` row added. -/
theorem b28_paired : PairedRecordLayout b28Exec := by
  show (consumedRecordList b28Exec).Perm (addedRecordList b28Exec)
  have hc : consumedRecordList b28Exec = [recA] := by
    simp [consumedRecordList, consumedRecords, b28_rows.2, readLabel, decompLabel, haltLabel,
      verifyLabel, memPub]
  have ha : addedRecordList b28Exec = [recA] := by
    simp [addedRecordList, MemoryTable.responseRecords, b28_rows.2, readLabel, decompLabel,
      haltLabel, verifyLabel, memPub]
  rw [hc, ha]

/-- The exact count premise needed by `M + 2L`; the stronger permutation witness above implies it
in this concrete positive control. -/
theorem b28_recordCountBalanced : RecordCountBalanced b28Exec :=
  recordCountBalanced_of_pairedRecordLayout b28_paired

/-- **Receipt.**  `memoryRows.length = M + 2L` fires on a concrete execution with `M = 3`,
`L = 1`, `M + 2L = 5`. -/
theorem b28_memory_rows_eq_M_add_two_mul_L :
    b28Exec.memoryRows.length = memoryM b28Exec + 2 * memoryL b28Exec :=
  memory_rows_eq_M_add_two_mul_memoryL_of_count_balance b28_recordCountBalanced

theorem b28_memory_rows_numeric : b28Exec.memoryRows.length = 5 := by
  rw [b28_memory_rows_eq_M_add_two_mul_L, b28_M, b28_L]

/-- The equivalence has teeth in this instance too: the budget holds exactly because the
`verify_child` count matches the `read_root` count. -/
theorem b28_layout_iff_balanced :
    b28Exec.memoryRows.length = memoryM b28Exec + 2 * memoryL b28Exec
      ↔ RecordCountBalanced b28Exec :=
  memory_rows_eq_M_add_two_mul_memoryL_iff b28Exec b28_honest_ver

/-! ## 2. The compute `N` receipt -/

theorem b28_computeRows_count : b28Exec.computeRows.length = b28Cfg.compRows :=
  computeRows_count b28Exec

theorem b28_computeRows_numeric : b28Exec.computeRows.length = 1 := by
  rw [b28_computeRows_count]
  rfl

/-- `N` is genuinely the opcode-row count: the eleven per-opcode counts sum to `N`, and here the
only occupied opcode is `OP_1`. -/
theorem b28_opcode_partition :
    (computeStates.map (opcodeRowCount b28Exec)).sum = b28Cfg.compRows :=
  computeRows_opcode_partition b28Exec

theorem b28_opcode_s1 : opcodeRowCount b28Exec .s1 = 1 := by
  simp [opcodeRowCount, fibreCount, b28_rows.1, cLabel]

/-! ## 3. Co-residence: no appended IO phase -/

/-- The rows' served-record list, encoded: exactly the one record the single `read_root` row
serves. -/
theorem b28_derivedResponseIO : b28Exec.derivedResponseIO = [encRecC recA 1] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, b28_rows.2]
  simp [MemoryTable.Pub.cprime, readLabel, decompLabel, haltLabel, verifyLabel, memPub]

@[reducible] def ioCoins : FiniteIO.IOCoins K17 := ⟨0, 0⟩

@[reducible] def ioRecords : FiniteIO.PreChallengeRecords K17 9 where
  requests := [encRecC recA 1]
  responses := [encRecC recA 1]

theorem b28_compress_recA : FiniteIO.compress ioCoins (encRecC recA 1) = 1 := by
  simp [FiniteIO.compress, Walk.rlc, Fin.sum_univ_succ, encRecC, recA, FP.atomFP]

def ioWitness : FiniteIO.PostChallengeIOWitness ioRecords ioCoins where
  requestInv := fun _ => 1
  responseInv := fun _ => 1
  multiplicity := fun _ => 1
  multInv := fun _ => 1
  requestAcc := ![0, 1]
  responseAcc := ![0, 1]
  terminal := 1

theorem b28_ioWitness_accepts : FiniteIO.FiniteIOAccepts ioRecords ioCoins ioWitness := by
  refine
    { requestInvPin := ?_, responseInvPin := ?_, multBool := ?_, multInvPin := ?_,
      requestInit := ?_, requestStep := ?_, responseInit := ?_, responseStep := ?_,
      requestTerm := ?_, responseTerm := ?_ }
  · intro i
    fin_cases i
    simpa [ioWitness, ioRecords] using b28_compress_recA
  · intro j
    fin_cases j
    simpa [ioWitness, ioRecords] using b28_compress_recA
  · intro _; norm_num [ioWitness]
  · intro _; norm_num [ioWitness]
  · rfl
  · intro i; fin_cases i; norm_num [ioWitness]
  · rfl
  · intro j; fin_cases j; norm_num [ioWitness]
  · rfl
  · rfl

/-- **Receipt.**  The Packet-C IO accumulator is co-resident with the memory table: it is a
`read_root`-gated column over the same five rows, reaching Packet C's record-indexed terminal at
row `M + 2L = 5`.  No `records + 1` phase is appended. -/
theorem b28_no_appended_io_phase :
    NoAppendedIOPhase b28Exec ioCoins ioWitness :=
  noAppendedIOPhase_of_accepts b28Exec b28_ioWitness_accepts b28_derivedResponseIO.symm

/-- The gated column is stationary on the `verify_child` row: it is the same column, not a second
one. -/
theorem b28_stationary_on_verify_child :
    coResidentAcc (FiniteIO.compress ioCoins) b28Exec.memoryRows 4 = coResidentAcc (FiniteIO.compress ioCoins) b28Exec.memoryRows 3 := by
  simp [coResidentAcc, b28_rows.2, ioRowTerm, ioSelector, readLabel, decompLabel, haltLabel,
    verifyLabel, memPub]

/-- The column's terminal at row `5` is the sum over the `L = 1` served records. -/
theorem b28_coResident_terminal :
    coResidentAcc (FiniteIO.compress ioCoins) b28Exec.memoryRows b28Exec.memoryRows.length = 1 := by
  rw [coResidentAcc_last b28Exec (FiniteIO.compress ioCoins), b28_derivedResponseIO]
  simp [b28_compress_recA]

/-! ## 4. Staging receipts -/

open Nock.NockVMROM.Thm54.Staging

/-- The compute chip: two rounds of interaction delivering three `K` elements;
the memory chip: one round delivering one element. -/
theorem b28_staged_round_counts :
    computeStagedRAP.rap.k = 2 ∧ computeStagedRAP.chronology.numChallenges = 3
      ∧ memoryStagedRAP.rap.k = 1 ∧ memoryStagedRAP.chronology.numChallenges = 1 :=
  staged_round_counts

/-- Staging carries the `Def:RAP` order condition the bare `RAP` structure omits. -/
theorem b28_staged_orbit_orders :
    orderOf computeStagedRAP.rap.ω
        = computeStagedRAP.rap.e * 2 ^ computeStagedRAP.rap.h ∧
      orderOf memoryStagedRAP.rap.ω
        = memoryStagedRAP.rap.e * 2 ^ memoryStagedRAP.rap.h :=
  ⟨computeStagedRAP_order, memoryStagedRAP_order⟩

/-- **Non-triviality.**  A metadata-only `k = 2` staging — an empty chronology, with the
constraint that really reads the round-`1` column claimed to be discharged at round `0` — is
rejected by `constraints_respect_chronology`. -/
theorem b28_metadata_only_staging_rejected :
    ¬ RespectsChronology computeBase computeSchedule emptyChronology
        (fun _ => 0) (fun _ => ∅) :=
  metadataOnlyStaging_rejected

/-- The same objects with the constraint honestly discharged at round `1` *are* accepted, so the
rejection above is a chronology check, not an unsatisfiable predicate. -/
theorem b28_honest_staging_accepted :
    RespectsChronology computeBase computeSchedule emptyChronology
      (fun _ => 1) (fun _ => ∅) :=
  honestStaging_accepted

/-- The challenge half is non-trivial too. -/
theorem b28_late_challenge_rejected :
    ¬ RespectsChronology computeBase computeSchedule lateChronology
        (fun _ => 0) (fun _ => {0}) :=
  lateChallengeStaging_rejected

/-- `commit_then_sample` is a real prohibition on the compute witness: its round-`1` column may
not depend on the element sampled after round `1`. -/
theorem b28_commit_then_sample :
    ∀ j ∈ computeColumnChallenges 1,
      (computeChronology.sampledAfter j : ℕ) < (computeSchedule.roundOf 1 : ℕ) :=
  computeStagedRAP.columns_commit_before_sampling 1

end

end Nock.RedTeam.Batch28

#print axioms Nock.RedTeam.Batch28.b28_omega_order
#print axioms Nock.RedTeam.Batch28.b28_rows
#print axioms Nock.RedTeam.Batch28.b28_state_counts
#print axioms Nock.RedTeam.Batch28.b28_M
#print axioms Nock.RedTeam.Batch28.b28_L
#print axioms Nock.RedTeam.Batch28.b28_nonvacuous
#print axioms Nock.RedTeam.Batch28.b28_paired
#print axioms Nock.RedTeam.Batch28.b28_recordCountBalanced
#print axioms Nock.RedTeam.Batch28.b28_memory_rows_eq_M_add_two_mul_L
#print axioms Nock.RedTeam.Batch28.b28_memory_rows_numeric
#print axioms Nock.RedTeam.Batch28.b28_layout_iff_balanced
#print axioms Nock.RedTeam.Batch28.b28_computeRows_count
#print axioms Nock.RedTeam.Batch28.b28_computeRows_numeric
#print axioms Nock.RedTeam.Batch28.b28_opcode_partition
#print axioms Nock.RedTeam.Batch28.b28_opcode_s1
#print axioms Nock.RedTeam.Batch28.b28_derivedResponseIO
#print axioms Nock.RedTeam.Batch28.b28_compress_recA
#print axioms Nock.RedTeam.Batch28.b28_ioWitness_accepts
#print axioms Nock.RedTeam.Batch28.b28_no_appended_io_phase
#print axioms Nock.RedTeam.Batch28.b28_stationary_on_verify_child
#print axioms Nock.RedTeam.Batch28.b28_coResident_terminal
#print axioms Nock.RedTeam.Batch28.b28_staged_round_counts
#print axioms Nock.RedTeam.Batch28.b28_staged_orbit_orders
#print axioms Nock.RedTeam.Batch28.b28_metadata_only_staging_rejected
#print axioms Nock.RedTeam.Batch28.b28_honest_staging_accepted
#print axioms Nock.RedTeam.Batch28.b28_late_challenge_rejected
#print axioms Nock.RedTeam.Batch28.b28_commit_then_sample
