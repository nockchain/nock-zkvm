/-
  Nock/NockVMROM/Thm54/TraceGen/Op1ConfigK3.lean

  Step 1 of re-basing the OP1 slice `*[0 [1 5]] = 5` over the computable cubic field
  `K3 = ZMod 97[X]/(X^3 - 5)`: the `ExactConfig (ZMod 97) K3` and `ExactExecution` carriers,
  with base field `F = ZMod 97` and table/RAP field `K = K3` (`finrank F K = 3`).

  This is the semantic-carrier re-basing named in `GenStatement.lean`'s footer: the `Inputs`
  wall (`inputs_op1Execution_isEmpty`) holds *only* because the original OP1 slice is over
  `F = K = ZMod 97` (`finrank = 1`).  Moving the table field to `K3` removes that obstruction.

  The seed `z = 8` and timestamp challenge `α = 4` are the base-field images
  `algebraMap (ZMod 97) K3 8` / `… 4`, and the orbit generator is `algebraMap … 64`, so every
  field equation reduces to `ZMod 97` arithmetic through the injective algebra map.  The
  field-free `Op1Skeleton` transports unchanged (it mentions only nouns/axes/topology).
-/
import Nock.NockVMROM.Thm54.Execution
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton
import Nock.NockVMROM.Thm54.TraceGen.CubicField97
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton
open Nock.NockVMROM.Thm54.TraceGen.CubicField97

/-- The base (semantic) field. -/
abbrev F : Type := ZMod 97

/-- The table/RAP field: the computable cubic extension with `finrank F K3 = 3`. -/
abbrev K : Type := CubicField97.K3

/-- The injective algebra map `ZMod 97 →+* K3`; every honest field value is one of its images. -/
noncomputable abbrev φ : F →+* K := algebraMap F K

theorem φ_injective : Function.Injective φ := RingHom.injective φ

/-! ## The execution orbit over `K3` -/

/-- `64` has multiplicative order eight in `ZMod 97`. -/
theorem omega64_order_base : orderOf (64 : F) = 8 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

/-- The image `φ 64` keeps multiplicative order eight in `K3` (order is preserved by the
injective ring hom). -/
theorem omega64_order : orderOf (φ (64 : F)) = 8 := by
  have h := orderOf_injective φ.toMonoidHom φ_injective (64 : F)
  rw [omega64_order_base] at h
  simpa using h

/-- The five-row exact execution orbit over `K3`. -/
noncomputable def executionOrbit : OrbitDomain K where
  h := 3
  ω := φ (64 : F)
  βcoset := 1
  βcoset_ne_zero := one_ne_zero
  order_ω := by simpa using omega64_order

/-! ## Seed-dependent field rows (parametrized by `z α : K3`) -/

noncomputable section

/-- The seed-`z` fingerprint of a committed noun, over `K3`. -/
noncomputable def fp (z : K) (n : Noun) : FP K := GlobalCarryRecognizer.enc z n

/-- The single live memory record of the `OP_1` row `(f, f_t, 3, α)`. -/
def requestRecord (z α : K) : MemRec K where
  root := fp z formulaNoun
  child := fp z resultNoun
  axis := 3
  ts := α

noncomputable def rowRecord (z α : K) : MemRec K :=
  NockVM.formRRow (requestRecord z α) MemoryTable.formRDefault

/-- Row-level `C'` of `requestRecord`. -/
noncomputable def rowCprime (z α : K) : K :=
  NockVM.formRCprime (requestRecord z α) MemoryTable.formRDefault

def computeInputs (z α : K) : ComputeTable.Inputs K where
  α := α
  z := z
  a := 0
  b := 0
  c := 0

def computeDec (z : K) : ComputeTable.Dec K where
  f_h := fp z headNoun
  f_t := fp z resultNoun
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

def computePub (z α : K) : ComputeTable.Pub K where
  state := .s1
  s := fp z subjectNoun
  f := fp z formulaNoun
  e := fp z resultNoun
  sf1_s := 0
  sf1_f := 0
  sf1_e := 0
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := α
  mr1 := requestRecord z α
  mr2 := MemRec.zero
  mr3 := MemRec.zero

def computeRow (z α : K) : ComputeTable.State × ComputeTable.DTcomp K :=
  (.s1, computeInputs z α, computePub z α, computeDec z)

def memoryInputs (z : K) : MemoryTable.Inputs K := ⟨z, 0, 0⟩

/-- Dummy-wired to `Gen.memReadPub` remaining (`0`) so `Op1GenDataK3` agrees. -/
def seedCell (z α : K) : Cell K := ⟨fp z formulaNoun, 0, 0⟩
/-- Dummy-wired to `Gen.memReadPub.lc` / `memDecomposePub.pt`. -/
def decomposeCell (z α : K) : Cell K := ⟨fp z formulaNoun, 4, 4⟩
def headCell (z : K) : Cell K := ⟨fp z headNoun, 0, 0⟩
/-- Dummy-wired to `Gen.memDecomposePub.rc` / `memVerifyPub.pt`. -/
def verifyCell (z α : K) : Cell K := ⟨fp z resultNoun, 4, 12⟩
def tailCell (z : K) : Cell K := ⟨fp z resultNoun, 0, 0⟩
def dummyHaltCell (z : K) : Cell K := ⟨fp z (.atom 0), 0, 0⟩

/-- The single service reciprocal `pole⁻¹` of the one committed record's root fingerprint. -/
def reqPoleInv (z : K) : K := ((fp z formulaNoun).size)⁻¹

def readPub (z α : K) : MemoryTable.Pub K where
  st := .read_root
  pt := seedCell z α
  lc := decomposeCell z α
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := rowRecord z α
  cprime? := some (rowCprime z α)
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := reqPoleInv z

def decomposePub (z _α : K) : MemoryTable.Pub K where
  st := .decompose
  pt := decomposeCell z _α
  lc := headCell z
  rc := verifyCell z _α
  lcSt := .halt
  rcSt := .verify_child
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := reqPoleInv z
  icur := reqPoleInv z

def headPub (z : K) : MemoryTable.Pub K where
  st := .halt
  pt := headCell z
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := reqPoleInv z
  icur := reqPoleInv z

def verifyPub (z α : K) : MemoryTable.Pub K where
  st := .verify_child
  pt := verifyCell z α
  lc := tailCell z
  rc := Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := rowRecord z α
  cprime? := some (rowCprime z α)
  lambda? := some MemoryTable.formRDefault
  ipre := reqPoleInv z
  icur := 0

def tailPub (z : K) : MemoryTable.Pub K where
  st := .halt
  pt := tailCell z
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

def dummyHaltPub (z : K) : MemoryTable.Pub K where
  st := .halt
  pt := dummyHaltCell z
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

def readRow (z α : K) : MState × MemoryTable.DTmem K := (.read_root, memoryInputs z, readPub z α)
def decomposeRow (z α : K) : MState × MemoryTable.DTmem K := (.decompose, memoryInputs z, decomposePub z α)
def headRow (z : K) : MState × MemoryTable.DTmem K := (.halt, memoryInputs z, headPub z)
def verifyRow (z α : K) : MState × MemoryTable.DTmem K := (.verify_child, memoryInputs z, verifyPub z α)
def tailRow (z : K) : MState × MemoryTable.DTmem K := (.halt, memoryInputs z, tailPub z)

def dummyHaltRow (z : K) : MState × MemoryTable.DTmem K := (.halt, memoryInputs z, dummyHaltPub z)

def dummyHaltTree (z : K) : NTree (MState × MemoryTable.DTmem K) := .node (dummyHaltRow z) []
def tailTree (z : K) : NTree (MState × MemoryTable.DTmem K) := .node (tailRow z) []
def verifyTree (z α : K) : NTree (MState × MemoryTable.DTmem K) := .node (verifyRow z α) [tailTree z]
def headTree (z : K) : NTree (MState × MemoryTable.DTmem K) := .node (headRow z) []
def decomposeTree (z α : K) : NTree (MState × MemoryTable.DTmem K) :=
  .node (decomposeRow z α) [headTree z, verifyTree z α]
def readTree (z α : K) : NTree (MState × MemoryTable.DTmem K) := .node (readRow z α) [decomposeTree z α]

/-! ## The concrete configuration and execution -/

/-- The OP1/K3 slice's shared configuration. -/
def cfg (z α : K) : ExactConfig F K where
  challenges := { a := 0, b := 0, c := 0, α := α, z := z, β := 0, γ := 0, lam := MemoryTable.formRDefault }
  Ksz := 4
  kMem := 2
  orbit := executionOrbit
  orbit_h_pos := by norm_num [executionOrbit]
  compRows := 1
  memRows := 6
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by norm_num [executionOrbit]
  memRows_le := by norm_num [executionOrbit]
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => executionOrbit.orbitPoint i
  compNodes_spec := by intro i; rfl
  memNodes := fun i => executionOrbit.orbitPoint i
  memNodes_spec := by intro i; rfl

/-- The fixture's configured `λ` is `formRDefault`. -/
@[simp] theorem cfg_lam (z α : K) : (cfg z α).challenges.lam = MemoryTable.formRDefault := rfl

/-- The OP1/K3 slice's authoritative forest-first execution. -/
def exec (z α : K) : ExactExecution (cfg z α) where
  computeTree := .node (computeRow z α) []
  memoryForest := [dummyHaltTree z, readTree z α]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [dummyHaltTree, readTree, decomposeTree, headTree, verifyTree, tailTree,
      bfsForest, NTree.size, totalSize, cfg]

/-! ## The a-bearing view

The served memory
trace and all axis accounting live on `execA`. -/

@[simp] def readPubA (z α : K) : MemoryTable.Pub K :=
  { readPub z α with mem := requestRecord z α, cprime? := none, lambda? := none }
@[simp] def decomposePubA (z α : K) : MemoryTable.Pub K := { decomposePub z α with lambda? := none }
@[simp] def headPubA (z : K) : MemoryTable.Pub K := { headPub z with lambda? := none }
@[simp] def verifyPubA (z α : K) : MemoryTable.Pub K :=
  { verifyPub z α with mem := requestRecord z α, cprime? := none, lambda? := none }
@[simp] def tailPubA (z : K) : MemoryTable.Pub K := { tailPub z with lambda? := none }
@[simp] def dummyHaltPubA (z : K) : MemoryTable.Pub K := { dummyHaltPub z with lambda? := none }

def readRowA (z α : K) : MState × MemoryTable.DTmem K :=
  (.read_root, memoryInputs z, readPubA z α)
def decomposeRowA (z α : K) : MState × MemoryTable.DTmem K :=
  (.decompose, memoryInputs z, decomposePubA z α)
def headRowA (z : K) : MState × MemoryTable.DTmem K := (.halt, memoryInputs z, headPubA z)
def verifyRowA (z α : K) : MState × MemoryTable.DTmem K :=
  (.verify_child, memoryInputs z, verifyPubA z α)
def tailRowA (z : K) : MState × MemoryTable.DTmem K := (.halt, memoryInputs z, tailPubA z)
def dummyHaltRowA (z : K) : MState × MemoryTable.DTmem K :=
  (.halt, memoryInputs z, dummyHaltPubA z)

def dummyHaltTreeA (z : K) : NTree (MState × MemoryTable.DTmem K) := .node (dummyHaltRowA z) []
def tailTreeA (z : K) : NTree (MState × MemoryTable.DTmem K) := .node (tailRowA z) []
def verifyTreeA (z α : K) : NTree (MState × MemoryTable.DTmem K) :=
  .node (verifyRowA z α) [tailTreeA z]
def headTreeA (z : K) : NTree (MState × MemoryTable.DTmem K) := .node (headRowA z) []
def decomposeTreeA (z α : K) : NTree (MState × MemoryTable.DTmem K) :=
  .node (decomposeRowA z α) [headTreeA z, verifyTreeA z α]
def readTreeA (z α : K) : NTree (MState × MemoryTable.DTmem K) :=
  .node (readRowA z α) [decomposeTreeA z α]

/-- The a-bearing view of `exec`: same compute tree, a-bearing memory rows. -/
def execA (z α : K) : ExactExecution (cfg z α) where
  computeTree := .node (computeRow z α) []
  memoryForest := [dummyHaltTreeA z, readTreeA z α]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [dummyHaltTreeA, readTreeA, decomposeTreeA, headTreeA, verifyTreeA, tailTreeA,
      bfsForest, NTree.size, totalSize, cfg]

end

/-- The concrete honest seed `z = 8` (`= φ 8`, the base-field image; kept as a `K3` literal so
the row-web field equations reduce by `decide`). -/
def seedZ : K := 8
/-- The concrete honest timestamp challenge `α = 4` (`= φ 4`). -/
def alphaA : K := 4

/-- The seed is the base-field image of `8 : ZMod 97`. -/
theorem seedZ_eq_image : seedZ = φ (8 : F) := by rw [seedZ]; simp [map_ofNat]
/-- The timestamp challenge is the base-field image of `4 : ZMod 97`. -/
theorem alphaA_eq_image : alphaA = φ (4 : F) := by rw [alphaA]; simp [map_ofNat]

theorem seedZ_ne_zero : seedZ ≠ 0 := by rw [seedZ]; decide

/-- The compute carrier is exactly one row, the memory carrier exactly six. -/
theorem exec_row_counts :
    (exec seedZ alphaA).computeRows.length = 1 ∧
      (exec seedZ alphaA).memoryRows.length = 6 :=
  ⟨(exec seedZ alphaA).computeRows_length, (exec seedZ alphaA).memoryRows_length⟩

end Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.exec
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.omega64_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1ConfigK3.exec_row_counts
