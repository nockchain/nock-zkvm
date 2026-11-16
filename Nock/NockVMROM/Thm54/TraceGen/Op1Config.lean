/-
  Nock/NockVMROM/Thm54/TraceGen/Op1Config.lean

  The concrete `ExactConfig` and `ExactExecution` carriers
  of the fresh ROM program `*[0 [1 5]] = 5`, over `F = K = ZMod 97`.

  These are the two structural halves of the eventual `BuildableNockExecution (ZMod 97) (ZMod 97)`
  that carry no soundness/semantic obligation: `ExactConfig` is the shared challenge/orbit/domain
  data, and `ExactExecution` is the authoritative forest-first carrier — one
  `OP_1` compute row and the five-row memory reconstruction `read_root -> decompose -> (halt,
  verify_child -> halt)` in BFS order `read, dec, halt_1, verify, halt_r` —
  whose only proof obligations are the tree BFS lengths.

  Constants (plan day-one): seed `z = 8` (order 16), timestamp challenge `α = 4`, `a = b = c = 0`,
  memory challenges `β = γ = 0`, execution orbit `⟨h := 3, ω := 64, βcoset := 1⟩` with
  `orderOf (64 : ZMod 97) = 8`, `compRows = 1`, `memRows = 5`, `kMem = 1`, `eDeg = 1`, `Ksz = 4`.

  The row fingerprint columns are `GlobalCarryRecognizer.enc z ·` of the committed nouns, so the
  rows bind to `Op1Skeleton.semanticSkeleton` at the sampled seed; the LogUp/timestamp accumulator
  layout mirrors the released F73 honest layout adapted to `result = 5`.  `ExactExecution` imposes
  no acceptance condition on these columns; their per-row AIR acceptance is part of the still-open
  `ExactExecutionSemanticData`/`ExactServedMemoryTrace` (see the module header of `Op1Skeleton`).
-/
import Nock.NockVMROM.Thm54.Execution
import Nock.GlobalCarryRecognizer
import Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

namespace Nock.NockVMROM.Thm54.TraceGen.Op1Config

open Nock Nock.Walk
open Nock.ComputeTable Nock.MemoryTable
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen.Op1Skeleton

/-- `ZMod 97` is a field. -/
instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The Phase-1 slice base and table field coincide (`eDeg = 1`). -/
abbrev F : Type := ZMod 97

/-! ## The execution orbit -/

/-- `64` has exact multiplicative order eight in `ZMod 97`, so it drives the five-row execution
orbit of exponent `h = 3`. -/
theorem omega64_order : orderOf (64 : ZMod 97) = 8 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

/-- The five-row exact execution orbit. -/
def executionOrbit : OrbitDomain F where
  h := 3
  ω := 64
  βcoset := 1
  βcoset_ne_zero := by norm_num
  order_ω := by simpa using omega64_order

/-! ## Seed-dependent field rows -/

noncomputable section

/-- The seed-`z` fingerprint of a committed noun. -/
def fp (z : F) (n : Noun) : FP F := GlobalCarryRecognizer.enc z n

/-- The single live memory record of the `OP_1` row `(f, f_t, 3, α)`. -/
def requestRecord (z α : F) : MemRec F where
  root := fp z formulaNoun
  child := fp z resultNoun
  axis := 3
  ts := α

noncomputable def rowRecord (z α : F) : MemRec F :=
  NockVM.formRRow (requestRecord z α) MemoryTable.formRDefault

/-- Row-level `C'` of `requestRecord`. -/
noncomputable def rowCprime (z α : F) : F :=
  NockVM.formRCprime (requestRecord z α) MemoryTable.formRDefault

def computeInputs (z α : F) : ComputeTable.Inputs F where
  α := α
  z := z
  a := 0
  b := 0
  c := 0

def computeDec (z : F) : ComputeTable.Dec F where
  f_h := fp z headNoun
  f_t := fp z resultNoun
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

def computePub (z α : F) : ComputeTable.Pub F where
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

def computeRow (z α : F) : ComputeTable.State × ComputeTable.DTcomp F :=
  (.s1, computeInputs z α, computePub z α, computeDec z)

def memoryInputs (z : F) : MemoryTable.Inputs F := ⟨z, 0, 0⟩

/-- Dummy-wired to `Gen.memReadPub` remaining (`0`) so `Op1GenData` agrees. -/
def seedCell (z α : F) : Cell F := ⟨fp z formulaNoun, 0, 0⟩
/-- Dummy-wired to `Gen.memReadPub.lc` / `memDecomposePub.pt`. -/
def decomposeCell (z α : F) : Cell F := ⟨fp z formulaNoun, 4, 4⟩
def headCell (z : F) : Cell F := ⟨fp z headNoun, 0, 0⟩
/-- Dummy-wired to `Gen.memDecomposePub.rc` / `memVerifyPub.pt`. -/
def verifyCell (z α : F) : Cell F := ⟨fp z resultNoun, 4, 12⟩
def tailCell (z : F) : Cell F := ⟨fp z resultNoun, 0, 0⟩
def dummyHaltCell (z : F) : Cell F := ⟨fp z (.atom 0), 0, 0⟩

/-- The single service reciprocal `pole⁻¹` of the one committed record's root fingerprint
`[1 5]`; the honest LogUp `intermediate` step reads `+pole⁻¹` at `read_root` and `-pole⁻¹` at
`verify_child`.  With `β = γ = 0` the pole is `(fp z [1 5]).size = z²`. -/
def reqPoleInv (z : F) : F := ((fp z formulaNoun).size)⁻¹

def readPub (z α : F) : MemoryTable.Pub F where
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

def decomposePub (z _α : F) : MemoryTable.Pub F where
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

def headPub (z : F) : MemoryTable.Pub F where
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

def verifyPub (z α : F) : MemoryTable.Pub F where
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

def tailPub (z : F) : MemoryTable.Pub F where
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

def dummyHaltPub (z : F) : MemoryTable.Pub F where
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

def readRow (z α : F) : MState × MemoryTable.DTmem F := (.read_root, memoryInputs z, readPub z α)
def decomposeRow (z α : F) : MState × MemoryTable.DTmem F := (.decompose, memoryInputs z, decomposePub z α)
def headRow (z : F) : MState × MemoryTable.DTmem F := (.halt, memoryInputs z, headPub z)
def verifyRow (z α : F) : MState × MemoryTable.DTmem F := (.verify_child, memoryInputs z, verifyPub z α)
def tailRow (z : F) : MState × MemoryTable.DTmem F := (.halt, memoryInputs z, tailPub z)

def dummyHaltRow (z : F) : MState × MemoryTable.DTmem F := (.halt, memoryInputs z, dummyHaltPub z)

def dummyHaltTree (z : F) : NTree (MState × MemoryTable.DTmem F) := .node (dummyHaltRow z) []
def tailTree (z : F) : NTree (MState × MemoryTable.DTmem F) := .node (tailRow z) []
def verifyTree (z α : F) : NTree (MState × MemoryTable.DTmem F) := .node (verifyRow z α) [tailTree z]
def headTree (z : F) : NTree (MState × MemoryTable.DTmem F) := .node (headRow z) []
def decomposeTree (z α : F) : NTree (MState × MemoryTable.DTmem F) :=
  .node (decomposeRow z α) [headTree z, verifyTree z α]
def readTree (z α : F) : NTree (MState × MemoryTable.DTmem F) := .node (readRow z α) [decomposeTree z α]

/-! ## The concrete configuration and execution -/

/-- The OP1 slice's shared configuration. -/
def cfg (z α : F) : ExactConfig F F where
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
@[simp] theorem cfg_lam (z α : F) : (cfg z α).challenges.lam = MemoryTable.formRDefault := rfl

/-- The OP1 slice's authoritative forest-first execution: one `OP_1` compute row and the five-row
memory reconstruction of its single request. -/
def exec (z α : F) : ExactExecution (cfg z α) where
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

@[simp] def readPubA (z α : F) : MemoryTable.Pub F :=
  { readPub z α with mem := requestRecord z α, cprime? := none, lambda? := none }
@[simp] def decomposePubA (z α : F) : MemoryTable.Pub F := { decomposePub z α with lambda? := none }
@[simp] def headPubA (z : F) : MemoryTable.Pub F := { headPub z with lambda? := none }
@[simp] def verifyPubA (z α : F) : MemoryTable.Pub F :=
  { verifyPub z α with mem := requestRecord z α, cprime? := none, lambda? := none }
@[simp] def tailPubA (z : F) : MemoryTable.Pub F := { tailPub z with lambda? := none }
@[simp] def dummyHaltPubA (z : F) : MemoryTable.Pub F := { dummyHaltPub z with lambda? := none }

def readRowA (z α : F) : MState × MemoryTable.DTmem F :=
  (.read_root, memoryInputs z, readPubA z α)
def decomposeRowA (z α : F) : MState × MemoryTable.DTmem F :=
  (.decompose, memoryInputs z, decomposePubA z α)
def headRowA (z : F) : MState × MemoryTable.DTmem F := (.halt, memoryInputs z, headPubA z)
def verifyRowA (z α : F) : MState × MemoryTable.DTmem F :=
  (.verify_child, memoryInputs z, verifyPubA z α)
def tailRowA (z : F) : MState × MemoryTable.DTmem F := (.halt, memoryInputs z, tailPubA z)
def dummyHaltRowA (z : F) : MState × MemoryTable.DTmem F :=
  (.halt, memoryInputs z, dummyHaltPubA z)

def dummyHaltTreeA (z : F) : NTree (MState × MemoryTable.DTmem F) := .node (dummyHaltRowA z) []
def tailTreeA (z : F) : NTree (MState × MemoryTable.DTmem F) := .node (tailRowA z) []
def verifyTreeA (z α : F) : NTree (MState × MemoryTable.DTmem F) :=
  .node (verifyRowA z α) [tailTreeA z]
def headTreeA (z : F) : NTree (MState × MemoryTable.DTmem F) := .node (headRowA z) []
def decomposeTreeA (z α : F) : NTree (MState × MemoryTable.DTmem F) :=
  .node (decomposeRowA z α) [headTreeA z, verifyTreeA z α]
def readTreeA (z α : F) : NTree (MState × MemoryTable.DTmem F) :=
  .node (readRowA z α) [decomposeTreeA z α]

/-- The a-bearing view of `exec`: same compute tree, a-bearing memory rows. -/
def execA (z α : F) : ExactExecution (cfg z α) where
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

/-- The concrete honest seed and timestamp challenge of the slice. -/
def seedZ : F := 8
def alphaA : F := 4

theorem seedZ_ne_zero : seedZ ≠ 0 := by decide

/-- The compute carrier is exactly one row, the memory carrier exactly six. -/
theorem exec_row_counts :
    (exec seedZ alphaA).computeRows.length = 1 ∧
      (exec seedZ alphaA).memoryRows.length = 6 :=
  ⟨(exec seedZ alphaA).computeRows_length, (exec seedZ alphaA).memoryRows_length⟩

end Nock.NockVMROM.Thm54.TraceGen.Op1Config

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.exec
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.omega64_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.exec_row_counts
