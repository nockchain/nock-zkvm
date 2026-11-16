import Nock.NockVMROM.Thm54.StrictPackage
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.IntervalCases

/-!
# Concrete strict-package carrier

This module starts the concrete inhabitance path for the strict Theorem 5.4 package. The replacement below is the shortest collision-free memory reconstruction of that request:

`read_root → decompose → (halt, verify_child → halt)`.

It is built over a genuine cubic extension of `𝔽₇₃`.  The change from `𝔽₁₃` is forced by the row
domain: five memory rows require an order-eight execution orbit, while
`|(GaloisField 13 3)ˣ| = 13^3 - 1` is not divisible by eight.

The semantic row is OP1, so the OP0/OP9 slot obligations and the OP3/OP4/OP6 size-window census are
genuinely empty by state discrimination; the execution and skeleton themselves are nonempty.

Paper trace: `Def:MES`, `Def:Canonical_RAP`,
NMR/slot semantics, and Theorem 5.4.
-/

open scoped Classical

namespace Nock.NockVMROM.Thm54.ConcreteStrictPackage

noncomputable section

open Nock Nock.Walk Nock.NockVM
open Nock.ComputeTable Nock.MemoryTable
open Nock.Framework.Thm54
open Module
open CoordinateBasis
open RawSemanticAssembly
open SemanticStrategy
open ServedLookupBridge
open StrictCommitment
open StrictExtension
open SemanticTimestampStrategy
open TemplateRawJointSoundness
open ProductionP8Containment
open ProductionAxisStructureVerifier
open StrictPackage

/-! ## Cubic field and the two required orbit domains -/

abbrev F73 : Type := ZMod 73

instance concrete_prime73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩

abbrev K73cubic : Type := GaloisField 73 3

noncomputable local instance concrete_fintype : Fintype K73cubic :=
  Fintype.ofFinite K73cubic

local instance concrete_char73 : CharP K73cubic 73 := inferInstance

/-- The concrete cubic coordinate basis used by the two named monolithic chips
. -/
def basis73 : Basis (Fin 3) F73 K73cubic :=
  stdCoordBasis F73 K73cubic 3
    (GaloisField.finrank 73 (by norm_num))

/-- `10` has exact order eight in the cubic field: it is the image of an order-eight element of
`𝔽₇₃`. -/
theorem omega10_order : orderOf (10 : K73cubic) = 8 := by
  have hbase : orderOf (10 : F73) = 8 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide
  have hcast : (10 : K73cubic) = algebraMap F73 K73cubic (10 : F73) :=
    (map_natCast (algebraMap F73 K73cubic) 10).symm
  rw [hcast]
  change orderOf ((algebraMap F73 K73cubic).toMonoidHom (10 : F73)) = 8
  exact (orderOf_injective (algebraMap F73 K73cubic).toMonoidHom
    (algebraMap F73 K73cubic).injective (10 : F73)).trans hbase

/-- The five-row exact execution orbit. -/
def executionOrbit : OrbitDomain K73cubic where
  h := 3
  ω := 10
  βcoset := 1
  βcoset_ne_zero := by norm_num
  order_ω := by simpa using omega10_order

/-- The paper's `e = 3` monolithic orbit over `𝔽₇₃`: `3` has order
`3 · 2^2 = 12`. -/
def strictOrbit : StrictOrbitDomain F73 3 2 where
  ω := 3
  βcoset := 1
  e_pos := by norm_num
  h_pos := by norm_num
  βcoset_ne_zero := by norm_num
  order_ω := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide

def honestSeed : K73cubic := 1
def honestAlpha : K73cubic := 4

theorem honestSeed_ne : honestSeed ≠ 0 := by norm_num [honestSeed]

/-! ## Why the proposed empty-request OP1 carrier is impossible -/

/-- OP1 has exactly one live memory-record slot.  Thus an OP1 skeleton cannot implement the
proposed "all memory records are padding" carrier without changing the production table
. -/
theorem op1_recordCount_is_one :
    Nock.Framework.recordCount ComputeTable.State.s1 = 1 :=
  rfl

/-- At any nonzero NPR seed, the OP1 request binding is nonzero.  This is the compiled rejection
of the proposed empty request list: a live record whose root is an encoded noun cannot equal the
padding record. -/
theorem op1_bound_request_ne_zero
    {z : K73cubic} (hz : z ≠ 0)
    {s : SemanticStrategy.ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K73cubic}
    (hs : s.state = .s1)
    (hbind : SemanticStrategy.BindComputeRow z s row) :
    computeMemRec row.2.2.1 (0 : Fin 3) ≠ MemRec.zero := by
  have hactive : ((0 : Fin 3) : ℕ) < Nock.Framework.recordCount s.state := by
    simp [hs, Nock.Framework.recordCount]
  have hrec := hbind.2.2.2.2.2.2.2.2 (0 : Fin 3)
  rw [dif_pos hactive] at hrec
  intro hzero
  have hroot : (computeMemRec row.2.2.1 (0 : Fin 3)).root = 0 := by
    rw [hzero]
    rfl
  have heq := hrec.1
  rw [hroot] at heq
  have hsize := congrArg FP.size heq
  change (0 : K73cubic) = z ^ (s.memoryRecord 0 hactive).root.leaves at hsize
  exact (pow_ne_zero _ hz) hsize.symm

/-! ## Seed-independent nouns and the OP1 semantic skeleton -/

def subjectNoun : Noun := .atom 0
def headNoun : Noun := .atom 1
def resultNoun : Noun := .atom 2
def formulaNoun : Noun := .cell headNoun resultNoun

def requestSkeleton : SemanticStrategy.MemRecSkeleton where
  root := formulaNoun
  child := resultNoun
  axis := 3

def computeSkeletonRow : SemanticStrategy.ComputeRowSkeleton where
  state := .s1
  subject := subjectNoun
  formula := formulaNoun
  evaluation := resultNoun
  decomposition := fun slot _ =>
    match slot with
    | .f_h => headNoun
    | .f_t => resultNoun
    | _ => .atom 0
  subformula := fun i hi _ => absurd hi (by
    simpa [ComputeTable.fanoutComp] using hi)
  memoryRecord := fun i _ =>
    if (i : ℕ) = 0 then requestSkeleton else ⟨.atom 0, .atom 0, 0⟩

def readSkeletonRow : SemanticStrategy.MemoryRowSkeleton where
  state := .read_root
  parent := formulaNoun
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ =>
    if (i : ℕ) = 0 then formulaNoun else .atom 0
  memoryRecord := fun _ => requestSkeleton

def decomposeSkeletonRow : SemanticStrategy.MemoryRowSkeleton where
  state := .decompose
  parent := formulaNoun
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun i _ => if (i : ℕ) = 0 then headNoun else resultNoun
  memoryRecord := fun h => nomatch h

def headSkeletonRow : SemanticStrategy.MemoryRowSkeleton where
  state := .halt
  parent := headNoun
  haltAtom := fun _ => 1
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def verifySkeletonRow : SemanticStrategy.MemoryRowSkeleton where
  state := .verify_child
  parent := resultNoun
  haltAtom := fun h => nomatch h
  haltParent := fun h => nomatch h
  child := fun _ _ => resultNoun
  memoryRecord := fun _ => requestSkeleton

def tailSkeletonRow : SemanticStrategy.MemoryRowSkeleton where
  state := .halt
  parent := resultNoun
  haltAtom := fun _ => 2
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def tailSkeletonTree : NTree SemanticStrategy.MemoryRowSkeleton :=
  .node tailSkeletonRow []

def verifySkeletonTree : NTree SemanticStrategy.MemoryRowSkeleton :=
  .node verifySkeletonRow [tailSkeletonTree]

def headSkeletonTree : NTree SemanticStrategy.MemoryRowSkeleton :=
  .node headSkeletonRow []

def decomposeSkeletonTree : NTree SemanticStrategy.MemoryRowSkeleton :=
  .node decomposeSkeletonRow [headSkeletonTree, verifySkeletonTree]

def readSkeletonTree : NTree SemanticStrategy.MemoryRowSkeleton :=
  .node readSkeletonRow [decomposeSkeletonTree]

def dummyHaltSkeletonRow : SemanticStrategy.MemoryRowSkeleton where
  state := .halt
  parent := .atom 0
  haltAtom := fun _ => 0
  haltParent := by intro h; rfl
  child := fun _ h => nomatch h
  memoryRecord := fun h => nomatch h

def dummyHaltSkeletonTree : NTree SemanticStrategy.MemoryRowSkeleton :=
  .node dummyHaltSkeletonRow []

def semanticSkeleton : SemanticStrategy.SemanticSkeleton where
  computeTree := .node computeSkeletonRow []
  memoryForest := [dummyHaltSkeletonTree, readSkeletonTree]

def commitment : StrictCommitment.SkeletonCommitment where
  skeleton := semanticSkeleton
  nounSizeBound := 2

/-! ## The same field rows at every seed and timestamp -/

def fp (z : K73cubic) (n : Noun) : FP K73cubic :=
  GlobalCarryRecognizer.enc z n

def requestRecord (z α : K73cubic) : MemRec K73cubic where
  root := fp z formulaNoun
  child := fp z resultNoun
  axis := 3
  ts := α

/-- Row-level memory record (`BindMemRow`): the Form R encode of `requestRecord` at the package
`λ = formRDefault`; `axis = T`. -/
def rowRecord (z α : K73cubic) : MemRec K73cubic :=
  NockVM.formRRow (requestRecord z α) MemoryTable.formRDefault

/-- Row-level `C'` of `requestRecord`. -/
def rowCprime (z α : K73cubic) : K73cubic :=
  NockVM.formRCprime (requestRecord z α) MemoryTable.formRDefault

/-- `λ^{n−1}` at `λ = formRDefault`. -/
def scaleL : K73cubic := MemoryTable.formRDefault ^ MemoryTable.pwScaleExp K73cubic

/-- `T` and `C'` of the axis-`3` record. -/
def rowT : K73cubic :=
  MemoryTable.formRT MemoryTable.formRDefault (MemoryTable.nockAxisOf (3 : K73cubic))
def rowC : K73cubic :=
  MemoryTable.formRC MemoryTable.formRDefault (MemoryTable.nockAxisOf (3 : K73cubic))

theorem rowRecord_axis (z α : K73cubic) : (rowRecord z α).axis = rowT := rfl
theorem rowRecord_ts (z α : K73cubic) : (rowRecord z α).ts = α := rfl
theorem rowRecord_root (z α : K73cubic) :
    (rowRecord z α).root = (requestRecord z α).root := rfl
theorem rowRecord_child (z α : K73cubic) :
    (rowRecord z α).child = (requestRecord z α).child := rfl
theorem rowCprime_eq (z α : K73cubic) : rowCprime z α = rowC := rfl

/-- The row-level read/verify rows serve the single Form R encode of the compute record. -/
theorem rowRecord_encRecC (z α : K73cubic) :
    encRecC (rowRecord z α) (rowCprime z α) =
      encRecFormR (requestRecord z α) MemoryTable.formRDefault := rfl

def computeInputs (z α : K73cubic) : ComputeTable.Inputs K73cubic where
  α := α
  z := z
  a := 0
  b := 0
  c := 0

def computeDec (z : K73cubic) : ComputeTable.Dec K73cubic where
  f_h := fp z headNoun
  f_t := fp z resultNoun
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

def computePub (z α : K73cubic) : ComputeTable.Pub K73cubic where
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

def computeRow (z α : K73cubic) :
    ComputeTable.State × ComputeTable.DTcomp K73cubic :=
  (.s1, computeInputs z α, computePub z α, computeDec z)

def memoryInputs (z : K73cubic) : MemoryTable.Inputs K73cubic :=
  ⟨z, 0, 0⟩

/-- Row-level `read_root` root cell at `λ = 2`, `ts = honestAlpha = 4`
. -/
def seedCell (z : K73cubic) : Cell K73cubic :=
  ⟨fp z formulaNoun, 8 * scaleL - scaleL * rowT * 4, 12 * scaleL - rowT * rowC * 4⟩

def decomposeCell (z : K73cubic) : Cell K73cubic :=
  ⟨fp z formulaNoun, 8 * scaleL, 12 * scaleL⟩

def headCell (z : K73cubic) : Cell K73cubic :=
  ⟨fp z headNoun, 0, 0⟩

def verifyCell (z : K73cubic) : Cell K73cubic :=
  ⟨fp z resultNoun, scaleL * 4, scaleL * 4⟩

def tailCell (z : K73cubic) : Cell K73cubic :=
  ⟨fp z resultNoun, 0, 0⟩

def dummyHaltCell (z : K73cubic) : Cell K73cubic :=
  ⟨fp z (.atom 0), 0, 0⟩

def readPub (z α : K73cubic) : MemoryTable.Pub K73cubic where
  st := .read_root
  pt := seedCell z
  lc := decomposeCell z
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := rowRecord z α
  lambda? := some MemoryTable.formRDefault
  cprime? := some (rowCprime z α)
  ipre := 0
  icur := 1

def decomposePub (z α : K73cubic) : MemoryTable.Pub K73cubic where
  st := .decompose
  pt := decomposeCell z
  lc := headCell z
  rc := verifyCell z
  lcSt := .halt
  rcSt := .verify_child
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def headPub (z : K73cubic) : MemoryTable.Pub K73cubic where
  st := .halt
  pt := headCell z
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def verifyPub (z α : K73cubic) : MemoryTable.Pub K73cubic where
  st := .verify_child
  pt := verifyCell z
  lc := tailCell z
  rc := Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := rowRecord z α
  lambda? := some MemoryTable.formRDefault
  cprime? := some (rowCprime z α)
  ipre := 1
  icur := 0

def tailPub (z : K73cubic) : MemoryTable.Pub K73cubic where
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

def readRow (z α : K73cubic) : MState × MemoryTable.DTmem K73cubic :=
  (.read_root, memoryInputs z, readPub z α)

def decomposeRow (z α : K73cubic) : MState × MemoryTable.DTmem K73cubic :=
  (.decompose, memoryInputs z, decomposePub z α)

def headRow (z : K73cubic) : MState × MemoryTable.DTmem K73cubic :=
  (.halt, memoryInputs z, headPub z)

def verifyRow (z α : K73cubic) : MState × MemoryTable.DTmem K73cubic :=
  (.verify_child, memoryInputs z, verifyPub z α)

def tailRow (z : K73cubic) : MState × MemoryTable.DTmem K73cubic :=
  (.halt, memoryInputs z, tailPub z)

def dummyHaltPub (z : K73cubic) : MemoryTable.Pub K73cubic where
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

def dummyHaltRow (z : K73cubic) : MState × MemoryTable.DTmem K73cubic :=
  (.halt, memoryInputs z, dummyHaltPub z)

def dummyHaltTree (z : K73cubic) : NTree (MState × MemoryTable.DTmem K73cubic) :=
  .node (dummyHaltRow z) []

def tailTree (z : K73cubic) : NTree (MState × MemoryTable.DTmem K73cubic) :=
  .node (tailRow z) []

def verifyTree (z α : K73cubic) : NTree (MState × MemoryTable.DTmem K73cubic) :=
  .node (verifyRow z α) [tailTree z]

def headTree (z : K73cubic) : NTree (MState × MemoryTable.DTmem K73cubic) :=
  .node (headRow z) []

def decomposeTree (z α : K73cubic) : NTree (MState × MemoryTable.DTmem K73cubic) :=
  .node (decomposeRow z α) [headTree z, verifyTree z α]

def readTree (z α : K73cubic) : NTree (MState × MemoryTable.DTmem K73cubic) :=
  .node (readRow z α) [decomposeTree z α]

def cfg (z α : K73cubic) : ExactConfig F73 K73cubic where
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

def exec (z α : K73cubic) : ExactExecution (cfg z α) where
  computeTree := .node (computeRow z α) []
  memoryForest := [dummyHaltTree z, readTree z α]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [dummyHaltTree, readTree, decomposeTree, headTree, verifyTree, tailTree,
      bfsForest, NTree.size, totalSize, cfg]

/-! ## The universal data-only timestamp specialization -/

/-- The complete configuration template fixed after `z`; only the table timestamp challenge is
inserted by specialization. -/
def configTemplate (z : K73cubic) : ExactConfigTemplate F73 K73cubic where
  challenges := { a := 0, b := 0, c := 0, z := z, β := 0, γ := 0 }
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

/-- The fixture's configured `λ` is `formRDefault` (the config's `lam` field). -/
@[simp] theorem cfg_lam (z α : K73cubic) : (cfg z α).challenges.lam = MemoryTable.formRDefault := rfl


def computeRowTemplate (z : K73cubic) : ComputeRowTemplate (K := K73cubic) where
  timestamp :=
    { state := .s1
      lnPrevExponent := 0
      lnExponent := 1
      recordExponent := fun _ => 1 }
  placeholder := computeRow z 0

/-- A-bearing template pubs: the record holds the address; specialization
writes `(T, C')`. -/
def readPubA (z α : K73cubic) : MemoryTable.Pub K73cubic :=
  { readPub z α with mem := requestRecord z α, cprime? := none }

def verifyPubA (z α : K73cubic) : MemoryTable.Pub K73cubic :=
  { verifyPub z α with mem := requestRecord z α, cprime? := none }

def readRowTemplate (z : K73cubic) : MemoryRowTemplate (K := K73cubic) where
  timestamp := { state := .read_root, recordExponent := 1 }
  placeholder := (.read_root, memoryInputs z, readPubA z 0)

def decomposeRowTemplate (z : K73cubic) : MemoryRowTemplate (K := K73cubic) where
  timestamp := { state := .decompose, recordExponent := 0 }
  placeholder := decomposeRow z 0

def headRowTemplate (z : K73cubic) : MemoryRowTemplate (K := K73cubic) where
  timestamp := { state := .halt, recordExponent := 0 }
  placeholder := headRow z

def verifyRowTemplate (z : K73cubic) : MemoryRowTemplate (K := K73cubic) where
  timestamp := { state := .verify_child, recordExponent := 1 }
  placeholder := (.verify_child, memoryInputs z, verifyPubA z 0)

def tailRowTemplate (z : K73cubic) : MemoryRowTemplate (K := K73cubic) where
  timestamp := { state := .halt, recordExponent := 0 }
  placeholder := tailRow z

def tailTemplateTree (z : K73cubic) : NTree (MemoryRowTemplate (K := K73cubic)) :=
  .node (tailRowTemplate z) []

def verifyTemplateTree (z : K73cubic) : NTree (MemoryRowTemplate (K := K73cubic)) :=
  .node (verifyRowTemplate z) [tailTemplateTree z]

def headTemplateTree (z : K73cubic) : NTree (MemoryRowTemplate (K := K73cubic)) :=
  .node (headRowTemplate z) []

def decomposeTemplateTree (z : K73cubic) : NTree (MemoryRowTemplate (K := K73cubic)) :=
  .node (decomposeRowTemplate z) [headTemplateTree z, verifyTemplateTree z]

def readTemplateTree (z : K73cubic) : NTree (MemoryRowTemplate (K := K73cubic)) :=
  .node (readRowTemplate z) [decomposeTemplateTree z]

def dummyHaltRowTemplate (z : K73cubic) : MemoryRowTemplate (K := K73cubic) where
  timestamp := { state := .halt, recordExponent := 0 }
  placeholder := dummyHaltRow z

def dummyHaltTemplateTree (z : K73cubic) : NTree (MemoryRowTemplate (K := K73cubic)) :=
  .node (dummyHaltRowTemplate z) []

/-- The seed-fixed α-free execution template specializes to the same execution used by every
package field. -/
def executionTemplate (z : K73cubic) : ExactExecutionTemplate (configTemplate z) where
  computeTree := .node (computeRowTemplate z) []
  memoryForest := [dummyHaltTemplateTree z, readTemplateTree z]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [bfsForest, NTree.size, totalSize, configTemplate]
  memory_bfs_length := by
    norm_num [dummyHaltTemplateTree, readTemplateTree, decomposeTemplateTree, headTemplateTree,
      verifyTemplateTree, tailTemplateTree, bfsForest, NTree.size, totalSize,
      configTemplate]

def timestampStrategy :
    DataOnlyTemplateFixedStagedTimestampStrategy (F := F73) (K := K73cubic) :=
  DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData
    semanticSkeleton.publicClaim
    (fun seed => configTemplate seed.1)
    (fun seed => executionTemplate seed.1)
    (fun _ => rfl)

/-- The fixture's sample of the Form R `λ` is `formRDefault`: the templates are λ-free and
specialize at the sampled `(α, λ)`; the concrete `cfg`/`exec` are the specialization at
`λ = formRDefault`. -/
theorem configTemplate_specialize (z α : K73cubic) :
    (configTemplate z).specialize α MemoryTable.formRDefault = cfg z α := rfl

theorem executionTemplate_specialize (z α : K73cubic) :
    (executionTemplate z).specialize α MemoryTable.formRDefault = exec z α := by
  apply ExactExecution.ext
  · simp [ExactExecutionTemplate.specialize, mapNTree, executionTemplate, computeRowTemplate,
      ComputeRowTemplate.specialize, specializeMemRecScaled, computeLineOrigin, computeMemRecKind,
      Nock.Framework.recordCount, exec,
      computeRow, computeInputs, computePub, requestRecord]
  · simp [ExactExecutionTemplate.specialize, mapNTree, executionTemplate, dummyHaltTemplateTree,
      dummyHaltRowTemplate, readTemplateTree, decomposeTemplateTree, headTemplateTree,
      verifyTemplateTree, tailTemplateTree, readRowTemplate, decomposeRowTemplate,
      headRowTemplate, verifyRowTemplate, tailRowTemplate, MemoryRowTemplate.specialize,
      MemoryRowTemplate.specializeA, MemoryRowTemplate.encodeRow, readPubA, verifyPubA,
      specializeMemRec, memoryMemRecKind, exec, dummyHaltTree, dummyHaltRow, dummyHaltPub,
      readTree, decomposeTree, headTree, verifyTree, tailTree, readRow, decomposeRow,
      headRow, verifyRow, tailRow, readPub, decomposePub, headPub, verifyPub, tailPub,
      requestRecord, rowRecord, rowCprime, NockVM.formRRow, NockVM.formRCprime]

/-! ### The a-bearing view

`execA` stores `requestRecord` (axis `3`) on the `read_root` / `verify_child` rows; the executed
`exec` is its Form R row encode (`exec_eq_encodeMem`).  The served memory trace and the axis tree
are stated on `execA` (`BuildableNockExecution.execA`). -/

def readRowA (z α : K73cubic) : MState × MemoryTable.DTmem K73cubic :=
  (.read_root, memoryInputs z, readPubA z α)

def verifyRowA (z α : K73cubic) : MState × MemoryTable.DTmem K73cubic :=
  (.verify_child, memoryInputs z, verifyPubA z α)

def verifyTreeA (z α : K73cubic) : NTree (MState × MemoryTable.DTmem K73cubic) :=
  .node (verifyRowA z α) [tailTree z]

def decomposeTreeA (z α : K73cubic) : NTree (MState × MemoryTable.DTmem K73cubic) :=
  .node (decomposeRow z α) [headTree z, verifyTreeA z α]

def readTreeA (z α : K73cubic) : NTree (MState × MemoryTable.DTmem K73cubic) :=
  .node (readRowA z α) [decomposeTreeA z α]

def execA (z α : K73cubic) : ExactExecution (cfg z α) where
  computeTree := .node (computeRow z α) []
  memoryForest := [dummyHaltTree z, readTreeA z α]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [bfsForest, NTree.size, totalSize, cfg]
  memory_bfs_length := by
    norm_num [dummyHaltTree, readTreeA, decomposeTreeA, headTree, verifyTreeA, tailTree,
      bfsForest, NTree.size, totalSize, cfg]

theorem exec_eq_encodeMem (z α : K73cubic) : exec z α = (execA z α).encodeMem := by
  apply ExactExecution.ext
  · rfl
  · simp [ExactExecution.encodeMem, exec, execA, mapNTree, MemoryRowTemplate.encodeRow,
      memoryMemRecKind, dummyHaltTree, dummyHaltRow, dummyHaltPub,
      readTree, decomposeTree, headTree, verifyTree, tailTree, readRow, decomposeRow,
      headRow, verifyRow, tailRow, readPub, decomposePub, headPub, verifyPub, tailPub,
      readTreeA, decomposeTreeA, verifyTreeA, readRowA, verifyRowA, readPubA, verifyPubA,
      rowRecord, rowCprime]

theorem executionTemplate_specializeA (z α : K73cubic) :
    (executionTemplate z).specializeA α MemoryTable.formRDefault = execA z α := by
  apply ExactExecution.ext
  · simp [ExactExecutionTemplate.specializeA, ExactExecutionTemplate.specialize, mapNTree,
      executionTemplate, computeRowTemplate,
      ComputeRowTemplate.specialize, specializeMemRecScaled, computeLineOrigin, computeMemRecKind,
      Nock.Framework.recordCount, execA,
      computeRow, computeInputs, computePub, requestRecord]
  · simp [ExactExecutionTemplate.specializeA, mapNTree, executionTemplate, dummyHaltTemplateTree,
      dummyHaltRowTemplate, readTemplateTree, decomposeTemplateTree, headTemplateTree,
      verifyTemplateTree, tailTemplateTree, readRowTemplate, decomposeRowTemplate,
      headRowTemplate, verifyRowTemplate, tailRowTemplate,
      MemoryRowTemplate.specializeA, readPubA, verifyPubA,
      specializeMemRec, memoryMemRecKind, execA, dummyHaltTree, dummyHaltRow, dummyHaltPub,
      readTreeA, decomposeTreeA, headTree, verifyTreeA, tailTree, readRowA, decomposeRow,
      headRow, verifyRowA, tailRow, readPub, decomposePub, headPub, verifyPub, tailPub,
      requestRecord]

theorem specializedProblem_eq (z : K73cubic) (hz : z ≠ 0) (α : K73cubic) :
    specializedProblem timestampStrategy z hz α MemoryTable.formRDefault =
      ⟨cfg z α, exec z α⟩ := by
  unfold specializedProblem timestampStrategy
    DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData
  change
    ({ cfg := cfg z α
       exec := (executionTemplate z).specialize α MemoryTable.formRDefault } :
        RawProblem F73 K73cubic) =
      ⟨cfg z α, exec z α⟩
  rw [executionTemplate_specialize]

/-! ## The staged raw verifier and shared raw row family -/

theorem stateTagChar : NodeEncoding.StateTagChar K73cubic :=
  NodeEncoding.stateTagChar_of_charP (K := K73cubic) 73 (by norm_num)

local instance concrete_charRing : CharP K73cubic (ringChar K73cubic) :=
  ringChar.charP K73cubic

def familyData (z : K73cubic) (hz : z ≠ 0) (α lmb : K73cubic) :
    AlphaMFamilyData timestampStrategy z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode stateTagChar
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode stateTagChar
  requests := 0
  responses := 0
  outMem := 0

def zeroAlphaMCommitment (z : K73cubic) (hz : z ≠ 0) (α lmb : K73cubic) :
    AlphaMCommitment (p := ringChar K73cubic) timestampStrategy z hz α lmb where
  familyData := familyData z hz α lmb
  tables :=
    { compute := fun _ => ⟨0, 0⟩
      memory := fun _ => 0 }
  io :=
    { multiplicity := fun _ => 0
      progAcc := fun _ => 0
      memAcc := fun _ => 0 }

def zeroRawStrategy :
    TemplateRawJointSoundness.Strategy F73 K73cubic (ringChar K73cubic) where
  timestamp := timestampStrategy
  afterAlphaM := zeroAlphaMCommitment
  afterCoins := fun _ _ _ =>
    { computeLn := fun _ => 0
      computeCount := fun _ => 0
      computeAcc := fun _ => 0
      memoryLn := fun _ => 0
      memoryCount := fun _ => 0
      memoryAcc := fun _ => 0 }

/-- Production verifier with topology arrays generated from the same exact execution. -/
def zeroVerifier :
    ProductionRawVerifier.TemplateAdapter.Strategy
      F73 K73cubic (ringChar K73cubic) :=
  ProductionRawVerifier.TemplateAdapter.Strategy.honest zeroRawStrategy

theorem timestamp_specializedProblem (z : K73cubic) (hz : z ≠ 0) (α : K73cubic) :
    specializedProblem zeroVerifier.raw.timestamp z hz α MemoryTable.formRDefault =
      ⟨cfg z α, exec z α⟩ :=
  specializedProblem_eq z hz α

def walkFamily : RawPlusIOSegmentedFamily F73 K73cubic :=
  (familyData honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).atCoins 0 0

theorem walkFamily_problem :
    walkFamily.problem = ⟨cfg honestSeed honestAlpha, exec honestSeed honestAlpha⟩ :=
  specializedProblem_eq honestSeed honestSeed_ne honestAlpha

theorem compEnc_inj :
    ∀ a b, walkFamily.compNodeEncode a = walkFamily.compNodeEncode b →
      ComputeTable.computeLabelOf a = ComputeTable.computeLabelOf b :=
  fun _ _ h => NodeEncoding.computeNodeEncode_labelOf_eq stateTagChar h

theorem memEnc_inj :
    ∀ a b, walkFamily.memNodeEncode a = walkFamily.memNodeEncode b →
      MemoryTable.memoryLabelOf a = MemoryTable.memoryLabelOf b :=
  fun _ _ h => NodeEncoding.memoryNodeEncode_labelOf_eq stateTagChar h

def objects : StrictThreadedObjects F73 K73cubic where
  cfg := cfg honestSeed honestAlpha
  exec := exec honestSeed honestAlpha
  reqRecs := (exec honestSeed honestAlpha).derivedRequestIO
  respRecs := (exec honestSeed honestAlpha).derivedResponseIO
  req_eq_derived := rfl
  resp_eq_derived := rfl

theorem execution_rows (z α : K73cubic) :
    (exec z α).computeRows = [computeRow z α] ∧
      (exec z α).memoryRows =
        [dummyHaltRow z, readRow z α, decomposeRow z α, headRow z, verifyRow z α, tailRow z] := by
  constructor <;>
    norm_num [ExactExecution.computeRows, ExactExecution.memoryRows, exec, dummyHaltTree,
      readTree, decomposeTree, headTree, verifyTree, tailTree, bfsForest, NTree.size, totalSize]

/-- Row-level `C'` is a function of the stored record on this execution. -/
theorem execution_cprime_eq (z α : K73cubic) :
    ∀ row ∈ (exec z α).memoryRows, row.2.2.cprime =
      (fun m => if m = rowRecord z α then rowCprime z α else 1) row.2.2.mem := by
  have hne : rowRecord z α ≠ MemRec.zero := by
    intro h
    have hax := congrArg MemRec.axis h
    simp only [rowRecord_axis, MemRec.zero] at hax
    have : (rowT : K73cubic) ≠ 0 := by
      have h2 : (2 : K73cubic) ≠ 0 := by
        letI : CharP K73cubic 73 := concrete_char73
        exact SetEq.Lcast_ne_zero (p := 73) (by norm_num) (by norm_num)
      simp [rowT, MemoryTable.formRT, MemoryTable.formRDefault, h2]
    exact this hax
  intro row hmem
  rw [(execution_rows z α).2] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [dummyHaltRow, readRow, decomposeRow, headRow, verifyRow, tailRow,
      dummyHaltPub, readPub, decomposePub, headPub, verifyPub, tailPub,
      MemoryTable.Pub.cprime, Ne.symm hne]

theorem execution_cprimeCoherent (z α : K73cubic) : (exec z α).CprimeCoherent :=
  ExactExecution.cprimeCoherent_of_fun
    (fun m => if m = rowRecord z α then rowCprime z α else 1) (execution_cprime_eq z α)

theorem memoryPubAt73_0 (z α : K73cubic) :
    (exec z α).memoryPubAt ⟨0, by norm_num [cfg]⟩ = dummyHaltPub z := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rows z α).2,
    cfg, dummyHaltRow]
theorem memoryPubAt73_1 (z α : K73cubic) :
    (exec z α).memoryPubAt ⟨1, by norm_num [cfg]⟩ = readPub z α := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rows z α).2,
    cfg, readRow]
theorem memoryPubAt73_2 (z α : K73cubic) :
    (exec z α).memoryPubAt ⟨2, by norm_num [cfg]⟩ = decomposePub z α := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rows z α).2,
    cfg, decomposeRow]
theorem memoryPubAt73_3 (z α : K73cubic) :
    (exec z α).memoryPubAt ⟨3, by norm_num [cfg]⟩ = headPub z := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rows z α).2,
    cfg, headRow]
theorem memoryPubAt73_4 (z α : K73cubic) :
    (exec z α).memoryPubAt ⟨4, by norm_num [cfg]⟩ = verifyPub z α := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rows z α).2,
    cfg, verifyRow]
theorem memoryPubAt73_5 (z α : K73cubic) :
    (exec z α).memoryPubAt ⟨5, by norm_num [cfg]⟩ = tailPub z := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, (execution_rows z α).2,
    cfg, tailRow]

/-- Every concrete memory row carries the package `λ = formRDefault` (written by specialization). -/
theorem exec_memory_lambda_unset (z α : K73cubic) :
    ∀ i, ((exec z α).memoryPubAt i).lambda? = some MemoryTable.formRDefault := by
  intro i
  fin_cases i
  · rw [memoryPubAt73_0]; rfl
  · rw [memoryPubAt73_1]; rfl
  · rw [memoryPubAt73_2]; rfl
  · rw [memoryPubAt73_3]; rfl
  · rw [memoryPubAt73_4]; rfl
  · rw [memoryPubAt73_5]; rfl

/-- Halt and decompose rows carry `MemRec.zero`; read/verify rows make the inactive-state
hypotheses unsatisfiable. W4 stage 2: the all-row pole-hit half of `interFailurePairs`. -/
theorem inactive_mem_zero (z α : K73cubic) (i : Fin (cfg z α).memRows)
    (hnr : ((exec z α).memoryPubAt i).st ≠ .read_root)
    (hnv : ((exec z α).memoryPubAt i).st ≠ .verify_child) :
    ((exec z α).memoryPubAt i).mem = ComputeTable.MemRec.zero := by
  fin_cases i <;>
    simp [memoryPubAt73_0, memoryPubAt73_1, memoryPubAt73_2, memoryPubAt73_3,
      memoryPubAt73_4, memoryPubAt73_5, dummyHaltPub, readPub, decomposePub, headPub,
      verifyPub, tailPub] at hnr hnv ⊢

-- Provisional: inactive rows keep the `C' = 1` default.
theorem inactive_cprime_one (z α : K73cubic) (i : Fin (cfg z α).memRows)
    (hnr : ((exec z α).memoryPubAt i).st ≠ .read_root)
    (hnv : ((exec z α).memoryPubAt i).st ≠ .verify_child) :
    ((exec z α).memoryPubAt i).cprime = 1 := by
  fin_cases i <;>
    simp [memoryPubAt73_0, memoryPubAt73_1, memoryPubAt73_2, memoryPubAt73_3,
      memoryPubAt73_4, memoryPubAt73_5, dummyHaltPub, readPub, decomposePub, headPub,
      verifyPub, tailPub, MemoryTable.Pub.cprime] at hnr hnv ⊢

/-! ## Honest specialization -/

theorem formula_fp :
    fp honestSeed formulaNoun = ⟨1, 1, 3⟩ := by
  unfold fp
  rw [show formulaNoun = .cell headNoun resultNoun by rfl,
    GlobalCarryRecognizer.enc_cons honestSeed_ne]
  ext <;>
    norm_num [fp, honestSeed, headNoun, resultNoun,
      GlobalCarryRecognizer.enc_atom, FP.cons, FP.atomFP]

theorem honest_request_ne_zero :
    requestRecord honestSeed honestAlpha ≠ (MemRec.zero : MemRec K73cubic) := by
  intro h
  have hd := congrArg (fun r : MemRec K73cubic => r.root.dyck) h
  norm_num [requestRecord, formula_fp, MemRec.zero] at hd

theorem compute_accepts :
    Vcomp (computeInputs honestSeed honestAlpha)
      (computePub honestSeed honestAlpha) (computeDec honestSeed) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (GlobalCarryRecognizer.enc_cons honestSeed_ne headNoun resultNoun)
  · ext <;>
      norm_num [computePub, requestRecord, computeDec, computeInputs,
        honestSeed, honestAlpha]
  · simp [SVhead, headAtom, computePub, computeDec, computeInputs, fp,
      headNoun, GlobalCarryRecognizer.enc_atom, State.toNat, honestSeed, honestAlpha]
  · norm_num [memBlk, computePub, computeInputs, MemRec.zero, honestSeed, honestAlpha]
  · simp [evalV, sfz1, sfz2, sfz3, computePub, computeDec]

theorem compute_wf :
    ComputeTable.WF (computeInputs honestSeed honestAlpha)
      (computePub honestSeed honestAlpha) where
  rlc5 := by simp [computePub]
  size8 := by simp [computePub]
  size11 := by simp [computePub]

theorem request_pole :
    pole (memoryInputs honestSeed) (rowRecord honestSeed honestAlpha)
      (rowCprime honestSeed honestAlpha) = 1 := by
  norm_num [pole, recRLC, memoryInputs, rowRecord_root, requestRecord, formula_fp,
    fp, resultNoun, GlobalCarryRecognizer.enc_atom, honestSeed, honestAlpha]

theorem dummy_accepts :
    Vmem (memoryInputs honestSeed) (dummyHaltPub honestSeed) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  · show (fp honestSeed (.atom 0)).size = honestSeed
    simp [fp, dummyHaltCell, dummyHaltPub, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]
  · show (fp honestSeed (.atom 0)).dyck = 0
    simp [fp, dummyHaltCell, dummyHaltPub, GlobalCarryRecognizer.enc_atom, ComputeTable.FP.atomFP]

theorem read_accepts :
    Vmem (memoryInputs honestSeed) (readPub honestSeed honestAlpha) := by
  refine ⟨MemoryTable.verBool_holds _, ⟨rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [readPub, seedCell, decomposeCell, Pub.lambda, Pub.cprime, scaleL, rowRecord_axis,
      rowRecord_ts, MemoryTable.formRDefault, honestAlpha] <;> ring
  · simp [readPub, seedCell, decomposeCell, Pub.lambda, Pub.cprime, scaleL, rowRecord_axis,
      rowRecord_ts, rowCprime_eq, MemoryTable.formRDefault, honestAlpha] <;> ring
  · simp [interV, readPub, Pub.cprime, request_pole]

theorem decompose_accepts :
    Vmem (memoryInputs honestSeed) (decomposePub honestSeed honestAlpha) := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, rfl⟩
    · exact (GlobalCarryRecognizer.enc_cons honestSeed_ne headNoun resultNoun)
    · simp [decomposePub, decomposeCell, headCell, verifyCell, Pub.lambda,
        MemoryTable.formRDefault]; ring
    · simp [decomposePub, decomposeCell, headCell, verifyCell, Pub.lambda,
        MemoryTable.formRDefault]; ring
  · rfl

theorem head_accepts :
    Vmem (memoryInputs honestSeed) (headPub honestSeed) := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · norm_num [eqBlk, headPub, headCell, memoryInputs, Cell.zero, MemRec.zero,
      fp, headNoun, GlobalCarryRecognizer.enc_atom, honestSeed]
  · rfl

theorem verify_accepts :
    Vmem (memoryInputs honestSeed) (verifyPub honestSeed honestAlpha) := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp [eqBlk, verifyPub, verifyCell, tailCell, Pub.lambda, scaleL, rowRecord,
      NockVM.formRRow, requestRecord, MemoryTable.formRDefault, honestAlpha]
  · change (1 : K73cubic) - 0 =
      (pole (memoryInputs honestSeed) (verifyPub honestSeed honestAlpha).mem
        (verifyPub honestSeed honestAlpha).cprime)⁻¹
    rw [show (verifyPub honestSeed honestAlpha).mem =
      rowRecord honestSeed honestAlpha by rfl,
      show (verifyPub honestSeed honestAlpha).cprime = rowCprime honestSeed honestAlpha by rfl,
      request_pole]
    norm_num

theorem tail_accepts :
    Vmem (memoryInputs honestSeed) (tailPub honestSeed) := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · norm_num [eqBlk, tailPub, tailCell, memoryInputs, Cell.zero, MemRec.zero,
      fp, resultNoun, GlobalCarryRecognizer.enc_atom, honestSeed]
  · rfl

theorem honest_computeRowsAccepted :
    (exec honestSeed honestAlpha).ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, (execution_rows _ _).1]
  intro row hrow
  simp only [List.mem_singleton] at hrow
  subst row
  exact ⟨rfl, rfl, compute_accepts⟩

theorem honest_memoryRowsAccepted :
    (exec honestSeed honestAlpha).MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, (execution_rows _ _).2]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, dummy_accepts, rfl⟩
  · exact ⟨rfl, rfl, read_accepts, rfl⟩
  · exact ⟨rfl, rfl, decompose_accepts, rfl⟩
  · exact ⟨rfl, rfl, head_accepts, rfl⟩
  · exact ⟨rfl, rfl, verify_accepts, rfl⟩
  · exact ⟨rfl, rfl, tail_accepts, rfl⟩

theorem topologyBinding : RawTopologyBindingResidual walkFamily := by
  have hcomputeTree :
      walkFamily.exec.computeTree = (exec honestSeed honestAlpha).computeTree :=
    congrArg (fun P : RawProblem F73 K73cubic => P.exec.computeTree) walkFamily_problem
  have hmemoryForest :
      walkFamily.exec.memoryForest = (exec honestSeed honestAlpha).memoryForest :=
    congrArg (fun P : RawProblem F73 K73cubic => P.exec.memoryForest) walkFamily_problem
  constructor
  · rw [RawPlusIOSegmentedFamily.computeWalkRows, hcomputeTree]
    intro t ht
    simp [exec, bfsForest] at ht
    rcases ht with rfl
    simp [RawComputeTopologyBinding, ComputeTable.fanoutComp,
      ComputeTable.childLinkComp, computeRow]
  · rw [RawPlusIOSegmentedFamily.memoryWalkRows, hmemoryForest]
    intro t ht
    simp [exec, dummyHaltTree, dummyHaltRow, dummyHaltPub, readTree, decomposeTree,
      headTree, verifyTree, tailTree, bfsForest] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [RawMemoryTopologyBinding, MemoryTable.fanoutMem,
        MemoryTable.childLinkMem, dummyHaltRow, dummyHaltPub]
    · simp [RawMemoryTopologyBinding, MemoryTable.fanoutMem,
        MemoryTable.childLinkMem, MemoryTable.memCell, NTree.childLabel, NTree.childOpt,
        readRow, readPub, decomposeRow, decomposePub]
    · simp [RawMemoryTopologyBinding, MemoryTable.fanoutMem,
        MemoryTable.childLinkMem, MemoryTable.memCell, NTree.childLabel, NTree.childOpt,
        decomposeRow, decomposePub, headRow, headPub, verifyRow, verifyPub]
    · simp [RawMemoryTopologyBinding, MemoryTable.fanoutMem,
        MemoryTable.childLinkMem, headRow]
    · simp [RawMemoryTopologyBinding, MemoryTable.fanoutMem,
        MemoryTable.childLinkMem, MemoryTable.memCell, NTree.childLabel, NTree.childOpt,
        verifyRow, verifyPub, tailRow, tailPub]
    · simp [RawMemoryTopologyBinding, MemoryTable.fanoutMem,
        MemoryTable.childLinkMem, tailRow]

theorem recordCountBalance : RowLayout.RecordCountBalanced (exec honestSeed honestAlpha) := by
  simp [RowLayout.RecordCountBalanced, RowLayout.memoryStateCount, RowLayout.fibreCount,
    (execution_rows _ _).2, dummyHaltRow, dummyHaltPub, readRow, decomposeRow, headRow, verifyRow, tailRow,
    dummyHaltPub, readPub, decomposePub, headPub, verifyPub, tailPub]

theorem computePubAt_zero :
    (exec honestSeed honestAlpha).computePubAt
      ⟨0, by norm_num [cfg]⟩ = computePub honestSeed honestAlpha := by
  norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt,
    (execution_rows _ _).1, cfg, computeRow]

theorem memoryPubAt_zero :
    (exec honestSeed honestAlpha).memoryPubAt
      ⟨0, by norm_num [cfg]⟩ = dummyHaltPub honestSeed := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    (execution_rows _ _).2, cfg, dummyHaltRow]

theorem memoryPubAt_one :
    (exec honestSeed honestAlpha).memoryPubAt
      ⟨1, by norm_num [cfg]⟩ = readPub honestSeed honestAlpha := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    (execution_rows _ _).2, cfg, readRow]

theorem memoryPubAt_two :
    (exec honestSeed honestAlpha).memoryPubAt
      ⟨2, by norm_num [cfg]⟩ = decomposePub honestSeed honestAlpha := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    (execution_rows _ _).2, cfg, decomposeRow]

theorem memoryPubAt_three :
    (exec honestSeed honestAlpha).memoryPubAt
      ⟨3, by norm_num [cfg]⟩ = headPub honestSeed := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    (execution_rows _ _).2, cfg, headRow]

theorem memoryPubAt_four :
    (exec honestSeed honestAlpha).memoryPubAt
      ⟨4, by norm_num [cfg]⟩ = verifyPub honestSeed honestAlpha := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    (execution_rows _ _).2, cfg, verifyRow]

theorem memoryPubAt_five :
    (exec honestSeed honestAlpha).memoryPubAt
      ⟨5, by norm_num [cfg]⟩ = tailPub honestSeed := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
    (execution_rows _ _).2, cfg, tailRow]

theorem dummy_wf :
    MemoryTable.WF (memoryInputs honestSeed) (dummyHaltPub honestSeed) where
  pole_ne h := by simp [dummyHaltPub] at h

theorem read_wf :
    MemoryTable.WF (memoryInputs honestSeed) (readPub honestSeed honestAlpha) where
  pole_ne _ := by simpa [readPub, Pub.cprime] using (show
    pole (memoryInputs honestSeed) (rowRecord honestSeed honestAlpha)
      (rowCprime honestSeed honestAlpha) ≠ 0 by
      rw [request_pole]; norm_num)

theorem decompose_wf :
    MemoryTable.WF (memoryInputs honestSeed) (decomposePub honestSeed honestAlpha) where
  pole_ne h := by simp [decomposePub] at h

theorem head_wf :
    MemoryTable.WF (memoryInputs honestSeed) (headPub honestSeed) where
  pole_ne h := by simp [headPub] at h

theorem verify_wf :
    MemoryTable.WF (memoryInputs honestSeed) (verifyPub honestSeed honestAlpha) where
  pole_ne _ := by simpa [verifyPub, Pub.cprime] using (show
    pole (memoryInputs honestSeed) (rowRecord honestSeed honestAlpha)
      (rowCprime honestSeed honestAlpha) ≠ 0 by
      rw [request_pole]; norm_num)

theorem tail_wf :
    MemoryTable.WF (memoryInputs honestSeed) (tailPub honestSeed) where
  pole_ne h := by simp [tailPub] at h

theorem derived_request_singleton :
    (exec honestSeed honestAlpha).derivedRequestIO =
      [encRecFormR (requestRecord honestSeed honestAlpha) formRDefault] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, (execution_rows _ _).1]
  simp [NockVM.activeRequestRecords, computeRow, computePub]

theorem derived_response_singleton :
    (exec honestSeed honestAlpha).derivedResponseIO =
      [encRecFormR (requestRecord honestSeed honestAlpha) formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, (execution_rows _ _).2]
  simp [dummyHaltRow, dummyHaltPub, readRow, decomposeRow, headRow, verifyRow, tailRow,
    readPub, decomposePub, headPub, verifyPub, tailPub, Pub.cprime, rowRecord_encRecC]

def ioRecords : FiniteIO.PreChallengeRecords K73cubic 9 where
  requests := (exec honestSeed honestAlpha).derivedRequestIO
  responses := (exec honestSeed honestAlpha).derivedResponseIO

def ioCoins : FiniteIO.IOCoins K73cubic := ⟨0, 0⟩

theorem io_lio :
    IO.LIO 4 ioRecords.requests ioRecords.responses := by
  change IO.LIO 4 (exec honestSeed honestAlpha).derivedRequestIO
    (exec honestSeed honestAlpha).derivedResponseIO
  rw [derived_request_singleton, derived_response_singleton]
  exact ⟨⟨by norm_num, by norm_num⟩, by simp, List.Perm.refl _⟩

theorem io_compress_ne_zero :
    ∀ v ∈ ioRecords.requests ++ ioRecords.responses,
      FiniteIO.compress ioCoins v ≠ 0 := by
  intro v hv
  change v ∈ (exec honestSeed honestAlpha).derivedRequestIO ++
    (exec honestSeed honestAlpha).derivedResponseIO at hv
  rw [derived_request_singleton, derived_response_singleton] at hv
  simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  all_goals
    simp [FiniteIO.compress, ioCoins, Walk.rlc, Fin.sum_univ_succ,
      NockVM.encRecFormR, encRecC, requestRecord, formula_fp]

noncomputable def ioWitness : FiniteIO.PostChallengeIOWitness ioRecords ioCoins :=
  Classical.choose (FiniteIO.finiteIO_complete_of_LIO ioRecords ioCoins io_lio
    io_compress_ne_zero)

theorem io_accepts : FiniteIO.FiniteIOAccepts ioRecords ioCoins ioWitness :=
  Classical.choose_spec (FiniteIO.finiteIO_complete_of_LIO ioRecords ioCoins io_lio
    io_compress_ne_zero)

theorem io_gammaGood :
    ioCoins.gamma ∉ FiniteIO.IORLCCollisionEvent ioRecords := by
  change (0 : K73cubic) ∉ FiniteIO.IORLCCollisionEvent
    { requests := (exec honestSeed honestAlpha).derivedRequestIO
      responses := (exec honestSeed honestAlpha).derivedResponseIO }
  rw [derived_request_singleton, derived_response_singleton]
  simp [FiniteIO.IORLCCollisionEvent]

theorem io_poleGood :
    ioCoins.pole ∉ FiniteIO.IOLogDerivEvent ioRecords ioCoins.gamma := by
  change (0 : K73cubic) ∉ FiniteIO.IOLogDerivEvent
    { requests := (exec honestSeed honestAlpha).derivedRequestIO
      responses := (exec honestSeed honestAlpha).derivedResponseIO } 0
  rw [derived_request_singleton, derived_response_singleton]
  have hQ :
      FiniteIO.ioQP
        { requests := [encRecFormR (requestRecord honestSeed honestAlpha) formRDefault]
          responses := [encRecFormR (requestRecord honestSeed honestAlpha) formRDefault] } 0 =
            0 := by
    unfold FiniteIO.ioQP FiniteIO.reqVals FiniteIO.respVals
    ring
  simp [FiniteIO.IOLogDerivEvent, hQ]

def ioStrategy :
    FiniteIO.FiniteIOStrategy K73cubic 9 4 (ringChar K73cubic) where
  records := ioRecords
  coins := ioCoins
  witness := ioWitness
  accepts := io_accepts
  uniqueRequest := by change (exec honestSeed honestAlpha).derivedRequestIO.Nodup
                      rw [derived_request_singleton]; simp
  uniqueResponse := by change (exec honestSeed honestAlpha).derivedResponseIO.Nodup
                       rw [derived_response_singleton]; simp
  requestRange := by change IO.InRange 4 (exec honestSeed honestAlpha).derivedRequestIO.length
                     rw [derived_request_singleton]; norm_num [IO.InRange]
  responseRange := by change (exec honestSeed honestAlpha).derivedResponseIO.length ≤ 4
                      rw [derived_response_singleton]; norm_num
  charBound := by
    rw [← Algebra.ringChar_eq F73 K73cubic, ZMod.ringChar_zmod_n]
    norm_num
  gammaGood := io_gammaGood
  poleGood := io_poleGood

def semanticRecord : (nmrMEF F73 K73cubic).Rec :=
  (3,
    ((((fp honestSeed formulaNoun).size,
        (fp honestSeed formulaNoun).dyck,
        (fp honestSeed formulaNoun).leaf),
      ((fp honestSeed resultNoun).size,
        (fp honestSeed resultNoun).dyck,
        (fp honestSeed resultNoun).leaf)),
    1))

theorem semantic_preimage_record :
    memRecOfNMR F73 K73cubic
        ((nmrEncoding F73 K73cubic (cfg honestSeed honestAlpha).challenges.α).encode
          semanticRecord) =
      requestRecord honestSeed honestAlpha := by
  ext <;>
    simp [memRecOfNMR, nmrEncoding, semanticRecord, cfg, requestRecord,
      honestSeed, honestAlpha]
  exact map_natCast (algebraMap F73 K73cubic) 3

theorem semantic_bridge_eq :
    bridge F73 K73cubic (cfg honestSeed honestAlpha).challenges.α (cfg honestSeed honestAlpha).challenges.lam semanticRecord =
      encRecFormR (requestRecord honestSeed honestAlpha) formRDefault := by
  rw [← d2_record_bridge_agrees, semantic_preimage_record]
  rfl

theorem honestAlpha_order : orderOf honestAlpha = 9 := by
  have hbase : orderOf (4 : F73) = 9 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide
  have hcast : honestAlpha = algebraMap F73 K73cubic (4 : F73) := by
    unfold honestAlpha
    exact (map_natCast (algebraMap F73 K73cubic) 4).symm
  rw [hcast]
  change orderOf ((algebraMap F73 K73cubic).toMonoidHom (4 : F73)) = 9
  exact (orderOf_injective (algebraMap F73 K73cubic).toMonoidHom
    (algebraMap F73 K73cubic).injective (4 : F73)).trans hbase

def semanticPreimage :
    SemanticIOPreimage (cfg honestSeed honestAlpha) (exec honestSeed honestAlpha) where
  timestampBound := 2
  timestampBound_le_order := by
    change 2 ≤ orderOf honestAlpha
    rw [honestAlpha_order]
    norm_num
  semanticRequests := [semanticRecord]
  semanticResponses := [semanticRecord]
  requestTimestampBound := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    norm_num [semanticRecord]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    norm_num [semanticRecord]
  semantic_lmio := by
    rw [IO.LmIO_iff]
    exact ⟨by norm_num [IO.InRange, cfg], by simp, by simp, by simp⟩
  requestTimestamp_determines := by
    intro x hx y hy _
    simp only [List.mem_singleton] at hx hy
    rw [hx, hy]
  requests_bridge := by
    rw [bridgeRecords, List.map_singleton, semantic_bridge_eq, derived_request_singleton]
  responses_bridge := by
    rw [bridgeRecords, List.map_singleton, semantic_bridge_eq, derived_response_singleton]

theorem honest_semanticExactLanguage :
    SemanticExactLanguage (cfg honestSeed honestAlpha) (exec honestSeed honestAlpha) :=
  ⟨honest_computeRowsAccepted, honest_memoryRowsAccepted, ⟨semanticPreimage⟩⟩

theorem honest_chained :
    ChainedSemanticExactLanguage (cfg honestSeed honestAlpha)
      (exec honestSeed honestAlpha) where
  semantic := honest_semanticExactLanguage
  z_ne_zero := honestSeed_ne
  compute_wf := by
    intro i
    fin_cases i
    rw [computePubAt_zero]
    exact compute_wf
  memory_wf := by
    intro i
    fin_cases i
    · rw [memoryPubAt_zero]
      exact dummy_wf
    · rw [memoryPubAt_one]
      exact read_wf
    · rw [memoryPubAt_two]
      exact decompose_wf
    · rw [memoryPubAt_three]
      exact head_wf
    · rw [memoryPubAt_four]
      exact verify_wf
    · rw [memoryPubAt_five]
      exact tail_wf
  compute_chain := by
    intro i hi
    fin_cases i
    norm_num [cfg] at hi
  memory_chain := by
    intro i hi
    fin_cases i
    · rw [memoryPubAt_zero, memoryPubAt_one]
      rfl
    · rw [memoryPubAt_one, memoryPubAt_two]
      rfl
    · rw [memoryPubAt_two, memoryPubAt_three]
      rfl
    · rw [memoryPubAt_three, memoryPubAt_four]
      rfl
    · rw [memoryPubAt_four, memoryPubAt_five]
      rfl
    · norm_num [cfg] at hi
  memory_first_counts := by rw [memoryPubAt_zero]; rfl
  memory_first_indicator := by rw [memoryPubAt_zero]; rfl
  memory_first_ipre := by rw [memoryPubAt_zero]; rfl
  memory_last_icur := by
    have hlast :
        (cfg honestSeed honestAlpha).orbit.lastIndex
          (cfg honestSeed honestAlpha).memRows
          (cfg honestSeed honestAlpha).memRows_pos =
            ⟨5, by norm_num [cfg]⟩ := rfl
    rw [hlast, memoryPubAt_five]
    rfl
  memory_same_lambda :=
    ExactExecution.memory_same_lambda_of_const _ _
      (exec_memory_lambda_unset honestSeed honestAlpha)

/-! ## A genuine six-family assignment and phase-correct raw commitment -/

def honestAlphaC : K73cubic := 0

def honestGamma : K73cubic := 0

def honestRawZeroFamily : RawPlusIOSegmentedFamily F73 K73cubic :=
  (familyData honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).atCoins honestAlphaC honestGamma

theorem honestRawZeroFamily_problem :
    honestRawZeroFamily.problem = ⟨cfg honestSeed honestAlpha,
      exec honestSeed honestAlpha⟩ :=
  specializedProblem_eq honestSeed honestSeed_ne honestAlpha

theorem honestRawZeroFamily_tableAssumptions :
    honestRawZeroFamily.problem.TableCompletenessAssumptions := by
  rw [honestRawZeroFamily_problem]
  exact ⟨honestSeed_ne, honest_chained.compute_wf, honest_chained.memory_wf,
    honest_chained.memory_same_lambda⟩

theorem honestRawZeroFamily_progCapacity :
    honestRawZeroFamily.exec.derivedRequestIO.length + 1 ≤
      2 ^ honestRawZeroFamily.cfg.orbit.h := by
  change
    (specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).exec.derivedRequestIO.length + 1 ≤
      2 ^ (specializedProblem timestampStrategy honestSeed honestSeed_ne
        honestAlpha MemoryTable.formRDefault).cfg.orbit.h
  rw [specializedProblem_eq]
  rw [derived_request_singleton]
  norm_num [cfg, executionOrbit]

theorem honestRawZeroFamily_memCapacity :
    honestRawZeroFamily.exec.derivedResponseIO.length + 1 ≤
      2 ^ honestRawZeroFamily.cfg.orbit.h := by
  change
    (specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).exec.derivedResponseIO.length + 1 ≤
      2 ^ (specializedProblem timestampStrategy honestSeed honestSeed_ne
        honestAlpha MemoryTable.formRDefault).cfg.orbit.h
  rw [specializedProblem_eq]
  rw [derived_response_singleton]
  norm_num [cfg, executionOrbit]

def honestLegacyZeroFamily : PlusIOSegmentedFamily F73 K73cubic :=
  honestRawZeroFamily.toLegacy honestRawZeroFamily_tableAssumptions
    (fun _ _ h => NodeEncoding.computeNodeEncode_labelOf_eq stateTagChar h)
    (fun _ _ h => NodeEncoding.memoryNodeEncode_labelOf_eq stateTagChar h)
    honestRawZeroFamily_progCapacity honestRawZeroFamily_memCapacity

theorem honestLegacyZeroFamily_chained :
    ChainedSemanticExactLanguage honestLegacyZeroFamily.problem.cfg
      honestLegacyZeroFamily.problem.exec := by
  change ChainedSemanticExactLanguage
    (specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).cfg
    (specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).exec
  rw [specializedProblem_eq]
  exact honest_chained

def honestLegacyZeroFamily_semanticWitness :
    SemanticIOWitness honestLegacyZeroFamily.problem.cfg
      honestLegacyZeroFamily.problem.exec := by
  change SemanticIOWitness
    (specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).cfg
    (specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).exec
  rw [specializedProblem_eq]
  exact
    { timestampBound := semanticPreimage.timestampBound
      timestampBound_le_order := semanticPreimage.timestampBound_le_order
      semanticRequests := semanticPreimage.semanticRequests
      semanticResponses := semanticPreimage.semanticResponses
      requestTimestampBound := semanticPreimage.requestTimestampBound
      responseTimestampBound := semanticPreimage.responseTimestampBound
      semantic_lmio := semanticPreimage.semantic_lmio
      requestTimestamp_determines := semanticPreimage.requestTimestamp_determines
      requests_bridge := semanticPreimage.requests_bridge
      responses_bridge := semanticPreimage.responses_bridge
      semanticRequests_nodup := by simp [semanticPreimage] }

theorem honestLegacyZeroFamily_KszBound :
    honestLegacyZeroFamily.problem.cfg.Ksz < ringChar K73cubic := by
  change
    (specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).cfg.Ksz <
      ringChar K73cubic
  rw [specializedProblem_eq]
  rw [← Algebra.ringChar_eq F73 K73cubic, ZMod.ringChar_zmod_n]
  norm_num [cfg]

structure HonestCompletion where
  requests : IOField K73cubic
  responses : IOField K73cubic
  outMem : IOField K73cubic
  assignment :
    JointAssignment
      (honestLegacyZeroFamily.withIOEndpoints requests responses outMem)
      (ringChar K73cubic)

theorem honestCompletion_nonempty : Nonempty HonestCompletion := by
  obtain ⟨requests, responses, outMem, ⟨A⟩⟩ :=
    jointVerification_complete honestLegacyZeroFamily
      honestLegacyZeroFamily_chained honestLegacyZeroFamily_semanticWitness
      honestLegacyZeroFamily_KszBound
  exact ⟨⟨requests, responses, outMem, A⟩⟩

noncomputable def honestCompletion : HonestCompletion :=
  Classical.choice honestCompletion_nonempty

abbrev honestLegacyFamily : PlusIOSegmentedFamily F73 K73cubic :=
  honestLegacyZeroFamily.withIOEndpoints honestCompletion.requests
    honestCompletion.responses honestCompletion.outMem

abbrev honestAssignment :
    PlusIOSameExecutionAssignment honestLegacyFamily (ringChar K73cubic) :=
  honestCompletion.assignment.sameExecution

/-- Same as `inactive_mem_zero`, on the legacy family's specialized problem. -/
-- Provisional.
theorem inactive_cprime_one_legacy
    (i : Fin honestLegacyFamily.problem.cfg.memRows)
    (hnr : (honestLegacyFamily.problem.exec.memoryPubAt i).st ≠ .read_root)
    (hnv : (honestLegacyFamily.problem.exec.memoryPubAt i).st ≠ .verify_child) :
    (honestLegacyFamily.problem.exec.memoryPubAt i).cprime = 1 := by
  revert i
  change ∀ i : Fin (specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).cfg.memRows,
    ((specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.memoryPubAt
        i).st ≠ .read_root →
      ((specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.memoryPubAt
        i).st ≠ .verify_child →
      ((specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.memoryPubAt
        i).cprime = 1
  rw [specializedProblem_eq]
  exact inactive_cprime_one honestSeed honestAlpha

theorem inactive_mem_zero_legacy
    (i : Fin honestLegacyFamily.problem.cfg.memRows)
    (hnr : (honestLegacyFamily.problem.exec.memoryPubAt i).st ≠ .read_root)
    (hnv : (honestLegacyFamily.problem.exec.memoryPubAt i).st ≠ .verify_child) :
    (honestLegacyFamily.problem.exec.memoryPubAt i).mem = ComputeTable.MemRec.zero := by
  revert i
  change ∀ i : Fin (specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).cfg.memRows,
    ((specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.memoryPubAt
        i).st ≠ .read_root →
      ((specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.memoryPubAt
        i).st ≠ .verify_child →
      ((specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.memoryPubAt
        i).mem = ComputeTable.MemRec.zero
  rw [specializedProblem_eq]
  exact inactive_mem_zero honestSeed honestAlpha

theorem execution_derivedResponseIO_length (z α : K73cubic) :
    (exec z α).derivedResponseIO.length = 1 := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, (execution_rows _ _).2]
  rfl

theorem honestAssignment_response_length :
    honestLegacyFamily.problem.exec.derivedResponseIO.length = 1 := by
  change
    (specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).exec.derivedResponseIO.length = 1
  rw [specializedProblem_eq]
  exact execution_derivedResponseIO_length honestSeed honestAlpha

def acceptedFamilyData (z : K73cubic) (hz : z ≠ 0) (α lmb : K73cubic) :
    AlphaMFamilyData timestampStrategy z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode stateTagChar
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode stateTagChar
  requests := honestCompletion.requests
  responses := honestCompletion.responses
  outMem := honestCompletion.outMem

theorem acceptedFamily_response_length (z : K73cubic) (hz : z ≠ 0)
    (α lmb : K73cubic) :
    (acceptedFamilyData z hz α lmb).base.exec.derivedResponseIO.length = 1 := by
  change ((executionTemplate z).specialize α lmb).derivedResponseIO.length = 1
  rw [ExactExecutionTemplate.specialize_derivedResponseIO_length_eq _ α lmb α
    MemoryTable.formRDefault, executionTemplate_specialize]
  exact execution_derivedResponseIO_length z α

def alphaMCommitment (z : K73cubic) (hz : z ≠ 0) (α lmb : K73cubic) :
    AlphaMCommitment (p := ringChar K73cubic) timestampStrategy z hz α lmb where
  familyData := acceptedFamilyData z hz α lmb
  tables :=
    { compute := honestAssignment.computeTableAux
      memory := honestAssignment.memoryTableAux }
  io :=
    { multiplicity := fun j =>
        honestAssignment.exactIO.multiplicity
          ⟨j, by
            have hj := j.isLt
            have hsource := acceptedFamily_response_length z hz α lmb
            have htarget := honestAssignment_response_length
            omega⟩
      progAcc := honestAssignment.exactIO.progAcc
      memAcc := honestAssignment.exactIO.memAcc }

def honestCoins : JointCoins K73cubic :=
  ((honestAlphaC, honestGamma), (honestAlpha, honestSeed))

def rawStrategy :
    TemplateRawJointSoundness.Strategy F73 K73cubic (ringChar K73cubic) where
  timestamp := timestampStrategy
  afterAlphaM := alphaMCommitment
  afterCoins := fun _ _ _ =>
    { computeLn := honestAssignment.computeWalk.ln
      computeCount := honestAssignment.computeWalk.count
      computeAcc := honestAssignment.computeWalk.acc
      memoryLn := honestAssignment.memoryWalk.ln
      memoryCount := honestAssignment.memoryWalk.count
      memoryAcc := honestAssignment.memoryWalk.acc }

/-- Production verifier with topology arrays generated from the same exact execution. -/
def verifier :
    ProductionRawVerifier.TemplateAdapter.Strategy
      F73 K73cubic (ringChar K73cubic) :=
  ProductionRawVerifier.TemplateAdapter.Strategy.honest rawStrategy

theorem verifier_specializedProblem (z : K73cubic) (hz : z ≠ 0) (α : K73cubic) :
    specializedProblem verifier.raw.timestamp z hz α MemoryTable.formRDefault =
      ⟨cfg z α, exec z α⟩ :=
  specializedProblem_eq z hz α

theorem rawStrategy_familyAt_honest :
    rawStrategy.familyAt honestCoins MemoryTable.formRDefault honestSeed_ne =
      RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily := by
  rfl

theorem rawStrategy_messageAt_honest :
    rawStrategy.messageAt honestCoins MemoryTable.formRDefault honestSeed_ne =
      RawMessage.ofLegacy honestAssignment := by
  rfl

theorem honestRawLegacy_problem :
    (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).problem =
      ⟨cfg honestSeed honestAlpha, exec honestSeed honestAlpha⟩ := by
  change specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault =
    ⟨cfg honestSeed honestAlpha, exec honestSeed honestAlpha⟩
  exact specializedProblem_eq honestSeed honestSeed_ne honestAlpha

theorem rowAlignment_of_rowsAccepted
    (R : RawPlusIOSegmentedFamily F73 K73cubic)
    (hc : R.exec.ComputeRowsAccepted) (hm : R.exec.MemoryRowsAccepted) :
    RawMessage.RowAlignmentGates (R := R) := by
  constructor
  · intro i
    have h := R.exec.computeRowAt_accepted hc i
    exact ⟨h.1, h.2.1⟩
  · intro i
    have h := R.exec.memoryRowAt_accepted hm i
    exact ⟨h.1, h.2.1⟩

theorem honestRawLegacy_computeRowsAccepted :
    (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).exec.ComputeRowsAccepted := by
  change
    (specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).exec.ComputeRowsAccepted
  rw [specializedProblem_eq]
  exact honest_computeRowsAccepted

theorem honestRawLegacy_memoryRowsAccepted :
    (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).exec.MemoryRowsAccepted := by
  change
    (specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).exec.MemoryRowsAccepted
  rw [specializedProblem_eq]
  exact honest_memoryRowsAccepted

theorem honestRawLegacy_computePubAt_zero :
    (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).exec.computePubAt
      ⟨0, (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).cfg.compRows_pos⟩ =
        computePub honestSeed honestAlpha := by
  change
    (specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).exec.computePubAt
        ⟨0, (specializedProblem timestampStrategy honestSeed honestSeed_ne
          honestAlpha MemoryTable.formRDefault).cfg.compRows_pos⟩ =
      computePub honestSeed honestAlpha
  rw [specializedProblem_eq]
  exact computePubAt_zero

theorem honestRawLegacy_memoryPubAt_zero :
    (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).exec.memoryPubAt
      ⟨0, (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).cfg.memRows_pos⟩ =
        dummyHaltPub honestSeed := by
  change
    (specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).exec.memoryPubAt
        ⟨0, (specializedProblem timestampStrategy honestSeed honestSeed_ne
          honestAlpha MemoryTable.formRDefault).cfg.memRows_pos⟩ =
      dummyHaltPub honestSeed
  rw [specializedProblem_eq]
  exact memoryPubAt_zero

theorem honestRawLegacy_memoryPubAt_one :
    (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).exec.memoryPubAt
      ⟨1, by
        change 1 < (specializedProblem timestampStrategy honestSeed honestSeed_ne
          honestAlpha MemoryTable.formRDefault).cfg.memRows
        rw [specializedProblem_eq]
        norm_num [cfg]⟩ =
        readPub honestSeed honestAlpha := by
  let Ps := specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault
  let Pc : RawProblem F73 K73cubic :=
    ⟨cfg honestSeed honestAlpha, exec honestSeed honestAlpha⟩
  have hp : Ps = Pc := specializedProblem_eq honestSeed honestSeed_ne honestAlpha
  have hs : 1 < Ps.cfg.memRows := by rw [hp]; norm_num [Pc, cfg]
  have hc : 1 < Pc.cfg.memRows := by norm_num [Pc, cfg]
  let xs : {P : RawProblem F73 K73cubic // 1 < P.cfg.memRows} := ⟨Ps, hs⟩
  let xc : {P : RawProblem F73 K73cubic // 1 < P.cfg.memRows} := ⟨Pc, hc⟩
  have hxc : xs = xc := Subtype.ext hp
  have hrow := congrArg
    (fun X : {P : RawProblem F73 K73cubic // 1 < P.cfg.memRows} =>
      X.1.exec.memoryPubAt ⟨1, X.2⟩) hxc
  let qS : Fin Ps.cfg.memRows := ⟨1, hs⟩
  let qC : Fin Pc.cfg.memRows := ⟨1, hc⟩
  have hrow' : Ps.exec.memoryPubAt qS = Pc.exec.memoryPubAt qC := by
    convert hrow using 1 <;> apply Fin.ext <;> rfl
  have hfinal : Pc.exec.memoryPubAt qC = readPub honestSeed honestAlpha := by
    simpa [qC, Pc] using memoryPubAt_one
  change Ps.exec.memoryPubAt ⟨1, hs⟩ = readPub honestSeed honestAlpha
  exact hrow'.trans hfinal

theorem honestRawLegacy_memoryPubAt_four :
    (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).exec.memoryPubAt
      ⟨4, by
        change 4 < (specializedProblem timestampStrategy honestSeed honestSeed_ne
          honestAlpha MemoryTable.formRDefault).cfg.memRows
        rw [specializedProblem_eq]
        norm_num [cfg]⟩ =
        verifyPub honestSeed honestAlpha := by
  let Ps := specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault
  let Pc : RawProblem F73 K73cubic :=
    ⟨cfg honestSeed honestAlpha, exec honestSeed honestAlpha⟩
  have hp : Ps = Pc := specializedProblem_eq honestSeed honestSeed_ne honestAlpha
  have hs : 4 < Ps.cfg.memRows := by rw [hp]; norm_num [Pc, cfg]
  have hc : 4 < Pc.cfg.memRows := by norm_num [Pc, cfg]
  let xs : {P : RawProblem F73 K73cubic // 4 < P.cfg.memRows} := ⟨Ps, hs⟩
  let xc : {P : RawProblem F73 K73cubic // 4 < P.cfg.memRows} := ⟨Pc, hc⟩
  have hxc : xs = xc := Subtype.ext hp
  have hrow := congrArg
    (fun X : {P : RawProblem F73 K73cubic // 4 < P.cfg.memRows} =>
      X.1.exec.memoryPubAt ⟨4, X.2⟩) hxc
  let qS : Fin Ps.cfg.memRows := ⟨4, hs⟩
  let qC : Fin Pc.cfg.memRows := ⟨4, hc⟩
  have hrow' : Ps.exec.memoryPubAt qS = Pc.exec.memoryPubAt qC := by
    convert hrow using 1 <;> apply Fin.ext <;> rfl
  have hfinal : Pc.exec.memoryPubAt qC = verifyPub honestSeed honestAlpha := by
    simpa [qC, Pc] using memoryPubAt_four
  change Ps.exec.memoryPubAt ⟨4, hs⟩ = verifyPub honestSeed honestAlpha
  exact hrow'.trans hfinal

theorem honestRawLegacy_Ksz :
    (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).cfg.Ksz = 4 := by
  change
    (specializedProblem timestampStrategy honestSeed honestSeed_ne honestAlpha MemoryTable.formRDefault).cfg.Ksz = 4
  rw [specializedProblem_eq]
  rfl

theorem honestRawLegacy_requests :
    (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).exec.derivedRequestIO =
      [encRecFormR (requestRecord honestSeed honestAlpha) formRDefault] := by
  change
    (specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).exec.derivedRequestIO = _
  rw [specializedProblem_eq]
  exact derived_request_singleton

theorem honestRawLegacy_responses :
    (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).exec.derivedResponseIO =
      [encRecFormR (requestRecord honestSeed honestAlpha) formRDefault] := by
  change
    (specializedProblem timestampStrategy honestSeed honestSeed_ne
      honestAlpha MemoryTable.formRDefault).exec.derivedResponseIO = _
  rw [specializedProblem_eq]
  exact derived_response_singleton

theorem honestVerifierGates :
    (RawMessage.ofLegacy honestAssignment).VerifierGates
      semanticSkeleton.publicClaim honestCoins := by
  refine ⟨honestSeed_ne, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact rowAlignment_of_rowsAccepted
      (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily)
      honestRawLegacy_computeRowsAccepted honestRawLegacy_memoryRowsAccepted
  · refine ⟨rfl, ?_, rfl, ?_⟩
    · intro hchar
      have hh : hchar = stateTagChar := Subsingleton.elim _ _
      subst hchar
      rfl
    · intro hchar
      have hh : hchar = stateTagChar := Subsingleton.elim _ _
      subst hchar
      rfl
  · rw [honestRawLegacy_computePubAt_zero]
    change fp honestSeed subjectNoun =
      GlobalCarryRecognizer.enc honestSeed subjectNoun
    rfl
  · rw [honestRawLegacy_computePubAt_zero]
    change fp honestSeed formulaNoun =
      GlobalCarryRecognizer.enc honestSeed formulaNoun
    rfl
  · rw [honestRawLegacy_computePubAt_zero]
    change fp honestSeed resultNoun =
      GlobalCarryRecognizer.enc honestSeed resultNoun
    rfl
  · exact honestCompletion.assignment.public_endpoints.1
  · exact honestCompletion.assignment.public_endpoints.2
  · exact honestAssignment.exactIO.multiplicity_ne_zero
  · rw [honestRawLegacy_requests, honestRawLegacy_Ksz]
    norm_num [IO.InRange]
  · rw [honestRawLegacy_requests]
    simp
  · rw [honestRawLegacy_responses, honestRawLegacy_Ksz]
    norm_num
  · rw [honestRawLegacy_responses]
    simp

theorem rawStrategy_accepts_honestCoins :
    rawStrategy.Accepts honestCoins MemoryTable.formRDefault := by
  apply (rawStrategy.accepts_iff_raw honestCoins MemoryTable.formRDefault honestSeed_ne).2
  change (RawMessage.ofLegacy honestAssignment).Accepts
    semanticSkeleton.publicClaim honestCoins
  exact RawMessage.accepts_of_legacy_assignment
    semanticSkeleton.publicClaim honestCoins honestAssignment
    honestCompletion.assignment.sixFamilies honestVerifierGates

theorem honest_exactTopology :
    ComputeExactTopology
        (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).exec ∧
      MemoryExactTopology
        (RawPlusIOSegmentedFamily.ofLegacy honestLegacyFamily).exec := by
  have hc : walkFamily.exec.ComputeRowsAccepted := by
    change
      (specializedProblem timestampStrategy honestSeed honestSeed_ne
        honestAlpha MemoryTable.formRDefault).exec.ComputeRowsAccepted
    rw [specializedProblem_eq]
    exact honest_computeRowsAccepted
  have hm : walkFamily.exec.MemoryRowsAccepted := by
    change
      (specializedProblem timestampStrategy honestSeed honestSeed_ne
        honestAlpha MemoryTable.formRDefault).exec.MemoryRowsAccepted
    rw [specializedProblem_eq]
    exact honest_memoryRowsAccepted
  have htop :=
    (exactTopology_iff_rawTopologyBindingResidual_of_rowsAccepted
      walkFamily hc hm).2 topologyBinding
  exact htop

theorem verifier_accepts_honestCoins :
    verifier.Accepts honestCoins MemoryTable.formRDefault := by
  exact ProductionRawVerifier.TemplateAdapter.Strategy.honest_accepts
    rawStrategy honestCoins MemoryTable.formRDefault honestSeed_ne rawStrategy_accepts_honestCoins
    honest_exactTopology

/-! ## One genuine binding supplies R3/R4 and the universal scan -/

theorem bind_computeRow (z α : K73cubic) :
    BindComputeRow z computeSkeletonRow (computeRow z α) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro slot
    cases slot <;>
      simp [decActive, hasTailDecomposition, decFP, bindFP,
        computeSkeletonRow, computeRow, computeDec, fp]
  · intro i
    have hi : ¬ ((i : ℕ) < ComputeTable.fanoutComp computeSkeletonRow.state) := by
      simp [computeSkeletonRow, ComputeTable.fanoutComp]
    rw [dif_neg hi]
    fin_cases i <;>
      simp [computeSubformulaFPs, ComputeTable.sfTriple, computeRow, computePub]
  · intro i
    fin_cases i
    · exact ⟨rfl, rfl, rfl⟩
    · rfl
    · rfl

theorem bind_dummyHaltRow (z : K73cubic) :
    BindMemoryRow z dummyHaltSkeletonRow (dummyHaltRow z) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem dummyHaltSkeletonRow.state) := by
      simp [dummyHaltSkeletonRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_readRow (z α : K73cubic) :
    BindMemoryRow z readSkeletonRow (readRow z α) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [readSkeletonRow, MemoryTable.fanoutMem, memoryChildCell, readRow, readPub]
  · refine ⟨rfl, rfl, ?_, ?_⟩ <;>
      simp [readSkeletonRow, verifySkeletonRow, requestSkeleton, readRow, verifyRow, readPub,
        verifyPub, Pub.cprime, rowCprime, NockVM.formRCprime, rowT, requestRecord,
        rowRecord, NockVM.formRRow]

theorem bind_decomposeRow (z α : K73cubic) :
    BindMemoryRow z decomposeSkeletonRow (decomposeRow z α) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bind_headRow (z : K73cubic) :
    BindMemoryRow z headSkeletonRow (headRow z) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem headSkeletonRow.state) := by
      simp [headSkeletonRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bind_verifyRow (z α : K73cubic) :
    BindMemoryRow z verifySkeletonRow (verifyRow z α) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [verifySkeletonRow, MemoryTable.fanoutMem, memoryChildCell, verifyRow, verifyPub]
  · refine ⟨rfl, rfl, ?_, ?_⟩ <;>
      simp [readSkeletonRow, verifySkeletonRow, requestSkeleton, readRow, verifyRow, readPub,
        verifyPub, Pub.cprime, rowCprime, NockVM.formRCprime, rowT, requestRecord,
        rowRecord, NockVM.formRRow]

theorem bind_tailRow (z : K73cubic) :
    BindMemoryRow z tailSkeletonRow (tailRow z) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem tailSkeletonRow.state) := by
      simp [tailSkeletonRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bindsAt (z α : K73cubic) :
    BindsAt z semanticSkeleton (cfg z α) (exec z α) := by
  have hcompute :
      ComputeTreeBinds z semanticSkeleton.computeTree (exec z α).computeTree :=
    .node (by simp [computeSkeletonRow, ComputeTable.fanoutComp])
      (bind_computeRow z α) .nil
  have hmemory :
      List.Forall₂ (MemoryTreeBinds z) semanticSkeleton.memoryForest
        (exec z α).memoryForest :=
    .cons
      (.node (by simp [dummyHaltSkeletonRow, MemoryTable.fanoutMem])
        (bind_dummyHaltRow z) .nil)
      (.cons
      (.node (by simp [readSkeletonRow, MemoryTable.fanoutMem]) (bind_readRow z α)
        (.cons
          (.node (by simp [decomposeSkeletonRow, MemoryTable.fanoutMem])
            (bind_decomposeRow z α)
            (.cons
              (.node (by simp [headSkeletonRow, MemoryTable.fanoutMem])
                (bind_headRow z) .nil)
              (.cons
                (.node (by simp [verifySkeletonRow, MemoryTable.fanoutMem])
                  (bind_verifyRow z α)
                  (.cons
                    (.node (by simp [tailSkeletonRow, MemoryTable.fanoutMem])
                      (bind_tailRow z) .nil)
                    .nil))
                .nil)))
          .nil))
      .nil)
  exact BindsAt.ofTreeBindings (F := F73) (K := K73cubic)
    (S := semanticSkeleton) (cfg := cfg z α) (exec := exec z α)
    rfl hcompute hmemory

theorem scanAt (z α : K73cubic) :
    ActiveFingerprintChecksAt z commitment (exec z α) :=
  activeFingerprintChecksAt_of_bindsAt (bindsAt z α)

theorem shapeMatchAt (z α : K73cubic) :
    ExecTreeShapeMatchesAt commitment (exec z α) :=
  execTreeShapeMatchesAt_of_bindsAt (bindsAt z α)

theorem rowFrameAt (z α : K73cubic) :
    RowFrameChecksAt z commitment (exec z α) :=
  rowFrameChecksAt_of_bindsAt (bindsAt z α)

/-! ### λ-free template binding

The a-bearing templates bind to the skeleton before `(α, λ)` are drawn, so every specialization
— at every sampled `λ`, not only the fixture's `formRDefault` — binds
(`TemplateSemanticConsistencyAt.specialize`). -/

theorem bindA_readRowTemplate (z : K73cubic) :
    MemoryRowTemplate.BindsRow z readSkeletonRow (readRowTemplate z) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [readSkeletonRow, MemoryTable.fanoutMem, memoryChildCell, readRowTemplate, readPubA,
        readPub]
  · refine ⟨rfl, rfl, ?_⟩
    simp [readSkeletonRow, requestSkeleton, readRowTemplate, readPubA, requestRecord]

theorem bindA_verifyRowTemplate (z : K73cubic) :
    MemoryRowTemplate.BindsRow z verifySkeletonRow (verifyRowTemplate z) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · rfl
    · simp [verifySkeletonRow, MemoryTable.fanoutMem, memoryChildCell, verifyRowTemplate,
        verifyPubA, verifyPub]
  · refine ⟨rfl, rfl, ?_⟩
    simp [verifySkeletonRow, requestSkeleton, verifyRowTemplate, verifyPubA, requestRecord]

theorem bindA_decomposeRowTemplate (z : K73cubic) :
    MemoryRowTemplate.BindsRow z decomposeSkeletonRow (decomposeRowTemplate z) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · rfl

theorem bindA_headRowTemplate (z : K73cubic) :
    MemoryRowTemplate.BindsRow z headSkeletonRow (headRowTemplate z) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem headSkeletonRow.state) := by
      simp [headSkeletonRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bindA_tailRowTemplate (z : K73cubic) :
    MemoryRowTemplate.BindsRow z tailSkeletonRow (tailRowTemplate z) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem tailSkeletonRow.state) := by
      simp [tailSkeletonRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem bindA_dummyHaltRowTemplate (z : K73cubic) :
    MemoryRowTemplate.BindsRow z dummyHaltSkeletonRow (dummyHaltRowTemplate z) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · intro i
    have hi : ¬ ((i : ℕ) < MemoryTable.fanoutMem dummyHaltSkeletonRow.state) := by
      simp [dummyHaltSkeletonRow, MemoryTable.fanoutMem]
    rw [dif_neg hi]
    fin_cases i <;> rfl
  · rfl

theorem templateConsistency (z : K73cubic) :
    TemplateSemanticConsistencyAt z semanticSkeleton (configTemplate z) (executionTemplate z) where
  sampledSeed := rfl
  computeTree :=
    .node (by simp [computeSkeletonRow, ComputeTable.fanoutComp])
      ⟨rfl, bind_computeRow z 0⟩ .nil
  memoryForest :=
    .cons
      (.node (by simp [dummyHaltSkeletonRow, MemoryTable.fanoutMem])
        (bindA_dummyHaltRowTemplate z) .nil)
      (.cons
      (.node (by simp [readSkeletonRow, MemoryTable.fanoutMem]) (bindA_readRowTemplate z)
        (.cons
          (.node (by simp [decomposeSkeletonRow, MemoryTable.fanoutMem])
            (bindA_decomposeRowTemplate z)
            (.cons
              (.node (by simp [headSkeletonRow, MemoryTable.fanoutMem])
                (bindA_headRowTemplate z) .nil)
              (.cons
                (.node (by simp [verifySkeletonRow, MemoryTable.fanoutMem])
                  (bindA_verifyRowTemplate z)
                  (.cons
                    (.node (by simp [tailSkeletonRow, MemoryTable.fanoutMem])
                      (bindA_tailRowTemplate z) .nil)
                    .nil))
                .nil)))
          .nil))
      .nil)

/-- Binding at every sampled `(α, λ)`. -/
theorem bindsAt_specialized (z : K73cubic) (hz : z ≠ 0) (α lmb : K73cubic) :
    BindsAt z semanticSkeleton
      (specializedProblem timestampStrategy z hz α lmb).cfg
      (specializedProblem timestampStrategy z hz α lmb).exec :=
  (templateConsistency z).specialize

theorem derivedRequestIO_singleton (z : K73cubic) (hz : z ≠ 0) (α : K73cubic) :
    (exec z α).derivedRequestIO = [encRecFormR (requestRecord z α) formRDefault] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, (execution_rows z α).1]
  simp [NockVM.activeRequestRecords, computeRow, computePub]

theorem derivedResponseIO_singleton (z α : K73cubic) :
    (exec z α).derivedResponseIO = [encRecFormR (requestRecord z α) formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, (execution_rows z α).2]
  simp [dummyHaltRow, dummyHaltPub, readRow, decomposeRow, headRow, verifyRow, tailRow,
    readPub, decomposePub, headPub, verifyPub, tailPub, Pub.cprime, rowRecord_encRecC]

/-! ## R5 and R7 on the actual nonempty OP1 skeleton -/

theorem slotSemantics :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonSlotSemantics s := by
  intro s hs
  have hrows : computeSkeletonRows semanticSkeleton = [computeSkeletonRow] := by
    norm_num [computeSkeletonRows, semanticSkeleton, bfsForest, NTree.size, totalSize]
  rw [hrows] at hs
  simp only [List.mem_singleton] at hs
  subst s
  exact
    { s0_slot := fun h => absurd h (by simp [computeSkeletonRow])
      s9_slot := fun h => absurd h (by simp [computeSkeletonRow]) }

theorem recordEquations :
    ∀ s ∈ computeSkeletonRows semanticSkeleton, SkeletonRecordEquations s := by
  intro s hs
  have hrows : computeSkeletonRows semanticSkeleton = [computeSkeletonRow] := by
    norm_num [computeSkeletonRows, semanticSkeleton, bfsForest, NTree.size, totalSize]
  rw [hrows] at hs
  simp only [List.mem_singleton] at hs
  subst s
  exact
    { s0_record := fun h => absurd h (by simp [computeSkeletonRow])
      s9_record := fun h => absurd h (by simp [computeSkeletonRow]) }

theorem sizeWindowBound :
    SizeWindowCounting.SizeWindowNounsBoundedBy semanticSkeleton 2 := by
  intro n hn
  simp [SizeWindowCounting.skeletonSizeWindowNouns,
    SizeWindowCounting.requiredSizeWindowNouns, semanticSkeleton,
    computeSkeletonRows, computeSkeletonRow, bfsForest, NTree.size, totalSize] at hn

/-- The replacement carrier is genuinely nonempty and both table languages accept every canonical
BFS row. -/
theorem honest_execution_nonempty :
    (exec honestSeed honestAlpha).computeRows.length = 1 ∧
      (exec honestSeed honestAlpha).memoryRows.length = 6 ∧
      (exec honestSeed honestAlpha).ComputeRowsAccepted ∧
      (exec honestSeed honestAlpha).MemoryRowsAccepted ∧
      ChainedSemanticExactLanguage (cfg honestSeed honestAlpha)
        (exec honestSeed honestAlpha) := by
  refine ⟨by rw [(execution_rows _ _).1]; rfl,
    by rw [(execution_rows _ _).2]; rfl,
    honest_computeRowsAccepted, honest_memoryRowsAccepted, honest_chained⟩

/-! ## The concrete strict package -/

def Hc : Finset F73 := {0}
def Hm : Finset F73 := {0, 1, 2, 3, 4, 5}

theorem Hc_card : Hc.card = (exec honestSeed honestAlpha).computeRows.length := by
  rw [(execution_rows _ _).1]
  norm_num [Hc]

theorem Hm_card : Hm.card = (exec honestSeed honestAlpha).memoryRows.length := by
  rw [(execution_rows _ _).2]
  change ({0, 1, 2, 3, 4, 5} : Finset F73).card = 6
  decide

def chalVal : ℕ → F73 := fun _ => 0
def pubVal : ℕ → F73 := fun _ => 0

def compRAP : Framework.RAP F73 :=
  MonolithicRAP.RAP_NockCompIO basis73 chalVal pubVal strictOrbit Hc

def memRAP : Framework.RAP F73 :=
  MonolithicRAP.RAP_NockMemIO basis73 chalVal pubVal strictOrbit Hm

def compLanguage : Nock.Reified.Env K73cubic → Prop :=
  fun envK => ∀ g ∈ (MonolithicRAP.compTemplate F73).extTransition ++
      (MonolithicRAP.compTemplate F73).extDeg1 ++
      (MonolithicRAP.compTemplate F73).extDeg3, g.eval envK = 0

def memLanguage : Nock.Reified.Env K73cubic → Prop :=
  fun envK => ∀ g ∈ (MonolithicRAP.memTemplate F73).extTransition ++
      (MonolithicRAP.memTemplate F73).extDeg1 ++
      (MonolithicRAP.memTemplate F73).extDeg3, g.eval envK = 0

theorem compSemanticTemplate :
    Nock.RedTeam.Batch29.B29SemanticTemplate
      (K := K73cubic) (MonolithicRAP.compTemplate F73) compLanguage :=
  Nock.RedTeam.Batch29.b29_residual_satisfiable _

theorem memSemanticTemplate :
    Nock.RedTeam.Batch29.B29SemanticTemplate
      (K := K73cubic) (MonolithicRAP.memTemplate F73) memLanguage :=
  Nock.RedTeam.Batch29.b29_residual_satisfiable _

theorem computeSkeletonRow_bounded :
    computeSkeletonRow.BoundedBy 73 := by
  refine ⟨by simp [computeSkeletonRow, subjectNoun, FieldEmbedding.BoundedBy],
    by simp [computeSkeletonRow, formulaNoun, headNoun, resultNoun,
      FieldEmbedding.BoundedBy],
    by simp [computeSkeletonRow, resultNoun, FieldEmbedding.BoundedBy], ?_, ?_, ?_⟩
  · intro slot h
    cases slot <;>
      simp [computeSkeletonRow, headNoun, resultNoun, FieldEmbedding.BoundedBy]
  · intro i h
    simp [computeSkeletonRow, ComputeTable.fanoutComp] at h
  · intro i h
    fin_cases i <;>
      simp [computeSkeletonRow, requestSkeleton, formulaNoun, headNoun, resultNoun,
        SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy] at h ⊢

theorem dummyHaltSkeletonRow_bounded : dummyHaltSkeletonRow.BoundedBy 73 := by
  refine ⟨by simp [dummyHaltSkeletonRow, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [dummyHaltSkeletonRow, MemoryTable.fanoutMem] at h
  · intro h
    simp [dummyHaltSkeletonRow, memoryMemRecKind] at h

theorem readSkeletonRow_bounded : readSkeletonRow.BoundedBy 73 := by
  refine ⟨by simp [readSkeletonRow, formulaNoun, headNoun, resultNoun,
    FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    fin_cases i <;>
      simp [readSkeletonRow, MemoryTable.fanoutMem, formulaNoun, headNoun, resultNoun,
        FieldEmbedding.BoundedBy] at h ⊢
  · intro h
    simp [readSkeletonRow, requestSkeleton, formulaNoun, headNoun, resultNoun,
      SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy]

theorem decomposeSkeletonRow_bounded : decomposeSkeletonRow.BoundedBy 73 := by
  refine ⟨by simp [decomposeSkeletonRow, formulaNoun, headNoun, resultNoun,
    FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    fin_cases i <;>
      simp [decomposeSkeletonRow, headNoun, resultNoun, FieldEmbedding.BoundedBy]
  · intro h
    simp [decomposeSkeletonRow, memoryMemRecKind] at h

theorem headSkeletonRow_bounded : headSkeletonRow.BoundedBy 73 := by
  refine ⟨by simp [headSkeletonRow, headNoun, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [headSkeletonRow, MemoryTable.fanoutMem] at h
  · intro h
    simp [headSkeletonRow, memoryMemRecKind] at h

theorem verifySkeletonRow_bounded : verifySkeletonRow.BoundedBy 73 := by
  refine ⟨by simp [verifySkeletonRow, resultNoun, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    fin_cases i <;>
      simp [verifySkeletonRow, resultNoun, FieldEmbedding.BoundedBy]
  · intro h
    simp [verifySkeletonRow, requestSkeleton, formulaNoun, headNoun, resultNoun,
      SemanticStrategy.MemRecSkeleton.BoundedBy, FieldEmbedding.BoundedBy]

theorem tailSkeletonRow_bounded : tailSkeletonRow.BoundedBy 73 := by
  refine ⟨by simp [tailSkeletonRow, resultNoun, FieldEmbedding.BoundedBy], ?_, ?_⟩
  · intro i h
    simp [tailSkeletonRow, MemoryTable.fanoutMem] at h
  · intro h
    simp [tailSkeletonRow, memoryMemRecKind] at h

theorem skeletonBounded : semanticSkeleton.BoundedBy 73 := by
  refine
    { computeRows := ?_
      memoryRows := ?_
      memoryTrees := ?_ }
  · have hrows : computeSkeletonRows semanticSkeleton = [computeSkeletonRow] := by
      norm_num [computeSkeletonRows, semanticSkeleton, bfsForest, NTree.size, totalSize]
    rw [hrows]
    simpa using computeSkeletonRow_bounded
  · have hrows :
        memorySkeletonRows semanticSkeleton =
          [dummyHaltSkeletonRow, readSkeletonRow, decomposeSkeletonRow, headSkeletonRow,
            verifySkeletonRow, tailSkeletonRow] := by
      norm_num [memorySkeletonRows, semanticSkeleton, dummyHaltSkeletonTree, readSkeletonTree,
        decomposeSkeletonTree, headSkeletonTree, verifySkeletonTree, tailSkeletonTree,
        bfsForest, NTree.size, totalSize]
    rw [hrows]
    exact ⟨dummyHaltSkeletonRow_bounded, readSkeletonRow_bounded, decomposeSkeletonRow_bounded,
      headSkeletonRow_bounded, verifySkeletonRow_bounded, tailSkeletonRow_bounded⟩
  · intro tree htree node hnode
    change tree ∈ [dummyHaltSkeletonTree, readSkeletonTree] at htree
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htree
    rcases htree with rfl | rfl
    · have hm : node ∈ bfsForest [dummyHaltSkeletonTree] :=
        (mem_bfsForest [dummyHaltSkeletonTree] node).2 ⟨dummyHaltSkeletonTree, by simp, hnode⟩
      simp [dummyHaltSkeletonTree, bfsForest] at hm
      subst node
      exact dummyHaltSkeletonRow_bounded
    · have hm : node ∈ bfsForest [readSkeletonTree] :=
        (mem_bfsForest [readSkeletonTree] node).2 ⟨readSkeletonTree, by simp, hnode⟩
      simp [readSkeletonTree, decomposeSkeletonTree, headSkeletonTree,
        verifySkeletonTree, tailSkeletonTree, bfsForest] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl
      · exact readSkeletonRow_bounded
      · exact decomposeSkeletonRow_bounded
      · exact headSkeletonRow_bounded
      · exact verifySkeletonRow_bounded
      · exact tailSkeletonRow_bounded

theorem combinedBounded :
    ProductionP8Containment.CombinedBoundedBy K73cubic 73 semanticSkeleton := by
  intro pair hp
  simp [EdgeComparisonCensus.combinedSkeletonPairs,
    BoundSemanticTrace.skeletonPairs, EdgeComparisonCensus.edgePairs,
    EdgeComparisonCensus.rowEdgePairs, P8Census.skeletonComparisonCensus,
    P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
    semanticSkeleton, computeSkeletonRow, NTree.childOpt,
    subjectNoun, formulaNoun, headNoun, resultNoun, requestSkeleton,
    SemanticStrategy.SemanticSkeleton.publicClaim, SemanticTrace.ComparisonUse.pair,
    decActive, computeSkeletonRows, bfsForest] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [FieldEmbedding.BoundedBy, subjectNoun, formulaNoun, headNoun, resultNoun,
      SemanticStrategy.SemanticSkeleton.publicClaim, SemanticTrace.ComparisonUse.pair,
      decActive]

def census : EdgeComparisonCensus.CombinedSkeletonCensus K73cubic semanticSkeleton 2 where
  p8 :=
    { leaves_bounded := by
        intro pair hp
        simp [BoundSemanticTrace.skeletonPairs, semanticSkeleton, computeSkeletonRow,
          P8Census.skeletonComparisonCensus, P8Census.skeletonComparisons,
          P8Census.skeletonUse, P8Census.skeletonDec,
          subjectNoun, formulaNoun, headNoun, resultNoun, requestSkeleton,
          SemanticStrategy.SemanticSkeleton.publicClaim,
          SemanticTrace.ComparisonUse.pair, decActive,
          computeSkeletonRows, bfsForest] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [subjectNoun, formulaNoun, headNoun, resultNoun,
            SemanticStrategy.SemanticSkeleton.publicClaim,
            SemanticTrace.ComparisonUse.pair, decActive, Noun.leaves] }
  edges :=
    { leaves_bounded := by
        intro pair hp
        simp [EdgeComparisonCensus.edgePairs, EdgeComparisonCensus.rowEdgePairs,
          semanticSkeleton, computeSkeletonRow, NTree.childOpt, bfsForest] at hp }

theorem q_eq_ringChar : 73 = ringChar K73cubic := by
  rw [← Algebra.ringChar_eq F73 K73cubic, ZMod.ringChar_zmod_n]

theorem KszBound (z : K73cubic) (hz : z ≠ 0) (α lmb : K73cubic) :
    (specializedProblem verifier.raw.timestamp z hz α lmb).cfg.Ksz <
      ringChar K73cubic := by
  change (configTemplate z).Ksz < ringChar K73cubic
  rw [← q_eq_ringChar]
  norm_num [configTemplate]

theorem progCapacity (z : K73cubic) (hz : z ≠ 0) (α lmb : K73cubic) :
    (specializedProblem verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1 ≤
      2 ^ (specializedProblem verifier.raw.timestamp z hz α lmb).cfg.orbit.h := by
  have hlen :
      (specializedProblem verifier.raw.timestamp z hz α lmb).exec.derivedRequestIO.length =
        (specializedProblem verifier.raw.timestamp z hz α
          MemoryTable.formRDefault).exec.derivedRequestIO.length :=
    ExactExecutionTemplate.specialize_derivedRequestIO_length_eq _ α lmb _
  have horb :
      (specializedProblem verifier.raw.timestamp z hz α lmb).cfg.orbit.h =
        (specializedProblem verifier.raw.timestamp z hz α MemoryTable.formRDefault).cfg.orbit.h :=
    rfl
  rw [hlen, horb, verifier_specializedProblem, derivedRequestIO_singleton z hz α]
  norm_num [cfg, executionOrbit]

theorem memCapacity (z : K73cubic) (hz : z ≠ 0) (α lmb : K73cubic) :
    (specializedProblem verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1 ≤
      2 ^ (specializedProblem verifier.raw.timestamp z hz α lmb).cfg.orbit.h := by
  have hlen :
      (specializedProblem verifier.raw.timestamp z hz α lmb).exec.derivedResponseIO.length =
        (specializedProblem verifier.raw.timestamp z hz α
          MemoryTable.formRDefault).exec.derivedResponseIO.length :=
    ExactExecutionTemplate.specialize_derivedResponseIO_length_eq _ α lmb α _
  have horb :
      (specializedProblem verifier.raw.timestamp z hz α lmb).cfg.orbit.h =
        (specializedProblem verifier.raw.timestamp z hz α MemoryTable.formRDefault).cfg.orbit.h :=
    rfl
  rw [hlen, horb, verifier_specializedProblem, derivedResponseIO_singleton]
  norm_num [cfg, executionOrbit]

/-- The production family at a coin and the fixture's sampled `λ = formRDefault` is the
seed-specialized concrete execution. -/
theorem verifier_familyAt_problem (ω : JointCoins K73cubic) (hz : nprSeed ω ≠ 0) :
    (verifier.familyAt ω MemoryTable.formRDefault hz).problem =
      ⟨cfg (nprSeed ω) (alphaM ω), exec (nprSeed ω) (alphaM ω)⟩ := by
  change
    (specializedProblem timestampStrategy (nprSeed ω) hz (alphaM ω) MemoryTable.formRDefault) =
      ⟨cfg (nprSeed ω) (alphaM ω), exec (nprSeed ω) (alphaM ω)⟩
  exact specializedProblem_eq (nprSeed ω) hz (alphaM ω)

/-- Every row of every sampled family carries the sampled `λ` (template specialization). -/
theorem concrete_verifier_memoryLambdaUniform :
    ∀ (ω : JointCoins K73cubic) (lmb : K73cubic) (hz : nprSeed ω ≠ 0) i,
      ((verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda =
        (verifier.familyAt ω lmb hz).cfg.challenges.lam :=
  fun ω lmb hz i => verifier.familyAt_memoryLambda ω lmb hz i

/-- Concrete inhabitant of the strict package.  The two Batch-29 fields use the package's
documented prover-named language factory; this constructs those fields but does not identify the
monolithic templates with the Nock language and therefore does not close R6/D1. -/
def concreteStrictPackage :
    StrictPackage.StrictNockVMROMPackage F73 K73cubic 2 73 2 where
  objects := objects
  verifier := verifier
  commitment := commitment
  claim_eq := rfl
  honestSeed := honestSeed
  honestSeed_ne := honestSeed_ne
  honestAlpha := honestAlpha
  honest_specialization :=
    verifier_specializedProblem honestSeed honestSeed_ne honestAlpha
  basis := basis73
  orbit := strictOrbit
  chalVal := chalVal
  pubVal := pubVal
  Hc := Hc
  Hm := Hm
  Hc_card := Hc_card
  Hm_card := Hm_card
  compRAP := compRAP
  memRAP := memRAP
  comp_is_named := rfl
  mem_is_named := rfl
  chained := honest_chained
  scan := fun z hz α lmb =>
    activeFingerprintChecksAt_of_bindsAt (bindsAt_specialized z hz α lmb)
  shapeMatch := fun z hz α lmb =>
    execTreeShapeMatchesAt_of_bindsAt (bindsAt_specialized z hz α lmb)
  rowFrame := fun z hz α lmb =>
    rowFrameChecksAt_of_bindsAt (bindsAt_specialized z hz α lmb)
  walkFamily := walkFamily
  walkFamily_problem := walkFamily_problem
  compEnc_inj := compEnc_inj
  memEnc_inj := memEnc_inj
  computeRowsAccepted := by
    change
      (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
        honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.ComputeRowsAccepted
    rw [specializedProblem_eq]
    exact honest_computeRowsAccepted
  memoryRowsAccepted := by
    change
      (TemplateRawJointSoundness.specializedProblem timestampStrategy honestSeed
        honestSeed_ne honestAlpha MemoryTable.formRDefault).exec.MemoryRowsAccepted
    rw [specializedProblem_eq]
    exact honest_memoryRowsAccepted
  topologyBinding := topologyBinding
  slotSemantics := slotSemantics
  recordEquations := recordEquations
  ioStrategy := ioStrategy
  io_requests := rfl
  io_responses := rfl
  compLanguage := compLanguage
  memLanguage := memLanguage
  compSemanticTemplate := compSemanticTemplate
  memSemanticTemplate := memSemanticTemplate
  recordCountBalance := recordCountBalance
  census := census
  sizeWindowBound := sizeWindowBound
  stateTagChar := stateTagChar
  q_gt_one := by norm_num
  q_eq_ringChar := q_eq_ringChar
  skeletonBounded := skeletonBounded
  combinedBounded := combinedBounded
  KszBound := KszBound
  progCapacity := progCapacity
  memCapacity := memCapacity

theorem honest_alphaFreeAxisStructureCheck :
    ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck
      (executionTemplate honestSeed) = true := by
  apply (ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck_eq_true_iff
    (executionTemplate honestSeed)).2
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp [Fin.cast_mk, Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, ProductionAxisStructureVerifier.alphaFreeRoot,
        TemplateAxisCounting.templateMemoryTreeAt, executionTemplate,
        dummyHaltTemplateTree, dummyHaltRowTemplate,
        TemplateAxisCounting.templateAxisTree, AxisBridge.ReadVerifyNested]
    · simp [Fin.cast_mk, Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, ProductionAxisStructureVerifier.alphaFreeRoot,
        TemplateAxisCounting.templateMemoryTreeAt, executionTemplate, readTemplateTree,
        decomposeTemplateTree, headTemplateTree, verifyTemplateTree,
        tailTemplateTree, readRowTemplate, decomposeRowTemplate, headRowTemplate,
        verifyRowTemplate, tailRowTemplate, TemplateAxisCounting.templateAxisTree,
        AxisBridge.ReadVerifyNested, AxisBatching.MTree.verifyCount]
  · intro i
    fin_cases i
    · simp [Fin.cast_mk, Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, ProductionAxisStructureVerifier.alphaFreeRoot,
        TemplateAxisCounting.templateMemoryTreeAt, executionTemplate,
        dummyHaltTemplateTree, dummyHaltRowTemplate,
        TemplateAxisCounting.templateAxisTree, AxisBridge.readExps]
    · simp [Fin.cast_mk, Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, ProductionAxisStructureVerifier.alphaFreeRoot,
        TemplateAxisCounting.templateMemoryTreeAt, executionTemplate, readTemplateTree,
        decomposeTemplateTree, headTemplateTree, verifyTemplateTree,
        tailTemplateTree, readRowTemplate, decomposeRowTemplate, headRowTemplate,
        verifyRowTemplate, tailRowTemplate, TemplateAxisCounting.templateAxisTree,
        AxisBridge.readExps]
  · simp [Fin.cast_mk, Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, TemplateAxisCounting.templateForestReadExps,
      TemplateAxisCounting.templateForestVerifyExps,
      TemplateAxisCounting.templateMemoryTreeAt, executionTemplate,
      dummyHaltTemplateTree, dummyHaltRowTemplate, readTemplateTree,
      decomposeTemplateTree, headTemplateTree, verifyTemplateTree,
      tailTemplateTree, readRowTemplate, decomposeRowTemplate, headRowTemplate,
      verifyRowTemplate, tailRowTemplate, TemplateAxisCounting.templateAxisTree,
      AxisBridge.readExps, AxisBridge.verifyExps, configTemplate, IO.LmIO_iff,
      IO.InRange, List.finRange, List.flatMap, List.get_cons_zero, List.get_cons_succ,
      Fin.cast, Fin.val_zero, Fin.val_one]

theorem honest_noWrapCheck :
    ProductionAxisStructureVerifier.noWrapCheck
      (executionTemplate honestSeed) honestAlpha = true := by
  apply (ProductionAxisStructureVerifier.noWrapCheck_eq_true_iff
    (executionTemplate honestSeed) honestAlpha).2
  intro i e he
  fin_cases i
  · simp [Fin.cast_mk, Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, ProductionAxisStructureVerifier.alphaFreeRoot,
      TemplateAxisCounting.templateMemoryTreeAt, executionTemplate,
      dummyHaltTemplateTree, dummyHaltRowTemplate,
      TemplateAxisCounting.templateAxisTree, AxisBridge.readExps] at he
  · simp [Fin.cast_mk, Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, ProductionAxisStructureVerifier.alphaFreeRoot,
      TemplateAxisCounting.templateMemoryTreeAt, executionTemplate, readTemplateTree,
      decomposeTemplateTree, headTemplateTree, verifyTemplateTree,
      tailTemplateTree, readRowTemplate, decomposeRowTemplate, headRowTemplate,
      verifyRowTemplate, tailRowTemplate, TemplateAxisCounting.templateAxisTree,
      AxisBridge.readExps] at he
    subst e
    rw [honestAlpha_order]
    norm_num

theorem honest_structuralChecks :
    ProductionAxisStructureVerifier.structuralChecksAt verifier
      honestSeed honestSeed_ne honestAlpha = true := by
  change
    (ProductionAxisStructureVerifier.alphaFreeAxisStructureCheck
        (executionTemplate honestSeed) &&
      ProductionAxisStructureVerifier.noWrapCheck
        (executionTemplate honestSeed) honestAlpha) = true
  simp [honest_alphaFreeAxisStructureCheck, honest_noWrapCheck]

theorem honest_rootAxisBoundary :
    concreteStrictPackage.strategy.RootAxisBoundaryAt
      honestSeed honestSeed_ne honestAlpha := by
  intro i
  have hct :
      ProductionAxisStructureVerifier.committedTemplate
        concreteStrictPackage.strategy.verifier honestSeed honestSeed_ne =
      executionTemplate honestSeed := rfl
  rw [hct]
  fin_cases i
  · simp [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, TemplateAxisCounting.templateMemoryTreeAt, executionTemplate,
      dummyHaltTemplateTree, dummyHaltRowTemplate,
      TemplateAxisCounting.templateAxisTree, AxisBatching.MTree.countsP_bin]
  · simp [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, TemplateAxisCounting.templateMemoryTreeAt, executionTemplate,
      readTemplateTree, decomposeTemplateTree, headTemplateTree, verifyTemplateTree,
      tailTemplateTree, readRowTemplate, decomposeRowTemplate, headRowTemplate,
      verifyRowTemplate, tailRowTemplate, TemplateAxisCounting.templateAxisTree,
      AxisBatching.MTree.countsP_bin, AxisBatching.MTree.indP_bin,
      verifyPubA, verifyPub, requestRecord]
    norm_num [honestAlpha]
    letI : CharP K73cubic 73 := concrete_char73
    have htwo : (2 : K73cubic) ≠ 0 := by
      exact SetEq.Lcast_ne_zero (p := 73) (by norm_num) (by norm_num)
    field_simp [htwo]
    ring

theorem production_accepts_honestCoins :
    concreteStrictPackage.strategy.Accepts honestCoins MemoryTable.formRDefault := by
  apply (concreteStrictPackage.strategy.accepts_iff honestCoins MemoryTable.formRDefault
    honestSeed_ne).2
  constructor
  · apply (ProductionAxisStructureVerifier.accepts_iff verifier honestCoins
      MemoryTable.formRDefault honestSeed_ne).2
    exact ⟨(verifier.accepts_iff_production honestCoins MemoryTable.formRDefault
      honestSeed_ne).1 verifier_accepts_honestCoins, honest_structuralChecks⟩
  · exact honest_rootAxisBoundary

theorem honestCoins_not_zeroSeedFailureEvent :
    honestCoins ∉
      (zeroSeedFailureEvent : Finset (JointCoins K73cubic)) := by
  rw [mem_zeroSeedFailureEvent_iff]
  change honestSeed ≠ 0
  exact honestSeed_ne

theorem honestCoins_not_collisionFailureEvent :
    honestCoins ∉ collisionFailureEvent concreteStrictPackage.census.census := by
  rw [mem_collisionFailureEvent_iff]
  rintro ⟨i, hi⟩
  apply hi
  have hmem :
      concreteStrictPackage.census.census.pair i ∈
        EdgeComparisonCensus.combinedSkeletonPairs K73cubic semanticSkeleton := by
    change
      (ComparisonCensus.ofPairList
        (EdgeComparisonCensus.combinedSkeletonPairs K73cubic semanticSkeleton) _).pair i ∈
          EdgeComparisonCensus.combinedSkeletonPairs K73cubic semanticSkeleton
    erw [ComparisonCensus.ofPairList_pair]
    exact List.get_mem _ _
  simp [EdgeComparisonCensus.combinedSkeletonPairs,
      BoundSemanticTrace.skeletonPairs, EdgeComparisonCensus.edgePairs,
      EdgeComparisonCensus.rowEdgePairs, P8Census.skeletonComparisonCensus,
      P8Census.skeletonComparisons, P8Census.skeletonUse, P8Census.skeletonDec,
      semanticSkeleton, computeSkeletonRow, NTree.childOpt,
      subjectNoun, formulaNoun, headNoun, resultNoun, requestSkeleton,
      SemanticStrategy.SemanticSkeleton.publicClaim,
      SemanticTrace.ComparisonUse.pair, decActive, computeSkeletonRows, bfsForest] at hmem
  rcases hmem with hmem | hmem | hmem | hmem | hmem | hmem <;> rw [hmem]
  all_goals
    change GlobalCarryRecognizer.SepSeed honestSeed _ _
  all_goals
    simp [GlobalCarryRecognizer.SepSeed]

theorem honestCoins_not_sizeWindowFailure :
    honestCoins ∉ SizeWindowCounting.SizeWindowFailure semanticSkeleton := by
  rw [SizeWindowCounting.mem_SizeWindowFailure_iff]
  simp [honestCoins, SizeWindowCounting.skeletonSizeWindowNouns,
    SizeWindowCounting.requiredSizeWindowNouns, semanticSkeleton,
    computeSkeletonRows, computeSkeletonRow, bfsForest]

theorem honestCoins_not_specializedTopologyFailureEvent :
    honestCoins ∉
      specializedTopologyFailureEvent concreteStrictPackage.verifier.raw
        MemoryTable.formRDefault := by
  rw [mem_specializedTopologyFailureEvent_iff]
  rintro ⟨hz, hbad⟩
  change honestGamma ∈ topologyBadGammas walkFamily at hbad
  have hcomputeTree :
      walkFamily.exec.computeTree = (exec honestSeed honestAlpha).computeTree :=
    congrArg (fun P : RawProblem F73 K73cubic => P.exec.computeTree)
      walkFamily_problem
  have hmemoryForest :
      walkFamily.exec.memoryForest = (exec honestSeed honestAlpha).memoryForest :=
    congrArg (fun P : RawProblem F73 K73cubic => P.exec.memoryForest)
      walkFamily_problem
  rw [topologyBadGammas, computeTopologyBadGammas, memoryTopologyBadGammas,
    RawPlusIOSegmentedFamily.computeWalkRows,
    RawPlusIOSegmentedFamily.memoryWalkRows, hcomputeTree] at hbad
  simp only [hmemoryForest] at hbad
  simp [honestGamma,
    computeTopologyBadGammas, memoryTopologyBadGammas,
    computeSlotBadGammas, memorySlotBadGammas,
    computeActualPayload, computeExpectedPayload,
    memoryActualPayload, memoryExpectedPayload,
    exec, dummyHaltTree, dummyHaltRow, dummyHaltPub, readTree, decomposeTree, headTree,
      verifyTree, tailTree, bfsForest,
    computeRow, readRow, decomposeRow, headRow, verifyRow, tailRow,
    computePub, readPub, decomposePub, headPub, verifyPub, tailPub,
    ComputeTable.fanoutComp, MemoryTable.fanoutMem,
    ComputeTable.sfTriple, MemoryTable.memCell, NTree.childLabel, NTree.childOpt] at hbad
  obtain ⟨a, ha, hbad⟩ := hbad
  interval_cases a <;>
    simp [memorySlotBadGammas, memoryActualPayload, memoryExpectedPayload,
      MemoryTable.fanoutMem, MemoryTable.memCell, NTree.childLabel, NTree.childOpt,
      dummyHaltRow, dummyHaltPub, readRow, decomposeRow, headRow, verifyRow, tailRow,
      readPub, decomposePub, headPub, verifyPub, tailPub] at hbad

theorem honestCoins_not_guardedAxisFailureEvent :
    honestCoins ∉
      ProductionP8Containment.guardedAxisFailureEvent concreteStrictPackage.strategy
        MemoryTable.formRDefault := by
  rw [ProductionP8Containment.mem_guardedAxisFailureEvent_iff]
  rintro ⟨hz, hbad⟩
  have hct :
      ProductionAxisStructureVerifier.committedTemplate
        concreteStrictPackage.strategy.verifier (nprSeed honestCoins) hz =
      executionTemplate honestSeed := rfl
  rw [hct] at hbad
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hbad
  have hparts := (Finset.mem_filter.mp hi).2
  have hk : (configTemplate honestSeed).kMem = 2 := rfl
  fin_cases i
  · have hnz := hparts.2.2.2.1
    simp [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, TemplateAxisCounting.templateAxisPolynomial,
      TemplateAxisCounting.templateMemoryTreeAt, executionTemplate,
      dummyHaltTemplateTree, dummyHaltRowTemplate,
      TemplateAxisCounting.templateAxisTree, AxisBatching.MTree.countsP_bin] at hnz
  · -- Provisional: the guarded event now prices `countsP_bin` (the polynomial
    -- `RootAxisBoundaryAt` checks); the honest a-bearing root polynomial is identically zero
    -- (`(x - 3)/2 · X` at `x = 3`), so the `≠ 0` conjunct fails.
    apply hparts.2.2.2.1
    simp [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, TemplateAxisCounting.templateAxisPolynomial,
      TemplateAxisCounting.templateMemoryTreeAt, executionTemplate,
      readTemplateTree, decomposeTemplateTree, headTemplateTree, verifyTemplateTree,
      tailTemplateTree, readRowTemplate, decomposeRowTemplate, headRowTemplate,
      verifyRowTemplate, tailRowTemplate, TemplateAxisCounting.templateAxisTree,
      AxisBatching.MTree.countsP_bin, AxisBatching.MTree.indP_bin,
      verifyPubA, verifyPub, requestRecord]
    letI : CharP K73cubic 73 := concrete_char73
    have htwo : (2 : K73cubic) ≠ 0 := by
      exact SetEq.Lcast_ne_zero (p := 73) (by norm_num) (by norm_num)
    have h3 : (Polynomial.C (3 : K73cubic)) = Polynomial.C 2 + 1 := by
      rw [← map_one Polynomial.C, ← map_add]; norm_num
    rw [h3, show (Polynomial.C (2 : K73cubic) + 1) * Polynomial.X - Polynomial.X =
        Polynomial.C 2 * Polynomial.X by ring, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ htwo, map_one, one_mul, sub_self]

theorem honestCoins_not_failureUnion :
    honestCoins ∉ ProductionP8Containment.FailureUnion
      concreteStrictPackage.strategy concreteStrictPackage.census MemoryTable.formRDefault := by
  intro hbad
  simp only [ProductionP8Containment.FailureUnion, Finset.mem_union] at hbad
  rcases hbad with hbad | hbad
  · rcases hbad with hbad | hbad
    · rcases hbad with hbad | hbad
      · rcases hbad with hbad | hbad
        · exact honestCoins_not_zeroSeedFailureEvent hbad
        · exact honestCoins_not_collisionFailureEvent hbad
      · exact honestCoins_not_specializedTopologyFailureEvent hbad
    · exact honestCoins_not_guardedAxisFailureEvent hbad
  · exact honestCoins_not_sizeWindowFailure hbad

theorem honest_genuineTarget :
    ProductionP8Containment.GenuineTargetAt
      concreteStrictPackage.strategy 73 2 honestCoins MemoryTable.formRDefault :=
  concreteStrictPackage.containment honestCoins MemoryTable.formRDefault
    production_accepts_honestCoins honestCoins_not_failureUnion

theorem containment_antecedents_jointly_satisfiable :
    ∃ ω : JointCoins K73cubic,
      concreteStrictPackage.strategy.Accepts ω MemoryTable.formRDefault ∧
        ω ∉ ProductionP8Containment.FailureUnion
          concreteStrictPackage.strategy concreteStrictPackage.census MemoryTable.formRDefault :=
  ⟨honestCoins, production_accepts_honestCoins, honestCoins_not_failureUnion⟩

/-- The acceptance premise of the package's pointwise containment implication is inhabited.
The outside-failure premise remains a separate hypothesis of the containment theorem. -/
theorem containment_acceptance_antecedent_satisfiable :
    concreteStrictPackage.strategy.Accepts honestCoins MemoryTable.formRDefault ∧
      (concreteStrictPackage.strategy.Accepts honestCoins MemoryTable.formRDefault →
        honestCoins ∉ ProductionP8Containment.FailureUnion
          concreteStrictPackage.strategy concreteStrictPackage.census MemoryTable.formRDefault →
        ProductionP8Containment.GenuineTargetAt
          concreteStrictPackage.strategy 73 2 honestCoins MemoryTable.formRDefault) := by
  exact ⟨production_accepts_honestCoins,
    concreteStrictPackage.containment honestCoins MemoryTable.formRDefault⟩

theorem concreteStrictPackage_nonempty :
    Nonempty (StrictPackage.StrictNockVMROMPackage F73 K73cubic 2 73 2) :=
  ⟨concreteStrictPackage⟩

def strictNockVMROM_of_concretePackage :
    StrictPackage.StrictThm54Statement concreteStrictPackage :=
  StrictPackage.strictNockVMROM_of_package concreteStrictPackage

#print axioms omega10_order
#print axioms op1_bound_request_ne_zero
#print axioms honest_execution_nonempty
#print axioms concreteStrictPackage
#print axioms rawStrategy_accepts_honestCoins
#print axioms verifier_accepts_honestCoins
#print axioms production_accepts_honestCoins
#print axioms honestCoins_not_failureUnion
#print axioms honest_genuineTarget
#print axioms containment_antecedents_jointly_satisfiable
#print axioms containment_acceptance_antecedent_satisfiable
#print axioms concreteStrictPackage_nonempty
#print axioms strictNockVMROM_of_concretePackage

end

end Nock.NockVMROM.Thm54.ConcreteStrictPackage
