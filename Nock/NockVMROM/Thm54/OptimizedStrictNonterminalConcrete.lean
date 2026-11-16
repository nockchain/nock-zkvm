import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.OptimizedComputeCollisionConcrete
import Nock.RedTeam.Thm54P2Nonvacuity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# Strict two-row nonterminal optimized-compute fixture

`SampledIOSameExecutionAssignment` stores a `FiniteIOStrategy`, whose committed request list is
required to be `Nodup`.  Therefore the duplicated request list of
`Thm54P2Nonvacuity.execDup` cannot be handled by that type's multiplicity witness.  This is a
compiled P2-specific statement-shape obstruction, not a general obstruction.

The second half of this module supplies the strict-release witness that P2 cannot: an accepted
OP4 parent and accepted OP1 child over `F97/K97cubic`, with distinct requests, a matching accepted
nine-row memory tree, one exact sampled same-execution assignment, and the corrected canonical
199/98 trace.  The larger characteristic is deliberate: `K73cubic` has only an order-eight
2-primary orbit, while the honest nested two-lookup memory tree has nine rows.  `K97cubic` has an
order-sixteen execution orbit and `F97` has the order-twelve orbit required by the cubic coordinate
compiler.
-/

namespace Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete

open Nock
open scoped Classical Polynomial

theorem sampled_assignment_requests_nodup
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {p : ℕ} [CharP K p] {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p) :
    R.problem.exec.derivedRequestIO.Nodup := by
  rw [← A.requests_eq]
  exact A.sampled.uniqueRequest

/-- No sampled same-execution assignment can represent two copies of the same request. -/
theorem no_sampled_assignment_with_duplicate_request
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {p : ℕ} [CharP K p] {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p) (v : Fin 9 → K)
    (hdup : R.problem.exec.derivedRequestIO = [v, v]) : False := by
  have hnd := sampled_assignment_requests_nodup A
  rw [hdup] at hnd
  simpa using hnd

/-- In particular, P2's exact duplicated request list cannot be the request side of the mandatory
`SampledIOSameExecutionAssignment`.  Its symbolic `SemanticExactLanguage` theorem remains valid;
the obstruction is specifically the finite sampled wrapper's `Nodup` field. -/
theorem p2_duplicate_request_not_finite_sampleable :
    ¬ ∃ (R : PlusIOSegmentedFamily
          Nock.RedTeam.Thm54P2Nonvacuity.K17
          Nock.RedTeam.Thm54P2Nonvacuity.K17)
        (A : SampledIOSameExecutionAssignment R 17),
      R.problem.exec.derivedRequestIO =
        Nock.RedTeam.Thm54P2Nonvacuity.execDup.derivedRequestIO := by
  rintro ⟨R, A, hreq⟩
  apply no_sampled_assignment_with_duplicate_request A
    (NockVM.encRecC
      Nock.RedTeam.Thm54P2Nonvacuity.rowRecord Nock.RedTeam.Thm54P2Nonvacuity.rowC)
  rw [hreq, Nock.RedTeam.Thm54P2Nonvacuity.derivedRequestIO_duplicate]

/-! ## Genuine cubic fields and orbits -/

noncomputable section

open Nock.Framework Nock.Framework.Thm54 Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.Reified
open Module
open CoordinateBasis
open StrictExtension
open OptimizedComputeCanonicalSatisfaction
open OptimizedComputeCollisionBound
open OptimizedComputeCorrectedFinal
open OptimizedComputeFinalTrace
open OptimizedComputeGateBasis
open OptimizedComputeSameExecution
open OptimizedComputeSemanticRealization
open OptimizedComputeSampledTrace
open OptimizedStrictPackage

abbrev F97 := ZMod 97

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
abbrev K97cubic := GaloisField 97 3
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance char97 : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

def basis97 : Basis (Fin 3) F97 K97cubic :=
  stdCoordBasis F97 K97cubic 3
    (GaloisField.finrank 97 (by norm_num))

/-- `2` in `𝔽₉₇` has order `48`; the cubic embedding preserves it. Used to discharge
`computeWalkOrder` on the two- and three-row F97 fixtures (`2 ≤` / `3 ≤`). -/
theorem omega2_order : orderOf (2 : K97cubic) = 48 := by
  have hbase : orderOf (2 : F97) = 48 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide
  have hcast : (2 : K97cubic) = algebraMap F97 K97cubic (2 : F97) :=
    (map_natCast (algebraMap F97 K97cubic) 2).symm
  rw [hcast]
  change orderOf ((algebraMap F97 K97cubic).toMonoidHom (2 : F97)) = 48
  exact (orderOf_injective (algebraMap F97 K97cubic).toMonoidHom
    (algebraMap F97 K97cubic).injective (2 : F97)).trans hbase


theorem omega3_order : orderOf (3 : K97cubic) = 48 := by
  have hbase : orderOf (3 : F97) = 48 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide
  have hcast : (3 : K97cubic) = algebraMap F97 K97cubic (3 : F97) :=
    (map_natCast (algebraMap F97 K97cubic) 3).symm
  rw [hcast]
  change orderOf ((algebraMap F97 K97cubic).toMonoidHom (3 : F97)) = 48
  exact (orderOf_injective (algebraMap F97 K97cubic).toMonoidHom
    (algebraMap F97 K97cubic).injective (3 : F97)).trans hbase

theorem omega2_order_ge : 3 ≤ orderOf (2 : K97cubic) := by
  rw [omega2_order]
  norm_num

theorem omega8_order : orderOf (8 : K97cubic) = 16 := by
  have hbase : orderOf (8 : F97) = 16 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide
  have hcast : (8 : K97cubic) = algebraMap F97 K97cubic (8 : F97) :=
    (map_natCast (algebraMap F97 K97cubic) 8).symm
  rw [hcast]
  change orderOf ((algebraMap F97 K97cubic).toMonoidHom (8 : F97)) = 16
  exact (orderOf_injective (algebraMap F97 K97cubic).toMonoidHom
    (algebraMap F97 K97cubic).injective (8 : F97)).trans hbase

def executionOrbit97 : OrbitDomain K97cubic where
  h := 4
  ω := 8
  βcoset := 1
  βcoset_ne_zero := by norm_num
  order_ω := by simpa using omega8_order

def strictOrbit97 : StrictOrbitDomain F97 3 2 where
  ω := 6
  βcoset := 1
  e_pos := by norm_num
  h_pos := by norm_num
  βcoset_ne_zero := by norm_num
  order_ω := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide

def fixtureSeed : K97cubic := 1
def fixtureAlpha : K97cubic := 4

theorem fixtureSeed_ne : fixtureSeed ≠ 0 := by norm_num [fixtureSeed]

def fixtureFP (n : Noun) : FP K97cubic :=
  GlobalCarryRecognizer.enc fixtureSeed n

/-! ## OP4 parent and OP1 child -/

def subject : Noun := .atom 0
def incrementInput : Noun := .atom 4
def incrementResult : Noun := .atom 5
def childHead : Noun := .atom 1
def parentHead : Noun := .atom 4
def childFormula : Noun := .cell childHead incrementInput
def parentFormula : Noun := .cell parentHead childFormula

def parentRequest : MemRec K97cubic where
  root := fixtureFP parentFormula
  child := fixtureFP childFormula
  axis := 3
  ts := fixtureAlpha

def childRequest : MemRec K97cubic where
  root := fixtureFP childFormula
  child := fixtureFP incrementInput
  axis := 3
  ts := fixtureAlpha ^ 2

def computeInputs97 : ComputeTable.Inputs K97cubic where
  α := fixtureAlpha
  z := fixtureSeed
  a := 0
  b := 0
  c := 0

def parentDec : ComputeTable.Dec K97cubic where
  f_h := fixtureFP parentHead
  f_t := fixtureFP childFormula
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

def childDec : ComputeTable.Dec K97cubic where
  f_h := fixtureFP childHead
  f_t := fixtureFP incrementInput
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

def parentPub : ComputeTable.Pub K97cubic where
  state := .s4
  s := fixtureFP subject
  f := fixtureFP parentFormula
  e := fixtureFP incrementResult
  sf1_s := fixtureFP subject
  sf1_f := fixtureFP childFormula
  sf1_e := fixtureFP incrementInput
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := 1
  ln := fixtureAlpha
  mr1 := parentRequest
  mr2 := MemRec.zero
  mr3 := MemRec.zero

def childPub : ComputeTable.Pub K97cubic where
  state := .s1
  s := fixtureFP subject
  f := fixtureFP childFormula
  e := fixtureFP incrementInput
  sf1_s := 0
  sf1_f := 0
  sf1_e := 0
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := fixtureAlpha
  ln := fixtureAlpha ^ 2
  mr1 := childRequest
  mr2 := MemRec.zero
  mr3 := MemRec.zero

def parentLabel : State × ComputeTable.DTcomp K97cubic :=
  (.s4, (computeInputs97, parentPub, parentDec))

def childLabel : State × ComputeTable.DTcomp K97cubic :=
  (.s1, (computeInputs97, childPub, childDec))

theorem parent_accepts : Vcomp computeInputs97 parentPub parentDec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons fixtureSeed_ne parentHead childFormula
  · ext <;>
      norm_num [parentPub, parentRequest, parentDec, computeInputs97, fixtureFP,
        fixtureSeed, fixtureAlpha]
  · simp [SVhead, headAtom, parentPub, parentDec, computeInputs97, fixtureFP,
      parentHead, GlobalCarryRecognizer.enc_atom, State.toNat, fixtureSeed, fixtureAlpha]
  · norm_num [memBlk, parentPub, computeInputs97, MemRec.zero, fixtureAlpha]
  · simp [evalV, parentPub, parentDec, computeInputs97, sfz2, sfz3, fixtureFP,
      incrementInput, incrementResult, GlobalCarryRecognizer.enc_atom, FP.inc, FP.atomFP,
      fixtureSeed] <;> norm_num

theorem child_accepts : Vcomp computeInputs97 childPub childDec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalCarryRecognizer.enc_cons fixtureSeed_ne childHead incrementInput
  · ext <;>
      norm_num [childPub, childRequest, childDec, computeInputs97, fixtureFP,
        fixtureSeed, fixtureAlpha]
  · simp [SVhead, headAtom, childPub, childDec, computeInputs97, fixtureFP,
      childHead, GlobalCarryRecognizer.enc_atom, State.toNat, fixtureSeed, fixtureAlpha]
  · norm_num [memBlk, childPub, computeInputs97, MemRec.zero, fixtureAlpha]
  · simp [evalV, childPub, childDec, computeInputs97, sfz1, sfz2, sfz3]

theorem parent_wf : ComputeTable.WF computeInputs97 parentPub where
  rlc5 := by simp [parentPub]
  size8 := by simp [parentPub]
  size11 := by simp [parentPub]

theorem child_wf : ComputeTable.WF computeInputs97 childPub where
  rlc5 := by simp [childPub]
  size8 := by simp [childPub]
  size11 := by simp [childPub]

def parentOut : Fin 3 → Option (State × ComputeTable.DTcomp K97cubic)
  | 0 => some childLabel
  | 1 => none
  | 2 => none

theorem parentLabel_accepts : ComputeTable.Fcomp parentLabel parentOut := by
  refine ⟨rfl, parent_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [parentLabel, parentOut, ComputeTable.fanoutComp]
  · intro i hi
    fin_cases i
    · simp [parentOut, ComputeTable.childLinkComp, ComputeTable.sfTriple,
        parentLabel, childLabel, parentPub, childPub]
    · simp [parentLabel, ComputeTable.fanoutComp] at hi
    · simp [parentLabel, ComputeTable.fanoutComp] at hi

theorem childLabel_accepts :
    ComputeTable.Fcomp childLabel (fun _ => none) := by
  refine ⟨rfl, child_accepts, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [childLabel, ComputeTable.fanoutComp]
  · intro i hi
    simp [childLabel, ComputeTable.fanoutComp] at hi

def computeTree : NTree (State × ComputeTable.DTcomp K97cubic) :=
  .node parentLabel [.node childLabel []]

theorem computeTree_rvt : RVT (ComputeTable.Fcomp (K := K97cubic)) computeTree := by
  unfold computeTree RVT
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun i : Fin 3 => (NTree.node parentLabel [.node childLabel []]).childLabel i) =
        parentOut by
      funext i
      fin_cases i <;> rfl]
    exact parentLabel_accepts
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    unfold RVT
    exact ⟨childLabel_accepts, by simp, ⟨fun _ => childLabel_accepts, fun _ => rfl⟩⟩
  · simp [NTree.isLeaf, ComputeTable.Fcomp, parentLabel, ComputeTable.fanoutComp]

theorem parent_is_genuinely_nonterminal :
    parentPub.state = .s4 ∧ ComputeTable.fanoutComp parentPub.state = 1 ∧
      parentOut 0 = some childLabel :=
  ⟨rfl, rfl, rfl⟩

theorem compute_line_handoff : parentPub.ln = childPub.ln_prev := rfl

/-! ## Matching accepted nine-row memory tree -/

def memoryInputs97 : MemoryTable.Inputs K97cubic := ⟨fixtureSeed, 0, 0⟩

/-- Form R row-level cells at the package `λ = formRDefault` (`MemoryTable.eqBlk`): `verify_child` adds `λ^{n−1}·ts` to both
columns; `read_root` subtracts `λ^{n−1}·T·ts` / `T·C'·ts` with `(T, C')` of the record's Nock axis;
`decompose` is `λ(I_L+I_R)` / `C_L+C_R+(λ−1)(I_L+I_R)+I_R`.  Each cell is written from its
children. -/
def rowVerifyCell {K : Type} [Field K] (noun : FP K) (lc : Cell K) (ts : K) : Cell K :=
  ⟨noun, lc.indicator + MemoryTable.formRDefault ^ MemoryTable.pwScaleExp K * ts,
    lc.counts + MemoryTable.formRDefault ^ MemoryTable.pwScaleExp K * ts⟩

def rowDecCell {K : Type} [Field K] (noun : FP K) (lc rc : Cell K) : Cell K :=
  ⟨noun, MemoryTable.formRDefault * (lc.indicator + rc.indicator),
    lc.counts + rc.counts + (MemoryTable.formRDefault - 1) * (lc.indicator + rc.indicator)
      + rc.indicator⟩

def rowReadCell {K : Type} [Field K] (noun : FP K) (lc : Cell K) (r : MemRec K) : Cell K :=
  ⟨noun, lc.indicator - MemoryTable.formRDefault ^ MemoryTable.pwScaleExp K *
      MemoryTable.formRT MemoryTable.formRDefault (MemoryTable.nockAxisOf r.axis) * r.ts,
    lc.counts - MemoryTable.formRT MemoryTable.formRDefault (MemoryTable.nockAxisOf r.axis) *
      MemoryTable.formRC MemoryTable.formRDefault (MemoryTable.nockAxisOf r.axis) * r.ts⟩

def tailCell : Cell K97cubic := ⟨fixtureFP incrementInput, 0, 0⟩
def secondVerifyCell : Cell K97cubic :=
  rowVerifyCell (fixtureFP incrementInput) tailCell childRequest.ts
def childHeadCell : Cell K97cubic := ⟨fixtureFP childHead, 0, 0⟩
def childDecomposeCell : Cell K97cubic :=
  rowDecCell (fixtureFP childFormula) childHeadCell secondVerifyCell
def firstVerifyCell : Cell K97cubic :=
  rowVerifyCell (fixtureFP childFormula) childDecomposeCell parentRequest.ts
def childReadCell : Cell K97cubic :=
  rowReadCell (fixtureFP childFormula) firstVerifyCell childRequest
def parentHeadCell : Cell K97cubic := ⟨fixtureFP parentHead, 0, 0⟩
def parentDecomposeCell : Cell K97cubic :=
  rowDecCell (fixtureFP parentFormula) parentHeadCell childReadCell
def parentReadCell : Cell K97cubic :=
  rowReadCell (fixtureFP parentFormula) parentDecomposeCell parentRequest

def dummyHaltCell : Cell K97cubic := ⟨fixtureFP (.atom 0), 0, 0⟩

def readParentPub : MemoryTable.Pub K97cubic where
  st := .read_root
  pt := parentReadCell
  lc := parentDecomposeCell
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := NockVM.formRRow parentRequest MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime parentRequest MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 1

def decomposeParentPub : MemoryTable.Pub K97cubic where
  st := .decompose
  pt := parentDecomposeCell
  lc := parentHeadCell
  rc := childReadCell
  lcSt := .halt
  rcSt := .read_root
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def parentHeadHaltPub : MemoryTable.Pub K97cubic where
  st := .halt
  pt := parentHeadCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def readChildPub : MemoryTable.Pub K97cubic where
  st := .read_root
  pt := childReadCell
  lc := firstVerifyCell
  rc := Cell.zero
  lcSt := .read_root
  rcSt := .halt
  mem := NockVM.formRRow childRequest MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime childRequest MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 2

def verifyParentPub : MemoryTable.Pub K97cubic where
  st := .verify_child
  pt := firstVerifyCell
  lc := childDecomposeCell
  rc := Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := NockVM.formRRow parentRequest MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime parentRequest MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := 2
  icur := 1

def decomposeChildPub : MemoryTable.Pub K97cubic where
  st := .decompose
  pt := childDecomposeCell
  lc := childHeadCell
  rc := secondVerifyCell
  lcSt := .halt
  rcSt := .verify_child
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def childHeadHaltPub : MemoryTable.Pub K97cubic where
  st := .halt
  pt := childHeadCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 1

def verifyChildPub : MemoryTable.Pub K97cubic where
  st := .verify_child
  pt := secondVerifyCell
  lc := tailCell
  rc := Cell.zero
  lcSt := .verify_child
  rcSt := .halt
  mem := NockVM.formRRow childRequest MemoryTable.formRDefault
  cprime? := some (NockVM.formRCprime childRequest MemoryTable.formRDefault)
  lambda? := some MemoryTable.formRDefault
  ipre := 1
  icur := 0

def tailHaltPub : MemoryTable.Pub K97cubic where
  st := .halt
  pt := tailCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

/-! The a-bearing view of the four active rows;
their Form R row encode (`MemoryRowTemplate.encodeRow`) is the executed row. -/

@[simp] def readParentPubA : MemoryTable.Pub K97cubic :=
  { readParentPub with mem := parentRequest, cprime? := none }
@[simp] def readChildPubA : MemoryTable.Pub K97cubic :=
  { readChildPub with mem := childRequest, cprime? := none }
@[simp] def verifyParentPubA : MemoryTable.Pub K97cubic :=
  { verifyParentPub with mem := parentRequest, cprime? := none }
@[simp] def verifyChildPubA : MemoryTable.Pub K97cubic :=
  { verifyChildPub with mem := childRequest, cprime? := none }

def memoryLabel (st : MState) (pub : MemoryTable.Pub K97cubic) :
    MState × MemoryTable.DTmem K97cubic :=
  (st, (memoryInputs97, pub))

abbrev readParentLabel := memoryLabel .read_root readParentPub
abbrev decomposeParentLabel := memoryLabel .decompose decomposeParentPub
abbrev parentHeadHaltLabel := memoryLabel .halt parentHeadHaltPub
abbrev readChildLabel := memoryLabel .read_root readChildPub
abbrev verifyParentLabel := memoryLabel .verify_child verifyParentPub
abbrev decomposeChildLabel := memoryLabel .decompose decomposeChildPub
abbrev childHeadHaltLabel := memoryLabel .halt childHeadHaltPub
abbrev verifyChildLabel := memoryLabel .verify_child verifyChildPub
abbrev tailHaltLabel := memoryLabel .halt tailHaltPub

def dummyHaltPub : MemoryTable.Pub K97cubic where
  st := .halt
  pt := dummyHaltCell
  lc := Cell.zero
  rc := Cell.zero
  lcSt := .halt
  rcSt := .halt
  mem := MemRec.zero
  lambda? := some MemoryTable.formRDefault
  ipre := 0
  icur := 0

abbrev dummyHaltLabel := memoryLabel .halt dummyHaltPub

/-- With `β = γ = 0` the pole reads only the root, which the Form R row encode keeps. -/
@[simp] theorem pole_row97 (r : MemRec K97cubic) :
    pole memoryInputs97 (NockVM.formRRow r MemoryTable.formRDefault)
      (NockVM.formRCprime r MemoryTable.formRDefault) = pole memoryInputs97 r 1 := by
  simp [pole, recRLC, memoryInputs97, NockVM.formRRow]

theorem parent_pole : pole memoryInputs97 parentRequest 1 = 1 := by
  norm_num [pole, recRLC, memoryInputs97, parentRequest, fixtureFP, fixtureSeed,
    parentFormula, parentHead, childFormula, childHead, incrementInput,
    GlobalCarryRecognizer.enc_atom, GlobalCarryRecognizer.enc_cons fixtureSeed_ne]

theorem child_pole : pole memoryInputs97 childRequest 1 = 1 := by
  norm_num [pole, recRLC, memoryInputs97, childRequest, fixtureFP, fixtureSeed,
    childFormula, childHead, incrementInput,
    GlobalCarryRecognizer.enc_atom, GlobalCarryRecognizer.enc_cons fixtureSeed_ne]

theorem readParent_accepts : Vmem memoryInputs97 readParentPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, readParentPub]
    repeat' constructor
  · simpa [interV, readParentPub, Pub.cprime] using parent_pole

theorem decomposeParent_accepts : Vmem memoryInputs97 decomposeParentPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, rfl, rfl, rfl⟩
    exact GlobalCarryRecognizer.enc_cons fixtureSeed_ne parentHead childFormula
  · rfl

theorem parentHeadHalt_accepts : Vmem memoryInputs97 parentHeadHaltPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · norm_num [eqBlk, parentHeadHaltPub, parentHeadCell, memoryInputs97, fixtureFP,
      fixtureSeed, parentHead, GlobalCarryRecognizer.enc_atom, Cell.zero, MemRec.zero]
  · rfl

theorem readChild_accepts : Vmem memoryInputs97 readChildPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, readChildPub]
    repeat' constructor
  · simpa [interV, readChildPub, Pub.cprime, child_pole] using
      (show (2 - 1 : K97cubic) = (1 : K97cubic)⁻¹ by norm_num)

theorem verifyParent_accepts : Vmem memoryInputs97 verifyParentPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, verifyParentPub]
    repeat' constructor
  · simpa [interV, verifyParentPub, Pub.cprime, parent_pole] using
      (show (2 - 1 : K97cubic) = (1 : K97cubic)⁻¹ by norm_num)

theorem decomposeChild_accepts : Vmem memoryInputs97 decomposeChildPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · refine ⟨?_, rfl, rfl, rfl⟩
    exact GlobalCarryRecognizer.enc_cons fixtureSeed_ne childHead incrementInput
  · rfl

theorem childHeadHalt_accepts : Vmem memoryInputs97 childHeadHaltPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · norm_num [eqBlk, childHeadHaltPub, childHeadCell, memoryInputs97, fixtureFP,
      fixtureSeed, childHead, GlobalCarryRecognizer.enc_atom, Cell.zero, MemRec.zero]
  · rfl

theorem verifyChild_accepts : Vmem memoryInputs97 verifyChildPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · simp only [eqBlk, verifyChildPub]
    repeat' constructor
  · simpa [interV, verifyChildPub, Pub.cprime, child_pole] using
      (show (1 - 0 : K97cubic) = (1 : K97cubic)⁻¹ by norm_num)

theorem dummyHalt_accepts : Vmem memoryInputs97 dummyHaltPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · norm_num [eqBlk, dummyHaltPub, dummyHaltCell, memoryInputs97, fixtureFP,
      fixtureSeed, GlobalCarryRecognizer.enc_atom, Cell.zero, MemRec.zero]
  · rfl

theorem tailHalt_accepts : Vmem memoryInputs97 tailHaltPub := by
  refine ⟨MemoryTable.verBool_holds _, ?_, ?_⟩
  · norm_num [eqBlk, tailHaltPub, tailCell, memoryInputs97, fixtureFP,
      fixtureSeed, incrementInput, GlobalCarryRecognizer.enc_atom, Cell.zero, MemRec.zero]
  · rfl

def tailTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node tailHaltLabel []
def verifyChildTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node verifyChildLabel [tailTree]
def childHeadTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node childHeadHaltLabel []
def decomposeChildTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node decomposeChildLabel [childHeadTree, verifyChildTree]
def verifyParentTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node verifyParentLabel [decomposeChildTree]
def readChildTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node readChildLabel [verifyParentTree]
def parentHeadTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node parentHeadHaltLabel []
def decomposeParentTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node decomposeParentLabel [parentHeadTree, readChildTree]
def memoryTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node readParentLabel [decomposeParentTree]
def dummyHaltTree : NTree (MState × MemoryTable.DTmem K97cubic) :=
  .node dummyHaltLabel []

/-! ## One exact same-execution problem -/

def cfg97 : ExactConfig F97 K97cubic where
  challenges :=
    { a := 0
      b := 0
      c := 0
      lam := MemoryTable.formRDefault
      α := fixtureAlpha
      z := fixtureSeed
      β := 0
      γ := 0 }
  Ksz := 4
  kMem := 2
  orbit := executionOrbit97
  orbit_h_pos := by norm_num [executionOrbit97]
  compRows := 2
  memRows := 10
  compRows_pos := by norm_num
  memRows_pos := by norm_num
  compRows_le := by norm_num [executionOrbit97]
  memRows_le := by norm_num [executionOrbit97]
  eDeg := 1
  eDeg_eq_one := rfl
  compNodes := fun i => executionOrbit97.orbitPoint i
  compNodes_spec := by intro i; rfl
  memNodes := fun i => executionOrbit97.orbitPoint i
  memNodes_spec := by intro i; rfl

/-- The fixture's configured `λ` is `formRDefault`. -/
@[simp] theorem cfg97_lam : cfg97.challenges.lam = MemoryTable.formRDefault := rfl

def exec97 : ExactExecution cfg97 where
  computeTree := computeTree
  memoryForest := [dummyHaltTree, memoryTree]
  memoryForest_nonempty := by simp
  memory_root_count := rfl
  compute_bfs_length := by
    norm_num [computeTree, bfsForest, NTree.size, totalSize, cfg97]
  memory_bfs_length := by
    norm_num [dummyHaltTree, memoryTree, decomposeParentTree, parentHeadTree, readChildTree,
      verifyParentTree, decomposeChildTree, childHeadTree, verifyChildTree, tailTree,
      bfsForest, NTree.size, totalSize, cfg97]

theorem execution_rows :
    exec97.computeRows = [parentLabel, childLabel] ∧
      exec97.memoryRows =
        [dummyHaltLabel, readParentLabel, decomposeParentLabel, parentHeadHaltLabel,
          readChildLabel, verifyParentLabel, decomposeChildLabel, childHeadHaltLabel,
          verifyChildLabel, tailHaltLabel] := by
  constructor <;>
    norm_num [ExactExecution.computeRows, ExactExecution.memoryRows, exec97, computeTree,
      dummyHaltTree, memoryTree, decomposeParentTree, parentHeadTree, readChildTree,
      verifyParentTree, decomposeChildTree, childHeadTree, verifyChildTree, tailTree,
      bfsForest, NTree.size, totalSize]

theorem derived_requests :
    exec97.derivedRequestIO = [NockVM.encRecFormR parentRequest MemoryTable.formRDefault,
      NockVM.encRecFormR childRequest MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedRequestIO_eq_computeRows, execution_rows.1]
  simp [NockVM.activeRequestRecords, parentLabel, childLabel, parentPub, childPub]

theorem derived_responses :
    exec97.derivedResponseIO = [NockVM.encRecFormR parentRequest MemoryTable.formRDefault,
      NockVM.encRecFormR childRequest MemoryTable.formRDefault] := by
  rw [ExactExecution.derivedResponseIO_eq_memoryRows, execution_rows.2]
  rfl

theorem memoryPubAt97_0 :
    exec97.memoryPubAt ⟨0, by norm_num [cfg97]⟩ = dummyHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rows.2,
    cfg97, dummyHaltLabel, memoryLabel]
theorem memoryPubAt97_1 :
    exec97.memoryPubAt ⟨1, by norm_num [cfg97]⟩ = readParentPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rows.2,
    cfg97, readParentLabel, memoryLabel]
theorem memoryPubAt97_2 :
    exec97.memoryPubAt ⟨2, by norm_num [cfg97]⟩ = decomposeParentPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rows.2,
    cfg97, decomposeParentLabel, memoryLabel]
theorem memoryPubAt97_3 :
    exec97.memoryPubAt ⟨3, by norm_num [cfg97]⟩ = parentHeadHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rows.2,
    cfg97, parentHeadHaltLabel, memoryLabel]
theorem memoryPubAt97_4 :
    exec97.memoryPubAt ⟨4, by norm_num [cfg97]⟩ = readChildPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rows.2,
    cfg97, readChildLabel, memoryLabel]
theorem memoryPubAt97_5 :
    exec97.memoryPubAt ⟨5, by norm_num [cfg97]⟩ = verifyParentPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rows.2,
    cfg97, verifyParentLabel, memoryLabel]
theorem memoryPubAt97_6 :
    exec97.memoryPubAt ⟨6, by norm_num [cfg97]⟩ = decomposeChildPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rows.2,
    cfg97, decomposeChildLabel, memoryLabel]
theorem memoryPubAt97_7 :
    exec97.memoryPubAt ⟨7, by norm_num [cfg97]⟩ = childHeadHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rows.2,
    cfg97, childHeadHaltLabel, memoryLabel]
theorem memoryPubAt97_8 :
    exec97.memoryPubAt ⟨8, by norm_num [cfg97]⟩ = verifyChildPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rows.2,
    cfg97, verifyChildLabel, memoryLabel]
theorem memoryPubAt97_9 :
    exec97.memoryPubAt ⟨9, by norm_num [cfg97]⟩ = tailHaltPub := by
  norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt, execution_rows.2,
    cfg97, tailHaltLabel, memoryLabel]

/-- Every fixture memory row carries the package `λ = formRDefault` (row encode). -/
theorem exec97_lambda_unset :
    ∀ i, (exec97.memoryPubAt i).lambda? = some MemoryTable.formRDefault := by
  intro i
  fin_cases i
  · rw [memoryPubAt97_0]; rfl
  · rw [memoryPubAt97_1]; rfl
  · rw [memoryPubAt97_2]; rfl
  · rw [memoryPubAt97_3]; rfl
  · rw [memoryPubAt97_4]; rfl
  · rw [memoryPubAt97_5]; rfl
  · rw [memoryPubAt97_6]; rfl
  · rw [memoryPubAt97_7]; rfl
  · rw [memoryPubAt97_8]; rfl
  · rw [memoryPubAt97_9]; rfl

theorem parent_child_requests_distinct :
    NockVM.encRecFormR parentRequest MemoryTable.formRDefault ≠
      NockVM.encRecFormR childRequest MemoryTable.formRDefault := by
  intro h
  have hts := congrFun h (7 : Fin 9)
  change parentRequest.ts = childRequest.ts at hts
  rw [show childRequest.ts = (16 : K97cubic) by
    norm_num [childRequest, fixtureAlpha]] at hts
  have hts' : (4 : K97cubic) = 16 := by
    simpa [parentRequest, fixtureAlpha] using hts
  letI : CharP K97cubic 97 := char97
  have hnat : 4 = 16 :=
    CharP.natCast_injOn_Iio K97cubic 97 (by norm_num) (by norm_num) hts'
  omega

theorem derived_requests_nodup : exec97.derivedRequestIO.Nodup := by
  rw [derived_requests]
  simp [parent_child_requests_distinct]

theorem derived_responses_nodup : exec97.derivedResponseIO.Nodup := by
  rw [derived_responses]
  simp [parent_child_requests_distinct]

/-- Row-level `C'` is a function of the stored record on `exec97`: the two active records have distinct timestamps (`α`, `α²`)
and padding rows store `MemRec.zero` beside the default `1`. -/
theorem exec97_cprimeCoherent : exec97.CprimeCoherent := by
  have hts : ∀ {a b : MemRec K97cubic}, a.ts ≠ b.ts →
      NockVM.formRRow a MemoryTable.formRDefault ≠ NockVM.formRRow b MemoryTable.formRDefault :=
    fun h he => h (by simpa [NockVM.formRRow] using congrArg MemRec.ts he)
  have hPC : parentRequest.ts ≠ childRequest.ts := by
    intro hts
    rw [show childRequest.ts = (16 : K97cubic) by
      norm_num [childRequest, fixtureAlpha]] at hts
    have hts' : (4 : K97cubic) = 16 := by
      simpa [parentRequest, fixtureAlpha] using hts
    letI : CharP K97cubic 97 := char97
    have hnat : 4 = 16 :=
      CharP.natCast_injOn_Iio K97cubic 97 (by norm_num) (by norm_num) hts'
    omega
  have h4 : (4 : K97cubic) ≠ 0 := by
    letI : CharP K97cubic 97 := char97
    intro h
    have hnat : (4 : ℕ) = 0 :=
      CharP.natCast_injOn_Iio K97cubic 97 (by norm_num) (by norm_num) (by simpa using h)
    omega
  have hzP : MemRec.zero ≠ NockVM.formRRow parentRequest MemoryTable.formRDefault := by
    intro h
    have := congrArg MemRec.ts h
    simp [NockVM.formRRow, MemRec.zero, parentRequest, fixtureAlpha] at this
    exact h4 this.symm
  have hzC : MemRec.zero ≠ NockVM.formRRow childRequest MemoryTable.formRDefault := by
    intro h
    have := congrArg MemRec.ts h
    simp [NockVM.formRRow, MemRec.zero, childRequest, fixtureAlpha] at this
    exact pow_ne_zero 2 h4 this.symm
  have hPC' := hts hPC
  refine ExactExecution.cprimeCoherent_of_fun
    (fun m => if m = NockVM.formRRow parentRequest MemoryTable.formRDefault then
        NockVM.formRCprime parentRequest MemoryTable.formRDefault
      else if m = NockVM.formRRow childRequest MemoryTable.formRDefault then
        NockVM.formRCprime childRequest MemoryTable.formRDefault
      else 1) ?_
  intro row hmem
  rw [execution_rows.2] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [memoryLabel, dummyHaltLabel, readParentLabel, decomposeParentLabel, parentHeadHaltLabel,
        readChildLabel, verifyParentLabel, decomposeChildLabel, childHeadHaltLabel,
            verifyChildLabel, tailHaltLabel, dummyHaltPub, readParentPub, decomposeParentPub,
                parentHeadHaltPub, readChildPub, verifyParentPub, decomposeChildPub,
                childHeadHaltPub, verifyChildPub, tailHaltPub, MemoryTable.Pub.cprime, hPC',
                Ne.symm hPC', hzP, hzC]

theorem compute_rows_accepted : exec97.ComputeRowsAccepted := by
  rw [ExactExecution.computeRowsAccepted_iff, execution_rows.1]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl
  · exact ⟨rfl, rfl, parent_accepts⟩
  · exact ⟨rfl, rfl, child_accepts⟩

theorem memory_rows_accepted : exec97.MemoryRowsAccepted := by
  rw [ExactExecution.memoryRowsAccepted_iff, execution_rows.2]
  intro row hrow
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, dummyHalt_accepts, rfl⟩
  · exact ⟨rfl, rfl, readParent_accepts, rfl⟩
  · exact ⟨rfl, rfl, decomposeParent_accepts, rfl⟩
  · exact ⟨rfl, rfl, parentHeadHalt_accepts, rfl⟩
  · exact ⟨rfl, rfl, readChild_accepts, rfl⟩
  · exact ⟨rfl, rfl, verifyParent_accepts, rfl⟩
  · exact ⟨rfl, rfl, decomposeChild_accepts, rfl⟩
  · exact ⟨rfl, rfl, childHeadHalt_accepts, rfl⟩
  · exact ⟨rfl, rfl, verifyChild_accepts, rfl⟩
  · exact ⟨rfl, rfl, tailHalt_accepts, rfl⟩

theorem compute_wf_all :
    ∀ i, ComputeTable.WF cfg97.challenges.computeInputs (exec97.computePubAt i) := by
  rw [show cfg97.challenges.computeInputs = computeInputs97 by rfl]
  intro i
  fin_cases i
  · simpa [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, ExactExecution.computePubAt, ExactExecution.computeRowAt,
      ExactExecution.computeRows, exec97, computeTree, bfsForest, cfg97, parentLabel,
      computeInputs97] using parent_wf
  · simpa [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, ExactExecution.computePubAt, ExactExecution.computeRowAt,
      ExactExecution.computeRows, exec97, computeTree, bfsForest, cfg97, childLabel,
      computeInputs97] using child_wf

theorem memory_wf_all :
    ∀ i, MemoryTable.WF cfg97.challenges.memoryInputs (exec97.memoryPubAt i) := by
  rw [show cfg97.challenges.memoryInputs = memoryInputs97 by rfl]
  intro i
  fin_cases i
  all_goals
    norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
      ExactExecution.memoryRows, exec97, dummyHaltTree, memoryTree, decomposeParentTree, parentHeadTree,
      readChildTree, verifyParentTree, decomposeChildTree, childHeadTree, verifyChildTree,
      tailTree, bfsForest, NTree.size, totalSize, cfg97, memoryLabel, memoryInputs97,
      dummyHaltPub, readParentPub, decomposeParentPub, parentHeadHaltPub, readChildPub, verifyParentPub,
      decomposeChildPub, childHeadHaltPub, verifyChildPub, tailHaltPub]
  ·
    constructor
    simp
  ·
    constructor
    intro _
    show pole memoryInputs97 (NockVM.formRRow parentRequest MemoryTable.formRDefault)
      (NockVM.formRCprime parentRequest MemoryTable.formRDefault) ≠ 0
    rw [pole_row97, parent_pole]
    norm_num
  ·
    constructor
    simp
  ·
    constructor
    simp
  ·
    constructor
    intro _
    show pole memoryInputs97 (NockVM.formRRow childRequest MemoryTable.formRDefault)
      (NockVM.formRCprime childRequest MemoryTable.formRDefault) ≠ 0
    rw [pole_row97, child_pole]
    norm_num
  ·
    constructor
    intro _
    show pole memoryInputs97 (NockVM.formRRow parentRequest MemoryTable.formRDefault)
      (NockVM.formRCprime parentRequest MemoryTable.formRDefault) ≠ 0
    rw [pole_row97, parent_pole]
    norm_num
  ·
    constructor
    simp
  ·
    constructor
    simp
  ·
    constructor
    intro _
    show pole memoryInputs97 (NockVM.formRRow childRequest MemoryTable.formRDefault)
      (NockVM.formRCprime childRequest MemoryTable.formRDefault) ≠ 0
    rw [pole_row97, child_pole]
    norm_num
  ·
    constructor
    simp

theorem compute_chain :
    ∀ i : Fin cfg97.compRows, ∀ hi : (i : ℕ) + 1 < cfg97.compRows,
      (exec97.computePubAt i).ln =
        (exec97.computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev := by
  intro i hi
  fin_cases i
  · norm_num [ExactExecution.computePubAt, ExactExecution.computeRowAt,
      ExactExecution.computeRows, exec97, computeTree, bfsForest, cfg97, parentLabel,
      childLabel, parentPub, childPub]
  · simp [cfg97] at hi

theorem memory_chain :
    ∀ i : Fin cfg97.memRows, ∀ hi : (i : ℕ) + 1 < cfg97.memRows,
      (exec97.memoryPubAt i).icur =
        (exec97.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre := by
  intro i hi
  fin_cases i
  all_goals
    norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
      ExactExecution.memoryRows, exec97, dummyHaltTree, memoryTree, decomposeParentTree, parentHeadTree,
      readChildTree, verifyParentTree, decomposeChildTree, childHeadTree, verifyChildTree,
      tailTree, bfsForest, NTree.size, totalSize, cfg97, memoryLabel, dummyHaltPub, readParentPub,
      decomposeParentPub, parentHeadHaltPub, readChildPub, verifyParentPub,
      decomposeChildPub, childHeadHaltPub, verifyChildPub, tailHaltPub]
  · simp [cfg97] at hi

def semanticParentRecord : (nmrMEF F97 K97cubic).Rec :=
  (3,
    (((fixtureFP parentFormula).size, (fixtureFP parentFormula).dyck,
      (fixtureFP parentFormula).leaf),
     ((fixtureFP childFormula).size, (fixtureFP childFormula).dyck,
      (fixtureFP childFormula).leaf)),
    1)

def semanticChildRecord : (nmrMEF F97 K97cubic).Rec :=
  (3,
    (((fixtureFP childFormula).size, (fixtureFP childFormula).dyck,
      (fixtureFP childFormula).leaf),
     ((fixtureFP incrementInput).size, (fixtureFP incrementInput).dyck,
      (fixtureFP incrementInput).leaf)),
    2)

theorem semantic_parent_bridge :
    bridge F97 K97cubic cfg97.challenges.α cfg97.challenges.lam semanticParentRecord =
      NockVM.encRecFormR parentRequest MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees]
  have hthree : algebraMap F97 K97cubic (3 : F97) = (3 : K97cubic) := by
    simpa using (map_natCast (algebraMap F97 K97cubic) 3)
  rw [show memRecOfNMR F97 K97cubic
      ((nmrEncoding F97 K97cubic cfg97.challenges.α).encode semanticParentRecord) =
        parentRequest by
    ext <;> norm_num [memRecOfNMR, nmrEncoding, semanticParentRecord, cfg97,
      parentRequest, fixtureAlpha, hthree]]
  rfl

theorem semantic_child_bridge :
    bridge F97 K97cubic cfg97.challenges.α cfg97.challenges.lam semanticChildRecord =
      NockVM.encRecFormR childRequest MemoryTable.formRDefault := by
  rw [← d2_record_bridge_agrees]
  have hthree : algebraMap F97 K97cubic (3 : F97) = (3 : K97cubic) := by
    simpa using (map_natCast (algebraMap F97 K97cubic) 3)
  rw [show memRecOfNMR F97 K97cubic
      ((nmrEncoding F97 K97cubic cfg97.challenges.α).encode semanticChildRecord) =
        childRequest by
    ext <;> norm_num [memRecOfNMR, nmrEncoding, semanticChildRecord, cfg97,
      childRequest, fixtureAlpha, hthree]]
  rfl

theorem fixtureAlpha_order : orderOf fixtureAlpha = 24 := by
  have hbase : orderOf (4 : F97) = 24 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm hpos
    interval_cases m <;> decide
  have hcast : fixtureAlpha = algebraMap F97 K97cubic (4 : F97) := by
    exact (map_natCast (algebraMap F97 K97cubic) 4).symm
  rw [hcast]
  change orderOf ((algebraMap F97 K97cubic).toMonoidHom (4 : F97)) = 24
  exact (orderOf_injective (algebraMap F97 K97cubic).toMonoidHom
    (algebraMap F97 K97cubic).injective (4 : F97)).trans hbase

theorem semantic_records_distinct : semanticParentRecord ≠ semanticChildRecord := by
  intro h
  have ht := congrArg (fun r : (nmrMEF F97 K97cubic).Rec => r.2.2) h
  norm_num [semanticParentRecord, semanticChildRecord] at ht

def semanticPreimage97 : SemanticIOPreimage cfg97 exec97 where
  timestampBound := 3
  timestampBound_le_order := by
    change 3 ≤ orderOf fixtureAlpha
    rw [fixtureAlpha_order]
    norm_num
  semanticRequests := [semanticParentRecord, semanticChildRecord]
  semanticResponses := [semanticParentRecord, semanticChildRecord]
  requestTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> norm_num [semanticParentRecord, semanticChildRecord]
  responseTimestampBound := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> norm_num [semanticParentRecord, semanticChildRecord]
  semantic_lmio := by
    rw [IO.LmIO_iff]
    exact ⟨by norm_num [IO.InRange, cfg97], by norm_num,
      (by
        exact List.nodup_cons.mpr
          ⟨by simpa only [List.mem_singleton] using semantic_records_distinct,
           List.nodup_singleton semanticChildRecord⟩),
      rfl⟩
  requestTimestamp_determines := by
    intro x hx y hy h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first | rfl | (norm_num [semanticParentRecord, semanticChildRecord] at h)
  requests_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_singleton,
      semantic_parent_bridge, semantic_child_bridge, derived_requests]
  responses_bridge := by
    rw [bridgeRecords, List.map_cons, List.map_singleton,
      semantic_parent_bridge, semantic_child_bridge, derived_responses]

def semanticWitness97 : SemanticIOWitness cfg97 exec97 where
  toSemanticIOPreimage := semanticPreimage97
  semanticRequests_nodup := by
    change [semanticParentRecord, semanticChildRecord].Nodup
    exact List.nodup_cons.mpr
      ⟨by simpa only [List.mem_singleton] using semantic_records_distinct,
       List.nodup_singleton semanticChildRecord⟩

theorem semantic_exact97 : SemanticExactLanguage cfg97 exec97 :=
  ⟨compute_rows_accepted, memory_rows_accepted, ⟨semanticPreimage97⟩⟩

theorem chained97 : ChainedSemanticExactLanguage cfg97 exec97 where
  semantic := semantic_exact97
  z_ne_zero := fixtureSeed_ne
  compute_wf := compute_wf_all
  memory_wf := memory_wf_all
  compute_chain := compute_chain
  memory_chain := memory_chain
  memory_first_counts := by
    norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
      ExactExecution.memoryRows, exec97, dummyHaltTree, memoryTree, decomposeParentTree, parentHeadTree,
      readChildTree, verifyParentTree, decomposeChildTree, childHeadTree, verifyChildTree,
      tailTree, bfsForest, NTree.size, totalSize, cfg97, memoryLabel, dummyHaltPub]
      <;> simp [dummyHaltCell]
  memory_first_indicator := by
    norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
      ExactExecution.memoryRows, exec97, dummyHaltTree, memoryTree, decomposeParentTree, parentHeadTree,
      readChildTree, verifyParentTree, decomposeChildTree, childHeadTree, verifyChildTree,
      tailTree, bfsForest, NTree.size, totalSize, cfg97, memoryLabel, dummyHaltPub]
      <;> simp [dummyHaltCell]
  memory_first_ipre := by
    norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
      ExactExecution.memoryRows, exec97, dummyHaltTree, memoryTree, decomposeParentTree, parentHeadTree,
      readChildTree, verifyParentTree, decomposeChildTree, childHeadTree, verifyChildTree,
      tailTree, bfsForest, NTree.size, totalSize, cfg97, memoryLabel, dummyHaltPub]
  memory_last_icur := by
    norm_num [ExactExecution.memoryPubAt, ExactExecution.memoryRowAt,
      ExactExecution.memoryRows, exec97, dummyHaltTree, memoryTree, decomposeParentTree, parentHeadTree,
      readChildTree, verifyParentTree, decomposeChildTree, childHeadTree, verifyChildTree,
      tailTree, bfsForest, NTree.size, totalSize, OrbitDomain.lastIndex, cfg97,
      memoryLabel, tailHaltPub]

  memory_same_lambda :=
    ExactExecution.memory_same_lambda_of_const _ (some MemoryTable.formRDefault)
      exec97_lambda_unset

def problem97 : ExactCanonicalRAPProblem F97 K97cubic :=
  ExactCanonicalRAPProblem.ofChained chained97

theorem stateTagChar97 : NodeEncoding.StateTagChar K97cubic :=
  by
    letI : CharP K97cubic 97 := char97
    exact NodeEncoding.stateTagChar_of_charP (K := K97cubic) 97 (by norm_num)

theorem progCapacity97 :
    problem97.exec.derivedRequestIO.length + 1 ≤ 2 ^ problem97.cfg.orbit.h := by
  change exec97.derivedRequestIO.length + 1 ≤ 2 ^ cfg97.orbit.h
  rw [derived_requests]
  norm_num [cfg97, executionOrbit97]

theorem memCapacity97 :
    problem97.exec.derivedResponseIO.length + 1 ≤ 2 ^ problem97.cfg.orbit.h := by
  change exec97.derivedResponseIO.length + 1 ≤ 2 ^ cfg97.orbit.h
  rw [derived_responses]
  norm_num [cfg97, executionOrbit97]

def zeroFamily97 : PlusIOSegmentedFamily F97 K97cubic :=
  PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders
    problem97 stateTagChar97 2 3 5 0 0 0 progCapacity97 memCapacity97

structure Completion97 where
  requests : IOField K97cubic
  responses : IOField K97cubic
  outMem : IOField K97cubic
  assignment :
    JointAssignment
      (zeroFamily97.withIOEndpoints requests responses outMem)
      (ringChar K97cubic)

theorem completion97_nonempty : Nonempty Completion97 := by
  obtain ⟨requests, responses, outMem, ⟨A⟩⟩ :=
    jointVerification_complete zeroFamily97
      (by simpa [zeroFamily97, problem97, ExactCanonicalRAPProblem.ofChained,
        PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders] using chained97)
      (by simpa [zeroFamily97, problem97, ExactCanonicalRAPProblem.ofChained,
        PlusIOSegmentedFamily.ofProblemWithConcreteNodeEncoders] using semanticWitness97)
      (by
        change cfg97.Ksz < ringChar K97cubic
        rw [← Algebra.ringChar_eq F97 K97cubic, ZMod.ringChar_zmod_n]
        norm_num [cfg97])
  exact ⟨⟨requests, responses, outMem, A⟩⟩

noncomputable def completion97 : Completion97 :=
  Classical.choice completion97_nonempty

abbrev family97 : PlusIOSegmentedFamily F97 K97cubic :=
  zeroFamily97.withIOEndpoints completion97.requests completion97.responses completion97.outMem

abbrev exactAssignment97 :
    PlusIOSameExecutionAssignment family97 (ringChar K97cubic) :=
  completion97.assignment.sameExecution

theorem family97_problem : family97.problem = problem97 := rfl

/-! ## Finite sampled IO with the same two distinct records -/

def sampledRecords97 : FiniteIO.PreChallengeRecords K97cubic 9 where
  requests := exec97.derivedRequestIO
  responses := exec97.derivedResponseIO

theorem ioFailureBound97 :
    (FiniteIO.IOFailureEvent sampledRecords97).card <
      Fintype.card (K97cubic × K97cubic) := by
  refine lt_of_le_of_lt (FiniteIO.IOFailureEvent_card_le sampledRecords97) ?_
  have hcard : Fintype.card K97cubic = 97 ^ 3 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 97 3 (by norm_num)
  simp [sampledRecords97, derived_requests, derived_responses,
    FiniteIO.ioFailureUnionBound]
  rw [hcard]
  norm_num

/-- The 31st: the honest ten-slot records of the fixture (`honestRecords10 family97`). -/
noncomputable def sampledRecords10_97 : FiniteIO.PreChallengeRecords K97cubic 10 :=
  RecordCarrier.extRecords exec97.derivedRequestIO sampledRecords97

/-- The fixture's coins miss the nine-slot and the ten-slot failure events at once. -/
theorem goodIOCoins97_exists :
    ∃ coins : FiniteIO.IOCoins K97cubic,
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent sampledRecords97 ∧
      (coins.gamma, coins.pole) ∉ FiniteIO.IOFailureEvent sampledRecords10_97 := by
  apply RecordCarrier.exists_io_coins_two_of_bounds
  have hcard : Fintype.card K97cubic = 97 ^ 3 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 97 3 (by norm_num)
  simp [sampledRecords10_97, RecordCarrier.extRecords, sampledRecords97, derived_requests,
    derived_responses, FiniteIO.ioFailureUnionBound, Fintype.card_prod]
  rw [hcard]
  norm_num

noncomputable def sampledCoins97 : FiniteIO.IOCoins K97cubic :=
  Classical.choose goodIOCoins97_exists

theorem sampledCoins97_good :
    (sampledCoins97.gamma, sampledCoins97.pole) ∉
      FiniteIO.IOFailureEvent sampledRecords97 :=
  (Classical.choose_spec goodIOCoins97_exists).1

theorem sampledCoins97_good10 :
    (sampledCoins97.gamma, sampledCoins97.pole) ∉
      FiniteIO.IOFailureEvent sampledRecords10_97 :=
  (Classical.choose_spec goodIOCoins97_exists).2

theorem sampledPoleHit97 :
    sampledCoins97.pole ∉
      FiniteIO.IOPoleHitEvent sampledRecords97 sampledCoins97.gamma := by
  intro h
  apply sampledCoins97_good
  simp [FiniteIO.IOFailureEvent, h]

theorem sampledWitness97_exists :
    ∃ witness : FiniteIO.PostChallengeIOWitness sampledRecords97 sampledCoins97,
      FiniteIO.FiniteIOAccepts sampledRecords97 sampledCoins97 witness :=
  FiniteIO.finiteIO_complete_of_LIO (Ksz := cfg97.Ksz) sampledRecords97 sampledCoins97
      (by
        rw [show sampledRecords97.requests = exec97.derivedRequestIO by rfl,
          show sampledRecords97.responses = exec97.derivedResponseIO by rfl,
          derived_requests, derived_responses]
        exact ⟨by norm_num [IO.InRange, cfg97],
          (by rw [← derived_requests]; exact derived_requests_nodup),
          List.Perm.refl _⟩)
      (by
        intro v hv hzero
        exact sampledPoleHit97 (by
          simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨v, hv, hzero⟩))

noncomputable def sampledWitness97 :
    FiniteIO.PostChallengeIOWitness sampledRecords97 sampledCoins97 :=
  Classical.choose sampledWitness97_exists

theorem sampledWitness97_accepts :
    FiniteIO.FiniteIOAccepts sampledRecords97 sampledCoins97 sampledWitness97 :=
  Classical.choose_spec sampledWitness97_exists

noncomputable def finiteStrategy97 :
    FiniteIO.FiniteIOStrategy K97cubic 9 cfg97.Ksz (ringChar K97cubic) where
  records := sampledRecords97
  coins := sampledCoins97
  witness := sampledWitness97
  accepts := sampledWitness97_accepts
  uniqueRequest := by simpa [sampledRecords97] using derived_requests_nodup
  uniqueResponse := by simpa [sampledRecords97] using derived_responses_nodup
  requestRange := by rw [show sampledRecords97.requests = exec97.derivedRequestIO by rfl,
    derived_requests]; norm_num [IO.InRange, cfg97]
  responseRange := by rw [show sampledRecords97.responses = exec97.derivedResponseIO by rfl,
    derived_responses]; norm_num [cfg97]
  charBound := by
    rw [← Algebra.ringChar_eq F97 K97cubic, ZMod.ringChar_zmod_n]
    norm_num [cfg97]
  gammaGood := by
    intro h
    apply sampledCoins97_good
    simp [FiniteIO.IOFailureEvent, h]
  poleGood := by
    intro h
    apply sampledCoins97_good
    simp [FiniteIO.IOFailureEvent, h]

theorem interRecords97_card :
    ((RowLayout.consumedRecordList exec97).map (fun r => NockVM.encRecC r
        (exec97.cprimeOf r))).length +
      exec97.derivedResponseIO.length <
        Fintype.card K97cubic := by
  simp only [List.length_map]
  have hmem : exec97.memoryRows.length = 10 := by
    rw [ExactExecution.memoryRows_length]
    rfl
  have hpart := RowLayout.memoryRows_state_partition exec97
  rw [hmem] at hpart
  have hcons : (RowLayout.consumedRecordList exec97).length ≤ 10 := by
    rw [← RowLayout.verifyChildCount_eq_consumed_length]
    omega
  have hresp : exec97.derivedResponseIO.length ≤ 10 := by
    have := ExactExecution.derivedResponseIO_length_le exec97
    omega
  have hcard : Fintype.card K97cubic = 97 ^ 3 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 97 3 (by norm_num)
  calc (RowLayout.consumedRecordList exec97).length + exec97.derivedResponseIO.length
      ≤ 10 + exec97.derivedResponseIO.length := Nat.add_le_add_right hcons _
    _ ≤ 10 + 10 := Nat.add_le_add_left hresp _
    _ = 20 := by norm_num
    _ < 97 ^ 3 := by norm_num
    _ = Fintype.card K97cubic := hcard.symm

theorem exists_interPole97 :
    ∃ pole : K97cubic,
      pole ∉ FiniteIO.IOPoleHitEvent
        { requests := (RowLayout.consumedRecordList exec97).map (fun r => NockVM.encRecC r
            (exec97.cprimeOf r))
          responses := exec97.derivedResponseIO }
        finiteStrategy97.coins.gamma ∧
      pole ∉ FiniteIO.IOPoleHitEvent
        (RecordCarrier.extRecords exec97.derivedRequestIO
          { requests := (RowLayout.consumedRecordList exec97).map (fun r => NockVM.encRecC r
              (exec97.cprimeOf r))
            responses := exec97.derivedResponseIO })
        finiteStrategy97.coins.gamma := by
  classical
  set recs : FiniteIO.PreChallengeRecords K97cubic 9 :=
    { requests := (RowLayout.consumedRecordList exec97).map (fun r => NockVM.encRecC r
        (exec97.cprimeOf r))
      responses := exec97.derivedResponseIO }
  set recs10 := RecordCarrier.extRecords exec97.derivedRequestIO recs
  have hle := FiniteIO.IOPoleHitEvent_card_le recs finiteStrategy97.coins.gamma
  have hle10 := FiniteIO.IOPoleHitEvent_card_le recs10 finiteStrategy97.coins.gamma
  have hlen : recs.requests.length + recs.responses.length < Fintype.card K97cubic := by
    simpa [recs] using interRecords97_card
  have hlen10 : recs10.requests.length + recs10.responses.length =
      recs.requests.length + recs.responses.length := by
    simp [recs10, RecordCarrier.extRecords]
  have hcard3 : Fintype.card K97cubic = 97 ^ 3 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 97 3 (by norm_num)
  have h20 : recs.requests.length + recs.responses.length ≤ 20 := by
    have := interRecords97_card
    simp only [List.length_map] at this ⊢
    have hmem : exec97.memoryRows.length = 10 := by
      rw [ExactExecution.memoryRows_length]; rfl
    have hpart := RowLayout.memoryRows_state_partition exec97
    rw [hmem] at hpart
    have hcons : (RowLayout.consumedRecordList exec97).length ≤ 10 := by
      rw [← RowLayout.verifyChildCount_eq_consumed_length]; omega
    have hresp : exec97.derivedResponseIO.length ≤ 10 := by
      have := ExactExecution.derivedResponseIO_length_le exec97; omega
    simp only [recs, List.length_map]
    omega
  have hlt : (FiniteIO.IOPoleHitEvent recs finiteStrategy97.coins.gamma ∪
      FiniteIO.IOPoleHitEvent recs10 finiteStrategy97.coins.gamma).card <
      Fintype.card K97cubic := by
    refine lt_of_le_of_lt (Finset.card_union_le _ _) ?_
    rw [hcard3]
    omega
  have hne : FiniteIO.IOPoleHitEvent recs finiteStrategy97.coins.gamma ∪
      FiniteIO.IOPoleHitEvent recs10 finiteStrategy97.coins.gamma ≠ Finset.univ := by
    intro hEq
    rw [hEq, Finset.card_univ] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨z, -, hz⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  rw [Finset.mem_union, not_or] at hz
  exact ⟨z, hz.1, hz.2⟩

noncomputable def interPole97 : K97cubic :=
  Classical.choose exists_interPole97

theorem interPole97_good :
    interPole97 ∉ FiniteIO.IOPoleHitEvent
      { requests := (RowLayout.consumedRecordList exec97).map (fun r => NockVM.encRecC r
          (exec97.cprimeOf r))
        responses := exec97.derivedResponseIO }
      finiteStrategy97.coins.gamma :=
  (Classical.choose_spec exists_interPole97).1

theorem interPole97_good10 :
    interPole97 ∉ FiniteIO.IOPoleHitEvent
      (RecordCarrier.extRecords exec97.derivedRequestIO
        { requests := (RowLayout.consumedRecordList exec97).map (fun r => NockVM.encRecC r
            (exec97.cprimeOf r))
          responses := exec97.derivedResponseIO })
      finiteStrategy97.coins.gamma :=
  (Classical.choose_spec exists_interPole97).2

set_option maxHeartbeats 800000 in
noncomputable def sampledAssignment97 :
    SampledIOSameExecutionAssignment family97 (ringChar K97cubic) where
  exact := exactAssignment97
  sampled := by
    change FiniteIO.FiniteIOStrategy K97cubic 9 cfg97.Ksz (ringChar K97cubic)
    exact finiteStrategy97
  requests_eq := by
    change exec97.derivedRequestIO = problem97.exec.derivedRequestIO
    rfl
  responses_eq := by
    change exec97.derivedResponseIO = problem97.exec.derivedResponseIO
    rfl
  poleHitGood := by
    exact sampledPoleHit97
  interPole := interPole97
  interPoleHitGood := by
    change interPole97 ∉ FiniteIO.IOPoleHitEvent
      { requests := (RowLayout.consumedRecordList exec97).map (fun r => NockVM.encRecC r
          (exec97.cprimeOf r))
        responses := exec97.derivedResponseIO }
      finiteStrategy97.coins.gamma
    exact interPole97_good
  honestVer := by
    change ∀ row ∈ exec97.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)
    intro row hrow
    rw [execution_rows.2] at hrow
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  ioGood10 := by
    change (sampledCoins97.gamma, sampledCoins97.pole) ∉
      FiniteIO.IOFailureEvent (RecordCarrier.extRecords exec97.derivedRequestIO
        ⟨exec97.derivedRequestIO, exec97.derivedResponseIO⟩)
    exact sampledCoins97_good10
  interPoleHitGood10 := by
    change interPole97 ∉ FiniteIO.IOPoleHitEvent
      (RecordCarrier.extRecords exec97.derivedRequestIO
        { requests := (RowLayout.consumedRecordList exec97).map (fun r => NockVM.encRecC r
            (exec97.cprimeOf r))
          responses := exec97.derivedResponseIO })
      finiteStrategy97.coins.gamma
    exact interPole97_good10

/-- H1.W walk-label obligations of the two-row F97 fixture: the encoder is the `LT_comp`
projection by construction; the parent's one child slot is the child row (`parentLabel_accepts`). -/
theorem walkLabelObligations97 : sampledAssignment97.WalkLabelObligations := by
  refine ⟨fun t => rfl, ?_⟩
  intro t ht
  change t ∈ Walk.bfsForest [computeTree] at ht
  simp [computeTree, Walk.bfsForest] at ht
  rcases ht with rfl | rfl
  · refine ⟨rfl, ?_, ?_⟩
    · simp [parentLabel, ComputeTable.fanoutComp]
    · rw [show (fun j : Fin 3 => (NTree.node parentLabel [.node childLabel []]).childLabel j) =
          parentOut by
        funext j
        fin_cases j <;> rfl]
      exact parentLabel_accepts.2.2.2
  · refine ⟨rfl, by simp [childLabel, ComputeTable.fanoutComp], ?_⟩
    intro i hi
    simp [childLabel, ComputeTable.fanoutComp] at hi

theorem sampled_obligations97 :
    sampledAssignment97.ComputeSampledObligations := by
  apply sampledAssignment97.computeSampledObligations_of_six
  · change exactAssignment97.SixConcreteObligations
    exact (exactAssignment97.satisfies_iff_six_concrete_obligations).1
      completion97.assignment.sixFamilies
  · exact walkLabelObligations97

/-! ## Corrected 199/98 trace, exact pins, and nonterminal decode -/

def computeNodes97 : Fin family97.problem.cfg.compRows → F97
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 6

theorem computeNodes97_injective : Function.Injective computeNodes97 := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · change (1 : F97) = 6 at h
    exact False.elim ((by decide : (1 : F97) ≠ 6) h)
  · change (6 : F97) = 1 at h
    exact False.elim ((by decide : (6 : F97) ≠ 1) h)
  · rfl

theorem computeNodes97_orbit :
    ∀ (i : Fin family97.problem.cfg.compRows)
      (hi : (i : ℕ) + 1 < family97.problem.cfg.compRows),
      computeNodes97 ⟨(i : ℕ) + 1, hi⟩ = strictOrbit97.ω * computeNodes97 i := by
  intro i hi
  fin_cases i
  · norm_num [computeNodes97, strictOrbit97]
  · have hc : family97.problem.cfg.compRows = 2 := rfl
    exfalso
    apply (show ¬ 2 < family97.problem.cfg.compRows by rw [hc]; omega)
    exact hi

def challengeCoordinates97 (i : ℕ) : F97 :=
  if hi : i < 36 then
    CoordinateBasis.coord basis97
      (exactFinalChallenge sampledAssignment97 (i / 3))
      ⟨i % 3, Nat.mod_lt _ (by omega)⟩
  else 0

theorem challengeCoordinates97_exact :
    ExactFinalChallengeCoordinates basis97 sampledAssignment97 challengeCoordinates97 := by
  intro q k
  rw [challengeCoordinates97, dif_pos (by omega)]
  have hdiv : (3 * (q : ℕ) + (k : ℕ)) / 3 = (q : ℕ) := by omega
  have hmod : (3 * (q : ℕ) + (k : ℕ)) % 3 = (k : ℕ) := by omega
  rw [hdiv]
  congr 1
  apply Fin.ext
  exact hmod

def publicCoordinates97 (i : ℕ) : F97 :=
  if hi : i < 6 then
    CoordinateBasis.coord basis97
      (if i / 3 = 0 then family97.computeWalkAlpha else family97.computeWalkSeed)
      ⟨i % 3, Nat.mod_lt _ (by omega)⟩
  else if h9 : 6 ≤ i ∧ i < 9 then
    -- `requests`: the sampled IO terminal
    CoordinateBasis.coord basis97 sampledAssignment97.witness10.terminal ⟨i - 6, by omega⟩
  else if hfirst : 20 ≤ i ∧ i < 31 then
    if i - 20 = OptimizedComputeCodec.stateIndex
        (family97.problem.exec.computePubAt ⟨0, family97.problem.cfg.compRows_pos⟩).state
      then 1 else 0
  else if hlast : 31 ≤ i ∧ i < 42 then
    if i - 31 = OptimizedComputeCodec.stateIndex
        (family97.problem.exec.computePubAt
          ⟨family97.problem.cfg.compRows - 1,
            Nat.sub_lt family97.problem.cfg.compRows_pos (by omega)⟩).state
      then 1 else 0
  else 0

theorem publicCoordinates97_requests :
    ExactFinalRequestsCoordinate basis97 sampledAssignment97 publicCoordinates97 := by
  intro k
  have hk := k.isLt
  rw [publicCoordinates97, dif_neg (by omega), dif_pos (by omega)]
  congr 1
  apply Fin.ext
  simp

/-- F97's first compute row (`parentPub`) has `ln_prev = 1` — the origin the W6.1 stage-2A gate
`finalLnInit` pins. -/
theorem lineOrigin97 : ExactFinalLineOrigin family97 family97.problem.cfg.compRows_pos := by
  show (exec97.computePubAt ⟨0, _⟩).ln_prev = 1
  simp [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, ExactExecution.computePubAt, ExactExecution.computeRowAt, ExactExecution.computeRows,
    exec97, computeTree, bfsForest, parentLabel, parentPub]

theorem publicCoordinates97_exact :
    ExactFinalPublicCoordinates basis97 family97 family97.problem.cfg.compRows_pos
      publicCoordinates97 := by
  constructor
  · intro q k
    rw [publicCoordinates97, dif_pos (by omega)]
    have hdiv : (3 * (q : ℕ) + (k : ℕ)) / 3 = (q : ℕ) := by omega
    have hmod : (3 * (q : ℕ) + (k : ℕ)) % 3 = (k : ℕ) := by omega
    rw [hdiv]
    by_cases hq : q = 0
    · subst q
      simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
      congr 1
      apply Fin.ext
      exact hmod
    · have hqnat : (q : ℕ) ≠ 0 := fun hv => hq (Fin.ext hv)
      simp only [hqnat, ↓reduceIte, hq]
      congr 1
      apply Fin.ext
      exact hmod
  constructor
  · intro j
    rw [publicCoordinates97, dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
    by_cases hs : j = OptimizedComputeCodec.stateIndex
        (family97.problem.exec.computePubAt
          ⟨0, family97.problem.cfg.compRows_pos⟩).state
    · simp [hs]
    · have hv : (j : ℕ) ≠
          (OptimizedComputeCodec.stateIndex
            (family97.problem.exec.computePubAt
              ⟨0, family97.problem.cfg.compRows_pos⟩).state : ℕ) :=
        fun h => hs (Fin.ext h)
      simp [hs, hv]
  · intro j
    rw [publicCoordinates97, dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
      dif_pos (by omega)]
    by_cases hs : j = OptimizedComputeCodec.stateIndex
        (family97.problem.exec.computePubAt
          ⟨family97.problem.cfg.compRows - 1,
            Nat.sub_lt family97.problem.cfg.compRows_pos (by omega)⟩).state
    · simp [hs]
    · have hv : (j : ℕ) ≠
          (OptimizedComputeCodec.stateIndex
            (family97.problem.exec.computePubAt
              ⟨family97.problem.cfg.compRows - 1,
                Nat.sub_lt family97.problem.cfg.compRows_pos (by omega)⟩).state : ℕ) :=
        fun h => hs (Fin.ext h)
      simp [hs, hv]

noncomputable def correctedTrace97 :=
  correctedCanonicalFinalTrace sampledAssignment97 family97.problem.cfg.compRows_pos
    computeNodes97 basis97 challengeCoordinates97 publicCoordinates97 strictOrbit97

theorem formRWidth97 : FormRWidth F97 := by
  have hc : ringChar F97 = 97 := ZMod.ringChar_zmod_n 97
  constructor
  · change Nat.size (ringChar F97) ≤ 64
    rw [hc]; decide
  · change 0 < Nat.size (ringChar F97) ∧ 3 < ringChar F97
    rw [hc]; decide

/-- Fixture rows are `.s4` / `.s1`; no committed axis leaf. -/
theorem formRAxisBound97 : FormRAxisBound sampledAssignment97 basis97 := by
  intro i L hL
  have hdec :
      OptimizedComputeCodec.decodeState (encodedRowAt sampledAssignment97 i).base =
        (family97.problem.exec.computePubAt i).state := by
    simp [encodedRowAt, OptimizedComputeOverlay.sampledEncode,
      OptimizedComputeCodec.decodeState_encodeBase]
  have hst : (family97.problem.exec.computePubAt i).state = .s4 ∨
      (family97.problem.exec.computePubAt i).state = .s1 := by
    change (exec97.computePubAt i).state = .s4 ∨ (exec97.computePubAt i).state = .s1
    fin_cases i
    · left
      simp [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, ExactExecution.computePubAt, ExactExecution.computeRowAt,
        ExactExecution.computeRows, exec97, computeTree, bfsForest, parentLabel, parentPub]
    · right
      simp [Fin.cast, Fin.val_mk, List.getElem_cons_zero, List.getElem_cons_succ, ExactExecution.computePubAt, ExactExecution.computeRowAt,
        ExactExecution.computeRows, exec97, computeTree, bfsForest, childLabel, childPub]
  revert hL
  simp [axisLeafCoord, hdec]
  rcases hst with hst | hst <;> simp [hst]

def computeRealization97
    (hbasis : FormRBasis basis97) :
    OptimizedComputeRealizationAt sampledAssignment97 sampled_obligations97 computeNodes97
      basis97 challengeCoordinates97 publicCoordinates97 strictOrbit97 :=
  optimizedComputeRealization sampledAssignment97 sampled_obligations97
    family97.problem.cfg.compRows_pos computeNodes97 computeNodes97_injective basis97
    challengeCoordinates97 publicCoordinates97 strictOrbit97 computeNodes97_orbit
    challengeCoordinates97_exact publicCoordinates97_exact publicCoordinates97_requests
    lineOrigin97
    (fun _ => by
      have hα : family97.computeWalkAlpha = (2 : K97cubic) := rfl
      have hrows : family97.problem.cfg.compRows = 2 := rfl
      rw [hα, omega2_order, hrows]
      norm_num)
    formRAxisBound97 hbasis formRWidth97

theorem corrected_trace97_satisfies (hbasis : FormRBasis basis97) :
    RAP.SatisfiesWithPreprocessing
      (ProductionNamedComputeRAP family97.problem.cfg.compRows_pos computeNodes97 basis97
        challengeCoordinates97 publicCoordinates97 strictOrbit97)
      correctedTrace97 := by
  simpa [correctedTrace97] using
    correctedCanonicalFinalTrace_satisfies
      sampledAssignment97 sampled_obligations97
      family97.problem.cfg.compRows_pos computeNodes97 computeNodes97_injective
      basis97 challengeCoordinates97 publicCoordinates97 strictOrbit97
      computeNodes97_orbit challengeCoordinates97_exact publicCoordinates97_exact
      publicCoordinates97_requests lineOrigin97
      (fun _ => by
        have hα : family97.computeWalkAlpha = (2 : K97cubic) := rfl
        have hrows : family97.problem.cfg.compRows = 2 := rfl
        rw [hα, omega2_order, hrows]
        norm_num)
      formRAxisBound97 hbasis formRWidth97

def row0 : Fin family97.problem.cfg.compRows :=
  ⟨0, by
    have hc : family97.problem.cfg.compRows = 2 := rfl
    omega⟩
def row0Next : Fin family97.problem.cfg.compRows :=
  ⟨1, by
    have hc : family97.problem.cfg.compRows = 2 := rfl
    omega⟩

theorem row0_not_last :
    let env := gatherCorrectedFinalTypedEnv basis97
      (Nock.Framework.Reify.envOfTrace correctedTrace97 strictOrbit97.ω
        (computeNodes97 row0) challengeCoordinates97 publicCoordinates97)
    env.baseTrace 12 = 0 := by
  dsimp only
  simp only [correctedTrace97]
  rw [canonical_gather_base_current sampledAssignment97 family97.problem.cfg.compRows_pos
    computeNodes97 computeNodes97_injective basis97 challengeCoordinates97 publicCoordinates97
    strictOrbit97 row0 (12 : Fin 13)]
  have hc : family97.problem.cfg.compRows = 2 := rfl
  simp [finalBaseCell, row0, hc]

theorem row0_in_domain :
    computeNodes97 row0 ∈ rowNodeSet computeNodes97 := by
  simp [rowNodeSet]

def nonterminalSourceGood97 (e : Expr) : Bool :=
  match correctedLowerFinal e with
  | none => false
  | some t => correctedResidualFreeB t && correctedPublicFreeB t

set_option maxRecDepth 300000 in
set_option maxHeartbeats 8000000 in
theorem nonterminalSourceGood97_receipt :
    ∀ e ∈ finalNonIOSourceFamilies17.flatten, nonterminalSourceGood97 e = true := by
  decide

theorem nonterminalSource97_lower_receipt
    (e : Expr) (he : e ∈ finalNonIOSourceFamilies17.flatten) :
    ∃ t, correctedLowerFinal e = some t ∧
      CorrectedResidualFree t ∧ CorrectedPublicFree t := by
  have hg := nonterminalSourceGood97_receipt e he
  cases ht : correctedLowerFinal e with
  | none => simp [nonterminalSourceGood97, ht] at hg
  | some t =>
      simp [nonterminalSourceGood97, ht] at hg
      exact ⟨t, rfl, (correctedResidualFreeB_iff t).mp hg.1,
        (correctedPublicFreeB_iff t).mp hg.2⟩

theorem canonical_row0_nonIO_source_zero
    (e : Expr) (he : e ∈ finalNonIOSourceFamilies17.flatten) :
    e.eval
      (gatherCorrectedFinalTypedEnv basis97
        (Nock.Framework.Reify.envOfTrace correctedTrace97 strictOrbit97.ω
          (computeNodes97 row0) challengeCoordinates97 publicCoordinates97)).toSourceEnv = 0 := by
  have hi : (row0 : ℕ) + 1 < family97.problem.cfg.compRows := by
    have hc : family97.problem.cfg.compRows = 2 := rfl
    simpa [row0] using (show 1 < family97.problem.cfg.compRows by omega)
  let can := gatherCorrectedFinalTypedEnv basis97
    (Nock.Framework.Reify.envOfTrace correctedTrace97 strictOrbit97.ω
      (computeNodes97 row0) challengeCoordinates97 publicCoordinates97)
  let ex := exactFinalTransitionEnv sampledAssignment97 row0 hi
  let exPub : CorrectedFinalTypedEnv F97 K97cubic :=
    { ex with extensionPublic := can.extensionPublic
              scalarPublic := can.scalarPublic }
  obtain ⟨t, htLower, htResidual, htPublic⟩ := nonterminalSource97_lower_receipt e he
  rw [correctedLowerFinal_eval can e t htLower]
  have hsame : t.eval can = t.eval exPub := by
    apply CorrectedFinalTypedExpr.eval_eq_of_residualFree
    · intro q
      simpa [can, exPub, ex, exactFinalTransitionEnv, correctedTrace97] using
        canonical_gather_base_current sampledAssignment97
          family97.problem.cfg.compRows_pos computeNodes97 computeNodes97_injective basis97
          challengeCoordinates97 publicCoordinates97 strictOrbit97 row0 q
    · intro q
      simpa [can, exPub, ex, exactFinalTransitionEnv, correctedTrace97] using
        canonical_gather_base_next sampledAssignment97
          family97.problem.cfg.compRows_pos computeNodes97 computeNodes97_injective basis97
          challengeCoordinates97 publicCoordinates97 strictOrbit97 row0 hi
          (by simpa [mul_comm] using computeNodes97_orbit row0 hi) q
    · intro role hrole
      rcases hrole with hlt | h61 | h62
      · let r : Fin 58 := ⟨role, hlt⟩
        have hc := canonical_gather_ext_core sampledAssignment97
          family97.problem.cfg.compRows_pos computeNodes97 computeNodes97_injective basis97
          challengeCoordinates97 publicCoordinates97 strictOrbit97 row0 r
        have hex : exPub.extTrace role =
            formRLeafCore basis97 (encodedRowAt sampledAssignment97 row0) r := by
          simp [exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow, hlt, r, formRLeafCore]
        have hc' : can.extTrace role =
            formRLeafCore basis97 (encodedRowAt sampledAssignment97 row0) r := by
          simpa [can, correctedTrace97, r, formRLeafCore] using hc
        exact hc'.trans hex.symm
      · have hr : role = (61 : Fin 63) := Fin.ext h61
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow,
          correctedTrace97] using canonical_gather_walkLine sampledAssignment97
            family97.problem.cfg.compRows_pos computeNodes97 computeNodes97_injective basis97
            challengeCoordinates97 publicCoordinates97 strictOrbit97 row0
      · have hr : role = (62 : Fin 63) := Fin.ext h62
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow,
          correctedTrace97] using canonical_gather_walkInv sampledAssignment97
            family97.problem.cfg.compRows_pos computeNodes97 computeNodes97_injective basis97
            challengeCoordinates97 publicCoordinates97 strictOrbit97 row0
    · intro role hrole
      rcases hrole with hlt | h61 | h62
      · let r : Fin 58 := ⟨role, hlt⟩
        have hc := canonical_gather_ext_core_next sampledAssignment97
          family97.problem.cfg.compRows_pos computeNodes97 computeNodes97_injective basis97
          challengeCoordinates97 publicCoordinates97 strictOrbit97 row0 hi
          (by simpa [mul_comm] using computeNodes97_orbit row0 hi) r
        have hex : exPub.extTraceNext role =
            formRLeafCore basis97
              (encodedRowAt sampledAssignment97 ⟨(row0 : ℕ) + 1, hi⟩) r := by
          simp [exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow, hlt, r, formRLeafCore]
        have hc' : can.extTraceNext role =
            formRLeafCore basis97
              (encodedRowAt sampledAssignment97 ⟨(row0 : ℕ) + 1, hi⟩) r := by
          simpa [can, correctedTrace97, r, formRLeafCore] using hc
        exact hc'.trans hex.symm
      · have hr : role = (61 : Fin 63) := Fin.ext h61
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow,
          correctedTrace97, Nat.add_assoc] using
            canonical_gather_walkLine_next sampledAssignment97
              family97.problem.cfg.compRows_pos computeNodes97 computeNodes97_injective basis97
              challengeCoordinates97 publicCoordinates97 strictOrbit97 row0 hi
              (by simpa [mul_comm] using computeNodes97_orbit row0 hi)
      · have hr : role = (62 : Fin 63) := Fin.ext h62
        subst role
        simpa [can, exPub, ex, exactFinalTransitionEnv, exactFinalExtensionRow,
          correctedTrace97, Nat.add_assoc] using
            canonical_gather_walkInv_next sampledAssignment97
              family97.problem.cfg.compRows_pos computeNodes97 computeNodes97_injective basis97
              challengeCoordinates97 publicCoordinates97 strictOrbit97 row0 hi
              (by simpa [mul_comm] using computeNodes97_orbit row0 hi)
    · intro q
      simpa [can, exPub, ex, exactFinalTransitionEnv, correctedTrace97] using
        canonical_gather_challenge sampledAssignment97 family97.problem.cfg.compRows_pos
          computeNodes97 basis97 challengeCoordinates97 publicCoordinates97 strictOrbit97
          challengeCoordinates97_exact row0 q
    · intro q; rfl
    · intro q; rfl
    · exact htResidual
  have hpub : t.eval exPub = t.eval ex := by
    apply CorrectedFinalTypedExpr.eval_eq_of_publicFree (hexp := by rfl)
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · intro q; rfl
    · exact htPublic
    · intro q; rfl
    · intro q; rfl
  have hex : t.eval ex = 0 := by
    rw [← correctedLowerFinal_eval ex e t htLower]
    exact exact_finalNonIOSourceFamilies17
      sampledAssignment97 sampled_obligations97 row0 hi e he
  rw [hsame, hpub, hex]

theorem row0_full_collision_good :
    let env := gatherCorrectedFinalTypedEnv basis97
      (Nock.Framework.Reify.envOfTrace correctedTrace97 strictOrbit97.ω
        (computeNodes97 row0) challengeCoordinates97 publicCoordinates97)
    FinalComputeCollisionFree env.toSourceEnv := by
  dsimp only
  intro es hes _ e he
  exact canonical_row0_nonIO_source_zero e
    (List.mem_flatten.mpr ⟨es, hes, he⟩)

/-- The release conclusion is obtained through the packaged `conditional_row_decode` field, on
the accepted corrected canonical 199/98 trace and the actual nonterminal row-zero environment. -/
theorem row0_decoded_via_conditional_row_decode (hbasis : FormRBasis basis97) :
    CorrectedDecodedTransitionSources
      (gatherCorrectedFinalTypedEnv basis97
        (Nock.Framework.Reify.envOfTrace correctedTrace97 strictOrbit97.ω
          (computeNodes97 row0) challengeCoordinates97 publicCoordinates97)) := by
  exact (computeRealization97 hbasis).conditional_row_decode correctedTrace97
    (corrected_trace97_satisfies hbasis) (computeNodes97 row0) row0_in_domain
    row0_not_last

theorem strict_release_nonterminal_fixture (hbasis : FormRBasis basis97) :
    family97.problem.cfg.compRows = 2 ∧
      parentPub.state = .s4 ∧ ComputeTable.fanoutComp parentPub.state = 1 ∧
      parentOut 0 = some childLabel ∧
      exec97.derivedRequestIO.Nodup ∧
      sampledAssignment97.ComputeSampledObligations ∧
      RAP.SatisfiesWithPreprocessing
        (ProductionNamedComputeRAP family97.problem.cfg.compRows_pos computeNodes97 basis97
          challengeCoordinates97 publicCoordinates97 strictOrbit97)
        correctedTrace97 ∧
      CorrectedDecodedTransitionSources
        (gatherCorrectedFinalTypedEnv basis97
          (Nock.Framework.Reify.envOfTrace correctedTrace97 strictOrbit97.ω
            (computeNodes97 row0) challengeCoordinates97 publicCoordinates97)) :=
  ⟨rfl, parent_is_genuinely_nonterminal.1, parent_is_genuinely_nonterminal.2.1,
    parent_is_genuinely_nonterminal.2.2, derived_requests_nodup, sampled_obligations97,
    corrected_trace97_satisfies hbasis, row0_decoded_via_conditional_row_decode hbasis⟩

#print axioms sampled_assignment_requests_nodup
#print axioms no_sampled_assignment_with_duplicate_request
#print axioms p2_duplicate_request_not_finite_sampleable
#print axioms parent_accepts
#print axioms child_accepts
#print axioms computeTree_rvt
#print axioms derived_requests_nodup
#print axioms memory_rows_accepted
#print axioms sampled_obligations97
#print axioms corrected_trace97_satisfies
#print axioms row0_not_last
#print axioms row0_full_collision_good
#print axioms row0_decoded_via_conditional_row_decode
#print axioms strict_release_nonterminal_fixture

end
end Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
