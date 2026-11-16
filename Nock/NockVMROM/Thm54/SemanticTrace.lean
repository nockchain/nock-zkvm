import Nock.NockVMROM.Thm54.OpcodeSemantics
import Nock.NockVMROM.Thm54.NounRealization
import Nock.Agreement

/-!
# Exact semantic-row data and finite comparison census

It does not decode fingerprints and no certificate
stores an opcode theorem's conclusion.  It packages concrete nouns, local collision events, and
memory lookups, then applies the production per-opcode theorems in
`OpcodeSemantics` through an eleven-constructor state-indexed certificate.

The authoritative row parameter of `ComputeRowSemanticData` is an actual
`ExactExecution.computeRowAt`; an execution data bundle contains no second row function.  The finite
comparison census is the flattening of the row-local lists of seed-independent noun pairs.

Every local `StepROM` and `evalFBy` result is derived by cases.  The remaining global seam is
contextual maximal-DFS scheduling: lifting those local steps through parent successor contexts
using canonical row order and the proven `Fcomp`/`childLinkComp` topology.
-/

namespace Nock.NockVMROM.Thm54.SemanticTrace

open scoped Classical
open Nock Nock.Noun Nock.Walk
open ComputeTable

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Proof-carrying row ingredients -/

/-- A realized recursive-call triple, retaining the exact three fingerprints it realizes. -/
structure RealizedCall (z : K) where
  subjectFP : FP K
  formulaFP : FP K
  resultFP : FP K
  realization : OpcodeSemantics.CallRealization z subjectFP formulaFP resultFP

/-- A size-window witness with its seed-independent noun exposed. -/
structure WindowedNoun (z : K) where
  noun : Noun
  window : OpcodeSemantics.SizeWindow z noun

/-- A served global-carry lookup tied to the exact table memory record it realizes. -/
structure ServedNounLookup (z : K) where
  record : MemRec K
  root : Noun
  axis : ℕ
  child : Noun
  realization : OpcodeSemantics.RealizesMemRec z record root child axis
  served : GlobalCarryAxis.ServedLookup
    (GlobalCarryRecognizer.ofNoun root 1) axis child

/-- OP9's updated axis premise.

The production `s9_vcomp_semantics` theorem now consumes this pair-local faithfulness premise and
derives `tail.head = atom axis` from the strengthened `Vcomp` axis-shape gate.  No free noun-syntax
equality and no duplicate verifier equation are stored here. -/
structure AxisAtomComparisonCertificate (z : K) (q : ℕ) (dec : Dec K)
    (tail : OpcodeSemantics.TailRealization z dec) where
  axis : ℕ
  faithful : OpcodeSemantics.PairFaithful z q tail.head (.atom axis)

/-- Why a comparison is used. -/
inductive ComparisonRole where
  | opcodeHead
  | formulaCons
  | tailCons
  | branchTailCons
  | recursiveSubject
  | recursiveFormula
  | recursiveResult
  | equalityOperand
  | producedResult
  | axisAtom
deriving DecidableEq, Repr

/-- One entry in the finite NPR comparison census.  Nouns, unlike fingerprints, are independent
of the sampled seed. -/
structure ComparisonUse where
  role : ComparisonRole
  left : Noun
  right : Noun

def ComparisonUse.pair (c : ComparisonUse) : Noun × Noun :=
  (c.left, c.right)

/-- Every noun in one comparison lies in the paper's leaf window `Λ`. -/
def ComparisonUse.LeavesBounded (Λ : ℕ) (c : ComparisonUse) : Prop :=
  c.left.leaves ≤ Λ ∧ c.right.leaves ≤ Λ

/-! ### State coverage matrix -/

def requiredTailRealizations : State → ℕ
  | .s2 | .s5 | .s6 | .s7 | .s8 | .s9 => 1
  | _ => 0

def requiredBranchTailRealizations : State → ℕ
  | .s6 => 1
  | _ => 0

def requiredCallRealizations : State → ℕ
  | .s0 | .s1 => 0
  | .s2 => 3
  | .s3 | .s4 => 1
  | .s5 | .s6 | .s7 | .s8 | .s9 | .cons => 2

def requiredSizeWindows : State → ℕ
  | .s3 | .s4 | .s6 => 1
  | _ => 0

def requiredServedLookups : State → ℕ
  | .s0 | .s9 => 1
  | _ => 0

def requiredAxisAtomGates : State → ℕ
  | .s9 => 1
  | _ => 0

/-- Exact comparison-role matrix of the production opcode theorem signatures.

The maximum is ten: OP2 and OP6.  OP9 has eight entries because its axis atom is deliberately a
PairFaithful verifier-gate reflection rather than a free syntax equation. -/
def requiredComparisonRoles : State → List ComparisonRole
  | .s0 =>
      [.opcodeHead, .formulaCons, .recursiveFormula]
  | .s1 =>
      [.opcodeHead, .formulaCons, .producedResult]
  | .s2 =>
      [.opcodeHead, .formulaCons, .tailCons,
        .recursiveSubject, .recursiveFormula,
        .recursiveSubject, .recursiveFormula,
        .recursiveSubject, .recursiveFormula, .producedResult]
  | .s3 =>
      [.opcodeHead, .formulaCons, .recursiveSubject, .recursiveFormula, .producedResult]
  | .s4 =>
      [.opcodeHead, .formulaCons, .recursiveSubject, .recursiveFormula, .producedResult]
  | .s5 =>
      [.opcodeHead, .formulaCons, .tailCons,
        .recursiveSubject, .recursiveFormula,
        .recursiveSubject, .recursiveFormula,
        .equalityOperand, .producedResult]
  | .s6 =>
      [.opcodeHead, .formulaCons, .tailCons, .branchTailCons,
        .recursiveSubject, .recursiveFormula, .recursiveFormula,
        .recursiveSubject, .recursiveFormula, .producedResult]
  | .s7 =>
      [.opcodeHead, .formulaCons, .tailCons,
        .recursiveSubject, .recursiveFormula,
        .recursiveSubject, .recursiveFormula, .producedResult]
  | .s8 =>
      [.opcodeHead, .formulaCons, .tailCons,
        .recursiveSubject, .recursiveFormula,
        .recursiveSubject, .recursiveFormula, .producedResult]
  | .s9 =>
      [.opcodeHead, .formulaCons, .tailCons, .axisAtom,
        .recursiveSubject, .recursiveFormula, .recursiveSubject, .producedResult]
  | .cons =>
      [.formulaCons, .recursiveSubject, .recursiveFormula,
        .recursiveSubject, .recursiveFormula, .producedResult]

theorem requiredComparisonRoles_length_le (st : State) :
    (requiredComparisonRoles st).length ≤ 10 := by
  cases st <;> decide

/-- Exact state-dependent side conditions not represented by pair comparisons.

Only OP0 and OP9 expose served lookups.  OP4's total modular target is a comparison occurrence, not
an overflow side condition. -/
structure RowStateNeeds (z : K) (st : State) where
  served : List (ServedNounLookup z)
  served_count : served.length = requiredServedLookups st

/-- Non-circular semantic input data for one *fixed* production compute row.

This structure deliberately has no `successor`, evaluator fuel, `StepROM`, `evalFBy`, or function
returning those conclusions.  The row-local maximum is ten comparisons (attained by OP2 and OP6);
OP9's updated axis PairFaithful premise is one explicitly listed comparison. -/
structure ComputeRowSemanticData (q Λ : ℕ)
    (row : State × DTcomp K) where
  root : OpcodeSemantics.RootRealization row.2.1 row.2.2.1 row.2.2.2
  tails : List (OpcodeSemantics.TailRealization row.2.1.z row.2.2.2)
  branchTails :
    List (OpcodeSemantics.BranchTailRealization row.2.1.z row.2.2.2)
  calls : List (RealizedCall row.2.1.z)
  windows : List (WindowedNoun row.2.1.z)
  axisGates : List
    (Σ tail : OpcodeSemantics.TailRealization row.2.1.z row.2.2.2,
      AxisAtomComparisonCertificate row.2.1.z q row.2.2.2 tail)
  tails_count : tails.length = requiredTailRealizations row.1
  branchTails_count :
    branchTails.length = requiredBranchTailRealizations row.1
  calls_count : calls.length = requiredCallRealizations row.1
  windows_count : windows.length = requiredSizeWindows row.1
  axisGates_count : axisGates.length = requiredAxisAtomGates row.1
  realizedNouns : List Noun
  subject_mem : root.subject ∈ realizedNouns
  formula_mem : root.formula ∈ realizedNouns
  result_mem : root.result ∈ realizedNouns
  bounded : ∀ n ∈ realizedNouns, FieldEmbedding.BoundedBy q n
  comparisons : List ComparisonUse
  comparison_faithful :
    ∀ c ∈ comparisons,
      OpcodeSemantics.PairFaithful row.2.1.z q c.left c.right
  comparison_leaves :
    ∀ c ∈ comparisons, c.LeavesBounded Λ
  comparison_roles :
    comparisons.map ComparisonUse.role = requiredComparisonRoles row.1
  axisGate_listed :
    ∀ gate ∈ axisGates,
      { role := .axisAtom
        left := gate.1.head
        right := .atom gate.2.axis } ∈ comparisons
  /-- Every axis-gate tail is one of the row's `TailRealization`s.

  Honest rows already use the same object for both lists (`BoundSemanticTrace`,
  Op9 `parentTailR`).  Without this, `decompNoun.f_th` (reads `tails`) and
  the OP9 `PairFaithful` gate (reads `axisGates`) can name different nouns, so
  C5 cannot inhabit `AxisAtomPremises` -/
  axisGate_tail_mem :
    ∀ gate ∈ axisGates, gate.1 ∈ tails
  needs : RowStateNeeds row.2.1.z row.1

namespace ComputeRowSemanticData

theorem root_bounded {q Λ : ℕ} {row : State × DTcomp K}
    (w : ComputeRowSemanticData q Λ row) :
    FieldEmbedding.BoundedBy q w.root.subject ∧
      FieldEmbedding.BoundedBy q w.root.formula ∧
      FieldEmbedding.BoundedBy q w.root.result :=
  ⟨w.bounded _ w.subject_mem, w.bounded _ w.formula_mem,
    w.bounded _ w.result_mem⟩

theorem comparison_count {q Λ : ℕ} {row : State × DTcomp K}
    (w : ComputeRowSemanticData q Λ row) :
    w.comparisons.length ≤ 10 := by
  calc
    w.comparisons.length = (w.comparisons.map ComparisonUse.role).length := by simp
    _ = (requiredComparisonRoles row.1).length :=
      congrArg List.length w.comparison_roles
    _ ≤ 10 := requiredComparisonRoles_length_le row.1

theorem axisGate_pairFaithful {q Λ : ℕ} {row : State × DTcomp K}
    (w : ComputeRowSemanticData q Λ row)
    (gate : Σ tail : OpcodeSemantics.TailRealization row.2.1.z row.2.2.2,
      AxisAtomComparisonCertificate row.2.1.z q row.2.2.2 tail)
    (_hgate : gate ∈ w.axisGates) :
    OpcodeSemantics.PairFaithful row.2.1.z q gate.1.head (.atom gate.2.axis) :=
  gate.2.faithful

/-- Seed, public, and private halves of the authoritative row, read from the
index of `ComputeRowSemanticData`. -/
def inpZ {q Λ : ℕ} {row : State × DTcomp K}
    (_w : ComputeRowSemanticData q Λ row) : K :=
  row.2.1.z

def rowPub {q Λ : ℕ} {row : State × DTcomp K}
    (_w : ComputeRowSemanticData q Λ row) : Pub K :=
  row.2.2.1

def rowDec {q Λ : ℕ} {row : State × DTcomp K}
    (_w : ComputeRowSemanticData q Λ row) : Dec K :=
  row.2.2.2

def rowState {q Λ : ℕ} {row : State × DTcomp K}
    (_w : ComputeRowSemanticData q Λ row) : State :=
  row.1

end ComputeRowSemanticData

theorem count_map_role_eq_length_filter
    (l : List ComparisonUse) (role : ComparisonRole) :
    (l.map ComparisonUse.role).count role =
      (l.filter (fun c => c.role = role)).length := by
  induction l with
  | nil => simp
  | cons c cs ih =>
      by_cases h : c.role = role
      · simp [h, List.count_cons, ih]
      · simp [h, List.count_cons, ih]

theorem exists_eq_singleton_of_length_one {α : Type*} {l : List α}
    (h : l.length = 1) : ∃ x, l = [x] := by
  match l with
  | [] => simp at h
  | [x] => exact ⟨x, rfl⟩
  | _ :: _ :: _ => simp at h

theorem requiredComparisonRoles_count_axisAtom (st : State) :
    (requiredComparisonRoles st).count ComparisonRole.axisAtom =
      if st = .s9 then 1 else 0 := by
  cases st <;> decide

/-! ## State-indexed local opcode certificates -/

/-- Exact occurrence of a production comparison premise in the row census. -/
def ComparisonListed {q Λ : ℕ} {row : State × DTcomp K}
    (data : ComputeRowSemanticData q Λ row)
    (role : ComparisonRole) (left right : Noun) : Prop :=
  { role := role, left := left, right := right } ∈ data.comparisons

theorem ComparisonListed.faithful
    {q Λ : ℕ} {row : State × DTcomp K}
    {data : ComputeRowSemanticData q Λ row}
    {role : ComparisonRole} {left right : Noun}
    (h : ComparisonListed data role left right) :
    OpcodeSemantics.PairFaithful row.2.1.z q left right :=
  data.comparison_faithful _ h

/-- A comparison role that occurs once in the production matrix names a unique
noun pair on the row -/
theorem comparison_of_role_unique
    {q Λ : ℕ} {row : State × DTcomp K}
    (w : ComputeRowSemanticData q Λ row)
    (role : ComparisonRole)
    (hcount : (requiredComparisonRoles row.1).count role = 1)
    {l₁ r₁ l₂ r₂ : Noun}
    (h₁ : ComparisonListed w role l₁ r₁)
    (h₂ : ComparisonListed w role l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  have hlen : (w.comparisons.filter (fun c => c.role = role)).length = 1 := by
    have hmap : (w.comparisons.map ComparisonUse.role).count role = 1 := by
      rw [w.comparison_roles, hcount]
    simpa [count_map_role_eq_length_filter] using hmap
  have h₁' :
      { role := role, left := l₁, right := r₁ } ∈
        w.comparisons.filter (fun c => c.role = role) :=
    List.mem_filter.mpr ⟨h₁, by simp⟩
  have h₂' :
      { role := role, left := l₂, right := r₂ } ∈
        w.comparisons.filter (fun c => c.role = role) :=
    List.mem_filter.mpr ⟨h₂, by simp⟩
  obtain ⟨c, hc⟩ := exists_eq_singleton_of_length_one hlen
  rw [hc] at h₁' h₂'
  simp only [List.mem_singleton] at h₁' h₂'
  exact ⟨congrArg ComparisonUse.left (h₁'.trans h₂'.symm),
    congrArg ComparisonUse.right (h₁'.trans h₂'.symm)⟩

/-- A non-circular local certificate indexed by the exact fixed row and its exact row data.

Each constructor stores only premises of its matching production opcode theorem. -/
inductive LocalOpcodeCertificate (q Λ : ℕ) :
    {row : State × DTcomp K} → ComputeRowSemanticData q Λ row → Type
  | s0 {inp pub dec}
      (data : ComputeRowSemanticData q Λ (.s0, (inp, pub, dec)))
      (fuel axis : ℕ)
      (hstate : pub.state = .s0) (hz : inp.z ≠ 0)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hhead : ComparisonListed data .opcodeHead data.root.head (.atom 0))
      (hformula : ComparisonListed data .formulaCons data.root.formula
        (.cell data.root.head data.root.tail))
      (htail : ComparisonListed data .recursiveFormula data.root.tail (.atom axis))
      (hmr : OpcodeSemantics.RealizesMemRec inp.z pub.mr2
        data.root.subject data.root.result axis)
      (hserved : GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun data.root.subject 1) axis data.root.result)
      (hv : Vcomp inp pub dec) :
      LocalOpcodeCertificate q Λ data
  | s1 {inp pub dec}
      (data : ComputeRowSemanticData q Λ (.s1, (inp, pub, dec)))
      (fuel : ℕ)
      (hstate : pub.state = .s1) (hz : inp.z ≠ 0)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hhead : ComparisonListed data .opcodeHead data.root.head (.atom 1))
      (hformula : ComparisonListed data .formulaCons data.root.formula
        (.cell data.root.head data.root.tail))
      (hresult : ComparisonListed data .producedResult data.root.result data.root.tail)
      (hv : Vcomp inp pub dec) :
      LocalOpcodeCertificate q Λ data
  | s2 {inp pub dec}
      (data : ComputeRowSemanticData q Λ (.s2, (inp, pub, dec)))
      (fuel : ℕ)
      (tail : OpcodeSemantics.TailRealization inp.z dec)
      (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
      (call2 : OpcodeSemantics.CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
      (call3 : OpcodeSemantics.CallRealization inp.z pub.sf3_s pub.sf3_f pub.sf3_e)
      (hstate : pub.state = .s2) (hz : inp.z ≠ 0)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hhead : ComparisonListed data .opcodeHead data.root.head (.atom 2))
      (hformula : ComparisonListed data .formulaCons data.root.formula
        (.cell data.root.head data.root.tail))
      (htail : ComparisonListed data .tailCons data.root.tail (.cell tail.head tail.tail))
      (h1s : ComparisonListed data .recursiveSubject call1.subject data.root.subject)
      (h1f : ComparisonListed data .recursiveFormula call1.formula tail.head)
      (h2s : ComparisonListed data .recursiveSubject call2.subject data.root.subject)
      (h2f : ComparisonListed data .recursiveFormula call2.formula tail.tail)
      (h3s : ComparisonListed data .recursiveSubject call3.subject call1.result)
      (h3f : ComparisonListed data .recursiveFormula call3.formula call2.result)
      (hresult : ComparisonListed data .producedResult data.root.result call3.result)
      (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
        some call1.result)
      (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
        some call2.result)
      (hcall3 : FieldEmbedding.evalFBy q fuel call3.subject call3.formula =
        some call3.result)
      (hv : Vcomp inp pub dec) :
      LocalOpcodeCertificate q Λ data
  | s3 {inp pub dec}
      (data : ComputeRowSemanticData q Λ (.s3, (inp, pub, dec)))
      (fuel : ℕ)
      (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
      (hstate : pub.state = .s3) (hz : inp.z ≠ 0)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hhead : ComparisonListed data .opcodeHead data.root.head (.atom 3))
      (hformula : ComparisonListed data .formulaCons data.root.formula
        (.cell data.root.head data.root.tail))
      (h1s : ComparisonListed data .recursiveSubject call1.subject data.root.subject)
      (h1f : ComparisonListed data .recursiveFormula call1.formula data.root.tail)
      (hresult : ComparisonListed data .producedResult data.root.result
        (Noun.wut call1.result))
      (hsize : OpcodeSemantics.SizeWindow inp.z call1.result)
      (hcall : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
        some call1.result)
      (hv : Vcomp inp pub dec) :
      LocalOpcodeCertificate q Λ data
  | s4 {inp pub dec}
      (data : ComputeRowSemanticData q Λ (.s4, (inp, pub, dec)))
      (fuel : ℕ)
      (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
      (hstate : pub.state = .s4) (hz : inp.z ≠ 0)
      (hq : q = ringChar K)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hhead : ComparisonListed data .opcodeHead data.root.head (.atom 4))
      (hformula : ComparisonListed data .formulaCons data.root.formula
        (.cell data.root.head data.root.tail))
      (h1s : ComparisonListed data .recursiveSubject call1.subject data.root.subject)
      (h1f : ComparisonListed data .recursiveFormula call1.formula data.root.tail)
      (hresult : ComparisonListed data .producedResult data.root.result
        (OpcodeSemantics.incMod (ringChar K) call1.result))
      (hsize : OpcodeSemantics.SizeWindow inp.z call1.result)
      (hcall : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
        some call1.result)
      (hv : Vcomp inp pub dec) :
      LocalOpcodeCertificate q Λ data
  | s5 {inp pub dec}
      (data : ComputeRowSemanticData q Λ (.s5, (inp, pub, dec)))
      (fuel : ℕ)
      (tail : OpcodeSemantics.TailRealization inp.z dec)
      (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
      (call2 : OpcodeSemantics.CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
      (hstate : pub.state = .s5) (hz : inp.z ≠ 0)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hhead : ComparisonListed data .opcodeHead data.root.head (.atom 5))
      (hformula : ComparisonListed data .formulaCons data.root.formula
        (.cell data.root.head data.root.tail))
      (htail : ComparisonListed data .tailCons data.root.tail (.cell tail.head tail.tail))
      (h1s : ComparisonListed data .recursiveSubject call1.subject data.root.subject)
      (h1f : ComparisonListed data .recursiveFormula call1.formula tail.head)
      (h2s : ComparisonListed data .recursiveSubject call2.subject data.root.subject)
      (h2f : ComparisonListed data .recursiveFormula call2.formula tail.tail)
      (hcompare : ComparisonListed data .equalityOperand call1.result call2.result)
      (hresult : ComparisonListed data .producedResult data.root.result
        (Noun.tis call1.result call2.result))
      (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
        some call1.result)
      (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
        some call2.result)
      (hv : Vcomp inp pub dec) :
      LocalOpcodeCertificate q Λ data
  | s6 {inp pub dec}
      (data : ComputeRowSemanticData q Λ (.s6, (inp, pub, dec)))
      (fuel : ℕ)
      (tail : OpcodeSemantics.TailRealization inp.z dec)
      (branch : OpcodeSemantics.BranchTailRealization inp.z dec)
      (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
      (call2 : OpcodeSemantics.CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
      (hstate : pub.state = .s6) (hz : inp.z ≠ 0) (hq : 1 < q)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hhead : ComparisonListed data .opcodeHead data.root.head (.atom 6))
      (hformula : ComparisonListed data .formulaCons data.root.formula
        (.cell data.root.head data.root.tail))
      (htail : ComparisonListed data .tailCons data.root.tail (.cell tail.head tail.tail))
      (hbranchTail : ComparisonListed data .branchTailCons tail.tail
        (.cell branch.head branch.tail))
      (h1s : ComparisonListed data .recursiveSubject call1.subject data.root.subject)
      (h1fZero : ComparisonListed data .recursiveFormula call1.formula branch.head)
      (h1fOne : ComparisonListed data .recursiveFormula call1.formula branch.tail)
      (h2s : ComparisonListed data .recursiveSubject call2.subject data.root.subject)
      (h2f : ComparisonListed data .recursiveFormula call2.formula tail.head)
      (hresult : ComparisonListed data .producedResult data.root.result call1.result)
      (hconditionBound : FieldEmbedding.BoundedBy q call2.result)
      (hconditionSize : OpcodeSemantics.SizeWindow inp.z call2.result)
      (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
        some call1.result)
      (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
        some call2.result)
      (hv : Vcomp inp pub dec) :
      LocalOpcodeCertificate q Λ data
  | s7 {inp pub dec}
      (data : ComputeRowSemanticData q Λ (.s7, (inp, pub, dec)))
      (fuel : ℕ)
      (tail : OpcodeSemantics.TailRealization inp.z dec)
      (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
      (call2 : OpcodeSemantics.CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
      (hstate : pub.state = .s7) (hz : inp.z ≠ 0)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hhead : ComparisonListed data .opcodeHead data.root.head (.atom 7))
      (hformula : ComparisonListed data .formulaCons data.root.formula
        (.cell data.root.head data.root.tail))
      (htail : ComparisonListed data .tailCons data.root.tail (.cell tail.head tail.tail))
      (h2s : ComparisonListed data .recursiveSubject call2.subject data.root.subject)
      (h2f : ComparisonListed data .recursiveFormula call2.formula tail.head)
      (h1s : ComparisonListed data .recursiveSubject call1.subject call2.result)
      (h1f : ComparisonListed data .recursiveFormula call1.formula tail.tail)
      (hresult : ComparisonListed data .producedResult data.root.result call1.result)
      (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
        some call1.result)
      (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
        some call2.result)
      (hv : Vcomp inp pub dec) :
      LocalOpcodeCertificate q Λ data
  | s8 {inp pub dec}
      (data : ComputeRowSemanticData q Λ (.s8, (inp, pub, dec)))
      (fuel : ℕ)
      (tail : OpcodeSemantics.TailRealization inp.z dec)
      (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
      (call2 : OpcodeSemantics.CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
      (hstate : pub.state = .s8) (hz : inp.z ≠ 0)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hhead : ComparisonListed data .opcodeHead data.root.head (.atom 8))
      (hformula : ComparisonListed data .formulaCons data.root.formula
        (.cell data.root.head data.root.tail))
      (htail : ComparisonListed data .tailCons data.root.tail (.cell tail.head tail.tail))
      (h2s : ComparisonListed data .recursiveSubject call2.subject data.root.subject)
      (h2f : ComparisonListed data .recursiveFormula call2.formula tail.head)
      (h1s : ComparisonListed data .recursiveSubject call1.subject
        (.cell call2.result data.root.subject))
      (h1f : ComparisonListed data .recursiveFormula call1.formula tail.tail)
      (hresult : ComparisonListed data .producedResult data.root.result call1.result)
      (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
        some call1.result)
      (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
        some call2.result)
      (hv : Vcomp inp pub dec) :
      LocalOpcodeCertificate q Λ data
  | s9 {inp pub dec}
      (data : ComputeRowSemanticData q Λ (.s9, (inp, pub, dec)))
      (fuel axis : ℕ)
      (tail : OpcodeSemantics.TailRealization inp.z dec)
      (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
      (call2 : OpcodeSemantics.CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
      (hstate : pub.state = .s9) (hz : inp.z ≠ 0)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hhead : ComparisonListed data .opcodeHead data.root.head (.atom 9))
      (hformula : ComparisonListed data .formulaCons data.root.formula
        (.cell data.root.head data.root.tail))
      (htail : ComparisonListed data .tailCons data.root.tail (.cell tail.head tail.tail))
      (haxis : ComparisonListed data .axisAtom tail.head (.atom axis))
      (h1s : ComparisonListed data .recursiveSubject call1.subject data.root.subject)
      (h1f : ComparisonListed data .recursiveFormula call1.formula tail.tail)
      (h2s : ComparisonListed data .recursiveSubject call2.subject call1.result)
      (hresult : ComparisonListed data .producedResult data.root.result call2.result)
      (hmr : OpcodeSemantics.RealizesMemRec inp.z pub.mr3
        call1.result call2.formula axis)
      (hserved : GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun call1.result 1) axis call2.formula)
      (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
        some call1.result)
      (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
        some call2.result)
      (hv : Vcomp inp pub dec) :
      LocalOpcodeCertificate q Λ data
  | cons {inp pub dec}
      (data : ComputeRowSemanticData q Λ (.cons, (inp, pub, dec)))
      (fuel : ℕ)
      (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
      (call2 : OpcodeSemantics.CallRealization inp.z pub.sf2_s pub.sf2_f pub.sf2_e)
      (hstate : pub.state = .cons) (hz : inp.z ≠ 0)
      (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
      (hformula : ComparisonListed data .formulaCons data.root.formula
        (.cell data.root.head data.root.tail))
      (h1s : ComparisonListed data .recursiveSubject call1.subject data.root.subject)
      (h1f : ComparisonListed data .recursiveFormula call1.formula data.root.head)
      (h2s : ComparisonListed data .recursiveSubject call2.subject data.root.subject)
      (h2f : ComparisonListed data .recursiveFormula call2.formula data.root.tail)
      (hresult : ComparisonListed data .producedResult data.root.result
        (.cell call1.result call2.result))
      (hcall1 : FieldEmbedding.evalFBy q fuel call1.subject call1.formula =
        some call1.result)
      (hcall2 : FieldEmbedding.evalFBy q fuel call2.subject call2.formula =
        some call2.result)
      (hv : Vcomp inp pub dec) :
      LocalOpcodeCertificate q Λ data

namespace LocalOpcodeCertificate

/-- Local semantics is derived by cases from the production opcode theorems; no constructor stores
either conjunct of this conclusion. -/
theorem semantics {q Λ : ℕ} {row : State × DTcomp K}
    {data : ComputeRowSemanticData q Λ row}
    (cert : LocalOpcodeCertificate q Λ data) :
    ∃ (fuel : ℕ) (successor : Verb),
      Verb.StepROM (Verb.program data.root.subject data.root.formula) successor ∧
        FieldEmbedding.evalFBy q (fuel + 1) data.root.subject data.root.formula =
          some data.root.result := by
  cases cert with
  | s0 data fuel axis hstate hz hcast hhead hformula htail hmr hserved hv =>
      exact ⟨fuel, _,
        OpcodeSemantics.s0_vcomp_semantics hstate hz hcast data.root
          hhead.faithful hformula.faithful htail.faithful hmr hserved hv⟩
  | s1 data fuel hstate hz hcast hhead hformula hresult hv =>
      exact ⟨fuel, _,
        OpcodeSemantics.s1_vcomp_semantics hstate hz hcast data.root
          hhead.faithful hformula.faithful hresult.faithful hv⟩
  | s2 data fuel tail call1 call2 call3 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f h3s h3f hresult hcall1 hcall2 hcall3 hv =>
      exact ⟨fuel, _,
        OpcodeSemantics.s2_vcomp_semantics hstate hz hcast data.root tail call1 call2 call3
          hhead.faithful hformula.faithful htail.faithful
          h1s.faithful h1f.faithful h2s.faithful h2f.faithful
          h3s.faithful h3f.faithful hresult.faithful
          hcall1 hcall2 hcall3 hv⟩
  | s3 data fuel call1 hstate hz hcast hhead hformula h1s h1f hresult
      hsize hcall hv =>
      exact ⟨fuel, _,
        OpcodeSemantics.s3_vcomp_semantics hstate hz hcast data.root call1
          hhead.faithful hformula.faithful h1s.faithful h1f.faithful
          hresult.faithful hsize hcall hv⟩
  | s4 data fuel call1 hstate hz hq hcast hhead hformula h1s h1f hresult
      hsize hcall hv =>
      exact ⟨fuel, _,
        OpcodeSemantics.s4_vcomp_semantics hstate hz hq hcast data.root call1
          hhead.faithful hformula.faithful h1s.faithful h1f.faithful
          hresult.faithful hsize hcall hv⟩
  | s5 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h1s h1f h2s h2f hcompare hresult hcall1 hcall2 hv =>
      exact ⟨fuel, _,
        OpcodeSemantics.s5_vcomp_semantics hstate hz hcast data.root tail call1 call2
          hhead.faithful hformula.faithful htail.faithful
          h1s.faithful h1f.faithful h2s.faithful h2f.faithful
          hcompare.faithful hresult.faithful hcall1 hcall2 hv⟩
  | s6 data fuel tail branch call1 call2 hstate hz hq hcast hhead hformula htail
      hbranchTail h1s h1fZero h1fOne h2s h2f hresult hconditionBound
      hconditionSize hcall1 hcall2 hv =>
      exact ⟨fuel, _,
        OpcodeSemantics.s6_vcomp_semantics hstate hz hq hcast data.root tail branch call1 call2
          hhead.faithful hformula.faithful htail.faithful hbranchTail.faithful
          h1s.faithful h1fZero.faithful h1fOne.faithful
          h2s.faithful h2f.faithful hresult.faithful
          hconditionBound hconditionSize hcall1 hcall2 hv⟩
  | s7 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hcall1 hcall2 hv =>
      exact ⟨fuel, _,
        OpcodeSemantics.s7_vcomp_semantics hstate hz hcast data.root tail call1 call2
          hhead.faithful hformula.faithful htail.faithful
          h2s.faithful h2f.faithful h1s.faithful h1f.faithful
          hresult.faithful hcall1 hcall2 hv⟩
  | s8 data fuel tail call1 call2 hstate hz hcast hhead hformula htail
      h2s h2f h1s h1f hresult hcall1 hcall2 hv =>
      exact ⟨fuel, _,
        OpcodeSemantics.s8_vcomp_semantics hstate hz hcast data.root tail call1 call2
          hhead.faithful hformula.faithful htail.faithful
          h2s.faithful h2f.faithful h1s.faithful h1f.faithful
          hresult.faithful hcall1 hcall2 hv⟩
  | s9 data fuel axis tail call1 call2 hstate hz hcast hhead hformula htail
      haxis h1s h1f h2s hresult hmr hserved hcall1 hcall2 hv =>
      exact ⟨fuel, _,
        OpcodeSemantics.s9_vcomp_semantics hstate hz hcast data.root tail call1 call2
          hhead.faithful hformula.faithful htail.faithful haxis.faithful
          h1s.faithful h1f.faithful h2s.faithful hresult.faithful
          hmr hserved hcall1 hcall2 hv⟩
  | cons data fuel call1 call2 hstate hz hcast hformula h1s h1f h2s h2f
      hresult hcall1 hcall2 hv =>
      exact ⟨fuel, _,
        OpcodeSemantics.cons_vcomp_semantics hstate hz hcast data.root call1 call2
          hformula.faithful h1s.faithful h1f.faithful
          h2s.faithful h2f.faithful hresult.faithful hcall1 hcall2 hv⟩

end LocalOpcodeCertificate

/-! ## Canonical execution data and finite census -/

/-- Row-local data over the one canonical indexed BFS accessor.

Every bundle is parameterized by `exec.computeRowAt i`; there is no alternate row list or row
function.  `rowAccepted` also pins every row's complete `Inputs` record, hence its NPR seed, to the
single configuration challenge vector. -/
structure ExactExecutionSemanticData
    (q Λ : ℕ) (cfg : ExactConfig F K) (exec : ExactExecution cfg) where
  language : NounRealizedTraversableChainedSemanticExactLanguage q cfg exec
  rowAccepted :
    ∀ i : Fin cfg.compRows,
      ExactExecution.ComputeRowAccepted cfg (exec.computeRowAt i)
  rows :
    ∀ i : Fin cfg.compRows,
      ComputeRowSemanticData q Λ (exec.computeRowAt i)

namespace ExactExecutionSemanticData

theorem same_inputs
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : ExactExecutionSemanticData q Λ cfg exec) (i : Fin cfg.compRows) :
    (exec.computeRowAt i).2.1 = cfg.challenges.computeInputs :=
  (w.rowAccepted i).2.1

theorem same_seed
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : ExactExecutionSemanticData q Λ cfg exec) (i : Fin cfg.compRows) :
    (exec.computeRowAt i).2.1.z = cfg.challenges.z := by
  have h := congrArg (fun inp : Inputs K => inp.z) (w.same_inputs i)
  simpa [ChallengeVector.computeInputs] using h

/-- Production `Fcomp` topology, exposed on the same authoritative execution. -/
theorem computeTopology
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : ExactExecutionSemanticData q Λ cfg exec) :
    ComputeExactTraversalClause exec :=
  (computeExactTopology_iff_traversalClause exec).1
    w.language.traversable.compute_topology

end ExactExecutionSemanticData

/-- Production-derived local certificates for every canonical compute row. -/
structure ExactExecutionLocalCertificates
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (data : ExactExecutionSemanticData q Λ cfg exec) where
  rows :
    ∀ i : Fin cfg.compRows,
      LocalOpcodeCertificate q Λ (data.rows i)

namespace ExactExecutionLocalCertificates

/-- Every canonical row has a genuine one-step ROM prefix derived from its production opcode
theorem. -/
theorem allRowROMPrefixes
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {data : ExactExecutionSemanticData q Λ cfg exec}
    (certs : ExactExecutionLocalCertificates data) :
    ∀ i : Fin cfg.compRows,
      ∃ successor : Verb,
        Verb.TraceOfROM
          (Verb.program (data.rows i).root.subject (data.rows i).root.formula)
          [Verb.program (data.rows i).root.subject (data.rows i).root.formula,
            successor] := by
  intro i
  obtain ⟨_, successor, hstep, _⟩ := (certs.rows i).semantics
  exact ⟨successor, OpcodeSemantics.traceOfROM_pair hstep⟩

/-- The matching bounded field evaluator result is likewise derived row by row. -/
theorem allRowEvalF
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    {data : ExactExecutionSemanticData q Λ cfg exec}
    (certs : ExactExecutionLocalCertificates data) :
    ∀ i : Fin cfg.compRows,
      ∃ fuel : ℕ,
        FieldEmbedding.evalFBy q (fuel + 1)
          (data.rows i).root.subject (data.rows i).root.formula =
            some (data.rows i).root.result := by
  intro i
  obtain ⟨fuel, _, _, heval⟩ := (certs.rows i).semantics
  exact ⟨fuel, heval⟩

end ExactExecutionLocalCertificates

/-- Canonical finite census: concatenate the declared comparisons in canonical compute-row order. -/
def comparisonCensus
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : ExactExecutionSemanticData q Λ cfg exec) : List ComparisonUse :=
  (List.ofFn fun i : Fin cfg.compRows => (w.rows i).comparisons).flatMap id

theorem comparison_mem_census
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : ExactExecutionSemanticData q Λ cfg exec)
    (i : Fin cfg.compRows) (c : ComparisonUse)
    (hc : c ∈ (w.rows i).comparisons) :
    c ∈ comparisonCensus w := by
  rw [comparisonCensus, List.mem_flatMap]
  exact ⟨(w.rows i).comparisons, by simp, hc⟩

/-- OP9's updated axis comparison is an actual census entry, not an untracked equality premise. -/
theorem axisGate_mem_census
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : ExactExecutionSemanticData q Λ cfg exec)
    (i : Fin cfg.compRows)
    (gate : Σ tail : OpcodeSemantics.TailRealization
        (exec.computeRowAt i).2.1.z (exec.computeRowAt i).2.2.2,
      AxisAtomComparisonCertificate
        (exec.computeRowAt i).2.1.z q (exec.computeRowAt i).2.2.2 tail)
    (hgate : gate ∈ (w.rows i).axisGates) :
    { role := .axisAtom
      left := gate.1.head
      right := .atom gate.2.axis } ∈ comparisonCensus w :=
  comparison_mem_census w i _ ((w.rows i).axisGate_listed gate hgate)

/-- Completeness lookup by canonical row, with the row's state available in the conclusion. -/
theorem comparison_lookup_by_state_row
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : ExactExecutionSemanticData q Λ cfg exec)
    (i : Fin cfg.compRows) (c : ComparisonUse)
    (hc : c ∈ (w.rows i).comparisons) :
    c ∈ comparisonCensus w ∧
      (exec.computeRowAt i).1 = (exec.computeRowAt i).1 :=
  ⟨comparison_mem_census w i c hc, rfl⟩

theorem census_pairFaithful
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : ExactExecutionSemanticData q Λ cfg exec)
    {c : ComparisonUse} (hc : c ∈ comparisonCensus w) :
    OpcodeSemantics.PairFaithful cfg.challenges.z q c.left c.right := by
  rw [comparisonCensus, List.mem_flatMap] at hc
  obtain ⟨rowComparisons, hrow, hc⟩ := hc
  simp only [List.mem_ofFn] at hrow
  obtain ⟨i, rfl⟩ := hrow
  rw [← w.same_seed i]
  exact (w.rows i).comparison_faithful c hc

theorem census_sepSeed
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : ExactExecutionSemanticData q Λ cfg exec)
    {c : ComparisonUse} (hc : c ∈ comparisonCensus w) :
    GlobalCarryRecognizer.SepSeed cfg.challenges.z c.left c.right :=
  (census_pairFaithful w hc).separates

theorem census_leaves_bounded
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : ExactExecutionSemanticData q Λ cfg exec)
    {c : ComparisonUse} (hc : c ∈ comparisonCensus w) :
    c.LeavesBounded Λ := by
  rw [comparisonCensus, List.mem_flatMap] at hc
  obtain ⟨rowComparisons, hrow, hc⟩ := hc
  simp only [List.mem_ofFn] at hrow
  obtain ⟨i, rfl⟩ := hrow
  exact (w.rows i).comparison_leaves c hc

private theorem flatMap_length_le
    {α β : Type*} (bound : ℕ) (xs : List α) (f : α → List β)
    (h : ∀ x ∈ xs, (f x).length ≤ bound) :
    (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, (f y).length ≤ bound :=
        fun y hy => h y (by simp [hy])
      have hi := ih hxs
      calc
        (f x).length + (List.flatMap f xs).length
            ≤ bound + xs.length * bound := Nat.add_le_add hx hi
        _ = (xs.length + 1) * bound := by
          simp [Nat.add_mul, Nat.add_comm]

/-- At most ten pair-local NPR comparisons per compute row.  Duplicate noun pairs are retained:
the bound counts consumed comparison occurrences, not merely distinct pairs. -/
theorem comparisonCensus_count_le
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : ExactExecutionSemanticData q Λ cfg exec) :
    (comparisonCensus w).length ≤ 10 * cfg.compRows := by
  unfold comparisonCensus
  have h := flatMap_length_le 10
    (List.ofFn fun i : Fin cfg.compRows => (w.rows i).comparisons) id
    (fun xs hxs => by
      simp only [List.mem_ofFn] at hxs
      obtain ⟨i, rfl⟩ := hxs
      exact (w.rows i).comparison_count)
  simpa [Nat.mul_comm] using h

/-! ## Production-derived row prefixes and the exact DFS seam -/

def rootRowIndex (cfg : ExactConfig F K) : Fin cfg.compRows :=
  ⟨0, cfg.compRows_pos⟩

/-- Strongest unconditional assembly currently available: exact `Fcomp`/`childLinkComp` topology
on the authoritative execution and a production-derived immediate ROM prefix for every canonical
row. -/
def GlobalRowPrefixTrace
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (data : ExactExecutionSemanticData q Λ cfg exec)
    (_certs : ExactExecutionLocalCertificates data) : Prop :=
  ComputeExactTraversalClause exec ∧
    ∀ i : Fin cfg.compRows,
      ∃ successor : Verb,
        Verb.TraceOfROM
          (Verb.program (data.rows i).root.subject (data.rows i).root.formula)
          [Verb.program (data.rows i).root.subject (data.rows i).root.formula,
            successor]

theorem globalRowPrefixTrace
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (data : ExactExecutionSemanticData q Λ cfg exec)
    (certs : ExactExecutionLocalCertificates data) :
    GlobalRowPrefixTrace data certs :=
  ⟨data.computeTopology, certs.allRowROMPrefixes⟩

/-- **Exact remaining seam.**

This proposition is not a local-semantics assumption: every local `StepROM` has already been
derived by `LocalOpcodeCertificate.semantics`.  The missing theorem must instead use canonical row
ordering and `ComputeExactTraversalClause`'s `Fcomp`/`childLinkComp` facts to lift child reductions
through their parent successor contexts in maximal-DFS order, with compatible recursive fuel, and
concatenate the row prefixes into this root trace. -/
def GlobalDFSScheduling
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (data : ExactExecutionSemanticData q Λ cfg exec)
    (_certs : ExactExecutionLocalCertificates data) : Prop :=
  let root := data.rows (rootRowIndex cfg)
  ∃ trace : List Verb,
    Verb.TraceOfROM (Verb.program root.root.subject root.root.formula) trace ∧
      trace.getLast? = some (Verb.ofNoun root.root.result)

theorem validROM_of_globalDFSScheduling
    {q Λ : ℕ} {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (data : ExactExecutionSemanticData q Λ cfg exec)
    (certs : ExactExecutionLocalCertificates data)
    (hschedule : GlobalDFSScheduling data certs) :
    Verb.ValidROM
      (Verb.program (data.rows (rootRowIndex cfg)).root.subject
        (data.rows (rootRowIndex cfg)).root.formula) := by
  obtain ⟨trace, htrace, hlast⟩ := hschedule
  refine ⟨trace, Verb.ofNoun (data.rows (rootRowIndex cfg)).root.result,
    htrace, hlast, ?_, ?_⟩
  · exact Verb.nextROM_none_of_terminal
      (Verb.ofNoun_terminal (data.rows (rootRowIndex cfg)).root.result)
  · exact Verb.ofNoun_terminal (data.rows (rootRowIndex cfg)).root.result

end

end Nock.NockVMROM.Thm54.SemanticTrace

#print axioms Nock.NockVMROM.Thm54.SemanticTrace.comparisonCensus_count_le
#print axioms Nock.NockVMROM.Thm54.SemanticTrace.LocalOpcodeCertificate.semantics
#print axioms Nock.NockVMROM.Thm54.SemanticTrace.globalRowPrefixTrace
