import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Asymptotic

/-! Degenerate instances for the bundle clauses of the Nock VM-ROM capstone. It builds a VM that accepts nothing, shows that `LanguageInhabited` fails for it, and shows that parameterising S1 to S4 alone does not exclude empty languages. -/

namespace RTBundle

open Nock Nock.Framework Nock.NockVMROM Nock.Walk

/-! ## Leaf-forest helpers (for the S4 clause) -/

theorem flatMap_children_nil {LT : Type} :
    ∀ (l : List (NTree LT)), (∀ t ∈ l, t.children = []) → l.flatMap NTree.children = []
  | [], _ => rfl
  | t :: rest, h => by
      have h1 : t.children = [] := h t (by simp)
      have h2 : rest.flatMap NTree.children = [] :=
        flatMap_children_nil rest (fun s hs => h s (by simp [hs]))
      simp [List.flatMap_cons, h1, h2]

theorem bfsForest_leaves {LT : Type} (l : List (NTree LT)) (h : ∀ t ∈ l, t.children = []) :
    bfsForest l = l := by
  cases l with
  | nil => exact bfsForest_nil
  | cons t rest =>
      rw [bfsForest_cons_eq _ (by simp), flatMap_children_nil _ h, bfsForest_nil,
        List.append_nil]

/-- With the always-true labeling relation, every leaf is in the exact arity-`n` RVT language. -/
theorem rvtWithArity_true_leaf {LT : Type} {n : ℕ} (l : LT) :
    RVTWithArity (fun (_ : LT) (_ : Fin n → Option LT) => True) (NTree.node l []) := by
  constructor
  · rw [RVT]
    refine ⟨trivial, ?_, ?_⟩
    · intro s hs; simp at hs
    · exact ⟨fun _ => trivial, fun _ => rfl⟩
  · intro s hs
    cases hs with
    | here => simp [NTree.children]
    | sub hs _ => simp [NTree.children] at hs

/-- The always-true labeling relation reconstructs any row sequence as a forest of leaves. -/
theorem true_recon {LT : Type} {n : ℕ} (lbl : ℕ → LT) (h : ℕ) :
    ∃ ts : List (NTree LT),
      (∀ t ∈ ts, RVTWithArity (fun (_ : LT) (_ : Fin n → Option LT) => True) t) ∧
      (bfsForest ts).map NTree.label = (List.range' 1 h).map lbl := by
  refine ⟨(List.range' 1 h).map (fun k => NTree.node (lbl k) []), ?_, ?_⟩
  · intro t ht
    simp only [List.mem_map] at ht
    obtain ⟨k, -, rfl⟩ := ht
    exact rvtWithArity_true_leaf _
  · rw [bfsForest_leaves]
    · simp [List.map_map, Function.comp_def, NTree.label]
    · intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨k, -, rfl⟩ := ht
      rfl

/-! ## A VM that accepts nothing -/

/-- A `VMSystem` whose verifier rejects every statement, so its language is empty. -/
structure RejVM : Type

instance instRej : VMSystem RejVM where
  Statement := Unit
  Witness := Unit
  accepts := fun _ _ => False

theorem rej_language_empty (x : VMSystem.Statement RejVM) : ¬ Language RejVM x := by
  rintro ⟨w, hw⟩; exact hw

/-! ## S1 — separability with `K = 0`, which makes `L_mIO` unsatisfiable -/

noncomputable instance rejMES : UniqueMemoryExecutionSeparable RejVM (nmrMEF ℚ ℚ) where
  ProgStatement := Unit
  MemStatement := Unit
  ProgWitness := Unit
  MemWitness := Unit
  ProgIO := Unit
  MemIO := Unit
  splitStatement := ⟨fun _ => ((), ()), fun _ => (), fun _ => rfl, fun _ => rfl⟩
  splitWitness := ⟨fun _ => ((), ()), fun _ => (), fun _ => rfl, fun _ => rfl⟩
  computeAccepts := fun _ _ _ => True
  memoryAccepts := fun _ _ _ => True
  ioRecords := fun _ _ => ([], [])
  K := 0
  correct := by
    intro x
    constructor
    · rintro ⟨w, hw⟩; exact absurd hw (by intro h; exact h)
    · rintro ⟨w, ioP, ioM, -, -, hio⟩
      simp only [Nock.IO.LmIO, Nock.IO.InRange, List.length_nil] at hio
      omega


noncomputable def rejCRAP : HasCanonicalRAP RejVM (nmrMEF ℚ ℚ) ℚ where
  Rprog := (nock_hasCanonicalRAP ℚ ℚ 0 1 1).Rprog
  Rmem := (nock_hasCanonicalRAP ℚ ℚ 0 1 1).Rmem
  ProgProblem := Unit
  MemProblem := Unit
  progAccepts := fun _ => True
  progSatisfiable := fun _ => True
  memAccepts := fun _ => True
  memSatisfiable := fun _ => True
  compute_iff := fun _ => Iff.rfl
  memory_iff := fun _ => Iff.rfl


noncomputable def rejOneHot :
    OpcodeMemoryOneHot RejVM (nmrMEF ℚ ℚ) ℚ 10 3 where
  Row := Empty
  numericSelector := Empty.elim
  structuralSelector := Empty.elim
  recordCount := Empty.elim
  numeric_boolean := fun row => Empty.elim row
  structural_boolean := fun row => Empty.elim row
  exactly_one_action_per_compute_row := fun row => Empty.elim row
  record_arity_le := fun row => Empty.elim row
  record_pos := fun row => Empty.elim row

/-! ## S4 — traversal data and traversability, at the paper's arities 3 / 2 -/

instance rejTM : TraversalModel RejVM (nmrMEF ℚ ℚ) where
  ComputeLabel := Unit
  MemoryLabel := Unit
  compArity := 3
  memArity := 2
  compRoots := 1
  memRoots := 1
  Fcomp := fun _ _ _ => True
  Fmem := fun _ _ _ => True

noncomputable def rejTraversable :
    IsTraversable RejVM (nmrMEF ℚ ℚ) where
  computeReadout := fun _ => ((), (), ())
  memoryReadout := fun _ => ((), (), ())
  recognizes_compute := fun _ _ _ _ => trivial
  recognizes_memory := fun _ _ _ _ => trivial
  compute_recognized := ⟨0, (), trivial, trivial⟩
  memory_recognized := ⟨0, (), trivial, trivial⟩
  recognized_complete_compute := fun _ _ lbl _ h _ _ _ _ _ => true_recon lbl h
  recognized_complete_memory := fun _ _ lbl _ h _ _ _ _ _ => true_recon lbl h

/-! ## S5–S8 — degenerate models -/

def rejTwoRAPModel : TwoRAPVerificationModel RejVM (nmrMEF ℚ ℚ) ℚ where
  ComputeTrial := Unit
  MemoryTrial := Unit
  IOWitness := Unit
  computeBadProbability := fun _ => 0
  memoryBadProbability := fun _ => 0
  computeBound := fun _ => 0
  memoryBound := fun _ => 0
  rapIOAccepts := fun _ => True
  ioBound := 0

def rejTwoRAP : HasTwoRAPVerification RejVM (nmrMEF ℚ ℚ) ℚ rejTwoRAPModel where
  compute_sound := fun _ => le_rfl
  memory_sound := fun _ => le_rfl
  shared_io := ⟨(), trivial⟩

def rejCompModel : CompletenessModel RejVM (nmrMEF ℚ ℚ) ℚ where
  Problem := Unit
  accepted := fun _ => True
  hasSatisfyingAssignment := fun _ => True

def rejComplete : HasPerfectCompleteness RejVM (nmrMEF ℚ ℚ) ℚ rejCompModel where
  complete := fun _ _ => trivial

def rejSoundModel : ConcreteSoundnessModel RejVM where
  Trial := Unit
  badProbability := fun _ => 0
  bound := fun _ => 0

def rejSound : HasConcreteSoundness RejVM rejSoundModel where
  sound := fun _ => le_rfl

/-! ## The empty-language VM cannot supply `LanguageInhabited` -/

/-- The `LanguageInhabited` parameter cannot be supplied for `RejVM`, because its top-level language is provably empty. -/
theorem rej_languageInhabited_false : ¬ LanguageInhabited RejVM := by
  rintro ⟨⟨x, hx⟩⟩
  exact rej_language_empty x hx

/-- The same VM's language is empty. -/
theorem rejBundle_language_empty : ∀ x : VMSystem.Statement RejVM, ¬ Language RejVM x :=
  rej_language_empty

#print axioms rej_languageInhabited_false
#print axioms rejBundle_language_empty

end RTBundle


namespace Atk

open Nock Nock.Framework Nock.NockVMROM RTBundle

/-! ### 1.  Making S1-S4 *parameters* alone does not exclude empty languages.

  A package class with S1-S4 hoisted to parameters is inhabited, at the same degenerate objects,
  by the same empty-language VM.  Parameterization pins the *alias type* (which excludes `fakeThm54`); it says nothing about which VMs can inhabit the class. -/

class ParamPkg (ι : Type) [VMSystem ι] (M : MEF) (F : Type) [CommRing F] (NOP MOP : ℕ)
    (security : ConcreteSoundnessModel ι) (cost : CostModel)
    (comp : CompletenessModel ι M F) (twoRAPModel : TwoRAPVerificationModel ι M F)
    (uniqueMES : UniqueMemoryExecutionSeparable ι M)
    (canonicalRAP : HasCanonicalRAP ι M F)
    (oneHot : @OpcodeMemoryOneHot ι _ M F _ NOP MOP uniqueMES)
    (traversalModel : TraversalModel ι M)
    (traversable : @IsTraversable ι _ M traversalModel uniqueMES) : Prop where
  twoRAP : HasTwoRAPVerification ι M F twoRAPModel
  complete : @HasPerfectCompleteness ι _ M F _ comp
  concreteSound : HasConcreteSoundness ι security
  costed : HasCostModel ι cost

noncomputable def rejParamPkg :
    ParamPkg RejVM (nmrMEF ℚ ℚ) ℚ 10 3 rejSoundModel reifiedNockCost rejCompModel
      rejTwoRAPModel rejMES rejCRAP rejOneHot rejTM rejTraversable where
  twoRAP := rejTwoRAP
  complete := rejComplete
  concreteSound := rejSound
  costed :=
    { compMaxDegree_eq_four := rfl
      memMaxDegree_eq_four := rfl
      memory_fewer_constraints := by decide
      memory_fewer_deg4 := by decide }

theorem parameterization_does_not_exclude_empty_languages :
    Nonempty (ParamPkg RejVM (nmrMEF ℚ ℚ) ℚ 10 3 rejSoundModel reifiedNockCost rejCompModel
        rejTwoRAPModel rejMES rejCRAP rejOneHot rejTM rejTraversable)
      ∧ (∀ x : VMSystem.Statement RejVM, ¬ Language RejVM x) :=
  ⟨⟨rejParamPkg⟩, rej_language_empty⟩

/-! ### 2.  The negation `p1_neg_empty_language` is refutable.

  The statement below refutes it for `ParamPkg`.  `VerifiableVMCompilation` does not have this
  defect: its type requires a
  `LanguageInhabited ι` value, and `rej_languageInhabited_false` rules that out for `RejVM`. -/

theorem p1_neg_empty_language_as_written_is_FALSE :
    ¬ (¬ ∃ _pkg : ParamPkg RejVM (nmrMEF ℚ ℚ) ℚ 10 3
          rejSoundModel reifiedNockCost rejCompModel rejTwoRAPModel
          rejMES rejCRAP rejOneHot rejTM rejTraversable,
        ∀ x : VMSystem.Statement RejVM, ¬ Language RejVM x) := by
  intro h
  exact h ⟨rejParamPkg, rej_language_empty⟩

/-! ### 3.  The package's compute sub-verifier is not definitionally `ComputeTableAccepts`.

  The honest Nock S1 instance's `computeAccepts` is a THREE-argument
  relation carrying the IO-derivation conjunct, so no such equation is even well-typed;
  the true statement is the `Iff` below. -/

theorem real_subverifier_is_NOT_ComputeTableAccepts
    (ps : List (ComputeTable.Inputs ℚ × ComputeTable.Pub ℚ))
    (pw : List (ComputeTable.Dec ℚ) × List ((nmrMEF ℚ ℚ).Rec))
    (io : List ((nmrMEF ℚ ℚ).Rec)) :
    (nock_uniqueMES ℚ ℚ 0 1 1).computeAccepts ps pw io
      ↔ (ComputeTableAccepts ps pw.1 ∧ io = pw.2) := Iff.rfl

end Atk

#print axioms Atk.p1_neg_empty_language_as_written_is_FALSE
#print axioms Atk.parameterization_does_not_exclude_empty_languages
#print axioms Atk.real_subverifier_is_NOT_ComputeTableAccepts
