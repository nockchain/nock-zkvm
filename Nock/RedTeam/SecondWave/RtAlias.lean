import Nock.NockVMROM.Capstone
import Nock.NockVMROM.Asymptotic

/-! Degeneracy witnesses for the separation, labeling and traversal clauses (S1 to S4) of the Nock VM-ROM capstone. It builds a fake bundle with trivial S1 to S4 objects, shows it is degenerate, and shows by `fail_if_success` that it does not have the type of the real structural theorem `realThm54`. -/

namespace RTAlias

open Nock Nock.Framework Nock.NockVMROM Nock.Walk

instance rt_fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

abbrev Z7 := ZMod 7
abbrev T7 := Tag Z7 Z7 0 1 1

local instance : CharP Z7 (ringChar Z7) := ringChar.charP Z7

/-- The zero semantic NMR record. -/
def r0 : (nmrMEF Z7 Z7).Rec := ((0 : Z7), ((0, 0, 0), (0, 0, 0)), 0)

theorem lmio_r0 : Nock.IO.LmIO 1 [r0] [r0] :=
  ⟨⟨le_refl 1, le_refl 1⟩, [r0], le_refl 1, List.nodup_singleton r0,
    fun _ => Iff.rfl, List.Perm.refl _⟩

/-! ## Leaf-forest helpers -/

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

/-! ## S1 — a "separation" that separates nothing

    `ProgStatement` is the WHOLE statement, the compute sub-verifier is the WHOLE language
    verifier, the memory sub-verifier is `True`, and the shared IO records are a constant
    self-matched pair.  `Def:MES` is satisfied because `x ↦ (x, )` and
    `T ↦ (T, )` are bijections and the biconditional collapses to `Language x ↔ Language x`. -/
noncomputable instance fakeMES : UniqueMemoryExecutionSeparable T7 (nmrMEF Z7 Z7) where
  ProgStatement := Stmt Z7 Z7
  MemStatement := Unit
  ProgWitness := Wit Z7 Z7
  MemWitness := Unit
  ProgIO := Unit
  MemIO := Unit
  splitStatement := ⟨fun x => (x, ()), fun p => p.1, fun _ => rfl, fun _ => rfl⟩
  splitWitness := ⟨fun w => (w, ()), fun p => p.1, fun _ => rfl, fun _ => rfl⟩
  computeAccepts ps _ _ := Language T7 ps
  memoryAccepts := fun _ _ _ => True
  ioRecords := fun _ _ => ([r0], [r0])
  K := 1
  correct := by
    intro x
    constructor
    · intro h
      exact ⟨⟨[], [], []⟩, (), (), h, trivial, lmio_r0⟩
    · rintro ⟨-, -, -, h, -, -⟩
      exact h


noncomputable instance fakeCRAP : HasCanonicalRAP T7 (nmrMEF Z7 Z7) Z7 where
  Rprog := (nock_hasCanonicalRAP Z7 Z7 0 1 1).Rprog
  Rmem := (nock_hasCanonicalRAP Z7 Z7 0 1 1).Rmem
  ProgProblem := Unit
  MemProblem := Unit
  progAccepts := fun _ => True
  progSatisfiable := fun _ => True
  memAccepts := fun _ => True
  memSatisfiable := fun _ => True
  compute_iff := fun _ => Iff.rfl
  memory_iff := fun _ => Iff.rfl


noncomputable instance fakeOneHot : OpcodeMemoryOneHot T7 (nmrMEF Z7 Z7) Z7 10 3 where
  Row := Empty
  numericSelector := Empty.elim
  structuralSelector := Empty.elim
  recordCount := Empty.elim
  numeric_boolean := fun row => Empty.elim row
  structural_boolean := fun row => Empty.elim row
  exactly_one_action_per_compute_row := fun row => Empty.elim row
  record_arity_le := fun row => Empty.elim row
  record_pos := fun row => Empty.elim row

/-! ## S4 — unit labels and the always-true labeling relation, at the paper's arities 3 / 2 -/

instance fakeTM : TraversalModel T7 (nmrMEF Z7 Z7) where
  ComputeLabel := Unit
  MemoryLabel := Unit
  compArity := 3
  memArity := 2
  compRoots := 1
  memRoots := 1
  Fcomp := fun _ _ _ => True
  Fmem := fun _ _ _ => True

/-- The empty statement is in the real NockVMROM language at `Ksz = 1`. -/
theorem empty_in_language : Language T7 (⟨[], []⟩ : Stmt Z7 Z7) :=
  language_nonempty Z7 Z7 0 1 (le_refl 1) r0

noncomputable instance fakeTraversable : IsTraversable T7 (nmrMEF Z7 Z7) where
  computeReadout := fun _ => (⟨[], []⟩, ⟨[], [], []⟩, ())
  memoryReadout := fun _ => ((), (), ())
  recognizes_compute := fun _ _ _ _ => empty_in_language
  recognizes_memory := fun _ _ _ _ => trivial
  compute_recognized := ⟨0, (), trivial, empty_in_language⟩
  memory_recognized := ⟨0, (), trivial, trivial⟩
  recognized_complete_compute := fun _ _ lbl _ h _ _ _ _ _ => true_recon lbl h
  recognized_complete_memory := fun _ _ lbl _ h _ _ _ _ _ => true_recon lbl h

/-! ## Fake and real S1–S4 produce different theorem types

    The degenerate S1–S4 objects assemble when they are explicitly named as parameters.  They do
    not inhabit the type of `NockVMROM_Thm54_structural`, whose parameters pin the genuine Nock
    separation, RAP, one-hot and traversal objects.  This rules out substituting degenerate S1–S4
    objects at the type level; it does not address empty-language VMs or the independence of the
    S5–S8 model bodies. -/
@[reducible] noncomputable def fakeThm54 :
    VerifiableVMCompilation T7 (nmrMEF Z7 Z7) Z7 10 3
      (Nock.NockVMROM.Thm54.ProductionP8Containment.ExactProductionFixedFieldSoundness Z7 Z7)
      (Nock.NockVMROM.Thm54.ProductionP8Containment.exactProductionFixedFieldSoundness Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactSegmentedCostVerification Z7 Z7)
      (Nock.NockVMROM.Thm54.exactSegmentedCostVerification Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactChainedHasPerfectCompleteness Z7 Z7)
      (Nock.NockVMROM.Thm54.exactChainedHasPerfectCompleteness Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactTwoRAPVerification Z7 Z7)
      (Nock.NockVMROM.Thm54.exactTwoRAPVerification Z7 Z7)
      fakeMES True trivial
      True trivial True trivial
      (nock_languageInhabited Z7 Z7 0 1 1) :=
  ⟨⟩

/-- The explicitly fake-parameterized bundle is degenerate; the real theorem type simply excludes it. -/
theorem fakeThm54_is_degenerate :
    fakeOneHot.Row = Empty ∧
    fakeCRAP.progAccepts () ∧
    fakeTM.ComputeLabel = Unit ∧
    (∀ (i : Fin fakeTM.compRoots) l x, fakeTM.Fcomp i l x) ∧
    (∀ x pw io, fakeMES.computeAccepts x pw io ↔ Language T7 x) :=
  ⟨rfl, trivial, rfl, fun _ _ _ => trivial, fun _ _ _ => Iff.rfl⟩

/-- The real structural target pins all five genuine Nock S1–S4 parameters in its type. -/
@[reducible] noncomputable def realThm54 :
    VerifiableVMCompilation T7 (nmrMEF Z7 Z7) Z7 10 3
      (Nock.NockVMROM.Thm54.ProductionP8Containment.ExactProductionFixedFieldSoundness Z7 Z7)
      (Nock.NockVMROM.Thm54.ProductionP8Containment.exactProductionFixedFieldSoundness Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactSegmentedCostVerification Z7 Z7)
      (Nock.NockVMROM.Thm54.exactSegmentedCostVerification Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactChainedHasPerfectCompleteness Z7 Z7)
      (Nock.NockVMROM.Thm54.exactChainedHasPerfectCompleteness Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactTwoRAPVerification Z7 Z7)
      (Nock.NockVMROM.Thm54.exactTwoRAPVerification Z7 Z7)
      (nock_uniqueMES Z7 Z7 0 1 1)
      (Nock.NockVMROM.Thm54.ExactChainedHasCanonicalRAP2 Z7 Z7)
      (Nock.NockVMROM.Thm54.exactChainedHasCanonicalRAP2 Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactChainedOneHot Z7 Z7)
      (Nock.NockVMROM.Thm54.exactChainedOneHot Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactDefTraversable Z7 Z7)
      (Nock.NockVMROM.Thm54.exactDefTraversable Z7 Z7)
      (nock_languageInhabited Z7 Z7 0 1 1) :=
  NockVMROM_Thm54_structural Z7 Z7 0 1 1

/-- The fake bundle `fakeThm54` fails to check against the real theorem type.  `fail_if_success` makes that elaboration failure part of the default build; the
    resulting declaration is also a positive inhabitant of the exact real target. -/
theorem fakeThm54_no_longer_has_real_type :
    VerifiableVMCompilation T7 (nmrMEF Z7 Z7) Z7 10 3
      (Nock.NockVMROM.Thm54.ProductionP8Containment.ExactProductionFixedFieldSoundness Z7 Z7)
      (Nock.NockVMROM.Thm54.ProductionP8Containment.exactProductionFixedFieldSoundness Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactSegmentedCostVerification Z7 Z7)
      (Nock.NockVMROM.Thm54.exactSegmentedCostVerification Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactChainedHasPerfectCompleteness Z7 Z7)
      (Nock.NockVMROM.Thm54.exactChainedHasPerfectCompleteness Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactTwoRAPVerification Z7 Z7)
      (Nock.NockVMROM.Thm54.exactTwoRAPVerification Z7 Z7)
      (nock_uniqueMES Z7 Z7 0 1 1)
      (Nock.NockVMROM.Thm54.ExactChainedHasCanonicalRAP2 Z7 Z7)
      (Nock.NockVMROM.Thm54.exactChainedHasCanonicalRAP2 Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactChainedOneHot Z7 Z7)
      (Nock.NockVMROM.Thm54.exactChainedOneHot Z7 Z7)
      (Nock.NockVMROM.Thm54.ExactDefTraversable Z7 Z7)
      (Nock.NockVMROM.Thm54.exactDefTraversable Z7 Z7)
      (nock_languageInhabited Z7 Z7 0 1 1) := by
  fail_if_success
    exact fakeThm54
  exact realThm54

#print axioms fakeThm54
#print axioms fakeThm54_is_degenerate
#print axioms realThm54
#print axioms fakeThm54_no_longer_has_real_type

end RTAlias
