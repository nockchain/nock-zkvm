/-
  Nock/NockVMROM/Thm54/SkeletonCommitment.lean

  The strict contract requires the prover to fix *all* semantic noun/tree data before the NPR seed
  `z` is sampled.  `SkeletonCommitment` is exactly that pre-seed object: a
  `SemanticStrategy.SemanticSkeleton` (nouns, Nat axes, ordered compute tree and memory forest) plus
  one scalar leaf-size bound.  It is proof-free data.

  `CanonicalCommitmentCheck p C` is the deterministic, *seed-independent* admissibility check on that
  data: every committed noun is a canonical residue noun (`FieldEmbedding.BoundedBy p`, i.e. every
  atom `< p`) and has leaf-size at most the committed bound.  Being seed-independent it is not a coin
  event; being a finite `List` quantification it is genuinely decidable (`instDecidable…` below), so
  it is a check a verifier can run, not an assumed hypothesis.

  Scope: this module is about the committed data alone.  It makes no acceptance, `BindsAt`, or
  evaluator claim.
-/

import Nock.NockVMROM.Thm54.P8Census

namespace Nock.NockVMROM.Thm54.StrictCommitment

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.SemanticStrategy

/-! ## The pre-seed commitment -/

/-- **The pre-seed commitment.**  All semantic data the prover is allowed to use, fixed before the
NPR seed `z` is sampled: the full `SemanticSkeleton` (nouns, Nat axes, ordered compute tree and
memory forest) together with a single committed leaf-size bound.  Proof-free data. -/
structure SkeletonCommitment where
  /-- The complete seed-independent semantic skeleton. -/
  skeleton : SemanticSkeleton
  /-- Committed upper bound on the leaf-size of every committed noun. -/
  nounSizeBound : ℕ

/-! ## Stable slot addresses

Both the pre-seed noun enumeration (this module) and the post-seed fingerprint scan
(`ActiveFingerprintScan`) are indexed by the *same* finite address types, so "active" is decided
once, from the row state, and applies to both sides simultaneously. -/

/-- A fingerprint-bearing noun slot of one compute row. -/
inductive ComputeSlotAddress
  | subject
  | formula
  | evaluation
  | dec (slot : DecSlot)
  | sub (i : Fin 3) (slot : TripleSlot)
  | memRec (i : Fin 3) (slot : MemRecNounSlot)
deriving DecidableEq, Repr

/-- A fingerprint-bearing noun slot of one memory row. -/
inductive MemorySlotAddress
  | parent
  | child (i : Fin 2)
  | memRec (slot : MemRecNounSlot)
deriving DecidableEq, Repr

/-- The six private decomposition slots, in stable order. -/
def decSlots : List DecSlot :=
  [.f_h, .f_t, .f_th, .f_tt, .f_tth, .f_ttt]

/-- The three components of one subformula triple, in stable order. -/
def tripleSlots : List TripleSlot :=
  [.subject, .formula, .result]

/-- The two noun components of one memory record, in stable order. -/
def memRecSlots : List MemRecNounSlot :=
  [.root, .child]

/-- Every compute noun slot, in stable canonical order: the three public fingerprints, the six
decomposition slots, the three subformula triples, then the three memory records. -/
def computeSlotAddresses : List ComputeSlotAddress :=
  [.subject, .formula, .evaluation] ++
    decSlots.map ComputeSlotAddress.dec ++
    (List.finRange 3).flatMap (fun i => tripleSlots.map (ComputeSlotAddress.sub i)) ++
    (List.finRange 3).flatMap (fun i => memRecSlots.map (ComputeSlotAddress.memRec i))

/-- Every memory noun slot, in stable canonical order. -/
def memorySlotAddresses : List MemorySlotAddress :=
  [.parent] ++
    (List.finRange 2).map MemorySlotAddress.child ++
    memRecSlots.map MemorySlotAddress.memRec

/-- The compute address list really is the complete address inventory. -/
theorem mem_computeSlotAddresses (a : ComputeSlotAddress) :
    a ∈ computeSlotAddresses := by
  cases a with
  | subject => decide
  | formula => decide
  | evaluation => decide
  | dec slot => cases slot <;> decide
  | sub i slot => fin_cases i <;> cases slot <;> decide
  | memRec i slot => fin_cases i <;> cases slot <;> decide

/-- The memory address list really is the complete address inventory. -/
theorem mem_memorySlotAddresses (a : MemorySlotAddress) :
    a ∈ memorySlotAddresses := by
  cases a with
  | parent => decide
  | child i => fin_cases i <;> decide
  | memRec slot => cases slot <;> decide

/-! ## State-decided activity

Activity is a function of the row *state* only — the same data that fixes the table's own
active/padding classification (`computeSubformulaKind`, `computeMemRecKind`, `memoryChildKind`,
`memoryMemRecKind`). -/

/-- Whether a compute noun slot is live in the given state. -/
def computeSlotActive (st : ComputeTable.State) : ComputeSlotAddress → Bool
  | .subject => true
  | .formula => true
  | .evaluation => true
  | .dec slot => decActive st slot
  | .sub i _ => decide ((i : ℕ) < ComputeTable.fanoutComp st)
  | .memRec i _ => decide ((i : ℕ) < Nock.Framework.recordCount st)

/-- Whether a memory noun slot is live in the given state. -/
def memorySlotActive (st : MemoryTable.MState) : MemorySlotAddress → Bool
  | .parent => true
  | .child i => decide ((i : ℕ) < MemoryTable.fanoutMem st)
  | .memRec _ => decide (memoryMemRecKind st = .active)

/-- The active compute noun slots of a state, in canonical order. -/
def activeComputeSlotAddresses (st : ComputeTable.State) : List ComputeSlotAddress :=
  computeSlotAddresses.filter (computeSlotActive st)

/-- The active memory noun slots of a state, in canonical order. -/
def activeMemorySlotAddresses (st : MemoryTable.MState) : List MemorySlotAddress :=
  memorySlotAddresses.filter (memorySlotActive st)

/-- **Enumeration completeness and inactive-slot exclusion, in one biconditional.**  A compute
address is scanned exactly when the row state makes it active. -/
theorem mem_activeComputeSlotAddresses_iff
    (st : ComputeTable.State) (a : ComputeSlotAddress) :
    a ∈ activeComputeSlotAddresses st ↔ computeSlotActive st a = true := by
  simp [activeComputeSlotAddresses, List.mem_filter, mem_computeSlotAddresses a]

/-- Memory analogue of `mem_activeComputeSlotAddresses_iff`. -/
theorem mem_activeMemorySlotAddresses_iff
    (st : MemoryTable.MState) (a : MemorySlotAddress) :
    a ∈ activeMemorySlotAddresses st ↔ memorySlotActive st a = true := by
  simp [activeMemorySlotAddresses, List.mem_filter, mem_memorySlotAddresses a]

/-- **Inactive compute slots are not scanned.** -/
theorem not_mem_activeComputeSlotAddresses
    {st : ComputeTable.State} {a : ComputeSlotAddress}
    (h : computeSlotActive st a = false) :
    a ∉ activeComputeSlotAddresses st := by
  rw [mem_activeComputeSlotAddresses_iff]
  simp [h]

/-- **Inactive memory slots are not scanned.** -/
theorem not_mem_activeMemorySlotAddresses
    {st : MemoryTable.MState} {a : MemorySlotAddress}
    (h : memorySlotActive st a = false) :
    a ∉ activeMemorySlotAddresses st := by
  rw [mem_activeMemorySlotAddresses_iff]
  simp [h]

/-! ## Total noun projections at an address -/

/-- Noun projection of a pre-seed memory record. -/
def memRecSkeletonNoun (m : MemRecSkeleton) : MemRecNounSlot → Noun
  | .root => m.root
  | .child => m.child

/-- The committed noun at one compute address.  Total; on an inactive address the value is the
unreachable `.atom 0` fallback (inactive addresses are never scanned, by
`not_mem_activeComputeSlotAddresses`).  The `dec`/`sub` cases reuse the existing `P8Census`
projections. -/
def computeSlotNoun (s : ComputeRowSkeleton) : ComputeSlotAddress → Noun
  | .subject => s.subject
  | .formula => s.formula
  | .evaluation => s.evaluation
  | .dec slot => P8Census.skeletonDec s slot
  | .sub i slot => P8Census.skeletonSubformula s i slot
  | .memRec i slot =>
      if h : (i : ℕ) < Nock.Framework.recordCount s.state
      then memRecSkeletonNoun (s.memoryRecord i h) slot
      else .atom 0

/-- The committed noun at one memory address; total in the same sense as `computeSlotNoun`. -/
def memorySlotNoun (s : MemoryRowSkeleton) : MemorySlotAddress → Noun
  | .parent => s.parent
  | .child i =>
      if h : (i : ℕ) < MemoryTable.fanoutMem s.state then s.child i h else .atom 0
  | .memRec slot =>
      if h : memoryMemRecKind s.state = .active
      then memRecSkeletonNoun (s.memoryRecord h) slot
      else .atom 0

@[simp] theorem computeSlotNoun_subject (s : ComputeRowSkeleton) :
    computeSlotNoun s .subject = s.subject := rfl

@[simp] theorem computeSlotNoun_formula (s : ComputeRowSkeleton) :
    computeSlotNoun s .formula = s.formula := rfl

@[simp] theorem computeSlotNoun_evaluation (s : ComputeRowSkeleton) :
    computeSlotNoun s .evaluation = s.evaluation := rfl

theorem computeSlotNoun_dec_of_active {s : ComputeRowSkeleton} {slot : DecSlot}
    (h : decActive s.state slot = true) :
    computeSlotNoun s (.dec slot) = s.decomposition slot h := by
  simp [computeSlotNoun, P8Census.skeletonDec, h]

theorem computeSlotNoun_sub_of_active {s : ComputeRowSkeleton} {i : Fin 3}
    (h : (i : ℕ) < ComputeTable.fanoutComp s.state) (slot : TripleSlot) :
    computeSlotNoun s (.sub i slot) = s.subformula i h slot := by
  simp [computeSlotNoun, P8Census.skeletonSubformula, h]

theorem computeSlotNoun_memRec_of_active {s : ComputeRowSkeleton} {i : Fin 3}
    (h : (i : ℕ) < Nock.Framework.recordCount s.state) (slot : MemRecNounSlot) :
    computeSlotNoun s (.memRec i slot) = memRecSkeletonNoun (s.memoryRecord i h) slot := by
  simp [computeSlotNoun, h]

@[simp] theorem memorySlotNoun_parent (s : MemoryRowSkeleton) :
    memorySlotNoun s .parent = s.parent := rfl

theorem memorySlotNoun_child_of_active {s : MemoryRowSkeleton} {i : Fin 2}
    (h : (i : ℕ) < MemoryTable.fanoutMem s.state) :
    memorySlotNoun s (.child i) = s.child i h := by
  simp [memorySlotNoun, h]

theorem memorySlotNoun_memRec_of_active {s : MemoryRowSkeleton}
    (h : memoryMemRecKind s.state = .active) (slot : MemRecNounSlot) :
    memorySlotNoun s (.memRec slot) = memRecSkeletonNoun (s.memoryRecord h) slot := by
  simp [memorySlotNoun, h]

/-! ## The committed noun inventory -/

/-- Every committed noun of one compute row, at its active addresses only. -/
def commitmentComputeRowNouns (s : ComputeRowSkeleton) : List Noun :=
  (activeComputeSlotAddresses s.state).map (computeSlotNoun s)

/-- Every committed noun of one memory row, at its active addresses only. -/
def commitmentMemoryRowNouns (s : MemoryRowSkeleton) : List Noun :=
  (activeMemorySlotAddresses s.state).map (memorySlotNoun s)

/-- **The complete finite inventory of committed nouns.**  Canonical compute BFS rows first, then
canonical memory-forest BFS rows, each contributing exactly its active addresses. -/
def commitmentNouns (C : SkeletonCommitment) : List Noun :=
  (computeSkeletonRows C.skeleton).flatMap commitmentComputeRowNouns ++
    (memorySkeletonRows C.skeleton).flatMap commitmentMemoryRowNouns

theorem mem_commitmentNouns_compute {C : SkeletonCommitment}
    {s : ComputeRowSkeleton} (hs : s ∈ computeSkeletonRows C.skeleton)
    {a : ComputeSlotAddress} (ha : a ∈ activeComputeSlotAddresses s.state) :
    computeSlotNoun s a ∈ commitmentNouns C := by
  refine List.mem_append_left _ ?_
  rw [List.mem_flatMap]
  exact ⟨s, hs, List.mem_map_of_mem ha⟩

theorem mem_commitmentNouns_memory {C : SkeletonCommitment}
    {s : MemoryRowSkeleton} (hs : s ∈ memorySkeletonRows C.skeleton)
    {a : MemorySlotAddress} (ha : a ∈ activeMemorySlotAddresses s.state) :
    memorySlotNoun s a ∈ commitmentNouns C := by
  refine List.mem_append_right _ ?_
  rw [List.mem_flatMap]
  exact ⟨s, hs, List.mem_map_of_mem ha⟩

/-! ## The canonical commitment check -/

/-- **The deterministic pre-seed admissibility check.**  Every committed noun is a canonical residue
noun for the strict modular prime `p` (every atom `< p`) and its leaf-size is at most the committed
`nounSizeBound`.  No seed, no coin, no acceptance: a check on the committed data alone. -/
def CanonicalCommitmentCheck (p : ℕ) (C : SkeletonCommitment) : Prop :=
  ∀ n ∈ commitmentNouns C,
    FieldEmbedding.BoundedBy p n ∧ n.leaves ≤ C.nounSizeBound

/-- Canonical-residue boundedness is structurally decidable. -/
instance instDecidableBoundedBy (q : ℕ) :
    ∀ n : Noun, Decidable (FieldEmbedding.BoundedBy q n)
  | .atom k => decidable_of_iff (k < q) (by simp [FieldEmbedding.BoundedBy])
  | .cell l r =>
      have := instDecidableBoundedBy q l
      have := instDecidableBoundedBy q r
      decidable_of_iff
        (FieldEmbedding.BoundedBy q l ∧ FieldEmbedding.BoundedBy q r)
        (by simp [FieldEmbedding.BoundedBy])

/-- **The check is decidable, not merely decidable in spirit.**  It is a bounded quantification over
one explicit finite list of nouns, with a structurally decidable body. -/
instance instDecidableCanonicalCommitmentCheck (p : ℕ) (C : SkeletonCommitment) :
    Decidable (CanonicalCommitmentCheck p C) := by
  unfold CanonicalCommitmentCheck
  infer_instance

/-- The check is exactly the pointwise conjunction over the finite committed inventory: nothing is
hidden in the definition. -/
theorem canonicalCommitmentCheck_iff (p : ℕ) (C : SkeletonCommitment) :
    CanonicalCommitmentCheck p C ↔
      ((∀ n ∈ commitmentNouns C, FieldEmbedding.BoundedBy p n) ∧
        ∀ n ∈ commitmentNouns C, n.leaves ≤ C.nounSizeBound) := by
  constructor
  · intro h
    exact ⟨fun n hn => (h n hn).1, fun n hn => (h n hn).2⟩
  · intro h n hn
    exact ⟨h.1 n hn, h.2 n hn⟩

namespace CanonicalCommitmentCheck

variable {p : ℕ} {C : SkeletonCommitment}

/-- Canonical-residue bound at one scanned compute address. -/
theorem computeSlot_bounded (h : CanonicalCommitmentCheck p C)
    {s : ComputeRowSkeleton} (hs : s ∈ computeSkeletonRows C.skeleton)
    {a : ComputeSlotAddress} (ha : a ∈ activeComputeSlotAddresses s.state) :
    FieldEmbedding.BoundedBy p (computeSlotNoun s a) :=
  (h _ (mem_commitmentNouns_compute hs ha)).1

/-- Leaf-size bound at one scanned compute address. -/
theorem computeSlot_leaves (h : CanonicalCommitmentCheck p C)
    {s : ComputeRowSkeleton} (hs : s ∈ computeSkeletonRows C.skeleton)
    {a : ComputeSlotAddress} (ha : a ∈ activeComputeSlotAddresses s.state) :
    (computeSlotNoun s a).leaves ≤ C.nounSizeBound :=
  (h _ (mem_commitmentNouns_compute hs ha)).2

/-- Canonical-residue bound at one scanned memory address. -/
theorem memorySlot_bounded (h : CanonicalCommitmentCheck p C)
    {s : MemoryRowSkeleton} (hs : s ∈ memorySkeletonRows C.skeleton)
    {a : MemorySlotAddress} (ha : a ∈ activeMemorySlotAddresses s.state) :
    FieldEmbedding.BoundedBy p (memorySlotNoun s a) :=
  (h _ (mem_commitmentNouns_memory hs ha)).1

/-- Leaf-size bound at one scanned memory address. -/
theorem memorySlot_leaves (h : CanonicalCommitmentCheck p C)
    {s : MemoryRowSkeleton} (hs : s ∈ memorySkeletonRows C.skeleton)
    {a : MemorySlotAddress} (ha : a ∈ activeMemorySlotAddresses s.state) :
    (memorySlotNoun s a).leaves ≤ C.nounSizeBound :=
  (h _ (mem_commitmentNouns_memory hs ha)).2

private theorem computeRow_boundedBy (h : CanonicalCommitmentCheck p C)
    {s : ComputeRowSkeleton} (hs : s ∈ computeSkeletonRows C.skeleton) :
    s.BoundedBy p := by
  have key : ∀ a : ComputeSlotAddress, computeSlotActive s.state a = true →
      FieldEmbedding.BoundedBy p (computeSlotNoun s a) := fun a ha =>
    h.computeSlot_bounded hs ((mem_activeComputeSlotAddresses_iff _ _).2 ha)
  refine ⟨key .subject rfl, key .formula rfl, key .evaluation rfl, ?_, ?_, ?_⟩
  · intro slot hslot
    have := key (.dec slot) (by simpa [computeSlotActive] using hslot)
    rwa [computeSlotNoun_dec_of_active hslot] at this
  · intro i hi slot
    have := key (.sub i slot) (by simp [computeSlotActive, hi])
    rwa [computeSlotNoun_sub_of_active hi slot] at this
  · intro i hi
    have hroot := key (.memRec i .root) (by simp [computeSlotActive, hi])
    have hchild := key (.memRec i .child) (by simp [computeSlotActive, hi])
    rw [computeSlotNoun_memRec_of_active hi .root] at hroot
    rw [computeSlotNoun_memRec_of_active hi .child] at hchild
    exact ⟨hroot, hchild⟩

private theorem memoryRow_boundedBy (h : CanonicalCommitmentCheck p C)
    {s : MemoryRowSkeleton} (hs : s ∈ memorySkeletonRows C.skeleton) :
    s.BoundedBy p := by
  have key : ∀ a : MemorySlotAddress, memorySlotActive s.state a = true →
      FieldEmbedding.BoundedBy p (memorySlotNoun s a) := fun a ha =>
    h.memorySlot_bounded hs ((mem_activeMemorySlotAddresses_iff _ _).2 ha)
  refine ⟨key .parent rfl, ?_, ?_⟩
  · intro i hi
    have := key (.child i) (by simp [memorySlotActive, hi])
    rwa [memorySlotNoun_child_of_active hi] at this
  · intro hactive
    have hroot := key (.memRec .root) (by simp [memorySlotActive, hactive])
    have hchild := key (.memRec .child) (by simp [memorySlotActive, hactive])
    rw [memorySlotNoun_memRec_of_active hactive .root] at hroot
    rw [memorySlotNoun_memRec_of_active hactive .child] at hchild
    exact ⟨hroot, hchild⟩

/-- **The deterministic check discharges the established pre-seed boundedness interface.**  Every
consumer of `SemanticSkeleton.BoundedBy` (in particular `BindsAt.nounRealization`) is served by
running `CanonicalCommitmentCheck` on the committed data; the memory-tree clause is covered because
canonical BFS enumeration visits exactly the `InTree` nodes (`Nock.Walk.mem_bfsForest`). -/
theorem skeletonBoundedBy (h : CanonicalCommitmentCheck p C) :
    C.skeleton.BoundedBy p := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.forall_iff_forall_mem]
    exact fun s hs => h.computeRow_boundedBy hs
  · rw [List.forall_iff_forall_mem]
    exact fun s hs => h.memoryRow_boundedBy hs
  · intro tree htree node hnode
    apply h.memoryRow_boundedBy
    unfold memorySkeletonRows
    exact List.mem_map_of_mem ((mem_bfsForest _ node).2 ⟨tree, htree, hnode⟩)

end CanonicalCommitmentCheck

/-! ## Non-vacuity: a concrete admissible commitment

`.s1` has `fanoutComp = 0` and `recordCount = 1`, so the live compute addresses are the three public
nouns, `f_h`, `f_t`, and the two noun components of `mr1`.  `.halt` has `fanoutMem = 0` and a padding
memory record, so its only live address is the parent.  Both rows are therefore leaves and the
skeleton is a genuine one-row/one-row commitment. -/

/-- One concrete admissible compute row: state `.s1`, all committed atoms `< 3`, all leaf-sizes `1`
except the two-leaf formula. -/
def sampleComputeRow : ComputeRowSkeleton where
  state := .s1
  subject := .atom 0
  formula := .cell (.atom 1) (.atom 2)
  evaluation := .atom 2
  decomposition := fun slot _ =>
    match slot with
    | .f_h => .atom 1
    | _ => .atom 2
  subformula := fun _ _ _ => .atom 0
  memoryRecord := fun _ _ => ⟨.atom 0, .atom 2, 1⟩

/-- One concrete admissible memory row: a `halt` leaf whose parent is its precommitted Nat atom. -/
def sampleMemoryRow : MemoryRowSkeleton where
  state := .halt
  parent := .atom 2
  haltAtom := fun _ => 2
  haltParent := fun _ => rfl
  child := fun _ _ => .atom 0
  memoryRecord := fun h => absurd h (by decide)

/-- The concrete one-row/one-row commitment, with leaf-size bound `2`. -/
def sampleCommitment : SkeletonCommitment where
  skeleton :=
    { computeTree := .node sampleComputeRow []
      memoryForest := [.node sampleMemoryRow []] }
  nounSizeBound := 2

theorem sampleCommitment_computeRows :
    computeSkeletonRows sampleCommitment.skeleton = [sampleComputeRow] := by
  have h : sampleCommitment.skeleton.computeTree = .node sampleComputeRow [] := rfl
  unfold computeSkeletonRows
  rw [h, bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

theorem sampleCommitment_memoryRows :
    memorySkeletonRows sampleCommitment.skeleton = [sampleMemoryRow] := by
  have h : sampleCommitment.skeleton.memoryForest = [.node sampleMemoryRow []] := rfl
  unfold memorySkeletonRows
  rw [h, bfsForest_cons_eq _ (by simp)]
  simp [bfsForest_nil]

/-- The committed inventory of the concrete commitment is a genuinely nonempty explicit list, so the
non-vacuity witness below is not a statement about an empty quantification. -/
theorem sampleCommitment_nouns_ne_nil :
    commitmentNouns sampleCommitment ≠ [] := by
  intro h
  have hsubject :
      computeSlotNoun sampleComputeRow .subject ∈ commitmentNouns sampleCommitment := by
    refine mem_commitmentNouns_compute (C := sampleCommitment) ?_ ?_
    · rw [sampleCommitment_computeRows]; simp
    · exact (mem_activeComputeSlotAddresses_iff _ .subject).2 rfl
  rw [h] at hsubject
  simp at hsubject

/-- **Non-vacuity of the canonical check at a concrete prime.**  The concrete commitment passes the
canonical commitment check at `p = 3`, and its committed inventory is nonempty. -/
theorem sampleCommitment_canonical :
    CanonicalCommitmentCheck 3 sampleCommitment ∧
      commitmentNouns sampleCommitment ≠ [] := by
  refine ⟨?_, sampleCommitment_nouns_ne_nil⟩
  unfold CanonicalCommitmentCheck commitmentNouns
  rw [sampleCommitment_computeRows, sampleCommitment_memoryRows]
  decide

end Nock.NockVMROM.Thm54.StrictCommitment

#print axioms Nock.NockVMROM.Thm54.StrictCommitment.mem_computeSlotAddresses
#print axioms Nock.NockVMROM.Thm54.StrictCommitment.mem_memorySlotAddresses
#print axioms Nock.NockVMROM.Thm54.StrictCommitment.mem_activeComputeSlotAddresses_iff
#print axioms Nock.NockVMROM.Thm54.StrictCommitment.mem_activeMemorySlotAddresses_iff
#print axioms Nock.NockVMROM.Thm54.StrictCommitment.not_mem_activeComputeSlotAddresses
#print axioms Nock.NockVMROM.Thm54.StrictCommitment.not_mem_activeMemorySlotAddresses
#print axioms Nock.NockVMROM.Thm54.StrictCommitment.canonicalCommitmentCheck_iff
#print axioms Nock.NockVMROM.Thm54.StrictCommitment.CanonicalCommitmentCheck.skeletonBoundedBy
#print axioms Nock.NockVMROM.Thm54.StrictCommitment.sampleCommitment_canonical
#print axioms Nock.NockVMROM.Thm54.StrictCommitment.sampleCommitment_nouns_ne_nil
