/-
  Nock/NockVMROM/Thm54/RawSemanticAssembly.lean

  This module goes
  the other way: from the checked scan it *rebuilds* `SemanticStrategy.BindsAt`, and then feeds that
  derived binding into the record-realization and containment consumers in place of an assumed
  `ProductionP8Containment.BareSemanticSupport.binds` field.

  ## What the scan does and does not see

  The scan enumerates exactly the *active fingerprint* addresses of
  `StrictCommitment.activeComputeSlotAddresses` / `activeMemorySlotAddresses`.  `BindComputeRow` and
  `BindMemoryRow` contain strictly more than that.  Their remaining content is:

  * the row's own state tags (`row.1 = s.state`, `row.2.2.1.state = s.state`) and seed tag
    (`row.2.1.z = z`);
  * the **padding-zero** equations at every *inactive* address — A1's exclusion lemma
    (`inactive_compute_slot_not_scanned`) is deliberately address-level, so it says a padding slot is
    *not scanned*, never that its field element is `0`;
  * the **Nat-axis cast** `r.axis = (s.axis : K)` of every live memory record — the scan covers a
    record's `root`/`child` noun slots only.

  Those residuals are named once, as `ComputeRowFrame` / `MemoryRowFrame`, and
  `bindComputeRow_iff_slots` / `bindMemoryRow_iff_slots` prove that scan + frame is *exactly*
  equivalent to the row binding.  So the frame is not a convenience assumption: it is the precise
  complement of the scan inside the row binding, and `bindComputeRow_frame` shows any genuine binding
  supplies it.

  ## The tree-shape datum

  `SemanticStrategy.ComputeTreeBinds.node` carries a `shape : sc.length = fanoutComp s.state`
  obligation and an ordered `Forall₂` on children.  Neither is a fingerprint fact, and
  `StrictRawStrategy.StrictRawP8Strategy` carries no structural field relating its raw execution tree
  to the committed skeleton tree.  The datum is therefore introduced explicitly, as the purely
  structural (seed-free, fingerprint-free) relation `ComputeShapeMatch` / `MemoryShapeMatch`, bundled
  as `ExecTreeShapeMatchesAt`.  `ComputeTreeBinds.shapeMatch` proves it is a *projection* of the
  binding, i.e. strictly weaker than what is being rebuilt, and
  `RedTeam.Batch24A2` compiles a witness showing the tree assembly genuinely fails without it.

  ## Honest scope

  * `bindsAt_iff_scan` is unconditional: `BindsAt` ⟺ seed pin ∧ tree-shape match ∧ frame checks ∧
    A1's scan.  Nothing is assumed about acceptance.
  * The `RealizesMemRec` record obligations are derived for the *production* row records
    (`scannedRowRecordRealization_of_bindComputeRow`).  The two `ServedLookup` fields of
    `StrictOperationalEvidence.StrictRowOperationalEvidence` are **not** derived here; they stay in
    `BoundSemanticTrace.SkeletonOperationalCore`, i.e. Packet B.
  * The containment capstone `verifierGeneratedTopologyRawContainment` supplies the derived `BindsAt`
    where `BareSemanticSupport.binds` used to be assumed.  Every other premise of
    `ProductionP8Containment.accepted_outside_failureUnion` — the operational core (served lookups,
    Packet B), the `Ksz`/IO-capacity bounds (Packet C), the census bounds and the character
    hypothesis — is passed through as an explicitly named hypothesis.  No acceptance-side derivation
    of the scan itself is claimed; that is Packet B.
-/

import Nock.NockVMROM.Thm54.StrictRawStrategy
import Nock.NockVMROM.Thm54.StrictOperationalEvidence
import Nock.NockVMROM.Thm54.ProductionP8Containment

namespace Nock.NockVMROM.Thm54.RawSemanticAssembly

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.ActiveFingerprintScan

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## List plumbing: splitting a `Forall₂` back apart

The scan is a flat statement about canonical BFS rows; `ComputeTreeBinds` is recursive.  Rebuilding
the recursive relation from the flat one needs the two inverses of `List.rel_append` and
`List.rel_flatMap`, which Mathlib does not provide directly. -/

private theorem forall₂_append_split {α β : Type} {Rel : α → β → Prop}
    {l₁ l₂ : List α} {m₁ m₂ : List β}
    (hlen : l₁.length = m₁.length)
    (h : List.Forall₂ Rel (l₁ ++ l₂) (m₁ ++ m₂)) :
    List.Forall₂ Rel l₁ m₁ ∧ List.Forall₂ Rel l₂ m₂ := by
  have htake := List.forall₂_take_append (l₁ ++ l₂) m₁ m₂ h
  have hdrop := List.forall₂_drop_append (l₁ ++ l₂) m₁ m₂ h
  rw [← hlen, List.take_left] at htake
  rw [← hlen, List.drop_left] at hdrop
  exact ⟨htake, hdrop⟩

private theorem forall₂_flatMap_split {α β γ δ : Type} {Rel : α → β → Prop}
    {f : γ → List α} {g : δ → List β} :
    ∀ {l : List γ} {m : List δ},
      List.Forall₂ (fun c d => (f c).length = (g d).length) l m →
      List.Forall₂ Rel (l.flatMap f) (m.flatMap g) →
      List.Forall₂ (fun c d => List.Forall₂ Rel (f c) (g d)) l m := by
  intro l m hlen h
  induction hlen with
  | nil => exact .nil
  | @cons c d l m hhead htail ih =>
      rw [List.flatMap_cons, List.flatMap_cons] at h
      obtain ⟨hfirst, hrest⟩ := forall₂_append_split hhead h
      exact .cons hfirst (ih hrest)

/-- **BFS-to-tree inversion.**  A purely structural node correspondence `Shape` plus the *flat*
canonical BFS label relation `Rel` reconstruct the recursive tree relation `TreeRel`.  This is the
exact converse of `SemanticStrategy`'s `bfsRows_ofTreeBindings`. -/
private theorem treeRel_of_bfs {A B : Type}
    (Shape : NTree A → NTree B → Prop) (Rel : A → B → Prop)
    (TreeRel : NTree A → NTree B → Prop)
    (childShape : ∀ s t, Shape s t → List.Forall₂ Shape s.children t.children)
    (mk : ∀ s t, Shape s t → Rel s.label t.label →
      List.Forall₂ TreeRel s.children t.children → TreeRel s t) :
    ∀ (n : ℕ) {ss : List (NTree A)} {trees : List (NTree B)},
      totalSize ss ≤ n →
      List.Forall₂ Shape ss trees →
      List.Forall₂ Rel
        ((bfsForest ss).map NTree.label) ((bfsForest trees).map NTree.label) →
      List.Forall₂ TreeRel ss trees := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro ss trees hsize hshape hrows
      cases hshape with
      | nil => exact .nil
      | @cons s tree ss trees hhead htail =>
          let source : List (NTree A) := s :: ss
          let target : List (NTree B) := tree :: trees
          have hall : List.Forall₂ Shape source target := .cons hhead htail
          have hsource : source ≠ [] := by simp [source]
          have htarget : target ≠ [] := by simp [target]
          rw [bfsForest_cons_eq source hsource, bfsForest_cons_eq target htarget,
            List.map_append, List.map_append] at hrows
          have hlenHead : (source.map NTree.label).length =
              (target.map NTree.label).length := by
            simp [hall.length_eq]
          obtain ⟨hheadRows, htailRows⟩ := forall₂_append_split hlenHead hrows
          have hlabels : List.Forall₂ (fun a b => Rel (NTree.label a) (NTree.label b))
              source target := by
            simpa using hheadRows
          have hchildShape : List.Forall₂ Shape
              (source.flatMap NTree.children) (target.flatMap NTree.children) :=
            List.rel_flatMap hall (fun _ _ hab => childShape _ _ hab)
          have hlt : totalSize (source.flatMap NTree.children) < n := by
            have htotal := totalSize_flatMap_children source
            have hsourceLen : 0 < source.length := List.length_pos_of_ne_nil hsource
            change totalSize source ≤ n at hsize
            omega
          have hchildTrees : List.Forall₂ TreeRel
              (source.flatMap NTree.children) (target.flatMap NTree.children) :=
            ih _ hlt le_rfl hchildShape htailRows
          have hchildLens : List.Forall₂
              (fun a b => (NTree.children a).length = (NTree.children b).length)
              source target :=
            hall.imp (fun _ _ hab => (childShape _ _ hab).length_eq)
          have hchildSplit : List.Forall₂
              (fun a b => List.Forall₂ TreeRel (NTree.children a) (NTree.children b))
              source target :=
            forall₂_flatMap_split hchildLens hchildTrees
          exact List.forall₂_of_length_eq_of_get hall.length_eq
            (fun i h₁ h₂ =>
              mk _ _ (hall.get h₁ h₂) (hlabels.get h₁ h₂) (hchildSplit.get h₁ h₂))

/-! ## The exact non-fingerprint residual of a row binding

`ComputeRowFrame` / `MemoryRowFrame` are, field for field, the conjuncts of
`SemanticStrategy.BindComputeRow` / `BindMemoryRow` that the active fingerprint scan does not
enumerate: state and seed tags, the padding-zero equations at inactive addresses, and the Nat-axis
cast of a live memory record. -/

/-- Everything in `BindComputeRow` that is not a scanned active fingerprint. -/
structure ComputeRowFrame (z : K) (s : ComputeRowSkeleton)
    (row : ComputeTable.State × ComputeTable.DTcomp K) : Prop where
  /-- The row's outer state tag is the committed state. -/
  stateTag : row.1 = s.state
  /-- The row's own seed column is the sampled seed. -/
  seedTag : row.2.1.z = z
  /-- The public state column is the committed state. -/
  publicStateTag : row.2.2.1.state = s.state
  /-- Inactive subformula triples are exact zero padding. -/
  subformulaPadding : ∀ i : Fin 3,
    ¬ ((i : ℕ) < ComputeTable.fanoutComp s.state) →
      computeSubformulaFPs row.2.2.1 i = (0, 0, 0)
  /-- Inactive memory-record slots are the whole production zero record. -/
  memoryRecordPadding : ∀ i : Fin 3,
    ¬ ((i : ℕ) < Nock.Framework.recordCount s.state) →
      computeMemRec row.2.2.1 i = ComputeTable.MemRec.zero
  /-- A live memory record's Nat axis is the cast of the precommitted axis.  The scan sees a
  record's `root`/`child` noun slots only, never its axis. -/
  memoryRecordAxis : ∀ (i : Fin 3) (h : (i : ℕ) < Nock.Framework.recordCount s.state),
    (computeMemRec row.2.2.1 i).axis = ((s.memoryRecord i h).axis : K)

/-- Everything in `BindMemoryRow` that is not a scanned active fingerprint. -/
structure MemoryRowFrame (z : K) (s : MemoryRowSkeleton)
    (row : MemoryTable.MState × MemoryTable.DTmem K) : Prop where
  stateTag : row.1 = s.state
  seedTag : row.2.1.z = z
  publicStateTag : row.2.2.st = s.state
  childPadding : ∀ i : Fin 2,
    ¬ ((i : ℕ) < MemoryTable.fanoutMem s.state) →
      memoryChildCell row.2.2 i = MemoryTable.Cell.zero
  memoryRecordPadding :
    memoryMemRecKind s.state ≠ .active → row.2.2.mem = ComputeTable.MemRec.zero
  /-- Row-level (`BindMemRow`): the row stores the Form R encode `(T, C')` of the skeleton's
      Nock axis at the row's own `λ` (`Pub.lambda`; honestly the package `cfg.challenges.lam`). -/
  memoryRecordAxis : ∀ h : memoryMemRecKind s.state = .active,
    row.2.2.mem.axis = MemoryTable.formRT row.2.2.lambda
        (MemoryTable.nockAxisOf (((s.memoryRecord h).axis : ℕ) : K)) ∧
      row.2.2.cprime = MemoryTable.formRC row.2.2.lambda
        (MemoryTable.nockAxisOf (((s.memoryRecord h).axis : ℕ) : K))
  -- Honest `ver = (st = read_root)`.
  honestVer : row.2.2.ver = decide (s.state = MemoryTable.MState.read_root)

/-- A genuine row binding supplies its own frame: the frame is the binding's non-fingerprint part,
not extra strength. -/
theorem bindComputeRow_frame {z : K} {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (h : BindComputeRow z s row) : ComputeRowFrame z s row := by
  obtain ⟨hstate, hseed, hpub, _, _, _, hdec, hsf, hmr⟩ := h
  refine ⟨hstate, hseed, hpub, ?_, ?_, ?_⟩
  · intro i hi
    have := hsf i
    rwa [dif_neg hi] at this
  · intro i hi
    have := hmr i
    rwa [dif_neg hi] at this
  · intro i hi
    have := hmr i
    rw [dif_pos hi] at this
    exact this.2.2

/-- Memory analogue of `bindComputeRow_frame`. -/
theorem bindMemoryRow_frame {z : K} {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (h : BindMemoryRow z s row) : MemoryRowFrame z s row := by
  obtain ⟨hstate, hseed, hpub, _, hchild, hmem, hver⟩ := h
  refine ⟨hstate, hseed, hpub, ?_, ?_, ?_, hver⟩
  · intro i hi
    have := hchild i
    rwa [dif_neg hi] at this
  · intro ha
    rwa [dif_neg ha] at hmem
  · intro ha
    rw [dif_pos ha] at hmem
    exact hmem.2.2

/-! ### Per-row bindings from the scan -/

/-- **Step 1, compute side.**  The scanned active fingerprint equalities of one row, together with
that row's frame, are exactly `BindComputeRow`.  Every fingerprint conjunct comes from a scanned
address; every remaining conjunct comes from the frame. -/
theorem bindComputeRow_of_slots {z : K} {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hscan : ∀ e ∈ computeRowSlots s row, e.2 = GlobalCarryRecognizer.enc z e.1)
    (frame : ComputeRowFrame z s row) :
    BindComputeRow z s row := by
  have scanAt : ∀ a : ComputeSlotAddress, computeSlotActive s.state a = true →
      computeSlotFP row a = GlobalCarryRecognizer.enc z (computeSlotNoun s a) := by
    intro a ha
    exact hscan _ (mem_computeRowSlots s row ha)
  refine ⟨frame.stateTag, frame.seedTag, frame.publicStateTag,
    scanAt .subject rfl, scanAt .formula rfl, scanAt .evaluation rfl, ?_, ?_, ?_⟩
  · intro slot
    by_cases ha : decActive s.state slot = true
    · rw [dif_pos ha]
      have := scanAt (.dec slot) (by simpa [computeSlotActive] using ha)
      rwa [computeSlotNoun_dec_of_active ha] at this
    · rw [dif_neg ha]
      trivial
  · intro i
    by_cases hi : (i : ℕ) < ComputeTable.fanoutComp s.state
    · rw [dif_pos hi]
      intro slot
      have := scanAt (.sub i slot) (by simp [computeSlotActive, hi])
      rwa [computeSlotNoun_sub_of_active hi slot] at this
    · rw [dif_neg hi]
      exact frame.subformulaPadding i hi
  · intro i
    by_cases hi : (i : ℕ) < Nock.Framework.recordCount s.state
    · rw [dif_pos hi]
      have hroot := scanAt (.memRec i .root) (by simp [computeSlotActive, hi])
      have hchild := scanAt (.memRec i .child) (by simp [computeSlotActive, hi])
      rw [computeSlotNoun_memRec_of_active hi .root] at hroot
      rw [computeSlotNoun_memRec_of_active hi .child] at hchild
      exact ⟨hroot, hchild, frame.memoryRecordAxis i hi⟩
    · rw [dif_neg hi]
      exact frame.memoryRecordPadding i hi

/-- **Step 1, memory side.** -/
theorem bindMemoryRow_of_slots {z : K} {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K}
    (hscan : ∀ e ∈ memoryRowSlots s row, e.2 = GlobalCarryRecognizer.enc z e.1)
    (frame : MemoryRowFrame z s row) :
    BindMemoryRow z s row := by
  have scanAt : ∀ a : MemorySlotAddress, memorySlotActive s.state a = true →
      memorySlotFP row a = GlobalCarryRecognizer.enc z (memorySlotNoun s a) := by
    intro a ha
    exact hscan _ (mem_memoryRowSlots s row ha)
  refine ⟨frame.stateTag, frame.seedTag, frame.publicStateTag,
    scanAt .parent rfl, ?_, ?_, frame.honestVer⟩
  · intro i
    by_cases hi : (i : ℕ) < MemoryTable.fanoutMem s.state
    · rw [dif_pos hi]
      have := scanAt (.child i) (by simp [memorySlotActive, hi])
      rwa [memorySlotNoun_child_of_active hi] at this
    · rw [dif_neg hi]
      exact frame.childPadding i hi
  · by_cases ha : memoryMemRecKind s.state = .active
    · rw [dif_pos ha]
      have hroot := scanAt (.memRec .root) (by simp [memorySlotActive, ha])
      have hchild := scanAt (.memRec .child) (by simp [memorySlotActive, ha])
      rw [memorySlotNoun_memRec_of_active ha .root] at hroot
      rw [memorySlotNoun_memRec_of_active ha .child] at hchild
      exact ⟨hroot, hchild, frame.memoryRecordAxis ha⟩
    · rw [dif_neg ha]
      exact frame.memoryRecordPadding ha

/-- **The scan plus the frame is exactly the row binding.**  This pins A2 as the genuine converse of
A1's `bindComputeRow_slots`, and names the residual precisely. -/
theorem bindComputeRow_iff_slots {z : K} {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K} :
    BindComputeRow z s row ↔
      ((∀ e ∈ computeRowSlots s row, e.2 = GlobalCarryRecognizer.enc z e.1) ∧
        ComputeRowFrame z s row) :=
  ⟨fun h => ⟨bindComputeRow_slots h, bindComputeRow_frame h⟩,
    fun h => bindComputeRow_of_slots h.1 h.2⟩

/-- Memory analogue of `bindComputeRow_iff_slots`. -/
theorem bindMemoryRow_iff_slots {z : K} {s : MemoryRowSkeleton}
    {row : MemoryTable.MState × MemoryTable.DTmem K} :
    BindMemoryRow z s row ↔
      ((∀ e ∈ memoryRowSlots s row, e.2 = GlobalCarryRecognizer.enc z e.1) ∧
        MemoryRowFrame z s row) :=
  ⟨fun h => ⟨bindMemoryRow_slots h, bindMemoryRow_frame h⟩,
    fun h => bindMemoryRow_of_slots h.1 h.2⟩

/-- The live memory-record binding carried by a bound compute row. -/
theorem bindComputeRow_memRec {z : K} {s : ComputeRowSkeleton}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (h : BindComputeRow z s row) (i : Fin 3)
    (hi : (i : ℕ) < Nock.Framework.recordCount s.state) :
    BindMemRec z (s.memoryRecord i hi) (computeMemRec row.2.2.1 i) := by
  have := h.2.2.2.2.2.2.2.2 i
  rwa [dif_pos hi] at this

/-! ## The tree-shape datum

`ComputeShapeMatch` is the seed-free, fingerprint-free skeleton of `ComputeTreeBinds`: each committed
node's arity is its committed state's fanout, and the execution tree branches identically in the same
order.  It is the structural datum `StrictRawP8Strategy` does not carry. -/

/-- Structural agreement between a committed compute skeleton tree and an execution compute tree. -/
inductive ComputeShapeMatch :
    NTree ComputeRowSkeleton →
      NTree (ComputeTable.State × ComputeTable.DTcomp K) → Prop
  | node {s sc row rc}
      (arity : sc.length = ComputeTable.fanoutComp s.state)
      (children : List.Forall₂ ComputeShapeMatch sc rc) :
      ComputeShapeMatch (.node s sc) (.node row rc)

/-- Structural agreement between a committed memory skeleton tree and an execution memory tree. -/
inductive MemoryShapeMatch :
    NTree MemoryRowSkeleton →
      NTree (MemoryTable.MState × MemoryTable.DTmem K) → Prop
  | node {s sc row rc}
      (arity : sc.length = MemoryTable.fanoutMem s.state)
      (children : List.Forall₂ MemoryShapeMatch sc rc) :
      MemoryShapeMatch (.node s sc) (.node row rc)

namespace ComputeShapeMatch

omit [Field K] in
theorem arity_eq {st : NTree ComputeRowSkeleton}
    {et : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (h : ComputeShapeMatch st et) :
    st.children.length = ComputeTable.fanoutComp st.label.state := by
  cases h with
  | node harity _ => exact harity

omit [Field K] in
theorem children_match {st : NTree ComputeRowSkeleton}
    {et : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (h : ComputeShapeMatch st et) :
    List.Forall₂ ComputeShapeMatch st.children et.children := by
  cases h with
  | node _ hchildren => exact hchildren

end ComputeShapeMatch

namespace MemoryShapeMatch

omit [Field K] in
theorem arity_eq {st : NTree MemoryRowSkeleton}
    {et : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryShapeMatch st et) :
    st.children.length = MemoryTable.fanoutMem st.label.state := by
  cases h with
  | node harity _ => exact harity

omit [Field K] in
theorem children_match {st : NTree MemoryRowSkeleton}
    {et : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryShapeMatch st et) :
    List.Forall₂ MemoryShapeMatch st.children et.children := by
  cases h with
  | node _ hchildren => exact hchildren

end MemoryShapeMatch

/-- **The shape datum is a projection of the binding**, hence strictly weaker than what A2
rebuilds. -/
theorem computeTreeBinds_shapeMatch {z : K} {st : NTree ComputeRowSkeleton}
    {et : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (h : ComputeTreeBinds z st et) : ComputeShapeMatch st et := by
  refine ComputeTreeBinds.rec
    (motive_1 := fun st et _ => ComputeShapeMatch st et)
    (motive_2 := fun sts ets _ => List.Forall₂ ComputeShapeMatch sts ets)
    ?_ ?_ ?_ h
  · intro s sc row rc hshape _ _ ihChildren
    exact .node hshape ihChildren
  · exact .nil
  · intro _ _ _ _ _ _ ihHead ihTail
    exact .cons ihHead ihTail

/-- Memory analogue of `computeTreeBinds_shapeMatch`. -/
theorem memoryTreeBinds_shapeMatch {z : K} {st : NTree MemoryRowSkeleton}
    {et : NTree (MemoryTable.MState × MemoryTable.DTmem K)}
    (h : MemoryTreeBinds z st et) : MemoryShapeMatch st et := by
  refine MemoryTreeBinds.rec
    (motive_1 := fun st et _ => MemoryShapeMatch st et)
    (motive_2 := fun sts ets _ => List.Forall₂ MemoryShapeMatch sts ets)
    ?_ ?_ ?_ h
  · intro s sc row rc hshape _ _ ihChildren
    exact .node hshape ihChildren
  · exact .nil
  · intro _ _ _ _ _ _ ihHead ihTail
    exact .cons ihHead ihTail

/-! ### Tree assembly -/

/-- **Step 2, compute forest form.**  The structural match plus the flat canonical BFS row bindings
rebuild the recursive `ComputeTreeBinds`. -/
theorem computeTreeBinds_forest_of_shapeMatch {z : K}
    {ss : List (NTree ComputeRowSkeleton)}
    {trees : List (NTree (ComputeTable.State × ComputeTable.DTcomp K))}
    (hshape : List.Forall₂ ComputeShapeMatch ss trees)
    (hrows : List.Forall₂ (BindComputeRow z)
      ((bfsForest ss).map NTree.label) ((bfsForest trees).map NTree.label)) :
    List.Forall₂ (ComputeTreeBinds z) ss trees := by
  refine treeRel_of_bfs ComputeShapeMatch (BindComputeRow z) (ComputeTreeBinds z)
    (fun _ _ hm => hm.children_match) ?_ (totalSize ss) le_rfl hshape hrows
  intro st et hmatch hrow hchildren
  cases st with
  | node s sc =>
      cases et with
      | node row rc =>
          exact .node hmatch.arity_eq hrow hchildren

/-- **Step 2, memory forest form.** -/
theorem memoryTreeBinds_forest_of_shapeMatch {z : K}
    {ss : List (NTree MemoryRowSkeleton)}
    {trees : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))}
    (hshape : List.Forall₂ MemoryShapeMatch ss trees)
    (hrows : List.Forall₂ (BindMemoryRow z)
      ((bfsForest ss).map NTree.label) ((bfsForest trees).map NTree.label)) :
    List.Forall₂ (MemoryTreeBinds z) ss trees := by
  refine treeRel_of_bfs MemoryShapeMatch (BindMemoryRow z) (MemoryTreeBinds z)
    (fun _ _ hm => hm.children_match) ?_ (totalSize ss) le_rfl hshape hrows
  intro st et hmatch hrow hchildren
  cases st with
  | node s sc =>
      cases et with
      | node row rc =>
          exact .node hmatch.arity_eq hrow hchildren

/-- Single-tree specialization of `computeTreeBinds_forest_of_shapeMatch`. -/
theorem computeTreeBinds_of_shapeMatch {z : K}
    {st : NTree ComputeRowSkeleton}
    {et : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (hshape : ComputeShapeMatch st et)
    (hrows : List.Forall₂ (BindComputeRow z)
      ((bfsForest [st]).map NTree.label) ((bfsForest [et]).map NTree.label)) :
    ComputeTreeBinds z st et := by
  have h := computeTreeBinds_forest_of_shapeMatch (.cons hshape .nil) hrows
  cases h with
  | cons hhead _ => exact hhead

/-! ### Row-count agreement from the shape datum

A1 states its full enumeration-completeness results under a row-count agreement hypothesis
(`scan_covers_all_compute_rows`) that `BindsAt` used to supply.  The structural datum supplies it
directly, before any binding exists. -/

private theorem bfs_forall₂ {A B : Type} (Shape : NTree A → NTree B → Prop)
    (childShape : ∀ s t, Shape s t → List.Forall₂ Shape s.children t.children) :
    ∀ (n : ℕ) {ss : List (NTree A)} {trees : List (NTree B)},
      totalSize ss ≤ n → List.Forall₂ Shape ss trees →
      List.Forall₂ Shape (bfsForest ss) (bfsForest trees) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro ss trees hsize hshape
      cases hshape with
      | nil => simp [bfsForest_nil]
      | @cons s tree ss trees hhead htail =>
          let source : List (NTree A) := s :: ss
          let target : List (NTree B) := tree :: trees
          have hall : List.Forall₂ Shape source target := .cons hhead htail
          have hsource : source ≠ [] := by simp [source]
          have htarget : target ≠ [] := by simp [target]
          have hchildShape : List.Forall₂ Shape
              (source.flatMap NTree.children) (target.flatMap NTree.children) :=
            List.rel_flatMap hall (fun _ _ hab => childShape _ _ hab)
          have hlt : totalSize (source.flatMap NTree.children) < n := by
            have htotal := totalSize_flatMap_children source
            have hsourceLen : 0 < source.length := List.length_pos_of_ne_nil hsource
            change totalSize source ≤ n at hsize
            omega
          rw [bfsForest_cons_eq source hsource, bfsForest_cons_eq target htarget]
          exact List.rel_append hall (ih _ hlt le_rfl hchildShape)

omit [Field K] in
/-- Canonical compute BFS row counts agree, from the structural datum alone. -/
theorem computeRows_length_eq_of_shapeMatch
    {st : NTree ComputeRowSkeleton}
    {et : NTree (ComputeTable.State × ComputeTable.DTcomp K)}
    (hshape : ComputeShapeMatch st et) :
    ((bfsForest [st]).map NTree.label).length =
      ((bfsForest [et]).map NTree.label).length := by
  have h := bfs_forall₂ ComputeShapeMatch (fun _ _ hm => hm.children_match)
    (totalSize [st]) le_rfl (.cons hshape .nil)
  simp [h.length_eq]

omit [Field K] in
/-- Canonical memory BFS row counts agree, from the structural datum alone. -/
theorem memoryRows_length_eq_of_shapeMatch
    {ss : List (NTree MemoryRowSkeleton)}
    {trees : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))}
    (hshape : List.Forall₂ MemoryShapeMatch ss trees) :
    ((bfsForest ss).map NTree.label).length =
      ((bfsForest trees).map NTree.label).length := by
  have h := bfs_forall₂ MemoryShapeMatch (fun _ _ hm => hm.children_match)
    (totalSize ss) le_rfl hshape
  simp [h.length_eq]

/-! ## Carrier-generic form of the A1 scan

`ActiveFingerprintScan.activeComputeSlotsOn` is phrased on a raw family's own arrays.  The same
enumeration is needed at the `(cfg, exec)` pair produced by the production verifier's
`specializedProblem`, so it is restated on a bare `ExactExecution`.  The two agree by `rfl`
(`activeComputeSlotsAt_eq`, `activeFingerprintChecksAt_iff`), so every A1 lemma transports; nothing is
re-derived. -/

/-- The A1 compute scan, on a bare execution carrier. -/
def activeComputeSlotsAt (C : SkeletonCommitment) {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) : List (Noun × ComputeTable.FP K) :=
  (List.zip (computeSkeletonRows C.skeleton) exec.computeRows).flatMap
    (fun q => computeRowSlots q.1 q.2)

/-- The A1 memory scan, on a bare execution carrier. -/
def activeMemorySlotsAt (C : SkeletonCommitment) {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) : List (Noun × ComputeTable.FP K) :=
  (List.zip (memorySkeletonRows C.skeleton) exec.memoryRows).flatMap
    (fun q => memoryRowSlots q.1 q.2)

/-- The A1 post-seed check, on a bare execution carrier. -/
def ActiveFingerprintChecksAt (z : K) (C : SkeletonCommitment) {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) : Prop :=
  (∀ e ∈ activeComputeSlotsAt C exec, e.2 = GlobalCarryRecognizer.enc z e.1) ∧
    ∀ e ∈ activeMemorySlotsAt C exec, e.2 = GlobalCarryRecognizer.enc z e.1

theorem activeComputeSlotsAt_eq (C : SkeletonCommitment)
    (R : RawPlusIOSegmentedFamily F K) :
    activeComputeSlotsAt C R.exec = activeComputeSlotsOn C R := rfl

theorem activeMemorySlotsAt_eq (C : SkeletonCommitment)
    (R : RawPlusIOSegmentedFamily F K) :
    activeMemorySlotsAt C R.exec = activeMemorySlotsOn C R := rfl

/-- The carrier-generic scan on a raw family's own arrays **is** the A1 scan. -/
theorem activeFingerprintChecksAt_iff (z : K) (C : SkeletonCommitment)
    (R : RawPlusIOSegmentedFamily F K) :
    ActiveFingerprintChecksAt z C R.exec ↔ ActiveFingerprintChecksOn z C R := Iff.rfl

/-! ## The two named A2 data -/

/-- **The tree-shape datum.**  Purely structural: no seed, no fingerprint, no noun.  This is the
`node.shape`/`children` content of `ComputeTreeBinds` and `MemoryTreeBinds`, which no field of
`StrictRawStrategy.StrictRawP8Strategy` supplies. -/
structure ExecTreeShapeMatchesAt (C : SkeletonCommitment) {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) : Prop where
  compute : ComputeShapeMatch C.skeleton.computeTree exec.computeTree
  memory : List.Forall₂ MemoryShapeMatch C.skeleton.memoryForest exec.memoryForest

/-- **The frame datum.**  The per-row non-fingerprint residual, on exactly the zip pairing the A1
scan itself uses. -/
structure RowFrameChecksAt (z : K) (C : SkeletonCommitment) {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) : Prop where
  compute : ∀ e ∈ List.zip (computeSkeletonRows C.skeleton) exec.computeRows,
    ComputeRowFrame z e.1 e.2
  memory : ∀ e ∈ List.zip (memorySkeletonRows C.skeleton) exec.memoryRows,
    MemoryRowFrame z e.1 e.2

/-- The canonical compute row bindings, rebuilt from the scan, the frame, and the row-count agreement
the shape datum supplies. -/
theorem forall₂_bindComputeRow_of_scan {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hlen : (computeSkeletonRows C.skeleton).length = exec.computeRows.length)
    (hframe : ∀ e ∈ List.zip (computeSkeletonRows C.skeleton) exec.computeRows,
      ComputeRowFrame z e.1 e.2)
    (hscan : ∀ e ∈ activeComputeSlotsAt C exec, e.2 = GlobalCarryRecognizer.enc z e.1) :
    List.Forall₂ (BindComputeRow z) (computeSkeletonRows C.skeleton) exec.computeRows := by
  refine List.forall₂_iff_zip.2 ⟨hlen, ?_⟩
  intro s row hzip
  refine bindComputeRow_of_slots ?_ (hframe (s, row) hzip)
  intro e he
  exact hscan e (List.mem_flatMap.2 ⟨(s, row), hzip, he⟩)

/-- Memory analogue of `forall₂_bindComputeRow_of_scan`. -/
theorem forall₂_bindMemoryRow_of_scan {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hlen : (memorySkeletonRows C.skeleton).length = exec.memoryRows.length)
    (hframe : ∀ e ∈ List.zip (memorySkeletonRows C.skeleton) exec.memoryRows,
      MemoryRowFrame z e.1 e.2)
    (hscan : ∀ e ∈ activeMemorySlotsAt C exec, e.2 = GlobalCarryRecognizer.enc z e.1) :
    List.Forall₂ (BindMemoryRow z) (memorySkeletonRows C.skeleton) exec.memoryRows := by
  refine List.forall₂_iff_zip.2 ⟨hlen, ?_⟩
  intro s row hzip
  refine bindMemoryRow_of_slots ?_ (hframe (s, row) hzip)
  intro e he
  exact hscan e (List.mem_flatMap.2 ⟨(s, row), hzip, he⟩)

/-! ### `BindsAt` from the scan -/

/-- The seed pin, the tree-shape datum, the frame
checks, and A1's active fingerprint scan rebuild the full canonical binding.  `BindsAt.ofTreeBindings`
is used, so the flat BFS row fields are derived rather than supplied. -/
theorem bindsAt_of_scan {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hseed : cfg.challenges.z = z)
    (hshape : ExecTreeShapeMatchesAt C exec)
    (hframe : RowFrameChecksAt z C exec)
    (hscan : ActiveFingerprintChecksAt z C exec) :
    BindsAt z C.skeleton cfg exec := by
  have hlenC : (computeSkeletonRows C.skeleton).length = exec.computeRows.length := by
    simpa [computeSkeletonRows, ExactExecution.computeRows] using
      computeRows_length_eq_of_shapeMatch hshape.compute
  have hlenM : (memorySkeletonRows C.skeleton).length = exec.memoryRows.length := by
    simpa [memorySkeletonRows, ExactExecution.memoryRows] using
      memoryRows_length_eq_of_shapeMatch hshape.memory
  have hrowsC := forall₂_bindComputeRow_of_scan hlenC hframe.compute hscan.1
  have hrowsM := forall₂_bindMemoryRow_of_scan hlenM hframe.memory hscan.2
  refine BindsAt.ofTreeBindings hseed ?_ ?_
  · refine computeTreeBinds_of_shapeMatch hshape.compute ?_
    simpa [computeSkeletonRows, ExactExecution.computeRows] using hrowsC
  · refine memoryTreeBinds_forest_of_shapeMatch hshape.memory ?_
    simpa [memorySkeletonRows, ExactExecution.memoryRows] using hrowsM

/-- A genuine binding supplies the tree-shape datum. -/
theorem execTreeShapeMatchesAt_of_bindsAt {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z C.skeleton cfg exec) : ExecTreeShapeMatchesAt C exec where
  compute := computeTreeBinds_shapeMatch h.computeTree
  memory := h.memoryForest.imp (fun _ _ hm => memoryTreeBinds_shapeMatch hm)

/-- A genuine binding supplies the frame checks. -/
theorem rowFrameChecksAt_of_bindsAt {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z C.skeleton cfg exec) : RowFrameChecksAt z C exec where
  compute := fun _ he => bindComputeRow_frame (List.forall₂_zip h.derived_computeRows he)
  memory := fun _ he => bindMemoryRow_frame (List.forall₂_zip h.derived_memoryRows he)

/-- A1's scan, in carrier-generic spelling. -/
theorem activeFingerprintChecksAt_of_bindsAt {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : BindsAt z C.skeleton cfg exec) : ActiveFingerprintChecksAt z C exec := by
  constructor
  · intro e he
    obtain ⟨q, hq, hmem⟩ := List.mem_flatMap.1 he
    exact bindComputeRow_slots (List.forall₂_zip h.derived_computeRows hq) e hmem
  · intro e he
    obtain ⟨q, hq, hmem⟩ := List.mem_flatMap.1 he
    exact bindMemoryRow_slots (List.forall₂_zip h.derived_memoryRows hq) e hmem

/-- **The exact characterization: A2 is the genuine converse of A1.**  The canonical binding is
equivalent to the seed pin, the tree-shape datum, the frame checks, and A1's active fingerprint scan
— nothing more and nothing less.  In particular the two named A2 data are the precise residual A1's
scan does not capture, and they are *implied* by the binding, hence never a strengthening. -/
theorem bindsAt_iff_scan {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} :
    BindsAt z C.skeleton cfg exec ↔
      (cfg.challenges.z = z ∧ ExecTreeShapeMatchesAt C exec ∧
        RowFrameChecksAt z C exec ∧ ActiveFingerprintChecksAt z C exec) :=
  ⟨fun h => ⟨h.sampledSeed, execTreeShapeMatchesAt_of_bindsAt h,
      rowFrameChecksAt_of_bindsAt h, activeFingerprintChecksAt_of_bindsAt h⟩,
    fun h => bindsAt_of_scan h.1 h.2.1 h.2.2.1 h.2.2.2⟩

/-! ### Raw-family spelling -/

/-- Step 3 on a raw family, consuming A1's `ActiveFingerprintChecksOn` verbatim. -/
theorem bindsAt_of_scanOn {z : K} {C : SkeletonCommitment}
    {R : RawPlusIOSegmentedFamily F K}
    (hseed : R.cfg.challenges.z = z)
    (hshape : ExecTreeShapeMatchesAt C R.exec)
    (hframe : RowFrameChecksAt z C R.exec)
    (hscan : ActiveFingerprintChecksOn z C R) :
    BindsAt z C.skeleton R.cfg R.exec :=
  bindsAt_of_scan hseed hshape hframe ((activeFingerprintChecksAt_iff z C R).2 hscan)

/-- Raw-family form of `bindsAt_iff_scan`. -/
theorem bindsAt_iff_scanOn {z : K} {C : SkeletonCommitment}
    {R : RawPlusIOSegmentedFamily F K} :
    BindsAt z C.skeleton R.cfg R.exec ↔
      (R.cfg.challenges.z = z ∧ ExecTreeShapeMatchesAt C R.exec ∧
        RowFrameChecksAt z C R.exec ∧ ActiveFingerprintChecksOn z C R) := by
  rw [bindsAt_iff_scan]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => activeFingerprintChecksAt_iff z C R

/-! ### Step 3 on the strict raw strategy -/

section Strict

open Nock.NockVMROM.Thm54.StrictRawStrategy

variable {p : ℕ}

/-- **The strict strategy's own post-seed check rebuilds the binding.**  `sampledSeed` and
`fingerprintChecks` are fields of `PostSeedRawCommitment`, so the only added inputs are the two named
A2 data. -/
theorem strictRawP8Strategy_bindsAt (T : StrictRawP8Strategy F K p)
    (hshape : ∀ (z : K) (hz : z ≠ 0),
      ExecTreeShapeMatchesAt T.beforeSeed (T.afterSeed z hz).family.exec)
    (hframe : ∀ (z : K) (hz : z ≠ 0),
      RowFrameChecksAt z T.beforeSeed (T.afterSeed z hz).family.exec)
    (z : K) (hz : z ≠ 0) :
    BindsAt z T.beforeSeed.skeleton
      (T.afterSeed z hz).family.cfg (T.afterSeed z hz).family.exec :=
  bindsAt_of_scanOn (T.afterSeed z hz).sampledSeed (hshape z hz) (hframe z hz)
    (T.afterSeed z hz).checks

/-- Whole-execution noun realization for a strict strategy, from the two deterministic checks plus the
two named A2 data.  No acceptance, no `BareSemanticSupport`. -/
theorem strictRawP8Strategy_nounRealization (T : StrictRawP8Strategy F K p)
    (hcanon : CanonicalCommitmentCheck p T.beforeSeed)
    (hshape : ∀ (z : K) (hz : z ≠ 0),
      ExecTreeShapeMatchesAt T.beforeSeed (T.afterSeed z hz).family.exec)
    (hframe : ∀ (z : K) (hz : z ≠ 0),
      RowFrameChecksAt z T.beforeSeed (T.afterSeed z hz).family.exec)
    (z : K) (hz : z ≠ 0) :
    ExactExecutionNounRealization p
      (T.afterSeed z hz).family.cfg (T.afterSeed z hz).family.exec :=
  (strictRawP8Strategy_bindsAt T hshape hframe z hz).nounRealization hz
    hcanon.skeletonBoundedBy

end Strict

/-! ## Production-record realizations

`StrictOperationalEvidence.strict_s0_record_of_bound` / `strict_s9_record_of_bound` take exactly a
`BindMemRec` for the live record, which the scan-derived row binding now supplies.  The two
`GlobalCarryAxis.ServedLookup` fields of `StrictRowOperationalEvidence` are **not** derived here: they
remain fields of `BoundSemanticTrace.SkeletonOperationalCore`, i.e. Packet B. -/

/-- The two memory-record obligations of `StrictOperationalEvidence.StrictRowOperationalEvidence`,
stated at the **actual** production table record of a canonical row rather than at the canonical
`encMemRec` fingerprint. -/
structure ScannedRowRecordRealization (z : K) (s : ComputeRowSkeleton)
    (row : ComputeTable.State × ComputeTable.DTcomp K) : Prop where
  s0_record : ∀ _h : s.state = .s0,
    OpcodeSemantics.RealizesMemRec z (computeMemRec row.2.2.1 (1 : Fin 3))
      s.subject s.evaluation (P8Census.skeletonMemoryAxis s 1)
  s9_record : ∀ _h : s.state = .s9,
    OpcodeSemantics.RealizesMemRec z (computeMemRec row.2.2.1 (2 : Fin 3))
      (P8Census.skeletonSubformula s 0 .result)
      (P8Census.skeletonSubformula s 1 .formula)
      (P8Census.skeletonMemoryAxis s 2)

/-- **Step 4.** -/
theorem scannedRowRecordRealization_of_bindComputeRow {z : K}
    {s : ComputeRowSkeleton} {row : ComputeTable.State × ComputeTable.DTcomp K}
    (core : BoundSemanticTrace.SkeletonOperationalCore s)
    (hbind : BindComputeRow z s row) :
    ScannedRowRecordRealization z s row where
  s0_record := fun h =>
    StrictOperationalEvidence.strict_s0_record_of_bound core h
      (bindComputeRow_memRec hbind 1 (by simp [h, Nock.Framework.recordCount]))
  s9_record := fun h =>
    StrictOperationalEvidence.strict_s9_record_of_bound core h
      (bindComputeRow_memRec hbind 2 (by simp [h, Nock.Framework.recordCount]))

/-- **Step 4, whole-family form.**  Every canonically paired compute row of a scanned execution
realizes its production memory records. -/
theorem scannedRowRecords_of_scan {q : ℕ} {z : K} {C : SkeletonCommitment}
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hshape : ExecTreeShapeMatchesAt C exec)
    (hframe : RowFrameChecksAt z C exec)
    (hscan : ActiveFingerprintChecksAt z C exec)
    (hop : ∀ s ∈ computeSkeletonRows C.skeleton,
      BoundSemanticTrace.SkeletonOperationalCore s) :
    ∀ e ∈ List.zip (computeSkeletonRows C.skeleton) exec.computeRows,
      ScannedRowRecordRealization z e.1 e.2 := by
  have hlenC : (computeSkeletonRows C.skeleton).length = exec.computeRows.length := by
    simpa [computeSkeletonRows, ExactExecution.computeRows] using
      computeRows_length_eq_of_shapeMatch hshape.compute
  have hrowsC := forall₂_bindComputeRow_of_scan hlenC hframe.compute hscan.1
  intro e he
  exact scannedRowRecordRealization_of_bindComputeRow
    (hop e.1 (List.of_mem_zip he).1) (List.forall₂_zip hrowsC he)

/-! ## The verifier-generated-topology scoped raw containment

The production containment consumes exactly one semantic input, `BareSemanticSupport.binds`, which is
an *assumed* field.  Here it is replaced by the derived binding of step 3: the prover supplies the
pre-seed commitment plus the two named A2 data, and the seed pin comes free from the timestamp
carrier (`TemplateRawJointSoundness.specializedProblem_seed`).

Every other premise of `ProductionP8Containment.accepted_outside_failureUnion` is passed through as an
explicitly named hypothesis, because A2 does not close it:

* `hop` — `BoundSemanticTrace.SkeletonOperationalCore`, whose two `ServedLookup` fields are Packet B;
* `hKp` / `hProgCap` / `hMemCap` — the `Ksz`/IO-capacity bounds, Packet C;
* `hchar`, `hcast`, `hcombined`, the combined census, and the size-window bound — the standing
  finite-field/census scope of the production theorem.

Interim scope, therefore: `BareSemanticSupport.binds` is **restated as three deterministic,
check-shaped premises (`hshape ∧ hframe ∧ hscan`) that are provably equivalent to it** (see
`bindsAt_iff_scan`), not weakened — the acceptance-side derivation of those checks (prover-committed
topology for `hshape`, and the served lookups in `hop`) remains Packet B/C. Nothing else has moved. -/

section Containment

open Nock.NockVMROM.Thm54.TemplateRawJointSoundness

variable [Fintype K] [DecidableEq K] [charRing : CharP K (ringChar K)]
variable {Λ : ℕ}

/-- **The scan-derived semantic support.**  `binds` is a theorem, not a field: it is produced by
`bindsAt_of_scan` from the pre-seed commitment and the two named A2 data. -/
def bareSemanticSupport_of_scan
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (C : SkeletonCommitment)
    (hclaim : C.skeleton.publicClaim = V.raw.claim)
    (hshape : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ExecTreeShapeMatchesAt C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hframe : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      RowFrameChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hscan : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ActiveFingerprintChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec) :
    ProductionP8Containment.BareSemanticSupport F K V where
  skeleton := C.skeleton
  publicClaim_eq := hclaim
  binds := fun z hz α lmb =>
    bindsAt_of_scan (specializedProblem_seed V.raw.timestamp z hz α lmb)
      (hshape z hz α lmb) (hframe z hz α lmb) (hscan z hz α lmb)

/-- The production strategy whose semantic support is derived rather than assumed. -/
def productionStrategy_of_scan
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (C : SkeletonCommitment)
    (hclaim : C.skeleton.publicClaim = V.raw.claim)
    (hshape : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ExecTreeShapeMatchesAt C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hframe : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      RowFrameChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hscan : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ActiveFingerprintChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec) :
    ProductionP8Containment.ProductionStrategy F K :=
  ProductionP8Containment.ProductionStrategy.ofBare
    (bareSemanticSupport_of_scan V C hclaim hshape hframe hscan)

/-- The scan-derived strategy binds at every specialization (`BareSemanticSupport.binds`). -/
theorem productionStrategy_of_scan_bindsAll
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (C : SkeletonCommitment)
    (hclaim : C.skeleton.publicClaim = V.raw.claim)
    (hshape : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ExecTreeShapeMatchesAt C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hframe : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      RowFrameChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hscan : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ActiveFingerprintChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec) :
    (productionStrategy_of_scan V C hclaim hshape hframe hscan).BindsAll :=
  ProductionP8Containment.ProductionStrategy.ofBare_bindsAll _

omit [Fintype K] [DecidableEq K] in
@[simp] theorem productionStrategy_of_scan_skeleton
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (C : SkeletonCommitment) (hclaim hshape hframe hscan) :
    (productionStrategy_of_scan V C hclaim hshape hframe hscan).skeleton = C.skeleton := rfl

omit [Fintype K] [DecidableEq K] in
@[simp] theorem productionStrategy_of_scan_verifier
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (C : SkeletonCommitment) (hclaim hshape hframe hscan) :
    (productionStrategy_of_scan V C hclaim hshape hframe hscan).verifier = V := rfl

/-- **Verifier-generated-topology scoped raw containment (interim).**  An accepting coin outside the
five-class failure union hits the genuine target, with the semantic binding *derived from the
deterministic pre-seed commitment check and the post-seed active fingerprint scan* instead of being
assumed as `ProductionP8Containment.BareSemanticSupport.binds`.  The named residual hypotheses are
the operational core (Packet B's served lookups), the IO-capacity bounds (Packet C), and the standing
census/character scope of the production theorem. -/
theorem verifierGeneratedTopologyRawContainment
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K))
    (C : SkeletonCommitment) (q : ℕ)
    (hclaim : C.skeleton.publicClaim = V.raw.claim)
    (hshape : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ExecTreeShapeMatchesAt C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hframe : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      RowFrameChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hscan : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ActiveFingerprintChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (census : EdgeComparisonCensus.CombinedSkeletonCensus K C.skeleton Λ)
    (hchar : NodeEncoding.StateTagChar K)
    (hq : 1 < q)
    (hqChar : q = ringChar K)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbound : C.skeleton.BoundedBy q)
    (hcombined : ProductionP8Containment.CombinedBoundedBy K q C.skeleton)
    (hop : ∀ s ∈ computeSkeletonRows C.skeleton,
      BoundSemanticTrace.SkeletonOperationalCore s)
    (hKp : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem V.raw.timestamp z hz α lmb).cfg.Ksz < ringChar K)
    (hProgCap : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem V.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1 ≤
        2 ^ (specializedProblem V.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hMemCap : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem V.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1 ≤
        2 ^ (specializedProblem V.raw.timestamp z hz α lmb).cfg.orbit.h)
    (ω : JointCoins K) (lmb : K)
    (hacc : (productionStrategy_of_scan V C hclaim hshape hframe hscan).Accepts ω lmb)
    (hout : ω ∉ ProductionP8Containment.FailureUnion
      (productionStrategy_of_scan V C hclaim hshape hframe hscan) census lmb)
    (hlam : ∀ (hz : nprSeed ω ≠ 0) i,
      (((productionStrategy_of_scan V C hclaim hshape hframe hscan).verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda = ((productionStrategy_of_scan V C hclaim hshape hframe hscan).verifier.familyAt ω lmb hz).cfg.challenges.lam) :
    ProductionP8Containment.GenuineTargetAt
      (productionStrategy_of_scan V C hclaim hshape hframe hscan) q Λ ω lmb :=
  ProductionP8Containment.accepted_outside_failureUnion
    (productionStrategy_of_scan V C hclaim hshape hframe hscan) census q
    hchar hq hqChar hcast hbound hcombined hop hKp hProgCap hMemCap
    (productionStrategy_of_scan_bindsAll V C hclaim hshape hframe hscan) ω lmb hacc hout hlam

/-- The false-acceptance probability bound with a **derived** semantic support.  Same interim scope as
`verifierGeneratedTopologyRawContainment`. -/
theorem verifierGeneratedTopology_jointProbability_falseAcceptance_le
    (h2 : (2 : K) ≠ 0)
    (V : ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K)) (lmb : K)
    (C : SkeletonCommitment) (q topologyBound axisWorkload : ℕ)
    (hclaim : C.skeleton.publicClaim = V.raw.claim)
    (hshape : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ExecTreeShapeMatchesAt C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hframe : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      RowFrameChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (hscan : ∀ (z : K) (hz : z ≠ 0) (α lmb : K),
      ActiveFingerprintChecksAt z C (specializedProblem V.raw.timestamp z hz α lmb).exec)
    (census : EdgeComparisonCensus.CombinedSkeletonCensus K C.skeleton Λ)
    (hchar : NodeEncoding.StateTagChar K)
    (hq : 1 < q)
    (hqChar : q = ringChar K)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbound : C.skeleton.BoundedBy q)
    (hcombined : ProductionP8Containment.CombinedBoundedBy K q C.skeleton)
    (hop : ∀ s ∈ computeSkeletonRows C.skeleton,
      BoundSemanticTrace.SkeletonOperationalCore s)
    (hwindowBound : SizeWindowCounting.SizeWindowNounsBoundedBy C.skeleton Λ)
    (hKp : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem V.raw.timestamp z hz α lmb).cfg.Ksz < ringChar K)
    (hProgCap : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem V.raw.timestamp z hz α lmb).exec.derivedRequestIO.length + 1 ≤
        2 ^ (specializedProblem V.raw.timestamp z hz α lmb).cfg.orbit.h)
    (hMemCap : ∀ z (hz : z ≠ 0) α lmb,
      (specializedProblem V.raw.timestamp z hz α lmb).exec.derivedResponseIO.length + 1 ≤
        2 ^ (specializedProblem V.raw.timestamp z hz α lmb).cfg.orbit.h)
    (htopology : ∀ z (hz : z ≠ 0) α lmb,
      topologyWorkload (V.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis : ∀ z (hz : z ≠ 0),
      TemplateAxisCounting.templateAxisWorkload
        (ProductionAxisStructureVerifier.committedTemplate V z hz) ≤ axisWorkload)
    (hlam : ∀ ω (hz : nprSeed ω ≠ 0) i,
      (((productionStrategy_of_scan V C hclaim hshape hframe hscan).verifier.familyAt ω lmb hz).exec.memoryPubAt i).lambda = ((productionStrategy_of_scan V C hclaim hshape hframe hscan).verifier.familyAt ω lmb hz).cfg.challenges.lam) :
    |jointProbability (ProductionP8Containment.FalseAcceptanceSet
        (productionStrategy_of_scan V C hclaim hshape hframe hscan) q Λ lmb)| ≤
      (ProductionP8Containment.workload (productionStrategy_of_scan V C hclaim hshape hframe hscan)
        Λ topologyBound axisWorkload : ℝ) / (Fintype.card K : ℝ) :=
  ProductionP8Containment.production_jointProbability_falseAcceptance_le h2
    (productionStrategy_of_scan V C hclaim hshape hframe hscan) lmb census
    q topologyBound axisWorkload hchar hq hqChar hcast hbound hcombined hop hwindowBound
    hKp hProgCap hMemCap htopology haxis hlam
    (productionStrategy_of_scan_bindsAll V C hclaim hshape hframe hscan)

end Containment

end

end Nock.NockVMROM.Thm54.RawSemanticAssembly

#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bindComputeRow_frame
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bindMemoryRow_frame
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bindComputeRow_of_slots
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bindMemoryRow_of_slots
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bindComputeRow_iff_slots
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bindMemoryRow_iff_slots
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bindComputeRow_memRec
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.ComputeShapeMatch.arity_eq
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.ComputeShapeMatch.children_match
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.MemoryShapeMatch.arity_eq
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.MemoryShapeMatch.children_match
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.computeTreeBinds_shapeMatch
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.memoryTreeBinds_shapeMatch
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.computeTreeBinds_forest_of_shapeMatch
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.memoryTreeBinds_forest_of_shapeMatch
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.computeTreeBinds_of_shapeMatch
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.computeRows_length_eq_of_shapeMatch
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.memoryRows_length_eq_of_shapeMatch
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.activeComputeSlotsAt
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.activeMemorySlotsAt
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.ActiveFingerprintChecksAt
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.activeComputeSlotsAt_eq
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.activeMemorySlotsAt_eq
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.activeFingerprintChecksAt_iff
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.forall₂_bindComputeRow_of_scan
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.forall₂_bindMemoryRow_of_scan
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bindsAt_of_scan
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.execTreeShapeMatchesAt_of_bindsAt
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.rowFrameChecksAt_of_bindsAt
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.activeFingerprintChecksAt_of_bindsAt
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bindsAt_iff_scan
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bindsAt_of_scanOn
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bindsAt_iff_scanOn
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.strictRawP8Strategy_bindsAt
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.strictRawP8Strategy_nounRealization
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.scannedRowRecordRealization_of_bindComputeRow
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.scannedRowRecords_of_scan
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.bareSemanticSupport_of_scan
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.productionStrategy_of_scan
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.productionStrategy_of_scan_skeleton
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.productionStrategy_of_scan_verifier
#print axioms Nock.NockVMROM.Thm54.RawSemanticAssembly.verifierGeneratedTopologyRawContainment
#print axioms
  Nock.NockVMROM.Thm54.RawSemanticAssembly.verifierGeneratedTopology_jointProbability_falseAcceptance_le
