/-
  Nock/NockVMROM/Thm54/StrictOperationalEvidence.lean

  `BoundSemanticTrace.SkeletonOperationalCore` states its two memory-record obligations as *noun
  equalities* on the pre-seed skeleton record.

  * the compute table only ever sees **fingerprints**, so the record obligation a consumer needs is
    `OpcodeSemantics.RealizesMemRec` (root/child fingerprint realization + a Nat axis), not a noun
    equality;
  * strict OP4 is the paper's modular increment `+(n) = (1+n) mod p`, which is **total** on atoms.  It therefore needs only
    `(lusFBy p operand).isSome`, never a no-overflow bound.

  `StrictRowOperationalEvidence` is that consumer-minimal package.  The `evalN` refinement layer
  (`IncrementNoOverflow`, `incNoWrap`) is kept in a clearly separated section below and is *not* a
  field of the strict structure.

  Scope note: the two `served` fields are *definitions* here, copied verbatim from
  `SkeletonOperationalCore`.  Deriving them from acceptance is Packet B and is not attempted.
-/

import Nock.NockVMROM.Thm54.BoundSemanticTrace
import Nock.PaperReferenceMod

namespace Nock.NockVMROM.Thm54.StrictOperationalEvidence

open scoped Classical
open Nock Nock.Walk

noncomputable section

variable {K : Type} [Field K]

/-- The pre-seed compute row, as in `BoundSemanticTrace`. -/
abbrev RowSkeleton := SemanticStrategy.ComputeRowSkeleton

/-! ## The canonical fingerprint of a pre-seed memory record

`SemanticStrategy.MemRecSkeleton` is noun/Nat data; `ComputeTable.MemRec K` is field data.  The
canonical seed-`z` fingerprint of a skeleton record is the record whose root/child are the NPR
encodings of the skeleton nouns and whose axis is the Nat axis cast into `K`.  The timestamp is not
interpreted by `RealizesMemRec` (timestamp faithfulness is `Thm54.RecordBridge`), so it is `0`. -/
def encMemRec (z : K) (m : SemanticStrategy.MemRecSkeleton) : ComputeTable.MemRec K where
  root := GlobalCarryRecognizer.enc z m.root
  child := GlobalCarryRecognizer.enc z m.child
  axis := (m.axis : K)
  ts := 0

@[simp] theorem encMemRec_root (z : K) (m : SemanticStrategy.MemRecSkeleton) :
    (encMemRec z m).root = GlobalCarryRecognizer.enc z m.root := rfl

@[simp] theorem encMemRec_child (z : K) (m : SemanticStrategy.MemRecSkeleton) :
    (encMemRec z m).child = GlobalCarryRecognizer.enc z m.child := rfl

@[simp] theorem encMemRec_axis (z : K) (m : SemanticStrategy.MemRecSkeleton) :
    (encMemRec z m).axis = (m.axis : K) := rfl

/-- The total axis projection agrees with the live record's axis on an active slot. -/
theorem skeletonMemoryAxis_eq (s : RowSkeleton) (i : Fin 3)
    (h : (i : ℕ) < Nock.Framework.recordCount s.state) :
    P8Census.skeletonMemoryAxis s i = (s.memoryRecord i h).axis := by
  simp [P8Census.skeletonMemoryAxis, h]

/-! ## Strict (modular) row operational evidence -/

/-- **Consumer-minimal strict operational evidence for one pre-seed compute row.**

Three differences from `BoundSemanticTrace.SkeletonOperationalCore`:

* the `s0`/`s9` record obligations are **fingerprint-level** (`OpcodeSemantics.RealizesMemRec` at the
  canonical seed-`z` record fingerprint), not noun equalities;
* the arithmetic obligation is the strict modular OP4 success `(lusFBy p operand).isSome`, i.e. the
  paper's `+(n) = (1+n) mod p`; there is **no** `IncrementNoOverflow` field;
* `p` is the strict modular prime of the paper fragment, and `z` the NPR seed.

`s0_served`/`s9_served` are copied verbatim from `SkeletonOperationalCore`; they are *definitions*
of the served-memory obligation, pending the acceptance-side derivation (Packet B). -/
structure StrictRowOperationalEvidence (p : ℕ) (z : K) (s : RowSkeleton) : Prop where
  s0_record :
    ∀ h : s.state = .s0,
      OpcodeSemantics.RealizesMemRec z
        (encMemRec z
          (s.memoryRecord (1 : Fin 3) (by simp [h, Nock.Framework.recordCount])))
        s.subject s.evaluation (P8Census.skeletonMemoryAxis s 1)
  s9_record :
    ∀ h : s.state = .s9,
      OpcodeSemantics.RealizesMemRec z
        (encMemRec z
          (s.memoryRecord (2 : Fin 3) (by simp [h, Nock.Framework.recordCount])))
        (P8Census.skeletonSubformula s 0 .result)
        (P8Census.skeletonSubformula s 1 .formula)
        (P8Census.skeletonMemoryAxis s 2)
  s0_served :
    s.state = .s0 →
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun s.subject 1)
        (P8Census.skeletonMemoryAxis s 1) s.evaluation
  s9_served :
    s.state = .s9 →
      GlobalCarryAxis.ServedLookup
        (GlobalCarryRecognizer.ofNoun
          (P8Census.skeletonSubformula s 0 .result) 1)
        (P8Census.skeletonMemoryAxis s 2)
        (P8Census.skeletonSubformula s 1 .formula)
  s4_modular :
    s.state = .s4 →
      (FieldEmbedding.lusFBy p (P8Census.skeletonSubformula s 0 .result)).isSome

/-! ## Strict modular OP4 facts -/

/-- **Strict modular OP4 is total.**  The paper's `+(n) = (1+n) mod p` never crashes on an atom, so
no no-overflow side condition is required. -/
theorem strict_op4_total (p n : ℕ) :
    (FieldEmbedding.lusFBy p (.atom n)).isSome = true := by
  simp [FieldEmbedding.lusFBy]

/-- Modular OP4 crashes exactly on a cell operand. -/
theorem strict_op4_cell (p : ℕ) (a b : Noun) :
    FieldEmbedding.lusFBy p (.cell a b) = none := by
  simp [FieldEmbedding.lusFBy]

/-- Success of modular OP4 forces an atom operand: the strict evidence still pins the shape. -/
theorem atom_of_strict_op4 {p : ℕ} {v : Noun}
    (h : (FieldEmbedding.lusFBy p v).isSome = true) : ∃ n, v = .atom n := by
  cases v with
  | atom n => exact ⟨n, rfl⟩
  | cell a b => simp [strict_op4_cell] at h

/-- **Strict modular OP4 wraps at the top residue** rather than overflowing. -/
theorem strict_op4_wraps_at_top (p : ℕ) (hp : 0 < p) :
    FieldEmbedding.lusFBy p (.atom (p - 1)) = some (.atom 0) := by
  simp only [FieldEmbedding.lusFBy, Option.some.injEq]
  have hp' : p - 1 + 1 = p := by omega
  rw [hp', Nat.mod_self]

/-- The exact value of strict modular OP4. -/
theorem strict_op4_value (p n : ℕ) :
    FieldEmbedding.lusFBy p (.atom n) = some (.atom ((n + 1) % p)) := rfl

/-- **Scheduling lemma.**  For the strict paper evaluator `evalPaperMod`, the OP4 clause on a formula
whose operand evaluates to an atom is exactly the modular increment of that atom. -/
theorem strict_op4_evalPaperMod (q fuel : ℕ) (subj operand : Noun) (n : ℕ)
    (hoperand : evalPaperMod q fuel subj operand = some (.atom n)) :
    evalPaperMod q (fuel + 1) subj (.cell (.atom 4) operand) =
      FieldEmbedding.lusFBy q (.atom n) := by
  simp [evalPaperMod, hoperand]

/-- Closed form of the scheduling lemma: the OP4 clause is total once the operand is an atom. -/
theorem strict_op4_evalPaperMod_value (q fuel : ℕ) (subj operand : Noun) (n : ℕ)
    (hoperand : evalPaperMod q fuel subj operand = some (.atom n)) :
    evalPaperMod q (fuel + 1) subj (.cell (.atom 4) operand) =
      some (.atom ((n + 1) % q)) := by
  rw [strict_op4_evalPaperMod q fuel subj operand n hoperand, strict_op4_value]

/-! `OpcodeSemantics.IncrementNoOverflow` / `incNoWrap` belong to the unbounded Nat evaluator.  They are
kept strictly outside `StrictRowOperationalEvidence`; the lemmas below are the only sanctioned
traffic between the two layers. -/

theorem legacy_noOverflow_of_atom_below_top (q n : ℕ) (h : n + 1 < q) :
    OpcodeSemantics.IncrementNoOverflow q (.atom n) := by
  simpa [OpcodeSemantics.IncrementNoOverflow] using h

theorem legacy_noOverflow_of_atom_shape {q n : ℕ} {v : Noun}
    (hshape : v = .atom n) (hbound : n + 1 < q) :
    OpcodeSemantics.IncrementNoOverflow q v := by
  subst hshape
  exact legacy_noOverflow_of_atom_below_top q n hbound

/-- This is diagnostic and is not a field of `SkeletonOperationalCore`. -/
theorem legacy_s4_noOverflow_of_atom_shape {q n : ℕ} {s : RowSkeleton}
    (hshape : P8Census.skeletonSubformula s 0 .result = .atom n) (hbound : n + 1 < q) :
    OpcodeSemantics.IncrementNoOverflow q
      (P8Census.skeletonSubformula s 0 .result) :=
  legacy_noOverflow_of_atom_shape hshape hbound

/-- The bound is *not* derivable from the strict
evidence: at the top residue it is false (see `RedTeam.Batch24`). -/
theorem legacy_s4_noOverflow_of_strict {p q : ℕ} {z : K} {s : RowSkeleton}
    (ev : StrictRowOperationalEvidence p z s) (hstate : s.state = .s4)
    (hbound : ∀ n, P8Census.skeletonSubformula s 0 .result = .atom n → n + 1 < q) :
    OpcodeSemantics.IncrementNoOverflow q
      (P8Census.skeletonSubformula s 0 .result) := by
  obtain ⟨n, hn⟩ := atom_of_strict_op4 (ev.s4_modular hstate)
  exact legacy_noOverflow_of_atom_shape hn (hbound n hn)

theorem strict_op4_isSome_of_legacy_noOverflow {q p : ℕ} {v : Noun}
    (h : OpcodeSemantics.IncrementNoOverflow q v) :
    (FieldEmbedding.lusFBy p v).isSome = true := by
  cases v with
  | atom n => exact strict_op4_total p n
  | cell a b => exact h.elim


/-- Any table record **bound** to a skeleton record realizes the skeleton nouns and Nat axis.

This is the exact seam to the production compute table: `SemanticStrategy.BindMemRec` is the
after-seed binding datum (supplied by `SemanticStrategy.BindsAt`). -/
theorem realizesMemRec_of_bindMemRec {z : K} {m : SemanticStrategy.MemRecSkeleton}
    {r : ComputeTable.MemRec K} (hbind : SemanticStrategy.BindMemRec z m r)
    {root child : Noun} {axis : ℕ}
    (hroot : m.root = root) (hchild : m.child = child) (haxis : m.axis = axis) :
    OpcodeSemantics.RealizesMemRec z r root child axis where
  root_realizes := by
    have := hbind.1
    simp only [SemanticStrategy.bindFP] at this
    simpa [OpcodeSemantics.Realizes, ← hroot] using this
  child_realizes := by
    have := hbind.2.1
    simp only [SemanticStrategy.bindFP] at this
    simpa [OpcodeSemantics.Realizes, ← hchild] using this
  axis_realizes := by
    have := hbind.2.2
    rw [this, haxis]

/-- The canonical fingerprint of a skeleton record is itself bound to it. -/
theorem bindMemRec_encMemRec (z : K) (m : SemanticStrategy.MemRecSkeleton) :
    SemanticStrategy.BindMemRec z m (encMemRec z m) :=
  ⟨rfl, rfl, rfl⟩

/-- **Forward bridge.**

The record fields go noun-equality ⟶ `RealizesMemRec` at the **canonical** seed-`z` record
fingerprint `encMemRec` (`bindMemRec_encMemRec`), which is the only record derivable from a pre-seed
skeleton without extra data.  Pinning the obligation to a *production* row record instead requires
the after-seed binding datum `SemanticStrategy.BindMemRec z (s.memoryRecord i _) r`; see
`strict_s0_record_of_bound` / `strict_s9_record_of_bound`. -/
theorem StrictRowOperationalEvidence_of_operationalCore
    {s : RowSkeleton} (core : BoundSemanticTrace.SkeletonOperationalCore s)
    (p : ℕ) (z : K)
    (hs4 : s.state = .s4 →
      (FieldEmbedding.lusFBy p (P8Census.skeletonSubformula s 0 .result)).isSome) :
    StrictRowOperationalEvidence p z s where
  s0_record := by
    intro h
    obtain ⟨hroot, hchild⟩ := core.s0_record h
    have haxis :
        P8Census.skeletonMemoryAxis s 1 =
          (s.memoryRecord (1 : Fin 3)
            (by simp [h, Nock.Framework.recordCount])).axis :=
      skeletonMemoryAxis_eq s 1 _
    exact realizesMemRec_of_bindMemRec (bindMemRec_encMemRec z _)
      hroot hchild haxis.symm
  s9_record := by
    intro h
    obtain ⟨hroot, hchild⟩ := core.s9_record h
    have haxis :
        P8Census.skeletonMemoryAxis s 2 =
          (s.memoryRecord (2 : Fin 3)
            (by simp [h, Nock.Framework.recordCount])).axis :=
      skeletonMemoryAxis_eq s 2 _
    exact realizesMemRec_of_bindMemRec (bindMemRec_encMemRec z _)
      hroot hchild haxis.symm
  s0_served := core.s0_served
  s9_served := core.s9_served
  s4_modular := hs4

theorem strict_s0_record_of_bound {z : K} {s : RowSkeleton}
    (core : BoundSemanticTrace.SkeletonOperationalCore s)
    (h : s.state = .s0) {r : ComputeTable.MemRec K}
    (hbind : SemanticStrategy.BindMemRec z
      (s.memoryRecord (1 : Fin 3) (by simp [h, Nock.Framework.recordCount])) r) :
    OpcodeSemantics.RealizesMemRec z r s.subject s.evaluation
      (P8Census.skeletonMemoryAxis s 1) := by
  obtain ⟨hroot, hchild⟩ := core.s0_record h
  have haxis :
      P8Census.skeletonMemoryAxis s 1 =
        (s.memoryRecord (1 : Fin 3)
          (by simp [h, Nock.Framework.recordCount])).axis :=
    skeletonMemoryAxis_eq s 1 _
  exact realizesMemRec_of_bindMemRec hbind hroot hchild haxis.symm

/-- Production-record form of the `s9` obligation, for the live `mr3`. -/
theorem strict_s9_record_of_bound {z : K} {s : RowSkeleton}
    (core : BoundSemanticTrace.SkeletonOperationalCore s)
    (h : s.state = .s9) {r : ComputeTable.MemRec K}
    (hbind : SemanticStrategy.BindMemRec z
      (s.memoryRecord (2 : Fin 3) (by simp [h, Nock.Framework.recordCount])) r) :
    OpcodeSemantics.RealizesMemRec z r
      (P8Census.skeletonSubformula s 0 .result)
      (P8Census.skeletonSubformula s 1 .formula)
      (P8Census.skeletonMemoryAxis s 2) := by
  obtain ⟨hroot, hchild⟩ := core.s9_record h
  have haxis :
      P8Census.skeletonMemoryAxis s 2 =
        (s.memoryRecord (2 : Fin 3)
          (by simp [h, Nock.Framework.recordCount])).axis :=
    skeletonMemoryAxis_eq s 2 _
  exact realizesMemRec_of_bindMemRec hbind hroot hchild haxis.symm

end

end Nock.NockVMROM.Thm54.StrictOperationalEvidence

#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.strict_op4_total
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.strict_op4_cell
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.atom_of_strict_op4
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.strict_op4_wraps_at_top
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.strict_op4_value
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.strict_op4_evalPaperMod
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.strict_op4_evalPaperMod_value
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.skeletonMemoryAxis_eq
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.legacy_noOverflow_of_atom_below_top
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.legacy_noOverflow_of_atom_shape
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.legacy_s4_noOverflow_of_atom_shape
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.legacy_s4_noOverflow_of_strict
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.strict_op4_isSome_of_legacy_noOverflow
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.realizesMemRec_of_bindMemRec
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.bindMemRec_encMemRec
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.StrictRowOperationalEvidence_of_operationalCore
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.strict_s0_record_of_bound
#print axioms Nock.NockVMROM.Thm54.StrictOperationalEvidence.strict_s9_record_of_bound
