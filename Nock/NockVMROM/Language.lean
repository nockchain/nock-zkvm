import Nock.Framework
import Nock.NMRMEF
import Nock.ComputeTable
import Nock.MemoryTable
import Nock.IO

/-!
# `L_NockVMROM` — the exact NockVMROM language

The core language is recognized by `V_comp ∧ V_mem ∧ (W^IO_comp, W^IO_mem) ∈ L_mIO^{NMR}`.  We
build it as a `VMSystem` on the phantom tag `Tag F K α β Ksz`:

* the **statement** carries the public per-row compute/memory `(Inputs × Pub)` data;
* the **witness** carries the decided compute columns `Dec` and the two semantic-`nmrMEF` IO
  record lists (`progIO`, `memIO`);
* **acceptance** is the per-row `Vcomp`/`Vmem` folds together with `L_mIO` on the IO records —
  i.e. exactly the paper recognizer.

`language_unfold` is the single authoritative unfolding theorem (SC1).  The deferred
`= Nock-minus-OP_10` equivalence is a companion, NOT built here.
-/

namespace Nock.NockVMROM

open Nock Nock.Framework

/-- **Phantom instance key.**  Distinguishes the NockVMROM instance by its field `F`, extension
    `K`, fingerprint point `α`, record-encoding base `β`, and `L_mIO` bound `Ksz`, so that each
    such choice is a distinct `VMSystem`/property-class instance key. -/
structure Tag (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) : Type

variable {F K : Type} [Field F] [Field K]

/-- Public per-row statement: the compute and memory `(Inputs × Pub)` label data. -/
structure Stmt (F K : Type) [Field F] [Field K] where
  /-- Compute rows' public `(Inputs, Pub)` data. -/
  compute : List (ComputeTable.Inputs K × ComputeTable.Pub K)
  /-- Memory rows' public `(Inputs, Pub)` data. -/
  memory : List (MemoryTable.Inputs K × MemoryTable.Pub K)

/-- Private witness: the decided compute columns and the two semantic `nmrMEF` IO record lists. -/
structure Wit (F K : Type) [Field F] [Field K] where
  /-- Decided compute columns `Dec`, one per compute row. -/
  computeDec : List (ComputeTable.Dec K)
  /-- Compute-chip IO records (`W^IO_comp`), as semantic `nmrMEF` records. -/
  progIO : List ((nmrMEF F K).Rec)
  /-- Memory-chip IO records (`W^IO_mem`), as semantic `nmrMEF` records. -/
  memIO : List ((nmrMEF F K).Rec)

/-- **`ComputeTableAccepts`** — the named per-row fold over the real `V_comp` API: every compute
    row `(inp, pub)` with its decided columns `dec` satisfies `Vcomp inp pub dec`. -/
def ComputeTableAccepts (cs : List (ComputeTable.Inputs K × ComputeTable.Pub K))
    (wd : List (ComputeTable.Dec K)) : Prop :=
  List.Forall₂ (fun sp d => ComputeTable.Vcomp sp.1 sp.2 d) cs wd

/-- **`MemoryTableAccepts`** — the named per-row fold over the real `V_mem` API. -/
def MemoryTableAccepts (ms : List (MemoryTable.Inputs K × MemoryTable.Pub K)) : Prop :=
  ∀ r ∈ ms, MemoryTable.Vmem r.1 r.2

/-- **The NockVMROM acceptance relation**: both table verifiers accept and
    the two IO record lists lie in `L_mIO^{NMR}` at bound `Ksz`. -/
def accepts (Ksz : ℕ) (x : Stmt F K) (w : Wit F K) : Prop :=
  ComputeTableAccepts x.compute w.computeDec ∧
  MemoryTableAccepts x.memory ∧
  IO.LmIO Ksz w.progIO w.memIO

/-- The `VMSystem` instance on the NockVMROM tag. -/
instance instVMSystem (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    VMSystem (Tag F K α β Ksz) where
  Statement := Stmt F K
  Witness := Wit F K
  accepts := accepts Ksz

/-- **`L_NockVMROM` unfolds exactly to `V_comp ∧ V_mem ∧ (W^IO) ∈ L_mIO`.**  The single authoritative unfolding of language membership. -/
theorem language_unfold (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) (x : Stmt F K) :
    Language (Tag F K α β Ksz) x ↔
      ∃ w : Wit F K,
        ComputeTableAccepts x.compute w.computeDec ∧
        MemoryTableAccepts x.memory ∧
        IO.LmIO Ksz w.progIO w.memIO :=
  Iff.rfl

/-- **Positive witness (smoke test).**  For `Ksz ≥ 1` the language is inhabited: the empty-table
    statement is accepted by the witness that carries a single self-matched IO record.  (The full
    concrete real-trace non-vacuity witness is Gate E / P11; this only certifies the recognizer is
    satisfiable and not vacuously false.) -/
theorem language_nonempty (F K : Type) [Field F] [Field K] (α β : K) {Ksz : ℕ} (hK : 1 ≤ Ksz)
    (r : (nmrMEF F K).Rec) : Language (Tag F K α β Ksz) (⟨[], []⟩ : Stmt F K) := by
  rw [language_unfold]
  refine ⟨⟨[], [r], [r]⟩, List.Forall₂.nil, ?_, ?_⟩
  · intro y hy; simp at hy
  · exact ⟨⟨le_refl 1, hK⟩, [r], le_refl 1, List.nodup_singleton r,
      fun _ => Iff.rfl, List.Perm.refl _⟩

/-- **Negative witness (smoke test).**  At bound `Ksz = 0` the language is empty: `L_mIO` forces
    `1 ≤ |requests| ≤ 0`, unsatisfiable, so no statement is recognized. -/
theorem not_language_Ksz_zero (F K : Type) [Field F] [Field K] (α β : K) (x : Stmt F K) :
    ¬ Language (Tag F K α β 0) x := by
  rw [language_unfold]
  rintro ⟨w, -, -, hlmio⟩
  simp only [IO.LmIO, IO.InRange] at hlmio
  obtain ⟨⟨h1, h2⟩, -⟩ := hlmio
  omega

end Nock.NockVMROM
