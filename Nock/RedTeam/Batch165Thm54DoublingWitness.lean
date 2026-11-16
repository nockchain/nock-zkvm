/-
  Nock/RedTeam/Batch165Thm54DoublingWitness.lean

  **The Λ window cannot be derived from the program: a program that doubles every step.**

  `DP` built the Lean image of that condition (`TraceConfined`) and projected it onto the per-row
  window.  This module supplies the missing half: a **witness** showing the condition genuinely
  cannot be dropped or derived, so the premise is necessary rather than merely convenient.

  **Where the growth is.** `OP_8` is the only rule
  that *pairs* the old subject with new material.  It is **not** the only source of subject growth:
  `OP_2`, `OP_7` and `OP_9` replace the subject with a *computed* value, which can be larger than
  what it replaced — which is exactly why `GenSubISAWindow` excludes all four rather than `OP_8`
  alone.  What is special about `OP_8` is that its growth is *local and unconditional*, which is what
  makes a saturating witness constructible.  The generator's OP8 case recurses on `c` against `.cell sb subject`, and the leaf
  window API already isolates exactly this: `genSkelOp8_leafWindow` takes a distinguished
  `hpush : (Noun.cell sb s).leaves ≤ Λ` alongside the row's own nouns, because that one slot is not
  implied by them.

  **The bound and its tightness.**  `push_le_two_mul` — a push at most doubles, when the helper
  result is no larger than the subject.  `push_eq_two_mul` — and doubling is attained.  The witness
  saturates it at every step: take `b = [0 1]` (the identity formula, `*[a 0 1] = a`), so
  `[8 [0 1] c]` sends subject `a` to `[a a]` exactly.

  ```
  doubler 0       = [0 1]
  doubler (n+1)   = [8 [0 1] (doubler n)]
  ```

  `doubler n` has `3n + 2` leaves and drives the subject to `2 ^ n` leaves in `n` steps.  So:

  * `doubler_not_traceConfined` — its trace is not `Λ`-confined for any `Λ < 2 ^ n`.
  * `doubler_defeats_any_window` — **for every `Λ` there is an accepted program of `3Λ + 2` leaves
    whose trace escapes `Λ`.**  No function of the program's own size can bound the window, so
    `TraceConfined` is not derivable from `NockProgram^Λ`'s bound on the *formula*; the paper is
    right to carry it as a membership condition, and `DP`'s premise is not removable.

  **The witness is inside the ROM.**  `NockVMROM^Λ` is `Def:Nock` *without `OP_10`*: "just the Nock opcodes without the ability to write to memory".  It removes the
  edit operator `#`; it keeps `OP_8` (push) and `OP_2` (eval).  The generator enforces exactly that
  — `Gen.lean` answers `.error.notROM` at `10` and `11` (`gen_op10_notROM`) — so
  `gen_doubler_eq` returning `.ok` is itself the proof that the doubler is a ROM program.  It uses
  only `OP_0` and `OP_8`.  Being in the ROM therefore does **not** stop the subject growing.

  **The threshold is exact.**  `dblTree_traceConfined_iff` — `dblTree n a` is `Λ`-confined **iff**
  `2^n·|a| ≤ Λ` and `3n + 2 ≤ Λ`, both read off the root row; `dblTree_threshold` collapses this at
  the standard subject to `max (2^n) (3n+2) ≤ Λ` (the doubled subject dominates from `n = 4` on,
  the program text below it).  So the tightness claim is a theorem, not an asymptotic remark.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericCensusWindow
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false

namespace Nock.RedTeam.Batch165

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open ComputeTable

variable {K : Type} [Field K]

/-! ## The doubling bound at the one slot that grows -/

/-- **A push at most doubles**, when the helper result is no larger than the subject. -/
theorem push_le_two_mul {sb s : Noun} (h : sb.leaves ≤ s.leaves) :
    (Noun.cell sb s).leaves ≤ 2 * s.leaves := by
  rw [cell_leaves]; omega

/-- **And doubling is attained** — the bound is tight, which is what makes the witness possible. -/
theorem push_eq_two_mul (a : Noun) : (Noun.cell a a).leaves = 2 * a.leaves := by
  rw [cell_leaves]; omega

/-! ## The witness program -/

/-- `[0 1]` — the identity formula, `*[a 0 1] = a`. -/
def idFormula : Noun := .cell (.atom 0) (.atom 1)

/-- The single-row OP0 tree the identity formula generates. -/
def idTree (a : Noun) : NTree (GenComputeRow K) :=
  .node (skelNode (genSkelOp0 a idFormula (.atom 0) (.atom 1) a 1)
    [⟨idFormula, .atom 1, 3, 0⟩, ⟨a, a, 1, 0⟩]) []

theorem gen_idFormula (m : ℕ) (a : Noun) :
    genComputeSkeleton (K := K) (m + 1) a idFormula = .ok (idTree a, a) := by
  simp [genComputeSkeleton, idFormula, idTree, Nock.Noun.slot]

/-- `doubler n` = `n` nested OP8 pushes with the identity helper. -/
def doubler : ℕ → Noun
  | 0 => idFormula
  | n + 1 => .cell (.atom 8) (.cell idFormula (doubler n))

/-- `dup n a` — `a` doubled `n` times, the subject `doubler n` drives the trace to. -/
def dup : ℕ → Noun → Noun
  | 0, a => a
  | n + 1, a => dup n (.cell a a)

/-- **The trace noun is exponential in the number of steps.** -/
theorem dup_leaves (n : ℕ) (a : Noun) : (dup n a).leaves = 2 ^ n * a.leaves := by
  induction n generalizing a with
  | zero => simp [dup]
  | succ m ih =>
    rw [dup, ih (.cell a a), push_eq_two_mul, pow_succ]
    ring

/-- **The program text is linear in the number of steps.** -/
theorem doubler_leaves (n : ℕ) : (doubler n).leaves = 3 * n + 2 := by
  induction n with
  | zero => rfl
  | succ m ih => simp [doubler, idFormula, cell_leaves, atom_leaves, ih]; ring

/-! ## The generator accepts it, and its trace carries the doubled noun

The tree is written out rather than left existential, so the exact confinement threshold below can
be proved by induction over it. -/

/-- The tree `doubler n` generates at subject `a`: `n` nested OP8 rows, each with the identity
leaf as its first child and the next push as its second. -/
def dblTree : ℕ → Noun → NTree (GenComputeRow K)
  | 0, a => idTree a
  | n + 1, a =>
    .node (skelNode (genSkelOp8 a (doubler (n + 1)) (.atom 8)
        (.cell idFormula (doubler n)) idFormula (doubler n) a (dup n (.cell a a)))
      [⟨doubler (n + 1), .cell idFormula (doubler n), 3, 0⟩,
       ⟨.cell idFormula (doubler n), idFormula, 2, 0⟩])
    [idTree a, dblTree n (.cell a a)]

/-- **`doubler n` is accepted at fuel `n + 2`, returns `dup n a`, and generates `dblTree n a`.**

The subject is threaded by the OP8 recursion `genComputeSkeleton n (.cell sb subject) c`, with
`sb = a` at every step because the helper is the identity. -/
theorem gen_doubler_eq (n : ℕ) (a : Noun) :
    genComputeSkeleton (K := K) (n + 2) a (doubler n) = .ok (dblTree n a, dup n a) := by
  induction n generalizing a with
  | zero => exact gen_idFormula 1 a
  | succ m ih =>
    have e1 : genComputeSkeleton (K := K) (m + 2) a idFormula = .ok (idTree a, a) :=
      gen_idFormula (m + 1) a
    show genComputeSkeleton (K := K) ((m + 2) + 1) a (doubler (m + 1)) = _
    rw [doubler, genComputeSkeleton, e1]
    simp only [ih (.cell a a)]
    rfl

/-- The root of `dblTree n a` carries subject `a`, formula `doubler n` and evaluation `dup n a`. -/
theorem dblTree_root (n : ℕ) (a : Noun) :
    (dblTree (K := K) n a).label.skel.subject = a ∧
      (dblTree (K := K) n a).label.skel.formula = doubler n ∧
      (dblTree (K := K) n a).label.skel.evaluation = dup n a := by
  cases n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ m => exact ⟨rfl, rfl, rfl⟩

/-- The **innermost** row of `dblTree n a` carries the fully doubled subject. -/
theorem dblTree_dup_row (n : ℕ) (a : Noun) :
    ∃ u, InTree (dblTree (K := K) n a) u ∧ u.label.skel.subject = dup n a := by
  induction n generalizing a with
  | zero => exact ⟨idTree a, InTree.here _, rfl⟩
  | succ m ih =>
    obtain ⟨u, hu, hsub⟩ := ih (.cell a a)
    exact ⟨u, InTree.sub (by simp [dblTree, NTree.children]) hu, hsub⟩

theorem gen_doubler (n : ℕ) (a : Noun) :
    ∃ t : NTree (GenComputeRow K),
      genComputeSkeleton (K := K) (n + 2) a (doubler n) = .ok (t, dup n a) ∧
        ∃ u, InTree t u ∧ u.label.skel.subject = dup n a :=
  ⟨dblTree n a, gen_doubler_eq n a, dblTree_dup_row n a⟩

/-! ## The doubling is Nock, not a generator artefact

The claim would be worth nothing if the growth were an accident of `genComputeSkeleton`.  It is
not: the reference interpreter `evalN` (`Reference.lean:77`) computes the same doubled noun. -/

theorem evalN_idFormula (m : ℕ) (a : Noun) :
    Nock.evalN (m + 1) a idFormula = some a := by
  simp [Nock.evalN, idFormula, Nock.Noun.slot]

/-- **The reference interpreter agrees**: `*[a (doubler n)] = dup n a`. -/
theorem evalN_doubler (n : ℕ) (a : Noun) :
    Nock.evalN (n + 2) a (doubler n) = some (dup n a) := by
  induction n generalizing a with
  | zero => exact evalN_idFormula 1 a
  | succ m ih =>
    show Nock.evalN ((m + 2) + 1) a (doubler (m + 1)) = _
    rw [doubler, Nock.evalN]
    rw [evalN_idFormula (m + 1) a]
    simp only [ih (.cell a a)]
    rfl

/-! ## The exact confinement threshold

The bound is not merely attained asymptotically: the confinement predicate at this family has an
exact threshold, so "tight" is a theorem rather than a remark. -/

theorem idTree_row (a : Noun) :
    (idTree (K := K) a).label.skel.subject = a ∧
      (idTree (K := K) a).label.skel.formula = idFormula ∧
      (idTree (K := K) a).label.skel.evaluation = a :=
  ⟨rfl, rfl, rfl⟩

theorem idFormula_leaves : idFormula.leaves = 2 := rfl

theorem idTree_rowsConfined (a : Noun) {Λ : ℕ}
    (ha : a.leaves ≤ Λ) (h2 : 2 ≤ Λ) :
    ∀ u, InTree (idTree (K := K) a) u → RowNounsConfined Λ u.label := by
  intro u hu
  cases hu with
  | here => exact ⟨ha, by rw [(idTree_row (K := K) a).2.1, idFormula_leaves]; exact h2, ha⟩
  | sub hc _ => simp [idTree, NTree.children] at hc

/-- **Every row of `dblTree n a` is within `Λ`, given the two bounds the root already forces.** -/
theorem dblTree_rowsConfined (n : ℕ) (a : Noun) {Λ : ℕ}
    (hs : 2 ^ n * a.leaves ≤ Λ) (hf : 3 * n + 2 ≤ Λ) :
    ∀ u, InTree (dblTree (K := K) n a) u → RowNounsConfined Λ u.label := by
  induction n generalizing a with
  | zero =>
    simp only [pow_zero, one_mul] at hs
    exact idTree_rowsConfined a hs (by omega)
  | succ m ih =>
    have hpos : 1 ≤ a.leaves := leaves_pos a
    have hle : a.leaves ≤ 2 ^ (m + 1) * a.leaves :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos (m + 1))
    have hsa : a.leaves ≤ Λ := le_trans hle hs
    have hsub : 2 ^ m * (Noun.cell a a).leaves ≤ Λ := by
      rw [push_eq_two_mul, ← mul_assoc]
      calc 2 ^ m * 2 * a.leaves = 2 ^ (m + 1) * a.leaves := by rw [pow_succ]
        _ ≤ Λ := hs
    intro u hu
    cases hu with
    | here =>
      refine ⟨hsa, ?_, ?_⟩
      · rw [(dblTree_root (K := K) (m + 1) a).2.1, doubler_leaves]; exact hf
      · rw [(dblTree_root (K := K) (m + 1) a).2.2, dup_leaves]; exact hs
    | sub hc hu' =>
      simp only [dblTree, NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact idTree_rowsConfined a hsa (by omega) _ hu'
      · exact ih (.cell a a) hsub (by omega) _ hu'

/-- **The exact threshold.**  `dblTree n a` is `Λ`-confined **iff** `Λ` admits both the doubled
subject and the program text.  Both directions are read off the root row, so nothing weaker
suffices and nothing stronger is needed. -/
theorem dblTree_traceConfined_iff (n : ℕ) (a : Noun) (Λ : ℕ) :
    TraceConfined Λ (dblTree (K := K) n a) ↔ (2 ^ n * a.leaves ≤ Λ ∧ 3 * n + 2 ≤ Λ) := by
  constructor
  · intro h
    obtain ⟨-, hf, he⟩ := confined_inTree h (InTree.here (dblTree (K := K) n a))
    rw [(dblTree_root (K := K) n a).2.2, dup_leaves] at he
    rw [(dblTree_root (K := K) n a).2.1, doubler_leaves] at hf
    exact ⟨he, hf⟩
  · rintro ⟨hs, hf⟩
    exact bfsRows_of_inTree _ _ (dblTree_rowsConfined n a hs hf)

/-- The same at the standard subject, as a single number: the window this program needs is exactly
`max (2 ^ n) (3n + 2)` — the doubled subject from `n = 4` on, the program text below it. -/
theorem dblTree_threshold (n Λ : ℕ) :
    TraceConfined Λ (dblTree (K := K) n (.atom 0)) ↔ max (2 ^ n) (3 * n + 2) ≤ Λ := by
  rw [dblTree_traceConfined_iff, max_le_iff, atom_leaves, mul_one]

/-! ## The witness is a ROM program

`NockVMROM^Λ` is `Def:Nock` **without `OP_10`** — Nock without the ability to
write to memory.  It keeps `OP_8`.  The generator enforces exactly that, so `gen_doubler_eq`
returning `.ok` already places the doubler inside the ROM; `doubler` uses only `OP_0` and `OP_8`. -/

/-- `OP_10` is what the ROM removes. -/
theorem gen_op10_notROM (m : ℕ) (a tail : Noun) :
    genComputeSkeleton (K := K) (m + 1) a (.cell (.atom 10) tail) = .error .notROM := by
  simp [genComputeSkeleton]

/-! ## Necessity -/

/-- **A tree carrying a doubled subject is not `Λ`-confined below `2 ^ n · |a|`.**  So
`TraceConfined` is a real constraint this program violates, not a formality. -/
theorem not_traceConfined_of_dup_row {Λ n : ℕ} {a : Noun}
    {t : NTree (GenComputeRow K)}
    (hu : ∃ u, InTree t u ∧ u.label.skel.subject = dup n a)
    (hlt : Λ < 2 ^ n * a.leaves) :
    ¬ TraceConfined Λ t := by
  intro hconf
  obtain ⟨u, hin, hsub⟩ := hu
  have hb := (confined_inTree hconf hin).1
  rw [hsub, dup_leaves] at hb
  omega

/-- **For every `Λ` there is an accepted program of `3Λ + 2` leaves whose trace escapes `Λ`.**

The window is therefore not a function of the program's size: no bound derived from
`NockProgram^Λ`'s constraint on the *formula* can imply `TraceConfined`.  This is why the paper
carries `λ ≤ Λ` as a membership condition and why `DP`'s premise is
necessary rather than removable. -/
theorem doubler_defeats_any_window (Λ : ℕ) :
    ∃ t : NTree (GenComputeRow K),
      genComputeSkeleton (K := K) (Λ + 2) (.atom 0) (doubler Λ) = .ok (t, dup Λ (.atom 0)) ∧
        (doubler Λ).leaves = 3 * Λ + 2 ∧
        ¬ TraceConfined Λ t := by
  obtain ⟨t, hgen, hu⟩ := gen_doubler (K := K) Λ (.atom 0)
  refine ⟨t, hgen, doubler_leaves Λ, not_traceConfined_of_dup_row hu ?_⟩
  have h : Λ < 2 ^ Λ := Nat.lt_two_pow_self
  simpa [atom_leaves] using h

/-! ## A concrete instance

Twenty pushes: a 62-leaf program whose trace carries a 1 048 576-leaf noun. -/

theorem doubler_20_leaves : (doubler 20).leaves = 62 := by
  rw [doubler_leaves]

theorem dup_20_leaves : (dup 20 (.atom 0)).leaves = 1048576 := by
  rw [dup_leaves, atom_leaves]; norm_num

end Nock.RedTeam.Batch165

#print axioms Nock.RedTeam.Batch165.push_le_two_mul
#print axioms Nock.RedTeam.Batch165.dup_leaves
#print axioms Nock.RedTeam.Batch165.doubler_leaves
#print axioms Nock.RedTeam.Batch165.gen_doubler
#print axioms Nock.RedTeam.Batch165.evalN_doubler
#print axioms Nock.RedTeam.Batch165.not_traceConfined_of_dup_row
#print axioms Nock.RedTeam.Batch165.dblTree_traceConfined_iff
#print axioms Nock.RedTeam.Batch165.dblTree_threshold
#print axioms Nock.RedTeam.Batch165.gen_op10_notROM
#print axioms Nock.RedTeam.Batch165.doubler_defeats_any_window
