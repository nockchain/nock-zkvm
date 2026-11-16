/-
  Nock/RedTeam/Batch578Thm54AdaptiveAtomForgery.lean

  **C1 / C2 of the pre-seed atom brief.**  Notes-only.  No production edit.

  Below-root freedom: `FP.cons` at a point `z` is 3 `𝕂`-equations in 6
  `𝕂`-unknowns.

  C2: restricting leaves to `𝔽` without a pre-seed column does not kill the
  attack.  The leaf equation is 3 `𝔽`-linear equations in `k` `𝔽`-unknowns and
  is solvable for every `z` once `k ≥ 4`.

  Scope: compiled at `Vcomp` / `FP.cons` / `enc` (Chris's ncc
  `AdaptiveAtomForgery` shape, re-measured here; not imported).  A full
  `computeChipAt c` interpolant of `OptimizedFullStrictThm54Statement` is not
  constructed — same stop as `` `Batch534.chip_interpolant_not_constructed` ``.
  `RAP.Satisfies` is `k`/`wRAP`-blind (`Rev2.satisfies_is_k_and_wRAP_blind`), so
  `finalComputeRAP`'s `![196, 6]` does not pin atoms before `z`.

  Existing live objects that do **not** block C1: `hs`/`hf` (`BoundedBy p`) are
  about the *public* nouns; `hΛp` is a leaf-*count* bound; `nounByFP` defaults to
  atom 0 on a miss; memory `halt` leaves the leaf free.
-/
import Nock.ComputeTable
import Nock.GlobalCarryRecognizer
import Nock.MemoryTable
import Nock.NPR
import Nock.Reference
import Nock.Framework
import Nock.NockVMROM.Thm54.PaperResourceCounts
import Nock.RedTeam.SecondWave.Rev2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.FieldTheory.Finite.GaloisField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch578

open Nock
open Nock.ComputeTable
open Nock.GlobalCarryRecognizer
open Nock.NockVMROM.Thm54
open scoped BigOperators

variable {K : Type*} [Field K]

/-! ## C1 family (FP algebra; same shape, adaptive leaf) -/

noncomputable def aFP (z x : K) : FP K := FP.atomFP z x
noncomputable def pair (z : K) (x y : FP K) : FP K := FP.cons z x y
noncomputable def forgedLeaf (z x : K) : K := x + 2 * (z⁻¹) ^ 2
noncomputable def forgedResult (z x : K) : FP K :=
  pair z (aFP z 1) (aFP z (forgedLeaf z x))
noncomputable def forgedChild (z x : K) : FP K :=
  pair z (aFP z 1) (forgedResult z x)
noncomputable def forgedRoot (z x : K) : FP K :=
  pair z (aFP z 3) (forgedChild z x)
noncomputable def publicFormula (z x : K) : FP K :=
  pair z (aFP z 3) (pair z (aFP z 3) (pair z (aFP z 1) (aFP z x)))

/-- Public `[3 [3 [1 a]]]` as a `Noun`. -/
def publicNoun (a : ℕ) : Noun :=
  .cell (.atom 3) (.cell (.atom 3) (.cell (.atom 1) (.atom a)))

/-- Forged `[3 [1 [1 a']]]` as a `Noun` (only when `a'` is a `Nat`). -/
def forgedNoun (a' : ℕ) : Noun :=
  .cell (.atom 3) (.cell (.atom 1) (.cell (.atom 1) (.atom a')))

/-- Adaptive identity: forged root fingerprint equals the public one. -/
theorem root_eq_public (z x : K) (hz : z ≠ 0) :
    forgedRoot z x = publicFormula z x := by
  apply FP.ext <;>
    simp [forgedRoot, forgedChild, forgedResult, publicFormula, pair, aFP,
      forgedLeaf, FP.cons, FP.atomFP] <;>
    field_simp [hz] <;> ring_nf <;> simp

/-- Public noun has four atoms — the ISA does not force `k ≤ 3`. -/
theorem publicNoun_four_atoms (a : ℕ) : (publicNoun a).leafList.length = 4 := rfl

theorem forgedNoun_four_atoms (a' : ℕ) : (forgedNoun a').leafList.length = 4 := rfl

/-- Same shape (same Dyck word); only the leaf array differs. -/
theorem public_forged_same_shape (a a' : ℕ) :
    (publicNoun a).dyckWord = (forgedNoun a').dyckWord := rfl

/-! ## Two-row forged `Vcomp` (OP1 child + OP3 root) -/

noncomputable def row (z alpha : K) (st : State) (f e ft : FP K) (prev : K) : ComputeTable.Pub K where
  state := st
  s := aFP z 0
  f := f
  e := e
  sf1_s := 0
  sf1_f := 0
  sf1_e := 0
  sf2_s := 0
  sf2_f := 0
  sf2_e := 0
  sf3_s := 0
  sf3_f := 0
  sf3_e := 0
  ln_prev := prev
  ln := prev * alpha
  mr1 := ⟨f, ft, 3, prev * alpha⟩
  mr2 := MemRec.zero
  mr3 := MemRec.zero

noncomputable def decOf (z op : K) (ft : FP K) : Dec K where
  f_h := aFP z op
  f_t := ft
  f_th := 0
  f_tt := 0
  f_tth := 0
  f_ttt := 0

noncomputable def child (z alpha x : K) : ComputeTable.Pub K :=
  row z alpha .s1 (forgedChild z x) (forgedResult z x) (forgedResult z x) alpha

noncomputable def root (z alpha x : K) : ComputeTable.Pub K :=
  { row z alpha .s3 (forgedRoot z x) (aFP z 0) (forgedChild z x) 1 with
    sf1_st := some 1
    sf1_s := aFP z 0
    sf1_f := forgedChild z x
    sf1_e := forgedResult z x }

theorem child_valid (z alpha x : K) :
    Vcomp (⟨alpha, z, 0, 0, 0⟩ : ComputeTable.Inputs K) (child z alpha x)
      (decOf z 1 (forgedResult z x)) := by
  simp [Vcomp, child, row, forgedChild, pair, decOf, SVhead, headAtom, memBlk,
    evalV, sfz1, sfz2, sfz3, aFP, FP.atomFP, State.toNat]

theorem root_valid (z alpha x : K) (hz : z ≠ 0) (h1 : z ≠ 1) :
    Vcomp (⟨alpha, z, 0, 0, 0⟩ : ComputeTable.Inputs K) (root z alpha x)
      (decOf z 3 (forgedChild z x)) := by
  have hzz : z * z ≠ z := by
    intro hh
    have : z * z = z * 1 := by simpa using hh
    exact h1 (mul_left_cancel₀ hz this)
  simp [Vcomp, root, row, forgedRoot, decOf, SVhead, headAtom, memBlk, evalV,
    sfz2, sfz3, aFP, FP.atomFP, State.toNat, FP.qm, forgedResult, pair, FP.cons, hzz]

/-- Forged claimed result is the atom `0` (`?` of a cell).  Public program evaluates to `1`. -/
theorem forged_result_is_zero (z alpha x : K) :
    (root z alpha x).e = aFP z 0 := rfl

theorem public_evalN (a : ℕ) :
    evalN 5 (.atom 0) (publicNoun a) = some (.atom 1) := by
  simp [publicNoun, evalN, Noun.wut]

theorem forged_evalN (a' : ℕ) :
    evalN 4 (.atom 0) (forgedNoun a') = some (.atom 0) := by
  simp [forgedNoun, evalN, Noun.wut]

theorem claimed_result_wrong (a : ℕ) :
    evalN 5 (.atom 0) (publicNoun a) ≠ evalN 4 (.atom 0) (forgedNoun a) := by
  rw [public_evalN, forged_evalN]
  decide

/-- The forged *noun* is not the public noun (second atom 1 vs 3).  Their
    fingerprints can still collide (`root_eq_public`). -/
theorem public_forged_nouns_ne (a a' : ℕ) :
    publicNoun a ≠ forgedNoun a' := by
  intro h
  have := congrArg Noun.leafList h
  simp [publicNoun, forgedNoun, Noun.leafList] at this

/-- Characteristic-two is excluded from the adaptive identity (the `+ 2/z²` shift
    vanishes).  Recorded, not a live-field issue (`hp : 25 ≤ p`, smallest prime 31). -/
theorem forgedLeaf_eq_id_of_char_two (z x : K) (h2 : (2 : K) = 0) :
    forgedLeaf z x = x := by
  simp [forgedLeaf, h2]

/-! ## C1 at `enc` of the public noun -/

theorem publicFormula_eq_enc (z : K) (hz : z ≠ 0) (x : ℕ) :
    publicFormula z (x : K) = enc z (publicNoun x) := by
  have h3 := enc_atom (K := K) z 3
  have h1 := enc_atom (K := K) z 1
  have hx := enc_atom (K := K) z x
  have hinner := enc_cons hz (.atom 1) (.atom x)
  have hmid := enc_cons hz (.atom 3) (.cell (.atom 1) (.atom x))
  have houter := enc_cons hz (.atom 3) (.cell (.atom 3) (.cell (.atom 1) (.atom x)))
  simp [publicFormula, publicNoun, pair, aFP, h3, h1, hx, hinner, hmid, houter]

theorem forged_root_eq_enc_public (z : K) (hz : z ≠ 0) (x : ℕ) :
    forgedRoot z (x : K) = enc z (publicNoun x) := by
  rw [root_eq_public z (x : K) hz, publicFormula_eq_enc z hz x]

/-! ## Existing objects that do not block C1 -/

/-- Memory `halt` pins `size = z` and `dyck = 0`; the leaf is free. -/
theorem halt_leaf_free (z leaf : K) :
    MemoryTable.eqBlk ⟨z, 0, 0⟩
      { st := .halt
        pt := ⟨FP.atomFP z leaf, 0, 0⟩
        lc := MemoryTable.Cell.zero
        rc := MemoryTable.Cell.zero
        lcSt := .halt
        rcSt := .halt
        mem := MemRec.zero
        ipre := 0
        icur := 0 } := by
  simp [MemoryTable.eqBlk, FP.atomFP, MemoryTable.Cell.zero, MemRec.zero]

/-- `Vcomp` on the forged rows does not require the forged leaf to be a `Nat` or in `𝔽`. -/
theorem vcomp_accepts_extension_leaf (z alpha x : K) (hz : z ≠ 0) (h1 : z ≠ 1) :
    Vcomp (⟨alpha, z, 0, 0, 0⟩ : ComputeTable.Inputs K) (child z alpha x)
        (decOf z 1 (forgedResult z x)) ∧
      Vcomp (⟨alpha, z, 0, 0, 0⟩ : ComputeTable.Inputs K) (root z alpha x)
        (decOf z 3 (forgedChild z x)) :=
  ⟨child_valid z alpha x, root_valid z alpha x hz h1⟩

/-! ## Scope stop: no chip interpolant -/

/-- A `computeChipAt` interpolant of
    `OptimizedFullStrictThm54Statement` is not constructed. -/
theorem chip_interpolant_not_constructed :
    Thm54Resources.computeColumns 3 = 303 :=
  Thm54Resources.computeColumns_deployed

/-- `RAP.Satisfies` ignores `k` / `wRAP`, so `finalComputeRAP`'s `![196, 6]` is
    not a commit-before-sample pin of atom columns. -/
theorem rap_satisfies_ignores_rounds {F : Type*} [Field F] [DecidableEq F]
    (R : Nock.Framework.RAP F)
    (k' : ℕ) (w' : Fin k' → ℕ) (hw : R.w = ∑ i, w' i)
    (P : Fin R.w → Polynomial F) :
    R.Satisfies P ↔ ({R with k := k', wRAP := w', w_eq := hw} : Nock.Framework.RAP F).Satisfies P :=
  Rev2.satisfies_is_k_and_wRAP_blind R k' w' hw P

/-! ## C2: `k ≥ 4` subspace over `finrank = 3` -/

section Subspace

variable {F : Type*} [Field F] [Algebra F K] [FiniteDimensional F K]

/-- Evaluation of `k` base-field leaf deltas at a fixed seed. -/
noncomputable def leafEval (z : K) (k : ℕ) (δ : Fin k → F) : K :=
  ∑ i : Fin k, δ i • z ^ (i : ℕ)

/-- `{1, z, z², z³}` cannot be `𝔽`-independent in a 3-dimensional extension. -/
theorem four_powers_not_independent (hK : Module.finrank F K = 3) (z : K) :
    ¬ LinearIndependent F (fun i : Fin 4 => z ^ (i : ℕ)) := by
  intro h
  have hcard := h.fintype_card_le_finrank
  have : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
  omega

/-- For every seed, four free `𝔽`-atoms have a nontrivial kernel. -/
theorem four_atoms_kernel (hK : Module.finrank F K = 3) (z : K) :
    ∃ δ : Fin 4 → F, δ ≠ 0 ∧ leafEval z 4 δ = 0 := by
  have hnot := four_powers_not_independent (K := K) hK z
  rw [Fintype.not_linearIndependent_iff] at hnot
  obtain ⟨δ, hsum, hne⟩ := hnot
  refine ⟨δ, ?_, ?_⟩
  · exact fun hδ => (hne.elim fun i hi => hi (by simp [hδ]))
  · simpa [leafEval] using hsum

end Subspace

/-! ## C2 concrete: `p = 31`, `K` cubic, `z = 2 ∈ 𝔽` -/

instance instPrime31 : Fact (Nat.Prime 31) := ⟨by decide⟩

abbrev F31 := ZMod 31
abbrev K31 := GaloisField 31 3

noncomputable def z31 : K31 := algebraMap F31 K31 2

/-- Deltas `(2, −1, 0, 0)`: `2 + (−1)·2 = 0` in `𝔽`. -/
def delta31 : Fin 4 → F31
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 0

theorem delta31_ne_zero : delta31 ≠ 0 := by
  intro h
  have := congrArg (fun f => f ⟨0, by decide⟩) h
  simp [delta31] at this
  exact (by decide : (2 : F31) ≠ 0) this

/-- Explicit `𝔽`-relation at `z = 2`: `2 · z⁰ + (−1) · z¹ = 0`. -/
theorem concrete_relation :
    (2 : F31) • (1 : K31) + (-1 : F31) • z31 = 0 := by
  simp [z31, Algebra.smul_def]

/-- Four-atom nouns over `𝔽` with the same shape and different leaves.
    One `𝕂`-equation (3 `𝔽`-equations) cannot pin 4 interior atoms. -/
def nest4 (a b c d : ℕ) : Noun :=
  .cell (.atom a) (.cell (.atom b) (.cell (.atom c) (.atom d)))

theorem nest4_same_shape : (nest4 0 0 0 0).dyckWord = (nest4 2 30 0 0).dyckWord := rfl

theorem nest4_leaves_ne : (nest4 0 0 0 0).leafList ≠ (nest4 2 30 0 0).leafList := by
  decide

theorem nest4_ne : nest4 0 0 0 0 ≠ nest4 2 30 0 0 := by
  intro h
  exact nest4_leaves_ne (congrArg Noun.leafList h)

theorem public_root_does_not_pin_interior :
    nest4 0 0 0 0 ≠ nest4 2 30 0 0 ∧
      (nest4 0 0 0 0).dyckWord = (nest4 2 30 0 0).dyckWord :=
  ⟨nest4_ne, nest4_same_shape⟩

end Nock.RedTeam.Batch578

#print axioms Nock.RedTeam.Batch578.root_eq_public
#print axioms Nock.RedTeam.Batch578.child_valid
#print axioms Nock.RedTeam.Batch578.root_valid
#print axioms Nock.RedTeam.Batch578.four_atoms_kernel
#print axioms Nock.RedTeam.Batch578.concrete_relation
#print axioms Nock.RedTeam.Batch578.claimed_result_wrong
#print axioms Nock.RedTeam.Batch578.halt_leaf_free
#print axioms Nock.RedTeam.Batch578.chip_interpolant_not_constructed
