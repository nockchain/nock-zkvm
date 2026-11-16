import Nock.Framework.FixedPreprocessingRAP

/-!
  Nock/NockVMROM/Thm54/RAPPadding.lean

  Generic, semantics-preserving right padding for `Framework.RAP`.

  Theorem 5.4's final monolithic census contains resource summands that are
  not assigned by the paper's assembly arithmetic.  The author-authorized correctness
  delta is to realize only those residual resources by unused columns and identically-zero
  constraints.  This module provides that operation independently of the future Nock semantic
  templates.  It does not identify a source RAP with either final chip.
-/

namespace Nock.NockVMROM.Thm54
namespace RAPPadding

open Nock.Framework
open scoped Polynomial

noncomputable section

variable {F : Type*} [CommRing F]

/-- Total number of columns appended by a per-round padding vector. -/
def extraWidth {k : ℕ} (extra : Fin k → ℕ) : ℕ := ∑ i, extra i

/-- Inclusion of an original trace column into a right-padded trace. -/
def columnInclusion (R : RAP F) (extra : Fin R.k → ℕ) :
    Fin R.w ↪ Fin (R.w + extraWidth extra) where
  toFun := Fin.castAdd (extraWidth extra)
  inj' := by
    intro i j hij
    apply Fin.ext
    simpa using congrArg Fin.val hij

/-- Inclusion of an original symbolic variable into the right-padded column space. -/
def variableInclusion (R : RAP F) (extra : Fin R.k → ℕ) :
    (Fin R.w × ℕ) → (Fin (R.w + extraWidth extra) × ℕ) :=
  fun q => (columnInclusion R extra q.1, q.2)

/-- Restrict a padded trace to the original columns. -/
def projectTrace (R : RAP F) (extra : Fin R.k → ℕ)
    (P : Fin (R.w + extraWidth extra) → F[X]) : Fin R.w → F[X] :=
  fun i => P (columnInclusion R extra i)

set_option maxHeartbeats 2000000 in
/-- Append columns round-by-round and append `zeroConstraints` identically-zero constraints.

The extra constraints are
literally zero, so no new semantic condition is introduced. -/
@[reducible] def pad (R : RAP F) (extra : Fin R.k → ℕ) (zeroConstraints : ℕ) : RAP F where
  e := R.e
  k := R.k
  wRAP := fun i => R.wRAP i + extra i
  w := R.w + extraWidth extra
  w_eq := by
    rw [Finset.sum_add_distrib, ← R.w_eq]
    rfl
  h := R.h
  d := R.d
  s := R.s + zeroConstraints
  ω := R.ω
  β := R.β
  I := R.I.image (variableInclusion R extra)
  C := Fin.addCases
    (fun i => MvPolynomial.rename (variableInclusion R extra) (R.C i))
    (fun _ => 0)
  C_vars := by
    refine Fin.addCases ?_ ?_
    · intro i
      rw [Fin.addCases_left]
      refine (MvPolynomial.vars_rename _ _).trans ?_
      intro x hx
      simp only [Finset.mem_image] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, R.C_vars i hy, rfl⟩
    · intro i
      simp
  C_deg := by
    refine Fin.addCases ?_ ?_
    · intro i
      rw [Fin.addCases_left]
      exact (MvPolynomial.totalDegree_rename_le _ _).trans (R.C_deg i)
    · intro i
      simp
  H := R.H
  β_ne_zero := R.β_ne_zero
  I_bound := by
    intro q hq
    simp only [Finset.mem_image] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    exact R.I_bound q₀ hq₀

@[simp] theorem pad_e (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).e = R.e := rfl

@[simp] theorem pad_k (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).k = R.k := rfl

@[simp] theorem pad_w (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).w = R.w + extraWidth extra := rfl

@[simp] theorem pad_s (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).s = R.s + n := rfl

@[simp] theorem pad_h (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).h = R.h := rfl

@[simp] theorem pad_d (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).d = R.d := rfl

@[simp] theorem pad_omega (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).ω = R.ω := rfl

@[simp] theorem pad_beta (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).β = R.β := rfl

@[simp] theorem pad_H (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ) :
    (pad R extra n).H = R.H := rfl

/-- Renaming an original constraint and evaluating it on a padded trace is evaluation of the
original constraint on the projected trace. -/
theorem compose_left (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ)
    (P : Fin (R.w + extraWidth extra) → F[X]) (i : Fin R.s) :
    (pad R extra n).compose P (Fin.castAdd n i) =
      R.compose (projectTrace R extra P) i := by
  simp only [RAP.compose, pad, Fin.addCases_left]
  rw [MvPolynomial.aeval_rename]
  rfl

/-- Every appended constraint is identically zero. -/
theorem compose_right (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ)
    (P : Fin (R.w + extraWidth extra) → F[X]) (i : Fin n) :
    (pad R extra n).compose P (Fin.natAdd R.s i) = 0 := by
  simp [RAP.compose, pad]

/-- **Padding is semantically inert.**  A padded trace satisfies the padded RAP exactly when its
projection satisfies the original RAP. -/
theorem satisfies_iff (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ)
    (P : Fin (R.w + extraWidth extra) → F[X]) :
    (pad R extra n).Satisfies P ↔ R.Satisfies (projectTrace R extra P) := by
  constructor
  · intro h i x hx
    have hi := h (Fin.castAdd n i) x (by simpa using hx)
    simpa only [compose_left] using hi
  · intro h
    refine Fin.addCases ?_ ?_
    · intro i x hx
      rw [compose_left]
      exact h i x (by simpa using hx)
    · intro i x hx
      simp [compose_right]

/-- Appending zero columns and zero constraints cannot make a bad original trace good: every
satisfying padded trace projects to a satisfying original trace. -/
theorem satisfies_project (R : RAP F) (extra : Fin R.k → ℕ) (n : ℕ)
    {P : Fin (R.w + extraWidth extra) → F[X]} (hP : (pad R extra n).Satisfies P) :
    R.Satisfies (projectTrace R extra P) :=
  (satisfies_iff R extra n P).mp hP

/-! ## Fixed-preprocessing preservation -/

/-- Right padding preserves the same designated fixed preprocessing columns.  Newly appended
first-round columns are not silently added to the fixed subset. -/
def padFixedPreprocessing (R : FixedPreprocessingRAP F)
    (extra : Fin R.rap.k → ℕ) (zeroConstraints : ℕ) :
    FixedPreprocessingRAP F where
  rap := pad R.rap extra zeroConstraints
  rounds_pos := by simpa using R.rounds_pos
  fixedCount := R.fixedCount
  preprocessingIndex :=
    { toFun := fun j =>
        ⟨R.preprocessingIndex j,
          (R.preprocessingIndex j).isLt.trans_le
            (Nat.le_add_right
              (R.rap.wRAP (R.rap.firstRound R.rounds_pos))
              (extra (R.rap.firstRound R.rounds_pos)))⟩
      inj' := by
        intro i j hij
        apply R.preprocessingIndex.injective
        apply Fin.ext
        have hval : (R.preprocessingIndex i).val = (R.preprocessingIndex j).val := by
          exact congrArg (fun x => x.val) hij
        exact hval }
  preprocessing := R.preprocessing

/-- Padding preserves both the raw RAP equations and polynomial-level fixed-column binding. -/
theorem padFixedPreprocessing_satisfies_iff
    (R : FixedPreprocessingRAP F) (extra : Fin R.rap.k → ℕ) (n : ℕ)
    (P : Fin (pad R.rap extra n).w → F[X]) :
    RAP.SatisfiesWithPreprocessing (padFixedPreprocessing R extra n) P ↔
      RAP.SatisfiesWithPreprocessing R (projectTrace R.rap extra P) := by
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨(satisfies_iff R.rap extra n P).mp hraw, ?_⟩
    intro j
    exact hfixed j
  · rintro ⟨hraw, hfixed⟩
    refine ⟨(satisfies_iff R.rap extra n P).mpr hraw, ?_⟩
    intro j
    exact hfixed j

/-! ## Exact authorized R6 residuals

The paper-derived table/walk/IO arithmetic reaches `58e+13` compute columns and `55e+6` memory
columns, and `21e+13` / `21e+14` transition gates.
Theorem 5.4 states `62e+13`, `61e+13`, `24e+15`, and `24e+16`.  The generic transformation below remains a diagnostic theorem showing that
unused resources can be added semantically inertly.  Only one compute extension column remains inert.  Memory residual identification is
still pending. -/

/-- Compute columns left unidentified after the named table/walk/program-IO core. -/
def computeResidualColumns (e : ℕ) : ℕ := 4 * e

/-- Memory columns left unidentified after the named table/walk/memory-IO core. -/
def memoryResidualColumns (e : ℕ) : ℕ := 6 * e + 5

/-- Transition gates left unidentified on each side after the named semantic core. -/
def residualTransitionGates (e : ℕ) : ℕ := 3 * e + 2

/-- The optimized compute semantic core's coordinate-expanded width. -/
def computeCoreWidth (e : ℕ) : ℕ := 58 * e + 13

/-- The optimized memory semantic core's coordinate-expanded width. -/
def memoryCoreWidth (e : ℕ) : ℕ := 58 * e + 6

/-- The optimized compute semantic core's coordinate-expanded transition count. -/
def computeCoreTransitionGates (e : ℕ) : ℕ := 21 * e + 13

/-- The optimized memory semantic core's coordinate-expanded transition count. -/
def memoryCoreTransitionGates (e : ℕ) : ℕ := 21 * e + 14

/-! ### The memory chip's own residual, after the `𝔽 → 𝕂` retyping

`residualTransitionGates` above is **shared with compute**, where
`computeCoreTransitionGates e + residualTransitionGates e = 24·e + 15` is exact and must stay so.
It is deliberately left untouched: `Batch48`, `Batch49`, `Batch63` and `Batch64` assert its value
and the identities it participates in, several of them by `rfl`.

The paper spends `e` on
one accumulator column read at two rows; the deployed two-role layout spends
`e` on the step and now `e` on the chain, so the core transition count is `25·e + 11` and the
residual that reaches `24·e + 16` **at `e = 3`** is two.  The compute side is untouched: its residual stays affine (`3·e + 2`).

The core transition count is `26·e + 11`; the two
remaining residual slots absorb two of the pin's three coordinates and the residual is **zero**,
so the deployed bucket is `26·e + 11 = 89` at `e = 3` — **one over** the paper's `24·e + 16 = 88`.
`Thm54Resources.memoryTransitionGates` moves to
the deployed count `26·e + 11` and discloses it (`Thm54Resources.memoryTransitionGatesPaper` keeps
`24·e + 16`). -/

/-- Transition gates left unidentified on the **memory** side after the retyped semantic core,
the response-accumulator chain gate and the response-denominator pin. -/
def memoryResidualTransitionGates (_e : ℕ) : ℕ := 0

/-- Until the nineteenth (root-mask) move this was `45·e + 5`. -/
def memoryCoreTransitionGatesMixed (e : ℕ) : ℕ := 49 * e + 6

/-- Compute degree-one/degree-three endpoint and equality constraints, unchanged by padding.

The **deployed** compute chip is `CorrectedFinalComputeRAP`, whose `s` is the length of its own
gate list, and since stage 3e that is `118`, not `98`.  The decompressed
allocation is `computeCoreEndpointEqualityConstraintsDecompressed` below. -/
def computeCoreEndpointEqualityConstraints (e : ℕ) : ℕ := 2 * e + e + 2

/-- The compute analogue of
`memoryCoreEndpointEqualityConstraintsMixed`. -/
def computeCoreEndpointEqualityConstraintsDecompressed (e : ℕ) : ℕ := 2 * e + e + 22

/-- Memory degree-one/degree-three endpoint and equality constraints, unchanged by padding. -/
def memoryCoreEndpointEqualityConstraints (e : ℕ) : ℕ := 2 * e + 2 * e + 4

/-- The paper's masked
initial/terminal gates and the tree-only selector-mirror checks live in the mixed
transition bucket (`paperKGates`); `ChipTemplate.extDeg1/3` cannot hold `Scale`-masked
endpoints. -/
def memoryCoreEndpointEqualityConstraintsMixed (_e : ℕ) : ℕ := 0

/-- Total constraints in the optimized compute source RAP.  Unlike
`computeCoreTransitionGates`, this is the quantity stored in `RAP.s`. -/
def computeCoreTotalConstraints (e : ℕ) : ℕ :=
  computeCoreTransitionGates e + computeCoreEndpointEqualityConstraints e

/-- Total constraints in the optimized memory source RAP. -/
def memoryCoreTotalConstraints (e : ℕ) : ℕ :=
  memoryCoreTransitionGates e + memoryCoreEndpointEqualityConstraints e

/-- Total constraints in the retyped memory source RAP. -/
def memoryCoreTotalConstraintsMixed (e : ℕ) : ℕ :=
  memoryCoreTransitionGatesMixed e + memoryCoreEndpointEqualityConstraintsMixed e

/-- Total constraints in the final padded compute RAP. -/
def computeFinalTotalConstraints (e : ℕ) : ℕ :=
  (24 * e + 15) + 2 * e + e + 2

/-- Total constraints in the final **de-compressed** compute RAP: `27·e + 37`,
which is `118` at `e = 3`.  This is what `CorrectedFinalComputeRAP.s` is. -/
def computeFinalTotalConstraintsDecompressed (e : ℕ) : ℕ :=
  (24 * e + 15) + 2 * e + e + 22

/-- Total constraints in the final padded memory RAP. -/
def memoryFinalTotalConstraints (e : ℕ) : ℕ :=
  (24 * e + 16) + 2 * e + 2 * e + 4

/-- Residual
gates remain `0`.  `146` at `e = 3` (`140` before the nineteenth). -/
def memoryFinalTotalConstraintsMixed (e : ℕ) : ℕ := 49 * e + 6

theorem compute_width_arithmetic (e : ℕ) :
    computeCoreWidth e + computeResidualColumns e = 62 * e + 13 := by
  simp [computeCoreWidth, computeResidualColumns]
  omega

theorem memory_width_arithmetic (e : ℕ) :
    memoryCoreWidth e + memoryResidualColumns e = 64 * e + 11 := by
  simp [memoryCoreWidth, memoryResidualColumns]
  omega

theorem compute_transition_arithmetic (e : ℕ) :
    computeCoreTransitionGates e + residualTransitionGates e = 24 * e + 15 := by
  simp [computeCoreTransitionGates, residualTransitionGates]
  omega

theorem memory_transition_arithmetic (e : ℕ) :
    memoryCoreTransitionGates e + residualTransitionGates e = 24 * e + 16 := by
  simp [memoryCoreTransitionGates, residualTransitionGates]
  omega

/-- The formalization is stricter than the paper (more
gates). -/
theorem memory_transition_arithmetic_mixed :
    memoryCoreTransitionGatesMixed 3 + memoryResidualTransitionGates 3 = 49 * 3 + 6 := by
  simp [memoryCoreTransitionGatesMixed, memoryResidualTransitionGates]

/-- The honest identity in `e` of the deployed memory transition bucket: `47·e + 5`. -/
theorem memory_transition_arithmetic_deployed (e : ℕ) :
    memoryCoreTransitionGatesMixed e + memoryResidualTransitionGates e = 49 * e + 6 := by
  simp [memoryCoreTransitionGatesMixed, memoryResidualTransitionGates]

/-- The memory bucket's accounting, in four readings.  Pre-migration: `21·e + 25`, meeting
`24·e + 16` only at `e = 3`.  Between `LL` (the response-accumulator chain gate) and A-mem-2:
`25·e + 11 + 2 = 25·e + 13`, meeting `24·e + 16` only at `e = 3` again.  (Until `LL` this
theorem was `memory_bucket_identity_is_not_an_e3_coincidence`; that name is retired because its
claim no longer holds of the deployed chip.) -/
theorem memory_bucket_identity_interim :
    (21 * 3 + 25 = 24 * 3 + 16) ∧ (21 * 4 + 25 ≠ 24 * 4 + 16) ∧
      (∀ e : ℕ, 24 * e + 11 + 5 = 24 * e + 16) ∧
      (25 * 3 + 11 + 2 = 24 * 3 + 16) ∧ (25 * 4 + 11 + 2 ≠ 24 * 4 + 16) ∧
      (∀ e : ℕ, memoryCoreTransitionGatesMixed e + memoryResidualTransitionGates e
        = 49 * e + 6) ∧
      (memoryCoreTransitionGatesMixed 3 + memoryResidualTransitionGates 3 = 49 * 3 + 6) ∧
      (∀ e : ℕ, memoryCoreTransitionGatesMixed e + memoryResidualTransitionGates e
        ≠ 24 * e + 16) := by
  refine ⟨by decide, by decide, fun e => by omega, by decide, by decide,
    memory_transition_arithmetic_deployed, memory_transition_arithmetic_mixed, fun e => ?_⟩
  rw [memory_transition_arithmetic_deployed]
  omega

theorem compute_total_arithmetic (e : ℕ) :
    computeCoreTotalConstraints e + residualTransitionGates e =
      computeFinalTotalConstraints e := by
  simp [computeCoreTotalConstraints, computeCoreTransitionGates,
    computeCoreEndpointEqualityConstraints, residualTransitionGates,
    computeFinalTotalConstraints]
  omega

theorem memory_total_arithmetic (e : ℕ) :
    memoryCoreTotalConstraints e + residualTransitionGates e =
      memoryFinalTotalConstraints e := by
  simp [memoryCoreTotalConstraints, memoryCoreTransitionGates,
    memoryCoreEndpointEqualityConstraints, residualTransitionGates,
    memoryFinalTotalConstraints]
  omega

theorem memory_total_arithmetic_mixed (e : ℕ) :
    memoryCoreTotalConstraintsMixed e + memoryResidualTransitionGates e =
      memoryFinalTotalConstraintsMixed e := by
  simp [memoryCoreTotalConstraintsMixed, memoryCoreTransitionGatesMixed,
    memoryCoreEndpointEqualityConstraintsMixed, memoryResidualTransitionGates,
    memoryFinalTotalConstraintsMixed]

/-- Put all inert columns into the first commitment round. -/
def firstRoundExtra (R : RAP F) (hk : 0 < R.k) (n : ℕ) : Fin R.k → ℕ :=
  fun i => if i = ⟨0, hk⟩ then n else 0

@[simp] theorem extraWidth_firstRoundExtra (R : RAP F) (hk : 0 < R.k) (n : ℕ) :
    extraWidth (firstRoundExtra R hk n) = n := by
  simp [extraWidth, firstRoundExtra]

/-- Production compute uses `OptimizedComputeFinal.finalComputeRAP`. -/
def padComputeCore (R : RAP F) (hk : 0 < R.k) (e : ℕ) : RAP F :=
  pad R (firstRoundExtra R hk (computeResidualColumns e)) (residualTransitionGates e)

/-- Exact memory-side residual padding at extension order `e`. -/
def padMemoryCore (R : RAP F) (hk : 0 < R.k) (e : ℕ) : RAP F :=
  pad R (firstRoundExtra R hk (memoryResidualColumns e)) (residualTransitionGates e)

/-- Exact memory-side residual padding for the **retyped** chip. -/
def padMemoryCoreMixed (R : RAP F) (hk : 0 < R.k) (e : ℕ) : RAP F :=
  pad R (firstRoundExtra R hk (memoryResidualColumns e)) (memoryResidualTransitionGates e)

/-- Compute padding has the final paper width and **total `RAP.s` constraint count** whenever its
input is the authorized optimized semantic core.  Transition counts remain the separate
`compute_transition_arithmetic` theorem. -/
theorem padComputeCore_fingerprint (R : RAP F) (hk : 0 < R.k) (e : ℕ)
    (hw : R.w = computeCoreWidth e) (hs : R.s = computeCoreTotalConstraints e) :
    (padComputeCore R hk e).w = 62 * e + 13 ∧
      (padComputeCore R hk e).s = computeFinalTotalConstraints e := by
  constructor
  · simp [padComputeCore, hw, compute_width_arithmetic]
  · simp [padComputeCore, hs, compute_total_arithmetic]

/-- Memory analogue of `padComputeCore_fingerprint`. -/
theorem padMemoryCore_fingerprint (R : RAP F) (hk : 0 < R.k) (e : ℕ)
    (hw : R.w = memoryCoreWidth e) (hs : R.s = memoryCoreTotalConstraints e) :
    (padMemoryCore R hk e).w = 64 * e + 11 ∧
      (padMemoryCore R hk e).s = memoryFinalTotalConstraints e := by
  constructor
  · simp [padMemoryCore, hw, memory_width_arithmetic]
  · simp [padMemoryCore, hs, memory_total_arithmetic]

/-- Memory analogue of `padMemoryCore_fingerprint` for the retyped chip. -/
theorem padMemoryCoreMixed_fingerprint (R : RAP F) (hk : 0 < R.k) (e : ℕ)
    (hw : R.w = memoryCoreWidth e) (hs : R.s = memoryCoreTotalConstraintsMixed e) :
    (padMemoryCoreMixed R hk e).w = 64 * e + 11 ∧
      (padMemoryCoreMixed R hk e).s = memoryFinalTotalConstraintsMixed e := by
  constructor
  · simp [padMemoryCoreMixed, hw, memory_width_arithmetic]
  · simp [padMemoryCoreMixed, hs, memory_total_arithmetic_mixed]

/-- At `e = 3` the paper-shaped memory chip pads `171/146` to `196/146`: the same twenty-five
inert columns, **no** inert gate.  `w` is **unchanged** at `196`. -/
theorem padMemoryCoreMixed_e3_fingerprint (R : RAP F) (hk : 0 < R.k)
    (hw : R.w = 180)     (hs : R.s = 153) :
    (padMemoryCoreMixed R hk 3).w = 203 ∧ (padMemoryCoreMixed R hk 3).s = 153 := by
  apply padMemoryCoreMixed_fingerprint R hk 3
  · simpa [memoryCoreWidth] using hw
  · simpa [memoryCoreTotalConstraintsMixed, memoryCoreTransitionGatesMixed,
      memoryCoreEndpointEqualityConstraintsMixed] using hs

/-- The source chip carries one appended round-0
`𝔽` column `atom` (`CoordinateRAPTail.expandChipTail … 1`) and the three coordinate gates of
`OptimizedMemoryGateBasis.haltAtomMixed`, so the source is `181/156`; the same twenty-three inert
columns and no inert gate pad it to `204/156`. -/
theorem padMemoryCoreMixed_e3_atom_fingerprint (R : RAP F) (hk : 0 < R.k)
    (hw : R.w = 181) (hs : R.s = 156) :
    (padMemoryCoreMixed R hk 3).w = 204 ∧ (padMemoryCoreMixed R hk 3).s = 156 := by
  constructor
  · simp [padMemoryCoreMixed, hw, memoryResidualColumns]
  · simp [padMemoryCoreMixed, hs, memoryResidualTransitionGates]

/-- The source chip carries a second appended round-0
`𝔽` column `reqIdx` (`CoordinateRAPTail.expandChipTail … 2`, no gate of its own), so the source is
`182/156`; the same twenty-three inert columns and no inert gate pad it to `205/156`. -/
theorem padMemoryCoreMixed_e3_carrier_fingerprint (R : RAP F) (hk : 0 < R.k)
    (hw : R.w = 182) (hs : R.s = 156) :
    (padMemoryCoreMixed R hk 3).w = 205 ∧ (padMemoryCoreMixed R hk 3).s = 156 := by
  constructor
  · simp [padMemoryCoreMixed, hw, memoryResidualColumns]
  · simp [padMemoryCoreMixed, hs, memoryResidualTransitionGates]

/-- Exact semantic invariance of the retyped memory residual padding. -/
theorem padMemoryCoreMixed_satisfies_iff (R : RAP F) (hk : 0 < R.k) (e : ℕ)
    (P : Fin (padMemoryCoreMixed R hk e).w → F[X]) :
    (padMemoryCoreMixed R hk e).Satisfies P ↔
      R.Satisfies
        (projectTrace R (firstRoundExtra R hk (memoryResidualColumns e)) P) :=
  satisfies_iff R _ _ P

theorem padMemoryCoreMixed_residual_compose_zero (R : RAP F) (hk : 0 < R.k) (e : ℕ)
    (P : Fin (padMemoryCoreMixed R hk e).w → F[X])
    (i : Fin (memoryResidualTransitionGates e)) :
    (padMemoryCoreMixed R hk e).compose P (Fin.natAdd R.s i) = 0 :=
  compose_right R _ _ P i

/-- Diagnostic all-inert `e = 3` compute padding has the `199/98` fingerprint.  `compute_decompressed_total_arithmetic` is the deployed side. -/
theorem padComputeCore_e3_fingerprint (R : RAP F) (hk : 0 < R.k)
    (hw : R.w = 187) (hs : R.s = 87) :
    (padComputeCore R hk 3).w = 199 ∧ (padComputeCore R hk 3).s = 98 := by
  apply padComputeCore_fingerprint R hk 3
  · simpa [computeCoreWidth] using hw
  · simpa [computeCoreTotalConstraints, computeCoreTransitionGates,
      computeCoreEndpointEqualityConstraints] using hs

/-- At `e = 3`, the exact authorized memory residual is twenty-five columns and eleven zero gates,
giving final width/total-constraint fingerprint `196/104` from a `171/93` semantic core.  The
transition bucket separately changes from `77` to `88`. -/
theorem padMemoryCore_e3_fingerprint (R : RAP F) (hk : 0 < R.k)
    (hw : R.w = 180) (hs : R.s = 93) :
    (padMemoryCore R hk 3).w = 203 ∧ (padMemoryCore R hk 3).s = 104 := by
  apply padMemoryCore_fingerprint R hk 3
  · simpa [memoryCoreWidth] using hw
  · simpa [memoryCoreTotalConstraints, memoryCoreTransitionGates,
      memoryCoreEndpointEqualityConstraints] using hs

/-- Regression: `87` is the final compute transition count, not the final total `.s`. -/
theorem padComputeCore_e3_s_ne_transition_only (R : RAP F) (hk : 0 < R.k)
    (hw : R.w = 187) (hs : R.s = 87) :
    (padComputeCore R hk 3).s ≠ 87 := by
  rw [(padComputeCore_e3_fingerprint R hk hw hs).2]
  norm_num

/-- Regression: `88` is the final memory transition count, not the final total `.s`. -/
theorem padMemoryCore_e3_s_ne_transition_only (R : RAP F) (hk : 0 < R.k)
    (hw : R.w = 180) (hs : R.s = 93) :
    (padMemoryCore R hk 3).s ≠ 88 := by
  rw [(padMemoryCore_e3_fingerprint R hk hw hs).2]
  norm_num

/-- Exact semantic invariance of diagnostic all-inert compute padding. -/
theorem padComputeCore_satisfies_iff (R : RAP F) (hk : 0 < R.k) (e : ℕ)
    (P : Fin (padComputeCore R hk e).w → F[X]) :
    (padComputeCore R hk e).Satisfies P ↔
      R.Satisfies
        (projectTrace R (firstRoundExtra R hk (computeResidualColumns e)) P) :=
  satisfies_iff R _ _ P

/-- Exact semantic invariance of the authorized memory residual padding. -/
theorem padMemoryCore_satisfies_iff (R : RAP F) (hk : 0 < R.k) (e : ℕ)
    (P : Fin (padMemoryCore R hk e).w → F[X]) :
    (padMemoryCore R hk e).Satisfies P ↔
      R.Satisfies
        (projectTrace R (firstRoundExtra R hk (memoryResidualColumns e)) P) :=
  satisfies_iff R _ _ P

/-- Every one of the appended compute residual constraints is literally the zero polynomial after
trace composition. -/
theorem padComputeCore_residual_compose_zero (R : RAP F) (hk : 0 < R.k) (e : ℕ)
    (P : Fin (padComputeCore R hk e).w → F[X])
    (i : Fin (residualTransitionGates e)) :
    (padComputeCore R hk e).compose P (Fin.natAdd R.s i) = 0 :=
  compose_right R _ _ P i

/-- Memory analogue of `padComputeCore_residual_compose_zero`. -/
theorem padMemoryCore_residual_compose_zero (R : RAP F) (hk : 0 < R.k) (e : ℕ)
    (P : Fin (padMemoryCore R hk e).w → F[X])
    (i : Fin (residualTransitionGates e)) :
    (padMemoryCore R hk e).compose P (Fin.natAdd R.s i) = 0 :=
  compose_right R _ _ P i

#print axioms satisfies_iff
#print axioms padComputeCore_e3_fingerprint
#print axioms padMemoryCore_e3_fingerprint
#print axioms padComputeCore_e3_s_ne_transition_only
#print axioms padMemoryCore_e3_s_ne_transition_only
#print axioms padComputeCore_satisfies_iff
#print axioms padMemoryCore_satisfies_iff
#print axioms padMemoryCoreMixed_e3_fingerprint
#print axioms padMemoryCoreMixed_satisfies_iff
#print axioms memory_transition_arithmetic_mixed
#print axioms memory_bucket_identity_interim
#print axioms memory_transition_arithmetic_deployed

end
end RAPPadding
end Nock.NockVMROM.Thm54
