/-
  Nock/NockVMROM/Thm54/ExtensionChallenges.lean

  **The five base-field challenge coordinates, re-typed over the extension field.**

  `optimizedMergedProductionFailureProbabilityBound` (`OptimizedStrictPackage.lean:724`), the
  bound the released capstone consumes, is

      (p8Work + 494N + 1 + 19M)/|𝕂| + ioWork/|𝕂|² + (20 + 14M)/|𝔽|,

  and at Goldilocks the third summand — over the **base** field — dominates, capping the
  formalized soundness at ~29 bits (`GoldilocksParameters.merged_soundness_at_paper_configuration`,
  `GoldilocksParameters.lean:459`; the pre-merge `soundness_at_paper_configuration` is `:399`).  That summand exists because five coordinates of the
  challenge tuple are typed `F`:

  * `FinalComputeChallengeTuple.challenge36` (`OptimizedComputeCollisionBound.lean:518`),
    contributing the `20` via `finalSelectorBadChallenges_card_le_twenty` (`:459`);

  **The base-field typing is a transcription artifact, not the design.**  The deployed client
  assembles *every* logical challenge as a degree-3 extension element: `make-pelt-chal`
  (`hoon/common/ztd/five.hoon:159`) builds each one as a three-coefficient `bpoly` from the
  three base-field draws `<name>-a`, `<name>-b`, `<name>-c`, and `init-ext-chals`
  (`hoon/common/ztd/seven.hoon:323`) routes every round-1 name of `chal-names-rd1` (`:288`)
  through it; `chal-names-rd2` (`:346`) is treated the same way by `init-mega-ext-chals`
  (`:395`).  The paper agrees: the paper states soundness as negligible in `𝕂`, and
  the paper (`Thm:NockVMROM`) says "negligible soundness error if `N,L ∈ negl(𝕂)`".

  This module builds the `𝕂`-typed variant **alongside** the existing one.  Nothing here
  edits or replaces the challenge tuple: `OptimizedStrictFullPackage.lean` and its consumer
  `optimizedFalseAcceptance_probability_le` still see the `F`-typed tuple.

  **What the counting argument needs, and why it survives (§1).**  Every base-field summand
  is a root count for a random-linear-combination polynomial whose *coefficients* are
  base-field AIR coordinate values.  Widening the challenge from `𝔽` to `𝕂` base-changes that
  polynomial along `algebraMap 𝔽 𝕂`: it stays nonzero (`liftValues_exists_ne_zero`), keeps its
  degree, and therefore still has at most `deg` roots — now inside a set of size `|𝕂|` rather
  than `|𝔽|` (`liftedValueBadChallenges_card_le`).  The *numerators* are unchanged; only the
  denominator moves.  `liftedRlc_eval_algebraMap` is the compatibility receipt: at a base-field
  challenge the widened gate agrees with the existing one, so this is a widening of the
  challenge domain and not a different constraint system.

  **What this module does NOT do.**  Re-typing needs those four gates recompiled
  to the gathered extension level; the machinery for that is already in the tree —
  `gatherEnv` (`CoordinateRAPCore.lean:186`) packs three consecutive base-field challenge slots
  into one `K` challenge at line `189`, which is precisely `make-pelt-chal`'s construction.
  Building those four gathered gates, and migrating the capstone onto this tuple, are separate
  steps that need explicit authorization.

  **Result (§6).**  `productionFailureProbabilityBoundK` is *exactly* the consumed bound with
  `(20 + 14M)/|𝔽|` replaced by `(20 + 14M)/|𝕂|`
  (`probabilityBoundK_eq_old_with_extension_denominator`), and at Goldilocks with
  `N = M = 2^31` it is below `2^-123`, against the old bound's `> 2^-30`.

  **Mood (§7).**  Everything in §6 is a statement about `goldilocksFailureBoundK`, the `𝕂`-typed
  variant.  The released capstone consumes the `𝔽`-typed bound, so this module says what retyping
  **would** give, not what the capstone gives — the capstone's figure at this same configuration
  is `29` bits.  §7 supplies the one composition the module was missing: the `𝕂`-typed *counted
  event* (not merely the rational function) has probability below `2^-123`.
-/
import Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxRecDepth 8000

namespace Nock.NockVMROM.Thm54
namespace ExtensionChallenges

open scoped Classical Polynomial
open Polynomial
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54.OptimizedComputeCollisionBound
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.TemplateAxisCounting

noncomputable section

/-! ## 1. Base change of the scalar root count

`valueBadChallenges` (`OptimizedComputeCollisionBound.lean:353`) is already field-generic in
its coefficient field.  The only new content is that a list of **base**-field coefficients may
be tested against an **extension**-field challenge, with the same root bound. -/

/-- The base-field coefficient list, viewed inside the extension. -/
def liftValues {F K : Type*} [Field F] [Field K] [Algebra F K] (as : List F) : List K :=
  as.map (algebraMap F K)

@[simp] theorem liftValues_length
    {F K : Type*} [Field F] [Field K] [Algebra F K] (as : List F) :
    (liftValues (K := K) as).length = as.length := by
  simp [liftValues]

/-- Nonzero-ness survives the base change: `algebraMap` between fields is injective. -/
theorem liftValues_exists_ne_zero
    {F K : Type*} [Field F] [Field K] [Algebra F K] (as : List F)
    (h : ∃ a ∈ as, a ≠ 0) :
    ∃ a ∈ liftValues (K := K) as, a ≠ 0 := by
  obtain ⟨a, ha, hane⟩ := h
  refine ⟨algebraMap F K a, ?_, ?_⟩
  · exact List.mem_map_of_mem ha
  · simpa using hane

theorem liftValues_forall_eq_zero
    {F K : Type*} [Field F] [Field K] [Algebra F K] (as : List F)
    (h : ∀ a ∈ liftValues (K := K) as, a = 0) : ∀ a ∈ as, a = 0 := by
  intro a ha
  have := h (algebraMap F K a) (List.mem_map_of_mem ha)
  simpa using this

/-- **Compatibility receipt.**  At a *base-field* challenge the widened random-linear
combination is the image of the existing one, so re-typing the coordinate widens the challenge
domain rather than changing the constraint. -/
theorem liftedRlc_eval_algebraMap
    {F K : Type*} [Field F] [Field K] [Algebra F K] (as : List F) (ρ : F) :
    (valueRlcPolynomial (liftValues (K := K) as)).eval (algebraMap F K ρ) =
      algebraMap F K ((valueRlcPolynomial as).eval ρ) := by
  induction as with
  | nil => simp [liftValues, valueRlcPolynomial]
  | cons a as ih =>
      simp only [liftValues, List.map_cons, valueRlcPolynomial, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X] at *
      rw [ih]
      simp [map_add, map_mul]

/-- The extension-field bad set for a base-field coefficient family. -/
def liftedValueBadChallenges
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    (as : List F) : Finset K :=
  valueBadChallenges (liftValues (K := K) as)

/-- **The root count is unchanged by the base change.**  This is the whole soundness content
of the re-typing: the numerator stays `as.length - 1` while the sample space grows to `|𝕂|`. -/
theorem liftedValueBadChallenges_card_le
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    (as : List F) :
    (liftedValueBadChallenges (K := K) as).card ≤ as.length - 1 := by
  have h := valueBadChallenges_card_le (liftValues (K := K) as)
  rw [liftValues_length] at h
  exact h

/-- Outside the bad set, a vanishing widened combination still forces every base-field
coefficient to vanish. -/
theorem liftedValueCollisionExcluded_of_not_bad
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    (ρ : K) (as : List F) (hgood : ρ ∉ liftedValueBadChallenges (K := K) as)
    (hroot : (valueRlcPolynomial (liftValues (K := K) as)).eval ρ = 0) :
    ∀ a ∈ as, a = 0 := by
  apply liftValues_forall_eq_zero (K := K)
  intro a ha
  by_contra hne
  apply hgood
  have hnz : ∃ x ∈ liftValues (K := K) as, x ≠ 0 := ⟨a, ha, hne⟩
  simp only [liftedValueBadChallenges, valueBadChallenges, if_pos hnz,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact hroot

/-! ## 2. The five re-typed coordinates

`MemoryChallengeTuple` (`OptimizedMemoryCollisionAccounting.lean:180`) and
`FinalComputeChallengeTuple` (`OptimizedComputeCollisionBound.lean:515`) with their
base-field coordinates moved to `K`.  Both are new types; the originals are untouched. -/

/-- The memory chip's five challenges, **all** in the extension field. -/
structure MemoryChallengeTupleK (K : Type*) where
  extensionFold : K
  selectorEquality : K
  firstMask : K
  lastMask : K
  chain : K
deriving DecidableEq, Fintype

/-- The compute chip's three challenges, **all** in the extension field. -/
structure FinalComputeChallengeTupleK (K : Type*) where
  challenge9 : K
  challenge11 : K
  challenge36 : K
deriving DecidableEq, Fintype

theorem memoryChallengeTupleK_card (K : Type*) [Fintype K] :
    Fintype.card (MemoryChallengeTupleK K) = Fintype.card K ^ 5 := by
  let e : MemoryChallengeTupleK K ≃ K × K × K × K × K :=
    { toFun := fun c =>
        (c.extensionFold, c.selectorEquality, c.firstMask, c.lastMask, c.chain)
      invFun := fun c => ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2⟩
      left_inv := by intro c; cases c; rfl
      right_inv := by intro c; rcases c with ⟨a, b, c, d, e⟩; rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod]
  ring

theorem finalComputeChallengeTupleK_card (K : Type*) [Fintype K] :
    Fintype.card (FinalComputeChallengeTupleK K) = Fintype.card K ^ 3 := by
  let e : FinalComputeChallengeTupleK K ≃ K × K × K :=
    { toFun := fun c => (c.challenge9, c.challenge11, c.challenge36)
      invFun := fun c => ⟨c.1, c.2.1, c.2.2⟩
      left_inv := by intro c; cases c; rfl
      right_inv := by intro c; rcases c with ⟨a, b, c⟩; rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod]
  ring

/-! ## 3. All-row memory accounting at the new typing

The extension-fold coordinate was already `K` and its merged `19 * M` bound
(`allMemoryExtensionBadChallenges_card_le_19`, `OptimizedMemoryCollisionAccounting.lean:216`) is
reused verbatim.  The four scalar coordinates are re-counted through §1. -/

/-- All-row bad set for one of the seven scalar families, now inside `K`. -/
def allMemoryScalarBadChallengesAtK
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {M : ℕ} (families : Fin M → Fin 7 → Fin 3 → F) (j : Fin 7) : Finset K :=
  Finset.univ.biUnion fun i =>
    liftedValueBadChallenges (K := K) (List.ofFn (families i j))

/-- All-row bad set for the four selector-equality families, now inside `K`. -/
def allMemorySelectorBadChallengesK
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {M : ℕ} (families : Fin M → Fin 7 → Fin 3 → F) : Finset K :=
  Finset.univ.biUnion fun j : Fin 4 =>
    allMemoryScalarBadChallengesAtK (K := K) families ⟨j, by omega⟩

theorem allMemoryScalarBadChallengesAtK_card_le
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {M : ℕ} (families : Fin M → Fin 7 → Fin 3 → F) (j : Fin 7) :
    (allMemoryScalarBadChallengesAtK (K := K) families j).card ≤ 2 * M := by
  calc
    _ ≤ ∑ i : Fin M,
        (liftedValueBadChallenges (K := K) (List.ofFn (families i j))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin M, 2 := Finset.sum_le_sum fun i _ =>
      (liftedValueBadChallenges_card_le (K := K) (List.ofFn (families i j))).trans_eq
        (by simp)
    _ = 2 * M := by simp [Nat.mul_comm]

theorem allMemorySelectorBadChallengesK_card_le
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {M : ℕ} (families : Fin M → Fin 7 → Fin 3 → F) :
    (allMemorySelectorBadChallengesK (K := K) families).card ≤ 8 * M := by
  calc
    _ ≤ ∑ j : Fin 4,
        (allMemoryScalarBadChallengesAtK (K := K) families ⟨j, by omega⟩).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin 4, 2 * M := Finset.sum_le_sum fun j _ =>
      allMemoryScalarBadChallengesAtK_card_le (K := K) families ⟨j, by omega⟩
    _ = 8 * M := by simp; ring

/-! ### Coordinate lifts into the five-coordinate `K` tuple -/

def toMemoryTupleK {K : Type*} (q : K × K × K × K × K) : MemoryChallengeTupleK K :=
  ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2⟩

def liftMemKFold {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) : Finset (MemoryChallengeTupleK K) :=
  (bad ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ Finset.univ)))).image
    toMemoryTupleK

def liftMemKSelector {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) : Finset (MemoryChallengeTupleK K) :=
  (Finset.univ ×ˢ (bad ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ Finset.univ)))).image
    toMemoryTupleK

def liftMemKFirstMask {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) : Finset (MemoryChallengeTupleK K) :=
  (Finset.univ ×ˢ (Finset.univ ×ˢ (bad ×ˢ (Finset.univ ×ˢ Finset.univ)))).image
    toMemoryTupleK

def liftMemKLastMask {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) : Finset (MemoryChallengeTupleK K) :=
  (Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ (bad ×ˢ Finset.univ)))).image
    toMemoryTupleK

def liftMemKChain {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) : Finset (MemoryChallengeTupleK K) :=
  (Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ bad)))).image
    toMemoryTupleK

theorem liftMemK_card_le {K : Type*} [Fintype K] [DecidableEq K] (bad : Finset K) :
    (liftMemKFold bad).card ≤ bad.card * Fintype.card K ^ 4 ∧
    (liftMemKSelector bad).card ≤ bad.card * Fintype.card K ^ 4 ∧
    (liftMemKFirstMask bad).card ≤ bad.card * Fintype.card K ^ 4 ∧
    (liftMemKLastMask bad).card ≤ bad.card * Fintype.card K ^ 4 ∧
    (liftMemKChain bad).card ≤ bad.card * Fintype.card K ^ 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Finset.card_image_le.trans_eq (by
      simp only [Finset.card_product, Finset.card_univ]; ring)

def fullMemoryCollisionEventK
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K)
    (families : Fin M → Fin 7 → Fin 3 → F) :
    Finset (MemoryChallengeTupleK K) :=
  (((liftMemKFold (allMemoryExtensionBadChallenges envK) ∪
      liftMemKSelector (allMemorySelectorBadChallengesK (K := K) families)) ∪
      liftMemKFirstMask (allMemoryScalarBadChallengesAtK (K := K) families 4)) ∪
      liftMemKLastMask (allMemoryScalarBadChallengesAtK (K := K) families 5)) ∪
    liftMemKChain (allMemoryScalarBadChallengesAtK (K := K) families 6)

def FullMemoryCollisionGoodK
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K)
    (families : Fin M → Fin 7 → Fin 3 → F)
    (c : MemoryChallengeTupleK K) : Prop :=
  c ∉ fullMemoryCollisionEventK envK families

/-- **The re-derived memory collision-event bound.**  The
*event numerators* `19M` and `14M` are unchanged — nothing in the counting needed the base
field — but they now sit over `|K|⁵` instead of `|K|·|F|⁴`, so they add: `19 + 8 + 2 + 2 + 2
= 33`. -/
theorem fullMemoryCollisionEventK_card_le
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K)
    (families : Fin M → Fin 7 → Fin 3 → F) :
    (fullMemoryCollisionEventK envK families).card ≤
      (33 * M) * Fintype.card K ^ 4 := by
  have hA := (liftMemK_card_le (allMemoryExtensionBadChallenges envK)).1
  have hB := (liftMemK_card_le
    (allMemorySelectorBadChallengesK (K := K) families)).2.1
  have hC := (liftMemK_card_le
    (allMemoryScalarBadChallengesAtK (K := K) families 4)).2.2.1
  have hD := (liftMemK_card_le
    (allMemoryScalarBadChallengesAtK (K := K) families 5)).2.2.2.1
  have hE := (liftMemK_card_le
    (allMemoryScalarBadChallengesAtK (K := K) families 6)).2.2.2.2
  set A := liftMemKFold (allMemoryExtensionBadChallenges envK) with hAdef
  set B := liftMemKSelector (allMemorySelectorBadChallengesK (K := K) families) with hBdef
  set C := liftMemKFirstMask (allMemoryScalarBadChallengesAtK (K := K) families 4) with hCdef
  set D := liftMemKLastMask (allMemoryScalarBadChallengesAtK (K := K) families 5) with hDdef
  set E := liftMemKChain (allMemoryScalarBadChallengesAtK (K := K) families 6) with hEdef
  have hUnion : ((((A ∪ B) ∪ C) ∪ D) ∪ E).card ≤
      A.card + B.card + C.card + D.card + E.card :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add
        ((Finset.card_union_le _ _).trans
          (Nat.add_le_add
            ((Finset.card_union_le _ _).trans
              (Nat.add_le_add (Finset.card_union_le _ _) le_rfl))
            le_rfl))
        le_rfl)
  calc
    (fullMemoryCollisionEventK envK families).card
        ≤ A.card + B.card + C.card + D.card + E.card := by
      simpa only [fullMemoryCollisionEventK, hAdef, hBdef, hCdef, hDdef, hEdef] using hUnion
    _ ≤ (allMemoryExtensionBadChallenges envK).card * Fintype.card K ^ 4 +
        (allMemorySelectorBadChallengesK (K := K) families).card * Fintype.card K ^ 4 +
        (allMemoryScalarBadChallengesAtK (K := K) families 4).card * Fintype.card K ^ 4 +
        (allMemoryScalarBadChallengesAtK (K := K) families 5).card * Fintype.card K ^ 4 +
        (allMemoryScalarBadChallengesAtK (K := K) families 6).card *
          Fintype.card K ^ 4 := by omega
    _ ≤ (19 * M) * Fintype.card K ^ 4 + (8 * M) * Fintype.card K ^ 4 +
        (2 * M) * Fintype.card K ^ 4 + (2 * M) * Fintype.card K ^ 4 +
        (2 * M) * Fintype.card K ^ 4 := by
      gcongr
      · exact allMemoryExtensionBadChallenges_card_le_19 envK
      · exact allMemorySelectorBadChallengesK_card_le (K := K) families
      all_goals exact allMemoryScalarBadChallengesAtK_card_le (K := K) families _
    _ = (33 * M) * Fintype.card K ^ 4 := by ring

theorem exists_fullMemoryCollisionGoodK_of_bound_lt
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K]
    {M : ℕ} (envK : Fin M → Env K)
    (families : Fin M → Fin 7 → Fin 3 → F)
    (hlt : (33 * M) * Fintype.card K ^ 4 < Fintype.card K ^ 5) :
    ∃ c : MemoryChallengeTupleK K, FullMemoryCollisionGoodK envK families c := by
  have hcard :
      (fullMemoryCollisionEventK envK families).card <
        (Finset.univ : Finset (MemoryChallengeTupleK K)).card := by
    rw [Finset.card_univ, memoryChallengeTupleK_card]
    exact (fullMemoryCollisionEventK_card_le envK families).trans_lt hlt
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨c, hc⟩

/-- The memory chip's failure probability at the new typing: `33M/|K|`, against the mixed
`19M/|K| + 14M/|F|` (`fullMemoryCollisionProbabilityBound`,
`OptimizedMemoryCollisionAccounting.lean:446`). -/
theorem fullMemoryCollisionProbabilityK_le
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [Nonempty K]
    {M : ℕ} (envK : Fin M → Env K)
    (families : Fin M → Fin 7 → Fin 3 → F) :
    ((fullMemoryCollisionEventK envK families).card : ℚ) / (Fintype.card K ^ 5) ≤
      (33 * M : ℚ) / Fintype.card K := by
  have hk : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hcast : ((fullMemoryCollisionEventK envK families).card : ℚ) ≤
      ((33 * M : ℕ) : ℚ) * (Fintype.card K : ℚ) ^ 4 := by
    have := fullMemoryCollisionEventK_card_le envK families
    exact_mod_cast this
  rw [div_le_div_iff₀ (by positivity) hk]
  push_cast at hcast ⊢
  nlinarith [hcast, pow_pos hk 4, hk]


/-! ## 4. The compute chip's selector challenge at the new typing

`finalSelectorBadChallenges` (`OptimizedComputeCollisionBound.lean:455`) unions two eleven-term
selector-versus-public families, each contributing at most ten roots.  Both families are
base-field lists; §1 re-counts their roots inside `K`. -/

/-- The two selector families' bad set, now inside `K`. -/
def liftedFinalSelectorBadChallenges
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    (env : Env F) : Finset K :=
  liftedValueBadChallenges (K := K) (selectorErrors env 20) ∪
    liftedValueBadChallenges (K := K) (selectorErrors env 31)

/-- The same `20` as `finalSelectorBadChallenges_card_le_twenty`
(`OptimizedComputeCollisionBound.lean:459`) — the numerator does not change. -/
theorem liftedFinalSelectorBadChallenges_card_le_twenty
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    (env : Env F) :
    (liftedFinalSelectorBadChallenges (K := K) env).card ≤ 20 := by
  have h20 : (liftedValueBadChallenges (K := K) (selectorErrors env 20)).card ≤ 10 :=
    (liftedValueBadChallenges_card_le (K := K) (selectorErrors env 20)).trans_eq (by simp)
  have h31 : (liftedValueBadChallenges (K := K) (selectorErrors env 31)).card ≤ 10 :=
    (liftedValueBadChallenges_card_le (K := K) (selectorErrors env 31)).trans_eq (by simp)
  have hu := Finset.card_union_le (liftedValueBadChallenges (K := K) (selectorErrors env 20))
    (liftedValueBadChallenges (K := K) (selectorErrors env 31))
  rw [liftedFinalSelectorBadChallenges]
  omega

def toComputeTupleK {K : Type*} (q : K × K × K) : FinalComputeChallengeTupleK K :=
  ⟨q.1, q.2.1, q.2.2⟩

def liftCompK9 {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) : Finset (FinalComputeChallengeTupleK K) :=
  (bad ×ˢ (Finset.univ ×ˢ Finset.univ)).image toComputeTupleK

def liftCompK11 {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) : Finset (FinalComputeChallengeTupleK K) :=
  (Finset.univ ×ˢ (bad ×ˢ Finset.univ)).image toComputeTupleK

def liftCompK36 {K : Type*} [Fintype K] [DecidableEq K]
    (bad : Finset K) : Finset (FinalComputeChallengeTupleK K) :=
  (Finset.univ ×ˢ (Finset.univ ×ˢ bad)).image toComputeTupleK

theorem liftCompK_card_le {K : Type*} [Fintype K] [DecidableEq K] (bad : Finset K) :
    (liftCompK9 bad).card ≤ bad.card * Fintype.card K ^ 2 ∧
    (liftCompK11 bad).card ≤ bad.card * Fintype.card K ^ 2 ∧
    (liftCompK36 bad).card ≤ bad.card * Fintype.card K ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    exact Finset.card_image_le.trans_eq (by
      simp only [Finset.card_product, Finset.card_univ]; ring)

/-- The `K`-typed analogue of `FullFinalComputeCollisionEvent`
(`OptimizedComputeCollisionBound.lean:556`). -/
def FullFinalComputeCollisionEventK
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) (envF : Env F) :
    Finset (FinalComputeChallengeTupleK K) :=
  liftCompK9 (finalRowsBadChallenges envK) ∪
    liftCompK11 (walkInitBadChallenges walkEnv) ∪
    liftCompK36 (liftedFinalSelectorBadChallenges (K := K) envF)

/-- **The re-derived compute collision-event bound.**  Compare
`fullFinalComputeCollisionEvent_card_le` (`OptimizedComputeCollisionBound.lean:821`), whose
right-hand side is `(494N)·|K|·|F| + |K|·1·|F| + |K|·|K|·20`. -/
theorem fullFinalComputeCollisionEventK_card_le
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    {N : ℕ} (envK : Fin N → Env K) (walkEnv : Env K) (envF : Env F) :
    (FullFinalComputeCollisionEventK envK walkEnv envF).card ≤
      (494 * N + 1 + 20) * Fintype.card K ^ 2 := by
  have h9 := (liftCompK_card_le (finalRowsBadChallenges envK)).1
  have h11 := (liftCompK_card_le (walkInitBadChallenges walkEnv)).2.1
  have h36 := (liftCompK_card_le (liftedFinalSelectorBadChallenges (K := K) envF)).2.2
  set A := liftCompK9 (finalRowsBadChallenges envK) with hAdef
  set B := liftCompK11 (walkInitBadChallenges walkEnv) with hBdef
  set C := liftCompK36 (liftedFinalSelectorBadChallenges (K := K) envF) with hCdef
  have hUnion : ((A ∪ B) ∪ C).card ≤ A.card + B.card + C.card :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_union_le _ _) le_rfl)
  calc
    (FullFinalComputeCollisionEventK envK walkEnv envF).card
        ≤ A.card + B.card + C.card := by
      simpa only [FullFinalComputeCollisionEventK, hAdef, hBdef, hCdef] using hUnion
    _ ≤ (finalRowsBadChallenges envK).card * Fintype.card K ^ 2 +
        (walkInitBadChallenges walkEnv).card * Fintype.card K ^ 2 +
        (liftedFinalSelectorBadChallenges (K := K) envF).card *
          Fintype.card K ^ 2 := by omega
    _ ≤ (494 * N) * Fintype.card K ^ 2 + 1 * Fintype.card K ^ 2 +
        20 * Fintype.card K ^ 2 := by
      gcongr
      · exact finalRowsBadChallenges_card_le envK
      · exact walkInitBadChallenges_card_le_one walkEnv
      · exact liftedFinalSelectorBadChallenges_card_le_twenty (K := K) envF
    _ = (494 * N + 1 + 20) * Fintype.card K ^ 2 := by ring

/-! ## 5. The production challenge tuple, all-extension

`OptimizedProductionChallengeTuple` (`OptimizedStrictPackage.lean:554`) has
`|K|⁹ · |F|⁵` points (`card_optimizedProductionChallengeTuple`, `:638`).  Its all-extension
analogue has `|K|¹⁴`: the same fourteen coordinates, five of which stopped being base-field. -/

abbrev ProductionChallengeTupleK (K : Type) [Fintype K] :=
  JointCoins K ×
    ((K × K) × (FinalComputeChallengeTupleK K × MemoryChallengeTupleK K))

/-- **`|K|¹⁴`.**  The analogue of `card_optimizedProductionChallengeTuple`
(`OptimizedStrictPackage.lean:638`). -/
theorem card_productionChallengeTupleK (K : Type) [Fintype K] :
    Fintype.card (ProductionChallengeTupleK K) = Fintype.card K ^ 14 := by
  simp only [ProductionChallengeTupleK, Fintype.card_prod,
    finalComputeChallengeTupleK_card, memoryChallengeTupleK_card]
  ring

def liftP8FailureK {K : Type} [Fintype K] [DecidableEq K]
    (bad : Finset (JointCoins K)) : Finset (ProductionChallengeTupleK K) :=
  bad ×ˢ Finset.univ

def liftIOFailureK {K : Type} [Fintype K] [DecidableEq K]
    (bad : Finset (K × K)) : Finset (ProductionChallengeTupleK K) :=
  Finset.univ ×ˢ (bad ×ˢ Finset.univ)

def liftComputeFailureK {K : Type} [Fintype K] [DecidableEq K]
    (bad : Finset (FinalComputeChallengeTupleK K)) :
    Finset (ProductionChallengeTupleK K) :=
  Finset.univ ×ˢ (Finset.univ ×ˢ (bad ×ˢ Finset.univ))

def liftMemoryFailureK {K : Type} [Fintype K] [DecidableEq K]
    (bad : Finset (MemoryChallengeTupleK K)) :
    Finset (ProductionChallengeTupleK K) :=
  Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ bad))

/-- The `K`-typed analogue of `OptimizedProductionFailureEvent`
(`OptimizedStrictPackage.lean:604`). -/
def ProductionFailureEventK
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M m : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (lmb : K)
    (records : FiniteIO.PreChallengeRecords K m)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    Finset (ProductionChallengeTupleK K) :=
  ((liftP8FailureK (ProductionP8Containment.FailureUnion T C lmb) ∪
      liftIOFailureK (FiniteIO.IOFailureEvent records)) ∪
      liftComputeFailureK
        (FullFinalComputeCollisionEventK computeEnvK computeWalkEnv computeEnvF)) ∪
    liftMemoryFailureK (fullMemoryCollisionEventK memoryEnvK memoryFamilies)

/-- The counted bound.  Every summand is `(something) * cardK ^ 13` or `ioWork * cardK ^ 12`,
against `|K|¹⁴` total. -/
def productionFailureCardBoundK (cardK p8Work ioWork N M : ℕ) : ℕ :=
  p8Work * cardK ^ 3 * (cardK ^ 2 * (cardK ^ 3 * cardK ^ 5)) +
    cardK ^ 4 * ioWork * (cardK ^ 3 * cardK ^ 5) +
    cardK ^ 6 * ((494 * N + 1 + 20) * cardK ^ 2 * cardK ^ 5) +
    cardK ^ 9 * ((33 * M) * cardK ^ 4)

/-- **The re-derived probability bound.**  The analogue of
`optimizedProductionFailureProbabilityBound` (`OptimizedStrictPackage.lean:632`), with **no
base-field denominator at all**. -/
def productionFailureProbabilityBoundK (cardK p8Work ioWork N M : ℕ) : ℚ :=
  (p8Work + 494 * N + 21 + 33 * M : ℚ) / cardK + (ioWork : ℚ) / cardK ^ 2

theorem normalized_cardK_bound_eq
    (cardK p8Work ioWork N M : ℕ) (hk : 0 < cardK) :
    (productionFailureCardBoundK cardK p8Work ioWork N M : ℚ) / (cardK ^ 14) =
      productionFailureProbabilityBoundK cardK p8Work ioWork N M := by
  have hkq : (cardK : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  simp only [productionFailureCardBoundK, productionFailureProbabilityBoundK,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  field_simp
  ring

theorem productionFailureEventK_card_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M m : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (records : FiniteIO.PreChallengeRecords K m)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    (ProductionFailureEventK T C lmb records computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies).card ≤
      productionFailureCardBoundK (Fintype.card K)
        (workload T Λ topologyBound axisWorkload)
        (FiniteIO.ioFailureUnionBound m records.requests.length records.responses.length
          (Fintype.card K)) N M := by
  set p8 := liftP8FailureK (ProductionP8Containment.FailureUnion T C lmb) with hp8def
  set io := liftIOFailureK (FiniteIO.IOFailureEvent records) with hiodef
  set comp := liftComputeFailureK
    (FullFinalComputeCollisionEventK computeEnvK computeWalkEnv computeEnvF) with hcompdef
  set mem := liftMemoryFailureK (fullMemoryCollisionEventK memoryEnvK memoryFamilies)
    with hmemdef
  have hrest : Fintype.card ((K × K) ×
      (FinalComputeChallengeTupleK K × MemoryChallengeTupleK K)) =
      Fintype.card K ^ 2 * (Fintype.card K ^ 3 * Fintype.card K ^ 5) := by
    simp only [Fintype.card_prod, finalComputeChallengeTupleK_card,
      memoryChallengeTupleK_card]
    ring
  have hp8 :
      p8.card ≤ workload T Λ topologyBound axisWorkload * Fintype.card K ^ 3 *
        (Fintype.card K ^ 2 * (Fintype.card K ^ 3 * Fintype.card K ^ 5)) := by
    rw [hp8def, liftP8FailureK, Finset.card_product, Finset.card_univ, hrest]
    exact Nat.mul_le_mul_right _
      (ProductionP8Containment.failureUnion_card_le
        h2 T lmb C topologyBound axisWorkload hwindow htopology haxis)
  have hio :
      io.card ≤ Fintype.card K ^ 4 *
        (FiniteIO.ioFailureUnionBound m records.requests.length records.responses.length
          (Fintype.card K)) *
        (Fintype.card K ^ 3 * Fintype.card K ^ 5) := by
    rw [hiodef, liftIOFailureK, Finset.card_product, Finset.card_product,
      Finset.card_univ, Finset.card_univ, card_jointCoins]
    calc
      Fintype.card K ^ 4 * ((FiniteIO.IOFailureEvent records).card *
          Fintype.card (FinalComputeChallengeTupleK K × MemoryChallengeTupleK K))
          ≤ Fintype.card K ^ 4 *
            ((FiniteIO.ioFailureUnionBound m records.requests.length
              records.responses.length (Fintype.card K)) *
              Fintype.card (FinalComputeChallengeTupleK K × MemoryChallengeTupleK K)) := by
        gcongr
        exact FiniteIO.IOFailureEvent_card_le records
      _ = _ := by
        simp only [Fintype.card_prod, finalComputeChallengeTupleK_card,
          memoryChallengeTupleK_card]
        ring
  have hcomp :
      comp.card ≤ Fintype.card K ^ 6 *
        ((494 * N + 1 + 20) * Fintype.card K ^ 2 * Fintype.card K ^ 5) := by
    rw [hcompdef, liftComputeFailureK, Finset.card_product, Finset.card_product,
      Finset.card_product, Finset.card_univ, Finset.card_univ, Finset.card_univ,
      card_jointCoins]
    calc
      Fintype.card K ^ 4 * (Fintype.card (K × K) *
          ((FullFinalComputeCollisionEventK computeEnvK computeWalkEnv computeEnvF).card *
            Fintype.card (MemoryChallengeTupleK K)))
          ≤ Fintype.card K ^ 4 * (Fintype.card (K × K) *
            (((494 * N + 1 + 20) * Fintype.card K ^ 2) *
              Fintype.card (MemoryChallengeTupleK K))) := by
        gcongr
        exact fullFinalComputeCollisionEventK_card_le computeEnvK computeWalkEnv computeEnvF
      _ = _ := by
        simp only [Fintype.card_prod, memoryChallengeTupleK_card]
        ring
  have hmem :
      mem.card ≤ Fintype.card K ^ 9 * ((33 * M) * Fintype.card K ^ 4) := by
    rw [hmemdef, liftMemoryFailureK, Finset.card_product, Finset.card_product,
      Finset.card_product, Finset.card_univ, Finset.card_univ, Finset.card_univ,
      card_jointCoins]
    calc
      Fintype.card K ^ 4 * (Fintype.card (K × K) *
          (Fintype.card (FinalComputeChallengeTupleK K) *
            (fullMemoryCollisionEventK memoryEnvK memoryFamilies).card))
          ≤ Fintype.card K ^ 4 * (Fintype.card (K × K) *
            (Fintype.card (FinalComputeChallengeTupleK K) *
              ((33 * M) * Fintype.card K ^ 4))) := by
        gcongr
        exact fullMemoryCollisionEventK_card_le memoryEnvK memoryFamilies
      _ = _ := by
        simp only [Fintype.card_prod, finalComputeChallengeTupleK_card]
        ring
  calc
    (ProductionFailureEventK T C lmb records computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card
        ≤ p8.card + io.card + comp.card + mem.card := by
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right
          ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _)
    _ ≤ productionFailureCardBoundK (Fintype.card K)
          (workload T Λ topologyBound axisWorkload)
          (FiniteIO.ioFailureUnionBound m records.requests.length records.responses.length
            (Fintype.card K)) N M :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp8 hio) hcomp) hmem

/-- **The re-derived production probability bound**, the analogue of
`optimizedProductionFailureProbability_le` (`OptimizedStrictPackage.lean:815`). -/
theorem productionFailureProbabilityK_le
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]
    {Λ N M m : ℕ}
    (h2 : (2 : K) ≠ 0)
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ)
    (lmb : K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (records : FiniteIO.PreChallengeRecords K m)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    ((ProductionFailureEventK T C lmb records computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card : ℚ) /
        Fintype.card (ProductionChallengeTupleK K) ≤
      productionFailureProbabilityBoundK (Fintype.card K)
        (workload T Λ topologyBound axisWorkload)
        (FiniteIO.ioFailureUnionBound m records.requests.length records.responses.length
          (Fintype.card K)) N M := by
  have hkpos : 0 < Fintype.card K := Fintype.card_pos
  have hcard := productionFailureEventK_card_le h2 T C lmb topologyBound axisWorkload
    hwindow htopology haxis records computeEnvK computeWalkEnv computeEnvF
    memoryEnvK memoryFamilies
  have hcast :
      ((ProductionFailureEventK T C lmb records computeEnvK computeWalkEnv computeEnvF
          memoryEnvK memoryFamilies).card : ℚ) ≤
        (productionFailureCardBoundK (Fintype.card K)
          (workload T Λ topologyBound axisWorkload)
          (FiniteIO.ioFailureUnionBound m records.requests.length records.responses.length
            (Fintype.card K)) N M : ℕ) := by
    exact_mod_cast hcard
  rw [card_productionChallengeTupleK]
  calc
    ((ProductionFailureEventK T C lmb records computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card : ℚ) / ((Fintype.card K ^ 14 : ℕ) : ℚ)
        ≤ (productionFailureCardBoundK (Fintype.card K)
            (workload T Λ topologyBound axisWorkload)
            (FiniteIO.ioFailureUnionBound m records.requests.length
              records.responses.length (Fintype.card K)) N M : ℕ) /
          ((Fintype.card K ^ 14 : ℕ) : ℚ) :=
      div_le_div_of_nonneg_right hcast (by positivity)
    _ = productionFailureProbabilityBoundK (Fintype.card K)
        (workload T Λ topologyBound axisWorkload)
        (FiniteIO.ioFailureUnionBound m records.requests.length records.responses.length
          (Fintype.card K)) N M := by
      push_cast
      exact normalized_cardK_bound_eq _ _ _ _ _ hkpos



/-! ## 6. Old versus new, and the figure at Goldilocks

The two bounds differ in exactly one place. -/

open Nock.NockVMROM.Thm54.GoldilocksParameters

/-- **Only the denominator moved.**  The new bound is the consumed bound
(`optimizedMergedProductionFailureProbabilityBound`,
`OptimizedStrictPackage.lean:724`) with `(20 + 14M)/cardF` replaced by `(20 + 14M)/cardK`.
Nothing else — no numerator changed, no term was dropped. -/
theorem probabilityBoundK_eq_old_with_extension_denominator
    (cardK p8Work ioWork N M : ℕ) (hk : 0 < cardK) :
    productionFailureProbabilityBoundK cardK p8Work ioWork N M =
      (p8Work + 494 * N + 1 + 19 * M : ℚ) / cardK + (ioWork : ℚ) / cardK ^ 2 +
        (20 + 14 * M : ℚ) / cardK := by
  have hkq : (cardK : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  simp only [productionFailureProbabilityBoundK]
  field_simp
  ring

/-- **The new bound is never worse**, whenever the base field is no larger than the
extension — which is every extension. -/
theorem probabilityBoundK_le_old
    (cardK cardF p8Work ioWork N M : ℕ)
    (hk : 0 < cardK) (hf : 0 < cardF) (hle : cardF ≤ cardK) :
    productionFailureProbabilityBoundK cardK p8Work ioWork N M ≤
      optimizedMergedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M := by
  rw [probabilityBoundK_eq_old_with_extension_denominator cardK p8Work ioWork N M hk,
    optimizedMergedProductionFailureProbabilityBound]
  have hfq : (0 : ℚ) < (cardF : ℚ) := by exact_mod_cast hf
  have hleq : (cardF : ℚ) ≤ (cardK : ℚ) := by exact_mod_cast hle
  have hnum : (0 : ℚ) ≤ (20 + 14 * M : ℚ) := by positivity
  have : (20 + 14 * M : ℚ) / cardK ≤ (20 + 14 * M : ℚ) / cardF :=
    div_le_div_of_nonneg_left hnum hfq hleq
  linarith

/-- The same comparison against the pre-merge `61·M` bound, which is only weaker. -/
theorem probabilityBoundK_le_legacy
    (cardK cardF p8Work ioWork N M : ℕ)
    (hk : 0 < cardK) (hf : 0 < cardF) (hle : cardF ≤ cardK) :
    productionFailureProbabilityBoundK cardK p8Work ioWork N M ≤
      optimizedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M :=
  (probabilityBoundK_le_old cardK cardF p8Work ioWork N M hk hf hle).trans
    (optimizedMergedProductionFailureProbabilityBound_le cardK cardF p8Work ioWork N M hk)

/-- The `K`-typed production bound with Goldilocks plugged in.  Compare
`GoldilocksParameters.goldilocksFailureBound` (`GoldilocksParameters.lean:253`). -/
def goldilocksFailureBoundK (p8Work ioWork N M : ℕ) : ℚ :=
  productionFailureProbabilityBoundK (Fintype.card Nock.Field.K) p8Work ioWork N M

/-- Two summands, **both over `p³`**. -/
theorem goldilocksFailureBoundK_eq (p8Work ioWork N M : ℕ) :
    goldilocksFailureBoundK p8Work ioWork N M
      = (p8Work + 494 * N + 21 + 33 * M : ℚ) / (cardKGold : ℚ)
        + (ioWork : ℚ) / (cardKGold : ℚ) ^ 2 := by
  simp only [goldilocksFailureBoundK, productionFailureProbabilityBoundK, card_K_gold]

theorem boundK_mono {p8 p8' io io' : ℕ} (N M : ℕ) (h1 : p8 ≤ p8') (h2 : io ≤ io') :
    goldilocksFailureBoundK p8 io N M ≤ goldilocksFailureBoundK p8' io' N M := by
  rw [goldilocksFailureBoundK_eq, goldilocksFailureBoundK_eq]
  have c1 : (p8 : ℚ) ≤ (p8' : ℚ) := by exact_mod_cast h1
  have c2 : (io : ℚ) ≤ (io' : ℚ) := by exact_mod_cast h2
  have s1 : (p8 + 494 * N + 21 + 33 * M : ℚ) / (cardKGold : ℚ)
      ≤ (p8' + 494 * N + 21 + 33 * M : ℚ) / (cardKGold : ℚ) := by
    gcongr
  have s2 : (io : ℚ) / (cardKGold : ℚ) ^ 2 ≤ (io' : ℚ) / (cardKGold : ℚ) ^ 2 := by
    gcongr
  linarith

/-- The row-count summand alone, as a lower bound (the analogue of
`GoldilocksParameters.memory_term_le`, `GoldilocksParameters.lean:276`). -/
theorem rowTerm_le (p8Work ioWork N M : ℕ) :
    (494 * N + 21 + 33 * M : ℚ) / (cardKGold : ℚ) ≤
      goldilocksFailureBoundK p8Work ioWork N M := by
  rw [goldilocksFailureBoundK_eq]
  have h1 : (0 : ℚ) ≤ (p8Work : ℚ) / (cardKGold : ℚ) := by positivity
  have h2 : (0 : ℚ) ≤ (ioWork : ℚ) / (cardKGold : ℚ) ^ 2 := by positivity
  have hd : (0 : ℚ) < (cardKGold : ℚ) := by norm_num
  have hsplit : (p8Work + 494 * N + 21 + 33 * M : ℚ) / (cardKGold : ℚ)
      = (p8Work : ℚ) / (cardKGold : ℚ) + (494 * N + 21 + 33 * M : ℚ) / (cardKGold : ℚ) := by
    field_simp
    ring
  rw [hsplit]
  linarith

/-- **≥ 123 bits at the paper's own headline configuration — a figure the retyping WOULD give.**
the paper claims `121` bits at "a maximal number of `2^31` unique data fields"; the
base-field transcription gives `29`
(`GoldilocksParameters.merged_soundness_at_paper_configuration`, `GoldilocksParameters.lean:459`)
and the extension-field typing would give **`123`**, i.e. it would clear the paper's own claim.
The ceilings are the same generous ones: `p8Work ≤ 2^60`, `ioWork ≤ 16^65 = 2^260`.

This is a
statement about the rational function `goldilocksFailureBoundK`, and the **capstone consumes the
`𝔽`-typed bound**, not this one — so `123` is not a figure about
`optimizedFalseAcceptance_probability_le`, whose own figure here is `29` bits.  `soundnessK_of_counted_event` below composes this
with the counted event. -/
theorem soundnessK_at_paper_configuration (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    1 / (2 : ℚ) ^ 152 < goldilocksFailureBoundK p8Work ioWork (2 ^ 31) (2 ^ 31)
      ∧ goldilocksFailureBoundK p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123 := by
  constructor
  · refine lt_of_lt_of_le ?_ (rowTerm_le p8Work ioWork (2 ^ 31) (2 ^ 31))
    norm_num
  · refine lt_of_le_of_lt (boundK_mono _ _ hp8 hio) ?_
    rw [goldilocksFailureBoundK_eq]
    norm_num

/-- The tight IO ceiling at `n ≤ 2^31` records: `|K|·(28n² + 4n) ≤ |K|·(28·2^62 + 2^33)`.
Sharper than `GoldilocksParameters.ioWork_le` (`GoldilocksParameters.lean:347`), which rounds
up to `16^65`. -/
theorem ioWork_le_tight (n : ℕ) (hn : n ≤ 2 ^ 31) :
    FiniteIO.ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K) ≤
      cardKGold * (28 * 2 ^ 62 + 2 ^ 33) := by
  rw [ioFailureUnionBound_eight, card_K_gold]
  have h1 : 28 * n * n ≤ 28 * 2 ^ 31 * 2 ^ 31 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 28 hn) hn
  have h2 : 4 * n ≤ 4 * 2 ^ 31 := Nat.mul_le_mul_left 4 hn
  exact Nat.mul_le_mul_left _ (by omega)

/-- **≥ 125 bits at the *actual* IO workload — again, what retyping WOULD give.**  Replacing the
`2^260` ceiling by the real `ioFailureUnionBound` at `n ≤ 2^31` buys two more bits.

**Requalified**: `hn : n ≤ 2^31` together with `N = 2^31` compute rows is
satisfiable only when essentially every compute row is a single-record opcode, which
`GatedIOChip.compRows_le_requests_length` (`:912`) forces and `NockVM.activeRequestRecords`
(`NockVM.lean:650`) permits for `.s1/.s3/.s4/.cons` only.  So `125` is a figure for an
all-`OP{1,3,4}`/`cons` program, not for a general one, and like `123` it is a figure about
`goldilocksFailureBoundK` rather than about the capstone. -/
theorem soundnessK_at_real_io_workload (p8Work n : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hn : n ≤ 2 ^ 31) :
    goldilocksFailureBoundK p8Work
        (FiniteIO.ioFailureUnionBound 8 n n (Fintype.card Nock.Field.K))
        (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 125 := by
  refine lt_of_le_of_lt (boundK_mono _ _ hp8 (ioWork_le_tight n hn)) ?_
  rw [goldilocksFailureBoundK_eq]
  norm_num

/-- **The improvement, stated as one sentence.**  At the paper's configuration the existing
bound is above `2^-30` and the re-typed bound below `2^-123`: the re-typing buys at least
**93 bits**, i.e. a factor of `2^93` in the soundness error. -/
theorem improvement_at_paper_configuration (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksFailureBoundK p8Work ioWork (2 ^ 31) (2 ^ 31) < 1 / (2 : ℚ) ^ 123
      ∧ 1 / (2 : ℚ) ^ 30 <
          GoldilocksParameters.goldilocksFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31)
      ∧ goldilocksFailureBoundK p8Work ioWork (2 ^ 31) (2 ^ 31) * 2 ^ 93 <
          GoldilocksParameters.goldilocksFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) := by
  have hnew := (soundnessK_at_paper_configuration p8Work ioWork hp8 hio).2
  have hold :=
    (GoldilocksParameters.soundness_at_paper_configuration p8Work ioWork hp8 hio).1
  refine ⟨hnew, hold, ?_⟩
  have hscaled : goldilocksFailureBoundK p8Work ioWork (2 ^ 31) (2 ^ 31) * 2 ^ 93 <
      (1 / (2 : ℚ) ^ 123) * 2 ^ 93 :=
    mul_lt_mul_of_pos_right hnew (by positivity)
  have heq : (1 / (2 : ℚ) ^ 123) * 2 ^ 93 = 1 / (2 : ℚ) ^ 30 := by
    norm_num
  rw [heq] at hscaled
  exact lt_trans hscaled hold

/-! ## 7. The composition the module was missing

`soundnessK_at_paper_configuration` is a statement about the rational *function*
`goldilocksFailureBoundK`, a `def` on naturals.  `productionFailureProbabilityK_le` is a statement
about the counted *event* `ProductionFailureEventK`.  This section is that join.

The composition is also where `ioWork` acquires its identity.  In `goldilocksFailureBoundK` it is
an abstract natural; here it is
`FiniteIO.ioFailureUnionBound m records.requests.length records.responses.length |𝕂|`, which at
`m = 8` is exactly the charge the capstone instantiates
(`OptimizedStrictFullPackage.optimizedFalseAcceptance_probability_le`).  Likewise `p8Work` is
`workload T Λ topologyBound axisWorkload`, the capstone's own quantity. -/

section Goldilocks

local instance extensionChallengesRingCharP :
    CharP Nock.Field.K (ringChar Nock.Field.K) := ringChar.charP _

/-- **The `𝕂`-typed counted event has probability below `2^-123` at the paper's configuration.**

This is `productionFailureProbabilityK_le` composed with `soundnessK_at_paper_configuration`:
the conclusion is about the **event**, not about the rational function, and the two ceilings are
carried on the *actual* quantities rather than on abstract naturals —
`hp8` on `workload T Λ topologyBound axisWorkload` and `hio` on
`FiniteIO.ioFailureUnionBound m |requests| |responses| |𝕂|`.

* This is the `𝕂`-typed tuple.  The released capstone consumes the `𝔽`-typed one, whose figure at
  this same configuration is **29 bits**
  (`GoldilocksParameters.merged_soundness_at_paper_configuration`).  So this theorem says what the
  retyping *would* buy, not what is deployed.
* `hio` is not free.  `V_comp` emits one, two or three memory records per
  compute row and `GatedIOChip.compRows_le_requests_length` is unconditional, so at `N = 2^31`
  compute rows `hio` holds only up to `≈1.51` records per row; for an arbitrary opcode mix the
  honest figure is `122`, not `123`.  `hp8` has no in-tree majorant at all.  Both are hypotheses
  here, visibly.
* `m` is left general.  At `m = 8` it is the capstone's own `ioFailureUnionBound 8 …` charge. -/
theorem soundnessK_of_counted_event
    {Λ m : ℕ}
    (h2 : (2 : Nock.Field.K) ≠ 0)
    (T : ProductionP8Containment.ProductionStrategy Nock.Field.Fp Nock.Field.K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus Nock.Field.K T.skeleton Λ)
    (lmb : Nock.Field.K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (records : FiniteIO.PreChallengeRecords Nock.Field.K m)
    (computeEnvK : Fin (2 ^ 31) → Env Nock.Field.K) (computeWalkEnv : Env Nock.Field.K)
    (computeEnvF : Env Nock.Field.Fp)
    (memoryEnvK : Fin (2 ^ 31) → Env Nock.Field.K)
    (memoryFamilies : Fin (2 ^ 31) → Fin 7 → Fin 3 → Nock.Field.Fp)
    (hp8 : workload T Λ topologyBound axisWorkload ≤ 2 ^ 60)
    (hio : FiniteIO.ioFailureUnionBound m records.requests.length records.responses.length
        (Fintype.card Nock.Field.K) ≤ 16 ^ 65) :
    ((ProductionFailureEventK T C lmb records computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card : ℚ) /
        Fintype.card (ProductionChallengeTupleK Nock.Field.K) < 1 / (2 : ℚ) ^ 123 :=
  lt_of_le_of_lt
    (productionFailureProbabilityK_le h2 T C lmb topologyBound axisWorkload hwindow htopology haxis
      records computeEnvK computeWalkEnv computeEnvF memoryEnvK memoryFamilies)
    (soundnessK_at_paper_configuration (workload T Λ topologyBound axisWorkload)
      (FiniteIO.ioFailureUnionBound m records.requests.length records.responses.length
        (Fintype.card Nock.Field.K)) hp8 hio).2

/-- The same composition against the **tight** IO workload rather than the `2^260` ceiling: at
`n ≤ 2^31` records on both sides the counted event is below `2^-125`.  Requalified exactly as
`soundnessK_at_real_io_workload` is — `hn` together with `N = 2^31` compute rows forces an
all-single-record opcode mix. -/
theorem soundnessK_of_counted_event_at_real_io_workload
    {Λ : ℕ}
    (h2 : (2 : Nock.Field.K) ≠ 0)
    (T : ProductionP8Containment.ProductionStrategy Nock.Field.Fp Nock.Field.K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus Nock.Field.K T.skeleton Λ)
    (lmb : Nock.Field.K)
    (topologyBound axisWorkload : ℕ)
    (hwindow : SizeWindowCounting.SizeWindowNounsBoundedBy T.skeleton Λ)
    (htopology :
      ∀ z (hz : z ≠ 0) α lmb,
        topologyWorkload (T.verifier.raw.afterAlphaM z hz α lmb).familyData.base ≤ topologyBound)
    (haxis :
      ∀ z (hz : z ≠ 0),
        templateAxisWorkload (committedTemplate T.verifier z hz) ≤ axisWorkload)
    (n : ℕ) (records : FiniteIO.PreChallengeRecords Nock.Field.K 8)
    (computeEnvK : Fin (2 ^ 31) → Env Nock.Field.K) (computeWalkEnv : Env Nock.Field.K)
    (computeEnvF : Env Nock.Field.Fp)
    (memoryEnvK : Fin (2 ^ 31) → Env Nock.Field.K)
    (memoryFamilies : Fin (2 ^ 31) → Fin 7 → Fin 3 → Nock.Field.Fp)
    (hp8 : workload T Λ topologyBound axisWorkload ≤ 2 ^ 60)
    (hn : n ≤ 2 ^ 31)
    (hreq : records.requests.length = n) (hresp : records.responses.length = n) :
    ((ProductionFailureEventK T C lmb records computeEnvK computeWalkEnv computeEnvF
        memoryEnvK memoryFamilies).card : ℚ) /
        Fintype.card (ProductionChallengeTupleK Nock.Field.K) < 1 / (2 : ℚ) ^ 125 := by
  refine lt_of_le_of_lt
    (productionFailureProbabilityK_le h2 T C lmb topologyBound axisWorkload hwindow htopology haxis
      records computeEnvK computeWalkEnv computeEnvF memoryEnvK memoryFamilies) ?_
  have hgoal := soundnessK_at_real_io_workload (workload T Λ topologyBound axisWorkload) n hp8 hn
  rw [hreq, hresp]
  exact hgoal

end Goldilocks

end

end ExtensionChallenges
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.liftedValueBadChallenges_card_le
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.liftedRlc_eval_algebraMap
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.liftedValueCollisionExcluded_of_not_bad
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.fullMemoryCollisionEventK_card_le
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.fullFinalComputeCollisionEventK_card_le
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.card_productionChallengeTupleK
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.productionFailureEventK_card_le
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.productionFailureProbabilityK_le
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.probabilityBoundK_eq_old_with_extension_denominator
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.probabilityBoundK_le_old
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.probabilityBoundK_le_legacy
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.soundnessK_at_paper_configuration
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.soundnessK_at_real_io_workload
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.improvement_at_paper_configuration
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.soundnessK_of_counted_event
#print axioms Nock.NockVMROM.Thm54.ExtensionChallenges.soundnessK_of_counted_event_at_real_io_workload
