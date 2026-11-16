/-
  Nock/RedTeam/Batch627Thm54FormREventMirror.lean

  Notes only; not a pass.

  `DeployedStaging.compute_core_classes` etc. classify typed SOURCES (`correctedCoreSource`, a
  hand mirror of `correctedCoreCoord`'s dispatch) through `typedCols` / `typedSlots`.  The deployed
  gates are `correctedFinalTypedCompile b source k`.  Two places where the mirror's extractors are
  NOT the compile's read set:
  * `typedCols (.pow x 0) = typedCols x`, but `powVec b _ 0 = oneVec b` reads NOTHING; `.pow _ 0`
    occurs in core 78–80, aux 0–1, endpoint-2 `walkCount1` and endpoint-4 (`hasPow0_sources`);
  * `typedSlots (.lamPow d) = [9]`, but the compile reads `λ` only when `d < pwScaleExp K` (else
    `.const 0`), a `K`-dependent shape; `lamPow` occurs in core 78–80 only (`lamPow_sources`; the
    λ pins read `λ` through `.challenge 9`, not `lamPow`).
  So `rfl` between the compiled and the mirrored class fails (it does: tried at core 73).  Here:
  * **Lemma A (columns, exact):** with `typedColsC` (`.pow _ 0 ↦ []`), the compiled coordinate-`k`
    gate's `maxRound computeColRound` equals the typed one, for every `t`, `k`, `b` — by induction
    through `mulVec` / `powVec` (all coordinates of a role share a round).
  * **Lemma B (slots, bounds):** `typedSlotsC` (`lamPow ↦ []`) gives a lower bound and
    `typedSlots` an upper bound on the compiled `maxRound computeRawChalRound`, for every `K`.
  The mirror's conclusions stand; its instrument does not (`typedCols` is not
    the compile's read set), which matters for any future gate where `.pow _ 0` or a lone `lamPow`
    carries the only read of a round.
  * Counts: `416 = 15 + 246 + 9 + 18 + 3 + 22 + 97 + 6`, `156 = 6 + 150`; `haltAtomMixed` is
    mixed source 49 (`decide` / `rfl`).

  -- the paper
-/
import Nock.NockVMROM.Thm54.DeployedStaging

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch627

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.Reified

/-! ## Syntactic scans of the deployed typed sources -/

def hasPow0 : CorrectedFinalTypedExpr → Bool
  | .pow x n => n == 0 || hasPow0 x
  | .add x y | .sub x y | .mul x y => hasPow0 x || hasPow0 y
  | .neg x => hasPow0 x
  | _ => false

def hasLamPow : CorrectedFinalTypedExpr → Bool
  | .lamPow _ => true
  | .add x y | .sub x y | .mul x y => hasLamPow x || hasLamPow y
  | .neg x => hasLamPow x
  | .pow x _ => hasLamPow x
  | _ => false

theorem hasPow0_sources :
    ((List.finRange 82).filter fun i => hasPow0 (correctedCoreSource i)).map Fin.val =
        [78, 79, 80] ∧
      ((List.finRange 3).filter fun j => hasPow0 (correctedAuxSource j)).map Fin.val = [0, 1] ∧
      correctedEndpoint2.map hasPow0 = [false, true, false, false, false, false] ∧
      correctedEndpoint4.map hasPow0 = [true] ∧
      formRLamPins.map hasPow0 = [false, false] := by
  decide

theorem lamPow_sources :
    ((List.finRange 82).filter fun i => hasLamPow (correctedCoreSource i)).map Fin.val =
        [78, 79, 80] ∧
      ((List.finRange 3).filter fun j => hasLamPow (correctedAuxSource j)) = [] ∧
      (correctedEndpoint2 ++ correctedEndpoint4).all (fun t => !hasLamPow t) = true ∧
      formRLamPins.map hasLamPow = [false, false] := by
  decide

/-! ## Corrected extractors -/

/-- `typedCols` with `.pow _ 0` reading nothing (what `powVec _ _ 0 = oneVec` does). -/
def typedColsC : CorrectedFinalTypedExpr → List ℕ
  | .baseCur i => [i.val]
  | .baseNext i => [i.val]
  | .extCur i => [13 + 3 * i.val, 14 + 3 * i.val, 15 + 3 * i.val]
  | .extNext i => [13 + 3 * i.val, 14 + 3 * i.val, 15 + 3 * i.val]
  | .certBase i => [202 + i.val]
  | .certExt i => [296 + 3 * i.val, 297 + 3 * i.val, 298 + 3 * i.val]
  | .expCur => [302]
  | .add x y => typedColsC x ++ typedColsC y
  | .sub x y => typedColsC x ++ typedColsC y
  | .mul x y => typedColsC x ++ typedColsC y
  | .neg x => typedColsC x
  | .pow x n => if n = 0 then [] else typedColsC x
  | _ => []

/-- `typedSlots` without the `lamPow` leaf (a lower bound valid at every `K`). -/
def typedSlotsC : CorrectedFinalTypedExpr → List ℕ
  | .challenge i => [i.val]
  | .add x y => typedSlotsC x ++ typedSlotsC y
  | .sub x y => typedSlotsC x ++ typedSlotsC y
  | .mul x y => typedSlotsC x ++ typedSlotsC y
  | .neg x => typedSlotsC x
  | .pow x n => if n = 0 then [] else typedSlotsC x
  | _ => []

/-! ## `maxRound` algebra -/

theorem maxRound_append (r : ℕ → ℕ) (a b : List ℕ) :
    maxRound r (a ++ b) = max (maxRound r a) (maxRound r b) := by
  induction a with
  | nil => simp [maxRound]
  | cons x xs ih =>
      simp only [maxRound, List.foldr_cons, List.cons_append] at ih ⊢
      rw [ih]; omega

theorem le_maxRound_of_mem (r : ℕ → ℕ) {l : List ℕ} {x : ℕ} (h : x ∈ l) : r x ≤ maxRound r l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
      simp only [maxRound, List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

theorem maxRound_le (r : ℕ → ℕ) {l : List ℕ} {m : ℕ} (h : ∀ x ∈ l, r x ≤ m) : maxRound r l ≤ m := by
  induction l with
  | nil => simp [maxRound]
  | cons y ys ih =>
      simp only [maxRound, List.foldr_cons]
      exact max_le (h y (List.mem_cons_self ..)) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- Covering: every element of `l₁` has a same-round partner in `l₂` ⇒ `maxRound l₁ ≤ maxRound l₂`. -/
theorem maxRound_le_of_cover (r₁ r₂ : ℕ → ℕ) {l₁ l₂ : List ℕ}
    (h : ∀ x ∈ l₁, ∃ y ∈ l₂, r₁ x = r₂ y) : maxRound r₁ l₁ ≤ maxRound r₂ l₂ := by
  apply maxRound_le
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h x hx
  rw [hxy]; exact le_maxRound_of_mem r₂ hy

/-! ## Read sets of `CoeffExpr.sumList` / `mulVec` / `powVec` -/

section Compile
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem mem_cols_sumList {ι : Type} (l : List ι) (f : ι → CoeffExpr F) (c : ℕ) :
    c ∈ coeffTraceCols (CoeffExpr.sumList l f) ↔ ∃ i ∈ l, c ∈ coeffTraceCols (f i) := by
  induction l with
  | nil => simp [CoeffExpr.sumList, coeffTraceCols]
  | cons x xs ih =>
      have hs : CoeffExpr.sumList (x :: xs) f = .add (f x) (CoeffExpr.sumList xs f) := rfl
      rw [hs]
      simp only [coeffTraceCols, List.mem_append, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact ⟨x, Or.inl rfl, h⟩
        · exact ⟨i, Or.inr hi, h⟩
      · rintro ⟨i, hi | hi, h⟩
        · subst hi; exact Or.inl h
        · exact Or.inr ⟨i, hi, h⟩

theorem mem_chals_sumList {ι : Type} (l : List ι) (f : ι → CoeffExpr F) (c : ℕ) :
    c ∈ coeffChals (CoeffExpr.sumList l f) ↔ ∃ i ∈ l, c ∈ coeffChals (f i) := by
  induction l with
  | nil => simp [CoeffExpr.sumList, coeffChals]
  | cons x xs ih =>
      have hs : CoeffExpr.sumList (x :: xs) f = .add (f x) (CoeffExpr.sumList xs f) := rfl
      rw [hs]
      simp only [coeffChals, List.mem_append, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact ⟨x, Or.inl rfl, h⟩
        · exact ⟨i, Or.inr hi, h⟩
      · rintro ⟨i, hi | hi, h⟩
        · subst hi; exact Or.inl h
        · exact Or.inr ⟨i, hi, h⟩

theorem mem_cols_mulVec (b : Module.Basis (Fin 3) F K) (u v : Fin 3 → CoeffExpr F) (k : Fin 3)
    (c : ℕ) :
    c ∈ coeffTraceCols (mulVec b u v k) ↔
      (∃ i, c ∈ coeffTraceCols (u i)) ∨ ∃ j, c ∈ coeffTraceCols (v j) := by
  unfold mulVec
  rw [mem_cols_sumList]
  constructor
  · rintro ⟨i, -, hi⟩
    rw [mem_cols_sumList] at hi
    obtain ⟨j, -, hj⟩ := hi
    simp only [coeffTraceCols, List.mem_append, List.not_mem_nil, or_false] at hj
    rcases hj with hj | hj
    · exact Or.inl ⟨i, hj⟩
    · exact Or.inr ⟨j, hj⟩
  · rintro (⟨i, h⟩ | ⟨j, h⟩)
    · refine ⟨i, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
      rw [mem_cols_sumList]
      refine ⟨0, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
      simp only [coeffTraceCols, List.mem_append, List.not_mem_nil, or_false]
      exact Or.inl h
    · refine ⟨0, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
      rw [mem_cols_sumList]
      refine ⟨j, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
      simp only [coeffTraceCols, List.mem_append, List.not_mem_nil, or_false]
      exact Or.inr h

theorem mem_chals_mulVec (b : Module.Basis (Fin 3) F K) (u v : Fin 3 → CoeffExpr F) (k : Fin 3)
    (c : ℕ) :
    c ∈ coeffChals (mulVec b u v k) ↔
      (∃ i, c ∈ coeffChals (u i)) ∨ ∃ j, c ∈ coeffChals (v j) := by
  unfold mulVec
  rw [mem_chals_sumList]
  constructor
  · rintro ⟨i, -, hi⟩
    rw [mem_chals_sumList] at hi
    obtain ⟨j, -, hj⟩ := hi
    simp only [coeffChals, List.mem_append, List.not_mem_nil, or_false] at hj
    rcases hj with hj | hj
    · exact Or.inl ⟨i, hj⟩
    · exact Or.inr ⟨j, hj⟩
  · rintro (⟨i, h⟩ | ⟨j, h⟩)
    · refine ⟨i, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
      rw [mem_chals_sumList]
      refine ⟨0, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
      simp only [coeffChals, List.mem_append, List.not_mem_nil, or_false]
      exact Or.inl h
    · refine ⟨0, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
      rw [mem_chals_sumList]
      refine ⟨j, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩
      simp only [coeffChals, List.mem_append, List.not_mem_nil, or_false]
      exact Or.inr h

theorem cols_powVec_zero (b : Module.Basis (Fin 3) F K) (u : Fin 3 → CoeffExpr F) (k : Fin 3) :
    coeffTraceCols (powVec b u 0 k) = [] := rfl

theorem chals_powVec_zero (b : Module.Basis (Fin 3) F K) (u : Fin 3 → CoeffExpr F) (k : Fin 3) :
    coeffChals (powVec b u 0 k) = [] := rfl

theorem mem_cols_powVec_succ (b : Module.Basis (Fin 3) F K) (u : Fin 3 → CoeffExpr F) (n : ℕ)
    (k : Fin 3) (c : ℕ) :
    c ∈ coeffTraceCols (powVec b u (n + 1) k) ↔ ∃ j, c ∈ coeffTraceCols (u j) := by
  induction n generalizing k with
  | zero =>
      rw [show powVec b u (0 + 1) k = mulVec b (powVec b u 0) u k from rfl, mem_cols_mulVec]
      simp [cols_powVec_zero]
  | succ n ih =>
      simp only [powVec, mem_cols_mulVec] at ih ⊢
      constructor
      · rintro (⟨i, h⟩ | h)
        · exact (ih i).1 h
        · exact h
      · intro h; exact Or.inr h

theorem mem_chals_powVec_succ (b : Module.Basis (Fin 3) F K) (u : Fin 3 → CoeffExpr F) (n : ℕ)
    (k : Fin 3) (c : ℕ) :
    c ∈ coeffChals (powVec b u (n + 1) k) ↔ ∃ j, c ∈ coeffChals (u j) := by
  induction n generalizing k with
  | zero =>
      rw [show powVec b u (0 + 1) k = mulVec b (powVec b u 0) u k from rfl, mem_chals_mulVec]
      simp [chals_powVec_zero]
  | succ n ih =>
      simp only [powVec, mem_chals_mulVec] at ih ⊢
      constructor
      · rintro (⟨i, h⟩ | h)
        · exact (ih i).1 h
        · exact h
      · intro h; exact Or.inr h

/-! ## Rounds are constant on a role / a slot -/

theorem colRound_role (i : ℕ) (hi : i < 63) (k : ℕ) (hk : k < 3) :
    computeColRound (13 + 3 * i + k) = computeRoleRound i := by
  have h1 : ¬ 13 + 3 * i + k < 13 := by omega
  have h2 : 13 + 3 * i + k < 202 := by omega
  have h3 : (13 + 3 * i + k - 13) / 3 = i := by omega
  simp [computeColRound, h1, h2, h3]

theorem colRound_certExt (i : ℕ) (hi : i < 2) (k : ℕ) (hk : k < 3) :
    computeColRound (296 + 3 * i + k) = 2 := by
  have h1 : ¬ 296 + 3 * i + k < 13 := by omega
  have h2 : ¬ 296 + 3 * i + k < 202 := by omega
  have h3 : ¬ 296 + 3 * i + k < 296 := by omega
  have h4 : 296 + 3 * i + k < 302 := by omega
  simp [computeColRound, h1, h2, h3, h4]

theorem rawChal_slot (q : ℕ) (hq : q < 12) (k : ℕ) (hk : k < 3) :
    computeRawChalRound (3 * q + k) = computeSlotRound q := by
  have h1 : 3 * q + k < 36 := by omega
  have h2 : (3 * q + k) / 3 = q := by omega
  simp [computeRawChalRound, h1, h2]

/-! ## Lemma A — columns, exact -/

/-- Every compiled column has a same-round partner in `typedColsC`, and conversely. -/
theorem cols_cover (b : Module.Basis (Fin 3) F K) (t : CorrectedFinalTypedExpr) (k : Fin 3) :
    (∀ c ∈ coeffTraceCols (correctedFinalTypedCompile b t k),
        ∃ c' ∈ typedColsC t, computeColRound c = computeColRound c') ∧
      (∀ c' ∈ typedColsC t,
        ∃ c ∈ coeffTraceCols (correctedFinalTypedCompile b t k),
          computeColRound c = computeColRound c') := by
  induction t generalizing k with
  | baseCur i => simp [correctedFinalTypedCompile, coeffTraceCols, typedColsC]
  | baseNext i => simp [correctedFinalTypedCompile, coeffTraceCols, typedColsC]
  | extCur i =>
      simp only [correctedFinalTypedCompile, coeffTraceCols, typedColsC,
        correctedFinalExtCoordIndex, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
      have hk : (k : ℕ) < 3 := k.isLt
      have hi : (i : ℕ) < 63 := i.isLt
      refine ⟨?_, ?_⟩
      · rintro c rfl
        refine ⟨13 + 3 * (i : ℕ), Or.inl rfl, ?_⟩
        rw [colRound_role _ hi _ hk]
        simpa using (colRound_role (i : ℕ) hi 0 (by omega)).symm
      · intro c' hc'
        refine ⟨_, rfl, ?_⟩
        rw [colRound_role _ hi _ hk]
        rcases hc' with rfl | rfl | rfl
        · simpa using (colRound_role (i : ℕ) hi 0 (by omega)).symm
        · have := colRound_role (i : ℕ) hi 1 (by omega)
          rw [show 14 + 3 * (i : ℕ) = 13 + 3 * (i : ℕ) + 1 by omega, this]
        · have := colRound_role (i : ℕ) hi 2 (by omega)
          rw [show 15 + 3 * (i : ℕ) = 13 + 3 * (i : ℕ) + 2 by omega, this]
  | extNext i =>
      simp only [correctedFinalTypedCompile, coeffTraceCols, typedColsC,
        correctedFinalExtCoordIndex, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
      have hk : (k : ℕ) < 3 := k.isLt
      have hi : (i : ℕ) < 63 := i.isLt
      refine ⟨?_, ?_⟩
      · rintro c rfl
        refine ⟨13 + 3 * (i : ℕ), Or.inl rfl, ?_⟩
        rw [colRound_role _ hi _ hk]
        simpa using (colRound_role (i : ℕ) hi 0 (by omega)).symm
      · intro c' hc'
        refine ⟨_, rfl, ?_⟩
        rw [colRound_role _ hi _ hk]
        rcases hc' with rfl | rfl | rfl
        · simpa using (colRound_role (i : ℕ) hi 0 (by omega)).symm
        · have := colRound_role (i : ℕ) hi 1 (by omega)
          rw [show 14 + 3 * (i : ℕ) = 13 + 3 * (i : ℕ) + 1 by omega, this]
        · have := colRound_role (i : ℕ) hi 2 (by omega)
          rw [show 15 + 3 * (i : ℕ) = 13 + 3 * (i : ℕ) + 2 by omega, this]
  | challenge i => simp [correctedFinalTypedCompile, coeffTraceCols, typedColsC]
  | extensionPublic i => simp [correctedFinalTypedCompile, coeffTraceCols, typedColsC]
  | scalarPublic i => simp [correctedFinalTypedCompile, coeffTraceCols, typedColsC]
  | const c => simp [correctedFinalTypedCompile, coeffTraceCols, typedColsC]
  | expCur => simp [correctedFinalTypedCompile, coeffTraceCols, typedColsC]
  | add x y ihx ihy =>
      simp only [correctedFinalTypedCompile, coeffTraceCols, typedColsC, List.mem_append]
      refine ⟨?_, ?_⟩
      · rintro c (h | h)
        · obtain ⟨c', hc', e⟩ := (ihx k).1 c h; exact ⟨c', Or.inl hc', e⟩
        · obtain ⟨c', hc', e⟩ := (ihy k).1 c h; exact ⟨c', Or.inr hc', e⟩
      · rintro c' (h | h)
        · obtain ⟨c, hc, e⟩ := (ihx k).2 c' h; exact ⟨c, Or.inl hc, e⟩
        · obtain ⟨c, hc, e⟩ := (ihy k).2 c' h; exact ⟨c, Or.inr hc, e⟩
  | sub x y ihx ihy =>
      simp only [correctedFinalTypedCompile, coeffTraceCols, typedColsC, List.mem_append]
      refine ⟨?_, ?_⟩
      · rintro c (h | h)
        · obtain ⟨c', hc', e⟩ := (ihx k).1 c h; exact ⟨c', Or.inl hc', e⟩
        · obtain ⟨c', hc', e⟩ := (ihy k).1 c h; exact ⟨c', Or.inr hc', e⟩
      · rintro c' (h | h)
        · obtain ⟨c, hc, e⟩ := (ihx k).2 c' h; exact ⟨c, Or.inl hc, e⟩
        · obtain ⟨c, hc, e⟩ := (ihy k).2 c' h; exact ⟨c, Or.inr hc, e⟩
  | mul x y ihx ihy =>
      simp only [correctedFinalTypedCompile, typedColsC, List.mem_append, mem_cols_mulVec]
      refine ⟨?_, ?_⟩
      · rintro c (⟨i, h⟩ | ⟨j, h⟩)
        · obtain ⟨c', hc', e⟩ := (ihx i).1 c h; exact ⟨c', Or.inl hc', e⟩
        · obtain ⟨c', hc', e⟩ := (ihy j).1 c h; exact ⟨c', Or.inr hc', e⟩
      · rintro c' (h | h)
        · obtain ⟨c, hc, e⟩ := (ihx k).2 c' h; exact ⟨c, Or.inl ⟨k, hc⟩, e⟩
        · obtain ⟨c, hc, e⟩ := (ihy k).2 c' h; exact ⟨c, Or.inr ⟨k, hc⟩, e⟩
  | neg x ihx =>
      simp only [correctedFinalTypedCompile, coeffTraceCols, typedColsC]
      exact ihx k
  | pow x n ihx =>
      cases n with
      | zero => simp [correctedFinalTypedCompile, cols_powVec_zero, typedColsC]
      | succ n =>
          simp only [correctedFinalTypedCompile, typedColsC, Nat.succ_ne_zero, if_false,
            mem_cols_powVec_succ]
          refine ⟨?_, ?_⟩
          · rintro c ⟨j, h⟩; exact (ihx j).1 c h
          · intro c' h
            obtain ⟨c, hc, e⟩ := (ihx k).2 c' h
            exact ⟨c, ⟨k, hc⟩, e⟩
  | certBase i => simp [correctedFinalTypedCompile, coeffTraceCols, typedColsC]
  | certExt i =>
      simp only [correctedFinalTypedCompile, coeffTraceCols, typedColsC, List.mem_singleton,
        List.mem_cons, List.not_mem_nil, or_false]
      have hk : (k : ℕ) < 3 := k.isLt
      have hi : (i : ℕ) < 2 := i.isLt
      refine ⟨?_, ?_⟩
      · rintro c rfl
        refine ⟨296 + 3 * (i : ℕ), Or.inl rfl, ?_⟩
        rw [colRound_certExt _ hi _ hk]
        simpa using (colRound_certExt (i : ℕ) hi 0 (by omega)).symm
      · intro c' hc'
        refine ⟨_, rfl, ?_⟩
        rw [colRound_certExt _ hi _ hk]
        rcases hc' with rfl | rfl | rfl
        · simpa using (colRound_certExt (i : ℕ) hi 0 (by omega)).symm
        · have := colRound_certExt (i : ℕ) hi 1 (by omega)
          rw [show 297 + 3 * (i : ℕ) = 296 + 3 * (i : ℕ) + 1 by omega, this]
        · have := colRound_certExt (i : ℕ) hi 2 (by omega)
          rw [show 298 + 3 * (i : ℕ) = 296 + 3 * (i : ℕ) + 2 by omega, this]
  | lamPow d =>
      simp only [correctedFinalTypedCompile, typedColsC]
      split_ifs with h
      · cases hn : MemoryTable.pwScaleExp K - (d : ℕ) with
        | zero => simp [cols_powVec_zero]
        | succ n => simp [mem_cols_powVec_succ, coeffTraceCols]
      · simp [coeffTraceCols]

theorem maxRound_cols_eq (b : Module.Basis (Fin 3) F K) (t : CorrectedFinalTypedExpr) (k : Fin 3) :
    maxRound computeColRound (coeffTraceCols (correctedFinalTypedCompile b t k)) =
      maxRound computeColRound (typedColsC t) :=
  le_antisymm (maxRound_le_of_cover _ _ (cols_cover b t k).1)
    (maxRound_le_of_cover _ _ fun x hx =>
      let ⟨y, hy, e⟩ := (cols_cover b t k).2 x hx; ⟨y, hy, e.symm⟩)

/-! ## Lemma B — slots, bounds valid at every `K` -/

theorem slots_cover (b : Module.Basis (Fin 3) F K) (t : CorrectedFinalTypedExpr) (k : Fin 3) :
    (∀ c ∈ coeffChals (correctedFinalTypedCompile b t k),
        ∃ q ∈ typedSlots t, computeRawChalRound c = computeSlotRound q) ∧
      (∀ q ∈ typedSlotsC t,
        ∃ c ∈ coeffChals (correctedFinalTypedCompile b t k),
          computeRawChalRound c = computeSlotRound q) := by
  induction t generalizing k with
  | challenge i =>
      simp only [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC,
        List.mem_singleton]
      have hk : (k : ℕ) < 3 := k.isLt
      refine ⟨?_, ?_⟩
      · rintro c rfl; exact ⟨i, rfl, rawChal_slot _ i.isLt _ hk⟩
      · rintro q rfl; exact ⟨_, rfl, rawChal_slot _ i.isLt _ hk⟩
  | expCur => simp [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC]
  | add x y ihx ihy =>
      simp only [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC, List.mem_append]
      refine ⟨?_, ?_⟩
      · rintro c (h | h)
        · obtain ⟨q, hq, e⟩ := (ihx k).1 c h; exact ⟨q, Or.inl hq, e⟩
        · obtain ⟨q, hq, e⟩ := (ihy k).1 c h; exact ⟨q, Or.inr hq, e⟩
      · rintro q (h | h)
        · obtain ⟨c, hc, e⟩ := (ihx k).2 q h; exact ⟨c, Or.inl hc, e⟩
        · obtain ⟨c, hc, e⟩ := (ihy k).2 q h; exact ⟨c, Or.inr hc, e⟩
  | sub x y ihx ihy =>
      simp only [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC, List.mem_append]
      refine ⟨?_, ?_⟩
      · rintro c (h | h)
        · obtain ⟨q, hq, e⟩ := (ihx k).1 c h; exact ⟨q, Or.inl hq, e⟩
        · obtain ⟨q, hq, e⟩ := (ihy k).1 c h; exact ⟨q, Or.inr hq, e⟩
      · rintro q (h | h)
        · obtain ⟨c, hc, e⟩ := (ihx k).2 q h; exact ⟨c, Or.inl hc, e⟩
        · obtain ⟨c, hc, e⟩ := (ihy k).2 q h; exact ⟨c, Or.inr hc, e⟩
  | mul x y ihx ihy =>
      simp only [correctedFinalTypedCompile, typedSlots, typedSlotsC, List.mem_append,
        mem_chals_mulVec]
      refine ⟨?_, ?_⟩
      · rintro c (⟨i, h⟩ | ⟨j, h⟩)
        · obtain ⟨q, hq, e⟩ := (ihx i).1 c h; exact ⟨q, Or.inl hq, e⟩
        · obtain ⟨q, hq, e⟩ := (ihy j).1 c h; exact ⟨q, Or.inr hq, e⟩
      · rintro q (h | h)
        · obtain ⟨c, hc, e⟩ := (ihx k).2 q h; exact ⟨c, Or.inl ⟨k, hc⟩, e⟩
        · obtain ⟨c, hc, e⟩ := (ihy k).2 q h; exact ⟨c, Or.inr ⟨k, hc⟩, e⟩
  | neg x ihx =>
      simp only [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC]
      exact ihx k
  | pow x n ihx =>
      cases n with
      | zero => simp [correctedFinalTypedCompile, chals_powVec_zero, typedSlots, typedSlotsC]
      | succ n =>
          simp only [correctedFinalTypedCompile, typedSlots, typedSlotsC, Nat.succ_ne_zero,
            if_false, mem_chals_powVec_succ]
          refine ⟨?_, ?_⟩
          · rintro c ⟨j, h⟩; exact (ihx j).1 c h
          · intro q h
            obtain ⟨c, hc, e⟩ := (ihx k).2 q h
            exact ⟨c, ⟨k, hc⟩, e⟩
  | lamPow d =>
      simp only [correctedFinalTypedCompile, typedSlots, typedSlotsC, List.not_mem_nil,
        false_imp_iff, implies_true, and_true]
      split_ifs with h
      · cases hn : MemoryTable.pwScaleExp K - (d : ℕ) with
        | zero => simp [chals_powVec_zero]
        | succ n =>
            simp only [mem_chals_powVec_succ, coeffChals, List.mem_singleton, List.mem_cons,
              List.not_mem_nil, or_false]
            rintro c ⟨j, rfl⟩
            exact ⟨9, rfl, rawChal_slot 9 (by omega) _ j.isLt⟩
      · simp [coeffChals]
  | baseCur i => simp [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC]
  | baseNext i => simp [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC]
  | extCur i => simp [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC]
  | extNext i => simp [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC]
  | extensionPublic i => simp [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC]
  | scalarPublic i => simp [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC]
  | const c => simp [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC]
  | certBase i => simp [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC]
  | certExt i => simp [correctedFinalTypedCompile, coeffChals, typedSlots, typedSlotsC]

theorem maxRound_slots_bounds (b : Module.Basis (Fin 3) F K) (t : CorrectedFinalTypedExpr)
    (k : Fin 3) :
    maxRound computeSlotRound (typedSlotsC t) ≤
        maxRound computeRawChalRound (coeffChals (correctedFinalTypedCompile b t k)) ∧
      maxRound computeRawChalRound (coeffChals (correctedFinalTypedCompile b t k)) ≤
        maxRound computeSlotRound (typedSlots t) :=
  ⟨maxRound_le_of_cover _ _ fun x hx =>
      let ⟨y, hy, e⟩ := (slots_cover b t k).2 x hx; ⟨y, hy, e.symm⟩,
    maxRound_le_of_cover _ _ (slots_cover b t k).1⟩

/-- Emptiness, both directions, through the covers. -/
theorem chals_empty_iff (b : Module.Basis (Fin 3) F K) (t : CorrectedFinalTypedExpr) (k : Fin 3)
    (hagree : typedSlotsC t = [] ↔ typedSlots t = []) :
    coeffChals (correctedFinalTypedCompile b t k) = [] ↔ typedSlotsC t = [] := by
  constructor
  · intro h
    rcases hC : typedSlotsC t with _ | ⟨q, qs⟩
    · rfl
    · obtain ⟨c, hc, _⟩ := (slots_cover b t k).2 q (by rw [hC]; exact List.mem_cons_self ..)
      rw [h] at hc; simp at hc
  · intro hC
    rcases h : coeffChals (correctedFinalTypedCompile b t k) with _ | ⟨c, cs⟩
    · rfl
    · obtain ⟨q, hq, _⟩ := (slots_cover b t k).1 c (by rw [h]; exact List.mem_cons_self ..)
      rw [hagree.1 hC] at hq; simp at hq

/-- Corrected typed class. -/
def typedClassC (t : CorrectedFinalTypedExpr) : ℕ :=
  failClass computeColRound computeSlotRound (typedColsC t) (typedSlotsC t)

/-- **The compiled coordinate gate has the corrected typed class**, whenever the two slot bounds
meet and emptiness agrees (both decided below on every deployed source). -/
theorem compiled_class_eq (b : Module.Basis (Fin 3) F K) (t : CorrectedFinalTypedExpr) (k : Fin 3)
    (hmax : maxRound computeSlotRound (typedSlotsC t) = maxRound computeSlotRound (typedSlots t))
    (hemp : typedSlotsC t = [] ↔ typedSlots t = []) :
    computeCoeffClass (correctedFinalTypedCompile b t k) = typedClassC t := by
  have hs : maxRound computeRawChalRound (coeffChals (correctedFinalTypedCompile b t k)) =
      maxRound computeSlotRound (typedSlotsC t) := by
    have := maxRound_slots_bounds b t k
    omega
  have hc := maxRound_cols_eq b t k
  have he := chals_empty_iff b t k hemp
  simp only [computeCoeffClass, typedClassC, failClass, gateReadsLaterColumn, hs, hc]
  by_cases h0 : coeffChals (correctedFinalTypedCompile b t k) = []
  · simp [h0, he.1 h0]
  · have h1 : ¬ typedSlotsC t = [] := fun h => h0 (he.2 h)
    simp [h0, h1]

end Compile

/-! ## The deployed sources: bounds meet, emptiness agrees, classes recomputed -/

def allTyped : List CorrectedFinalTypedExpr :=
  (List.finRange 82).map correctedCoreSource ++ (List.finRange 3).map correctedAuxSource ++
    correctedEndpoint2 ++ correctedEndpoint4 ++ formRLamPins

theorem allTyped_length : allTyped.length = 94 := by decide

theorem slot_bounds_meet :
    allTyped.all (fun t =>
      decide (maxRound computeSlotRound (typedSlotsC t) = maxRound computeSlotRound (typedSlots t)) &&
      decide ((typedSlotsC t = []) ↔ (typedSlots t = []))) = true := by
  decide


theorem lane_core_unchanged :
    ∀ i : Fin 82, computeTypedClass (correctedCoreSource i) = typedClassC (correctedCoreSource i) := by
  decide
theorem lane_aux_unchanged :
    ∀ j : Fin 3, computeTypedClass (correctedAuxSource j) = typedClassC (correctedAuxSource j) := by
  decide
theorem lane_rest_unchanged :
    correctedEndpoint2.map computeTypedClass = correctedEndpoint2.map typedClassC ∧
      correctedEndpoint4.map computeTypedClass = correctedEndpoint4.map typedClassC ∧
      formRLamPins.map computeTypedClass = formRLamPins.map typedClassC := by
  decide

/-- One coordinate column of a role has the same `maxRound` as the role's three columns. -/
theorem role_cols_max (r : ℕ) (hr : r < 63) (k : ℕ) (hk : k < 3) :
    maxRound computeColRound [13 + 3 * r + k] =
      maxRound computeColRound [13 + 3 * r, 14 + 3 * r, 15 + 3 * r] := by
  simp only [maxRound, List.foldr_cons, List.foldr_nil, Nat.max_zero]
  have e0 := colRound_role r hr k hk
  have e1 := colRound_role r hr 0 (by omega)
  have e2 := colRound_role r hr 1 (by omega)
  have e3 := colRound_role r hr 2 (by omega)
  simp only [Nat.add_zero] at e1
  rw [e0, e1, show 14 + 3 * r = 13 + 3 * r + 1 by omega, show 15 + 3 * r = 13 + 3 * r + 2 by omega,
    e2, e3]
  omega

section Dispatch
variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem isLastVar_cols : coeffTraceCols (OptimizedComputeBaseGates.isLastVar (F := F)) = [12] := rfl
theorem isLastVar_chals : coeffChals (OptimizedComputeBaseGates.isLastVar (F := F)) = [] := rfl

/-- The `notLast ·` dispatch branches: the deployed gate is `.mul notLastCoeff Y` with `Y` the
compile (or the residual-witness column), the mirror is `notLastTyped X`. -/
theorem class_mul_notLast (Y : CoeffExpr F) (X : CorrectedFinalTypedExpr)
    (hc : maxRound computeColRound (coeffTraceCols Y) = maxRound computeColRound (typedColsC X))
    (hs : maxRound computeRawChalRound (coeffChals Y) = maxRound computeSlotRound (typedSlotsC X))
    (he : coeffChals Y = [] ↔ typedSlotsC X = []) :
    computeCoeffClass (.mul OptimizedComputeFinal.notLastCoeff Y) = typedClassC (notLastTyped X) := by
  have hcols : coeffTraceCols (CoeffExpr.mul (OptimizedComputeFinal.notLastCoeff (F := F)) Y) =
      [12] ++ coeffTraceCols Y := by
    simp [coeffTraceCols, OptimizedComputeFinal.notLastCoeff, isLastVar_cols]
  have hchals : coeffChals (CoeffExpr.mul (OptimizedComputeFinal.notLastCoeff (F := F)) Y) =
      coeffChals Y := by
    simp [coeffChals, OptimizedComputeFinal.notLastCoeff, isLastVar_chals]
  have htc : typedColsC (notLastTyped X) = [12] ++ typedColsC X := by
    simp [notLastTyped, typedColsC]
  have hts : typedSlotsC (notLastTyped X) = typedSlotsC X := by
    simp [notLastTyped, typedSlotsC]
  simp only [computeCoeffClass, typedClassC, failClass, gateReadsLaterColumn, hcols, hchals, htc,
    hts, maxRound_append, hc, hs]
  by_cases h0 : coeffChals Y = []
  · simp [h0, he.1 h0]
  · have h1 : ¬ typedSlotsC X = [] := fun h => h0 (he.2 h)
    simp [h0, h1]

theorem meet_of_mem (t : CorrectedFinalTypedExpr) (ht : t ∈ allTyped) :
    maxRound computeSlotRound (typedSlotsC t) = maxRound computeSlotRound (typedSlots t) ∧
      (typedSlotsC t = [] ↔ typedSlots t = []) := by
  have h := List.all_eq_true.mp slot_bounds_meet _ ht
  simpa using h

/-- Slot facts for the compile of `X`, from the covers and the decided agreement. -/
theorem compile_slot_facts (b : Module.Basis (Fin 3) F K) (X : CorrectedFinalTypedExpr) (k : Fin 3)
    (hmeet : maxRound computeSlotRound (typedSlotsC X) = maxRound computeSlotRound (typedSlots X) ∧
      (typedSlotsC X = [] ↔ typedSlots X = [])) :
    maxRound computeRawChalRound (coeffChals (correctedFinalTypedCompile b X k)) =
        maxRound computeSlotRound (typedSlotsC X) ∧
      (coeffChals (correctedFinalTypedCompile b X k) = [] ↔ typedSlotsC X = []) := by
  refine ⟨?_, chals_empty_iff b X k hmeet.2⟩
  have := maxRound_slots_bounds b X k
  omega

theorem notLastTyped_meet (X : CorrectedFinalTypedExpr)
    (h : maxRound computeSlotRound (typedSlotsC (notLastTyped X)) =
          maxRound computeSlotRound (typedSlots (notLastTyped X)) ∧
        (typedSlotsC (notLastTyped X) = [] ↔ typedSlots (notLastTyped X) = [])) :
    maxRound computeSlotRound (typedSlotsC X) = maxRound computeSlotRound (typedSlots X) ∧
      (typedSlotsC X = [] ↔ typedSlots X = []) := by
  simpa [notLastTyped, typedSlotsC, typedSlots] using h


theorem deployed_core_class (b : Module.Basis (Fin 3) F K) (i : Fin 82) (k : Fin 3) :
    computeCoeffClass (correctedCoreCoord b i k) =
      computeTypedClass (correctedCoreSource i) := by
  have hi : correctedCoreSource i ∈ allTyped := by simp [allTyped]
  have hmeet := meet_of_mem _ hi
  rw [lane_core_unchanged i]
  by_cases h1 : i = packedWalkCountId
  · subst h1
    simp only [correctedCoreCoord, correctedCoreSource, if_true] at hmeet ⊢
    apply class_mul_notLast
    · have hc : coeffTraceCols (OptimizedComputeFinal.residualWitnessCoord (F := F) 0 k) =
          [13 + 3 * 58 + (k : ℕ)] := by
        simp [OptimizedComputeFinal.residualWitnessCoord, OptimizedComputeFinal.finalExtCoordIndex,
          OptimizedComputeFinal.residualWitnessRole, coeffTraceCols]
      rw [hc]
      simpa [typedColsC] using role_cols_max 58 (by omega) (k : ℕ) k.isLt
    · rfl
    · simp [OptimizedComputeFinal.residualWitnessCoord, coeffChals, typedSlotsC]
  by_cases h2 : i = packedWalkAccId
  · subst h2
    simp only [correctedCoreCoord, correctedCoreSource, if_true, h1, if_false] at hmeet ⊢
    apply class_mul_notLast
    · have hc : coeffTraceCols (OptimizedComputeFinal.residualWitnessCoord (F := F) 1 k) =
          [13 + 3 * 59 + (k : ℕ)] := by
        simp [OptimizedComputeFinal.residualWitnessCoord, OptimizedComputeFinal.finalExtCoordIndex,
          OptimizedComputeFinal.residualWitnessRole, coeffTraceCols]
      rw [hc]
      simpa [typedColsC] using role_cols_max 59 (by omega) (k : ℕ) k.isLt
    · rfl
    · simp [OptimizedComputeFinal.residualWitnessCoord, coeffChals, typedSlotsC]
  by_cases h3 : i = packedChainId
  · subst h3
    simp only [correctedCoreCoord, correctedCoreSource, h1, h2, if_false, if_true] at hmeet ⊢
    exact compiled_class_eq b _ k hmeet.1 hmeet.2
  by_cases h4 : i = packedLnChainId ∨ i = packedWalkLnId
  · simp only [correctedCoreCoord, correctedCoreSource, h1, h2, h3, h4, if_false, if_true]
      at hmeet ⊢
    have hm := notLastTyped_meet _ hmeet
    have hf := compile_slot_facts b (correctedFinalExtGate i) k hm
    exact class_mul_notLast _ _ (maxRound_cols_eq b _ k) hf.1 hf.2
  · simp only [correctedCoreCoord, correctedCoreSource, h1, h2, h3, h4, if_false] at hmeet ⊢
    exact compiled_class_eq b _ k hmeet.1 hmeet.2

/-- The aux `.sub` dispatch branch. -/
theorem class_sub_role (r : Fin 63) (k : Fin 3) (Y : CoeffExpr F) (X : CorrectedFinalTypedExpr)
    (hc : maxRound computeColRound (coeffTraceCols Y) = maxRound computeColRound (typedColsC X))
    (hs : maxRound computeRawChalRound (coeffChals Y) = maxRound computeSlotRound (typedSlotsC X))
    (he : coeffChals Y = [] ↔ typedSlotsC X = []) :
    computeCoeffClass (.sub (.var .traceCur (13 + 3 * (r : ℕ) + (k : ℕ))) Y) =
      typedClassC (.sub (.extCur r) X) := by
  have hcols : coeffTraceCols (CoeffExpr.sub (.var .traceCur (13 + 3 * (r : ℕ) + (k : ℕ))) Y) =
      [13 + 3 * (r : ℕ) + (k : ℕ)] ++ coeffTraceCols Y := by
    simp [coeffTraceCols]
  have hchals : coeffChals (CoeffExpr.sub (.var .traceCur (13 + 3 * (r : ℕ) + (k : ℕ))) Y) =
      coeffChals Y := by
    simp [coeffChals]
  have htc : typedColsC (.sub (.extCur r) X) =
      [13 + 3 * (r : ℕ), 14 + 3 * (r : ℕ), 15 + 3 * (r : ℕ)] ++ typedColsC X := by
    simp [typedColsC]
  have hts : typedSlotsC (.sub (.extCur r) X) = typedSlotsC X := by
    simp [typedSlotsC]
  have hr := role_cols_max (r : ℕ) r.isLt (k : ℕ) k.isLt
  simp only [computeCoeffClass, typedClassC, failClass, gateReadsLaterColumn, hcols, hchals, htc,
    hts, maxRound_append, hc, hs, hr]
  by_cases h0 : coeffChals Y = []
  · simp [h0, he.1 h0]
  · have h1 : ¬ typedSlotsC X = [] := fun h => h0 (he.2 h)
    simp [h0, h1]

/-- Aux: the same, through `correctedAuxCoord`. -/
theorem deployed_aux_class (b : Module.Basis (Fin 3) F K) (j : Fin 3) (k : Fin 3) :
    computeCoeffClass (correctedAuxCoord b j k) =
      computeTypedClass (correctedAuxSource j) := by
  have hj : correctedAuxSource j ∈ allTyped := by simp [allTyped]
  have hmeet := meet_of_mem _ hj
  rw [lane_aux_unchanged j]
  by_cases h2 : j = 2
  · subst h2
    simp only [correctedAuxCoord, correctedAuxSource, if_true] at hmeet ⊢
    exact compiled_class_eq b _ k hmeet.1 hmeet.2
  · simp only [correctedAuxCoord, correctedAuxSource, h2, if_false] at hmeet ⊢
    have hf := compile_slot_facts b (correctedFinalResidualSource j) k
      (by simpa [typedSlotsC, typedSlots] using hmeet)
    have hc := maxRound_cols_eq b (correctedFinalResidualSource j) k
    have hform : OptimizedComputeFinal.residualWitnessCoord (F := F) j k =
        .var .traceCur (13 + 3 * ((⟨58 + (j : ℕ), by omega⟩ : Fin 63) : ℕ) + (k : ℕ)) := rfl
    rw [hform]
    exact class_sub_role _ k _ _ hc hf.1 hf.2

end Dispatch

/-! ## Counts and `haltAtomMixed` -/

theorem compute_count : 15 + 82 * 3 + 3 * 3 + 6 * 3 + 1 * 3 + 22 + 97 + 2 * 3 = 416 := by decide
theorem compute_lane_tally : 133 + 199 + 42 + 42 = 416 := by decide
theorem memory_count : 6 + 50 * 3 = 156 := by decide
theorem memory_lane_tally : 15 + 105 + 6 + 30 = 156 := by decide

theorem haltAtomMixed_is_source_49 {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Module.Basis (Fin 3) F K) :
    (OptimizedMemoryGateBasis.mixedTransitionGates (F := F) (K := K) b)[49]? =
      some OptimizedMemoryGateBasis.haltAtomMixed := by
  unfold OptimizedMemoryGateBasis.mixedTransitionGates
  have hl := OptimizedMemoryGateBasis.paperKGates_length (F := F) (K := K)
  rw [List.getElem?_append_right (by omega)]
  simp [hl]

end Nock.RedTeam.Batch627
