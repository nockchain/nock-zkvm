/-
  Nock/NockVMROM/Thm54/VclL/Chips/ChipV.lean

  `MemSoundnessFamily.serves` / `response_sound` receive no `VerifierData.Checks`, so the chip of
  table `t` enforces the public conditions the chip ⇒ row-model bridge reads and is UNSATISFIABLE
  otherwise (one extra base gate `const 1` when they fail, `okGates`):
  * `GoodM V t` — memory row adjacency on table `t`'s orbit (`V.AdjacentM t`, R-LC8's `hadjM`
    shape), injective row nodes (`memNodes_injective`), `PrimeFieldElems F` (`Checks.hF`'s field),
    **`2^63 < ringChar F` — a chip-enforced public condition (true at Goldilocks,
    `p = 2^64 − 2^32 + 1`)**, and `memRows t + 1 < ringChar F` (the serial / chain-length window;
    implied by `Checks.hcons` on honest data);
  * `cellChipOk ok` / `pathChipOk ok` — `cellChip` / `pathChip` with the `ok` gate; an accepted
    trace has `ok = true` and satisfies the plain chip (`cellChipOk_sat`, `pathChipOk_sat`), so the
    whole bridge (`RowModel`, `PathModel`) applies with no premise on `V`;
  * `okOf V t` (the decided `GoodM V t`), `goodM_of_ok`.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.PathModel
import Nock.NockVMROM.Thm54.P8Core.SVFrame.MemSoundnessFamily

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.SVFrame
open Module
open scoped Polynomial

noncomputable section

variable {F : Type} [Field F]

/-- The rejecting gate (`1 = 0`) when the checks fail. -/
def okGates (ok : Bool) : List (CoeffExpr F) := if ok then [] else [.const 1]

theorem okGates_deg (ok : Bool) : ∀ g ∈ (okGates ok : List (CoeffExpr F)), g.degree ≤ 4 := by
  intro g hg; cases ok <;> simp [okGates] at hg; subst hg; simp [CoeffExpr.degree]

/-- The cell template with the `ok` gate. -/
def cellTemplateOk (δF : F) (ok : Bool) : ChipTemplate F :=
  { cellTemplate δF with
    baseTransition := Cell.baseGates ++ okGates ok
    baseTransition_deg := by
      intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact cellBase_deg g h
      · exact okGates_deg ok g h }

def pathTemplateOk (δF : F) (ok : Bool) : ChipTemplate F :=
  { pathTemplate δF with
    baseTransition := Path.baseGates ++ okGates ok
    baseTransition_deg := by
      intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact pathBase_deg g h
      · exact okGates_deg ok g h }

section Chips
-- The gate lists are opaque to the unifier here: comparing `cellTemplateOk` with `cellTemplate`
-- field-by-field must not normalise the gate lists (whnf timeout); the widths agree by projection.
attribute [local irreducible] Cell.baseGates Path.baseGates Cell.mixedGates Path.mixedGates

variable {K : Type} [Field K] [Algebra F K] [FiniteDimensional F K]
  (δF : F) (b : Basis (Fin 3) F K) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
  (orbit : StrictOrbitDomain F 3 h) (chals pubs : ℕ → K) (ok : Bool)

/-- **The cell chip with the `ok` gate.** -/
def cellChipOk : FixedPreprocessingRAP F where
  rap := expandChip (cellTemplateOk δF ok) b (slotVal b 129 chals) (slotVal b 129 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 129 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

def pathChipOk : FixedPreprocessingRAP F where
  rap := expandChip (pathTemplateOk δF ok) b (slotVal b 16 chals) (slotVal b 16 pubs) orbit
    (rowNodeSet nodes)
  rounds_pos := by show 0 < 3; omega
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨j, by
        have := j.isLt
        show (j : ℕ) < 16 + 0 * 3
        omega⟩
      inj' := by intro i j hij; exact Fin.ext (by simpa using congrArg Fin.val hij) }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

theorem cellChipOk_w : (cellChipOk δF b hn nodes orbit chals pubs ok).rap.w = 225 :=
  (cellChip_fingerprint δF b hn nodes orbit chals pubs).1

theorem pathChipOk_w : (pathChipOk δF b hn nodes orbit chals pubs ok).rap.w = 112 :=
  (pathChip_fingerprint δF b hn nodes orbit chals pubs).1

/-- **An accepted `ok`-gated cell trace has `ok = true` and satisfies the plain cell chip.** -/
theorem cellChipOk_sat (Q : Fin (cellChipOk δF b hn nodes orbit chals pubs ok).rap.w → F[X])
    (hQ : RAP.SatisfiesWithPreprocessing (cellChipOk δF b hn nodes orbit chals pubs ok) Q) :
    ok = true ∧ RAP.SatisfiesWithPreprocessing (cellChip δF b hn nodes orbit chals pubs) Q := by
  have hl := (expandChip_satisfies_iff_language (cellTemplateOk δF ok) b _ _ orbit (rowNodeSet nodes)
    Q).mp hQ.1
  refine ⟨?_, ?_, hQ.2⟩
  · cases ok
    · have := (hl _ (mem_rowNodeSet nodes ⟨0, hn⟩)).1 (.const 1)
        (show (CoeffExpr.const 1 : CoeffExpr F) ∈ Cell.baseGates ++ okGates false from
          List.mem_append_right _ (by simp [okGates]))
      simp [CoeffExpr.eval] at this
    · rfl
  · refine (expandChip_satisfies_iff_language (cellTemplate δF) b _ _ orbit (rowNodeSet nodes) Q).mpr
      fun x hx => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hl x hx
    exact ⟨fun g hg => h1 g (List.mem_append_left _ hg), h2, h3, h4⟩

theorem pathChipOk_sat (Q : Fin (pathChipOk δF b hn nodes orbit chals pubs ok).rap.w → F[X])
    (hQ : RAP.SatisfiesWithPreprocessing (pathChipOk δF b hn nodes orbit chals pubs ok) Q) :
    ok = true ∧ RAP.SatisfiesWithPreprocessing (pathChip δF b hn nodes orbit chals pubs) Q := by
  have hl := (expandChip_satisfies_iff_language (pathTemplateOk δF ok) b _ _ orbit (rowNodeSet nodes)
    Q).mp hQ.1
  refine ⟨?_, ?_, hQ.2⟩
  · cases ok
    · have := (hl _ (mem_rowNodeSet nodes ⟨0, hn⟩)).1 (.const 1)
        (show (CoeffExpr.const 1 : CoeffExpr F) ∈ Path.baseGates ++ okGates false from
          List.mem_append_right _ (by simp [okGates]))
      simp [CoeffExpr.eval] at this
    · rfl
  · refine (expandChip_satisfies_iff_language (pathTemplate δF) b _ _ orbit (rowNodeSet nodes) Q).mpr
      fun x hx => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hl x hx
    exact ⟨fun g hg => h1 g (List.mem_append_left _ hg), h2, h3, h4⟩

end Chips

/-! ## The checks of a verifier datum -/

section Datum
variable {K : Type} [Field K] [Algebra F K] {hC : ℕ} {S : MemShape}

/-- **The public conditions table `t`'s chip enforces.**  `2^63 < ringChar F` is a chip-enforced
public condition (true at Goldilocks). -/
def GoodM (V : VerifierData F K hC S) (t : Fin S.k) : Prop :=
  V.AdjacentM t ∧ Function.Injective (V.memNodes t) ∧ GeneratedField.PrimeFieldElems F ∧
    2 ^ 63 < ringChar F ∧ V.memRows t + 1 < ringChar F

def okOf (V : VerifierData F K hC S) (t : Fin S.k) : Bool :=
  @decide (GoodM V t) (Classical.propDecidable _)

theorem goodM_of_ok {V : VerifierData F K hC S} {t : Fin S.k} (h : okOf V t = true) : GoodM V t :=
  @of_decide_eq_true _ (Classical.propDecidable _) h

theorem ok_of_goodM {V : VerifierData F K hC S} {t : Fin S.k} (h : GoodM V t) : okOf V t = true :=
  @decide_eq_true _ (Classical.propDecidable _) h

/-- Adjacency in the bridge's orientation. -/
theorem GoodM.adj {V : VerifierData F K hC S} {t : Fin S.k} (h : GoodM V t) :
    ∀ (i : Fin (V.memRows t)) (hi : (i : ℕ) + 1 < V.memRows t),
      V.memNodes t ⟨(i : ℕ) + 1, hi⟩ = V.memNodes t i * (V.orbitM t).ω := h.1

end Datum

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
