/-
  Nock/NockVMROM/Thm54/BelowDefs/P8Core/Batch471Thm54ComputeTopologyPrefix.lean

  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/P8Core/Batch471Thm54ComputeTopologyPrefix.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackageDefs` or the statement file, directly or transitively.
-/
import Nock.NockVMROM.Thm54.ComputeWalkLabel

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch471

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.Framework
open MonolithicRAP

section ClabC

variable {K : Type} [Field K]

/-- The parent's `Pub` with `(s, f, e)` replaced by slot `j`'s `sfTriple` — what `clabC`
builds (state and everything else kept from the parent). -/
def childOfSlot (pub : Pub K) (j : Fin 3) : Pub K :=
  { pub with s := (sfTriple pub j).1, f := (sfTriple pub j).2.1, e := (sfTriple pub j).2.2 }

/-- Drop coordinate `0` (the state tag) of a `LT_comp` label vector. -/
def sfeProj (v : Fin 10 → K) : Fin 9 → K := fun k => v k.succ

/-- The child-link projection `childLinkComp` reads. -/
def sfeOf (l : State × DTcomp K) : FP K × FP K × FP K := (l.2.2.1.s, l.2.2.1.f, l.2.2.1.e)

/-- The projected encoder: coordinates `1..9` of `labelVecOfPub`. -/
def encSFE (l : State × DTcomp K) : Fin 9 → K := sfeProj (labelVecOfPub l.2.2.1)

/-- **Route-around, 1:** after projecting away the tag, the `clabC`-shaped label IS the declared
child vector, for ANY hosted tags. -/
theorem encSFE_clab (pub : Pub K) (tags : Fin 3 → K) (j : Fin 3) :
    sfeProj (labelVecOfPub (childOfSlot pub j)) = sfeProj (childVec pub tags j) := by
  funext k
  fin_cases k <;> rfl

/-- **Route-around, 2:** the projected encoder determines the child-link projection. -/
theorem encSFE_label (a b : State × DTcomp K) (h : encSFE a = encSFE b) : sfeOf a = sfeOf b := by
  have hc : ∀ k : Fin 9, encSFE a k = encSFE b k := fun k => congrFun h k
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2; have h3 := hc 3; have h4 := hc 4
  have h5 := hc 5; have h6 := hc 6; have h7 := hc 7; have h8 := hc 8
  simp only [encSFE, sfeProj, labelVecOfPub] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp only [sfeOf, Prod.mk.injEq]
  refine ⟨FP.ext ?_ ?_ ?_, FP.ext ?_ ?_ ?_, FP.ext ?_ ?_ ?_⟩ <;> assumption

/-- **Route-around, 3:** `Fcomp` reads children only through `sfeOf` (and `none`/`some`). -/
theorem respects_sfe : RespectsChildLabels (Fcomp (K := K)) sfeOf := by
  intro lbl xout xout' hx hF
  obtain ⟨hst, hV, hslot, hlink⟩ := hF
  refine ⟨hst, hV, ?_, ?_⟩
  · intro i
    rw [hslot i]
    have := hx i
    constructor
    · intro hne hnone; rw [hnone] at this; cases h : xout i
      · exact hne h
      · rw [h] at this; simp at this
    · intro hne hnone; rw [hnone] at this; cases h : xout' i
      · exact hne h
      · rw [h] at this; simp at this
  · intro i hi
    show Option.map sfeOf (xout' i) = _
    rw [← hx i]
    exact hlink i hi

end ClabC

section VecMap

variable {K : Type*} [Field K] {n m : ℕ}

theorem vecBFT_map (π : (Fin n → K) → (Fin m → K)) {V : ℕ → Fin n → K}
    {Cv : ℕ → ℕ → Fin n → K} {fo : ℕ → ℕ} {h : ℕ} (hb : VecBFT V Cv fo h) :
    VecBFT (fun i => π (V i)) (fun i l => π (Cv i l)) fo h := by
  unfold VecBFT at hb ⊢
  have := congrArg (List.map π) hb
  simpa [curValsV, flatBlksV, blkValsV, List.map_flatMap, List.map_map, Function.comp_def] using this

theorem vecBFT_congr_children {V : ℕ → Fin n → K} {Cv Cv' : ℕ → ℕ → Fin n → K} {fo : ℕ → ℕ}
    {h : ℕ} (hC : ∀ i l, l < fo i → Cv i (l + 1) = Cv' i (l + 1)) (hb : VecBFT V Cv fo h) :
    VecBFT V Cv' fo h := by
  unfold VecBFT at hb ⊢
  rw [hb]
  congr 1
  unfold flatBlksV
  apply List.flatMap_congr
  intro i _
  unfold blkValsV
  apply List.map_congr_left
  intro l hl
  exact hC (i + 1) l (List.mem_range.mp hl)

end VecMap

section Generic

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The `clabC`-shaped child label of slot `l` (1-indexed) of row `i`. -/
def clabOf (lbl : ℕ → State × DTcomp K) (i l : ℕ) : State × DTcomp K :=
  ((lbl i).1, ((lbl i).2.1, childOfSlot (lbl i).2.2.1 ⟨(l - 1) % 3, Nat.mod_lt _ (by norm_num)⟩,
    (lbl i).2.2.2))

end Generic

end Nock.RedTeam.Batch471
