import Nock.NockVMROM.Thm54.VclL.Compute.AccVCL
import Nock.NockVMROM.Thm54.VclL.Compute.LnReadSet
import Nock.NockVMROM.Thm54.P8Core.SVFrame.MemSoundnessFamily

/-!
# The Q7 compute chip — the `ln` gates deleted, `frameVCL`'s coin map

.

* **The deletion.**  Roles `54`/`55` (`ln_prev`/`ln`)
  become dead columns (like `34..36`); the width does not move.
* **The chip tuple** `(e, w, s, d, k) = (3, 232, 321, 4, 2)` (was `(3, 232, 339, 4, 2)`: `−15`
  core coordinates, `−3` for `finalLnInit`).  Every gate is a gate of `computeChipVCLE`
  (`vclGatesQ7_sub`), so the degree stays `≤ 4`.
* **The coin map** (`chalKQ7`, compute `𝕂` slot `q` ← `frameVCL` coin; limbs `3q..3q+2` are
  `coord b · k`, `chalVQ7`), pre-tower, `z = z₁`:
  `0 ↦ 0` (dead), `1 ↦ χ 2` (`z₁`), `2 ↦ χ 8` (`a`), `3 ↦ χ 9` (`b`), `4 ↦ χ 10` (`c`),
  `5 ↦ (χ 2)⁻¹`, `6 ↦ χ 0` (`αC`), `7 ↦ χ 4` (IO `γ₀`), `8 ↦ χ 5` (IO `ρ₀`), `9 ↦ 0` (`λ`, dead),
  `10 ↦ χ 1` (walk `γ`), `11 ↦ 0`; the IO coin limb bases are `γc = 21`, `ρc = 24`.  The map is a
  function `ℕ → K` with a `0` default, so route (d)'s slots `12..15` extend it without retyping.
  `frameVCL` has no `α` and none is added.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Reified Nock.Framework Nock.Framework.Reify Module
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedComputeFinal Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering hiding finalExtCoordIndex
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp
open Nock.NockVMROM.Thm54.VclL.Compute.LnRead
open scoped Polynomial

set_option maxRecDepth 300000

noncomputable section

/-! ## 1. The gate list -/

section gates
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The kept core at Q7: `correctedCoreVCL` without ids `50, 58, 65, 72, 78`. -/
def correctedCoreVCLQ7 (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  (keptCoreIdsQ7.map fun i => List.ofFn fun k : Fin 3 => correctedCoreCoord309 b i k).flatten

/-- The kept `allGates309` groups at Q7, before the reindex. -/
def keptGatesQ7 (n : ℕ) (b : Basis (Fin 3) F K) : List (CoeffExpr F) :=
  finalBaseTransitionGates n ++ correctedCoreVCLQ7 b ++ correctedAux309 b ++
    compileList309 b endpoint2Q7 ++ compileList309 b endpoint4_309 ++ finalEndpointEqualityChecks

/-- **The gates of the Q7 chip**: `vclGatesE`'s shape with the Q7 kept groups. -/
def vclGatesQ7 (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) : List (CoeffExpr F) :=
  ((keptGatesQ7 n b).map reindexE ++ serialGates) ++ axGates b ++ lookupGatesD b γc ρc ++
    accGates 3 accSlotsX accExportBase rhoExportPub ++ accGates 3 accSlotsP accPathBase rhoPathPub

theorem keptCoreIdsQ7_sub : ∀ i ∈ keptCoreIdsQ7, i ∈ keptCoreIds := fun _ hi =>
  (List.mem_filter.mp hi).1

theorem endpoint2Q7_sub : ∀ t ∈ endpoint2Q7, t ∈ endpoint2_309 := fun _ ht =>
  (List.mem_filter.mp ht).1

theorem correctedCoreVCLQ7_sub (b : Basis (Fin 3) F K) :
    ∀ g ∈ correctedCoreVCLQ7 b, g ∈ correctedCoreVCL b := by
  intro g hg
  simp only [correctedCoreVCLQ7, correctedCoreVCL, List.mem_flatten, List.mem_map] at hg ⊢
  obtain ⟨_, ⟨i, hi, rfl⟩, hg⟩ := hg
  exact ⟨_, ⟨i, keptCoreIdsQ7_sub i hi, rfl⟩, hg⟩

theorem compileList309_sub (b : Basis (Fin 3) F K) {ts ts' : List WTyped}
    (h : ∀ t ∈ ts, t ∈ ts') : ∀ g ∈ compileList309 b ts, g ∈ compileList309 b ts' := by
  intro g hg
  simp only [compileList309, List.mem_flatMap] at hg ⊢
  obtain ⟨t, ht, hg⟩ := hg
  exact ⟨t, h t ht, hg⟩

theorem keptGatesQ7_sub (n : ℕ) (b : Basis (Fin 3) F K) :
    ∀ g ∈ keptGatesQ7 n b, g ∈ keptGates309 n b := by
  intro g hg
  simp only [keptGatesQ7, keptGates309, List.mem_append] at hg ⊢
  rcases hg with ((((hb | hc) | ha) | h2) | h4) | heq
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hb))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (correctedCoreVCLQ7_sub b g hc)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ha)))
  · exact Or.inl (Or.inl (Or.inr (compileList309_sub b endpoint2Q7_sub g h2)))
  · exact Or.inl (Or.inr h4)
  · exact Or.inr heq

/-- **Every Q7 gate is a gate of `computeChipVCLE`** (the deletion only removes gates). -/
theorem vclGatesQ7_sub (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    ∀ g ∈ vclGatesQ7 n b γc ρc, g ∈ vclGatesE n b γc ρc := by
  intro g hg
  simp only [vclGatesQ7, vclGatesE, vclGatesD, vclGatesA, vclGates, List.mem_append,
    List.mem_map] at hg ⊢
  rcases hg with (((((⟨g', hg', rfl⟩ | hs) | hax) | hl) | hx) | hp)
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨g', keptGatesQ7_sub n b g' hg', rfl⟩))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hs))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hax)))
  · exact Or.inl (Or.inl (Or.inr hl))
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hp

theorem correctedCoreVCLQ7_length (b : Basis (Fin 3) F K) :
    (correctedCoreVCLQ7 (F := F) b).length = 225 := by
  simp only [correctedCoreVCLQ7, List.length_flatten, List.map_map]
  simp [Function.comp_def, keptCoreIdsQ7_length]

theorem endpoint2Q7_length : endpoint2Q7.length = 5 := by rw [endpoint2Q7_eq]; rfl

theorem keptGatesQ7_length (n : ℕ) (b : Basis (Fin 3) F K) : (keptGatesQ7 n b).length = 289 := by
  simp only [keptGatesQ7, List.length_append, finalBaseTransitionGates_length,
    correctedCoreVCLQ7_length, correctedAux309_length, compileList309_length,
    finalEndpointEqualityChecks_length, endpoint2Q7_length]
  have h := endpoint_lengths309
  omega

theorem vclGatesQ7_length (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    (vclGatesQ7 n b γc ρc).length = 321 := by
  simp [vclGatesQ7, keptGatesQ7_length, lookupGatesD_length, accGates_length]

theorem vclGatesQ7_degree (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    ∀ g ∈ vclGatesQ7 n b γc ρc, g.degree ≤ 4 := fun g hg =>
  vclGatesE_degree n b γc ρc g (vclGatesQ7_sub n b γc ρc g hg)

end gates

/-! ## 2. The RAP and the chip -/

def vclRAPQ7 {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) : RAP F :=
  { e := 3
    k := 2
    wRAP := ![vclRound0, 24]
    w := vclWidthE
    w_eq := by simp [Fin.sum_univ_two, vclRound0, vclWidthE]
    h := h
    d := 4
    s := (vclGatesQ7 n b γc ρc).length
    ω := orbit.ω
    β := orbit.βcoset
    I := Finset.univ ×ˢ ({0, 1} : Finset ℕ)
    C := fun i => coeffToMv chalV pubVal ((vclGatesQ7 n b γc ρc).get i)
    C_vars := fun _i => coeffToMv_vars chalV pubVal _
    C_deg := fun _i => (coeffToMv_totalDegree_le chalV pubVal _).trans
      (vclGatesQ7_degree n b γc ρc _ (List.get_mem _ _))
    H := H
    β_ne_zero := orbit.βcoset_ne_zero
    I_bound := by
      intro q hq
      have hq2 : q.2 = 0 ∨ q.2 = 1 := by
        have h2 := (Finset.mem_product.mp hq).2
        simpa [Finset.mem_insert, Finset.mem_singleton] using h2
      have hge : 2 ≤ 2 ^ h := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) orbit.h_pos
      rcases hq2 with hq' | hq' <;> rw [hq'] <;> omega }

/-- **`computeChipVCLQ7`**: `computeChipVCLE` with the Q7 deletion. -/
def computeChipVCLQ7
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) : FixedPreprocessingRAP F where
  rap := vclRAPQ7 (n := n) b γc ρc chalV pubVal orbit (rowNodeSet nodes)
  rounds_pos := by norm_num [vclRAPQ7]
  fixedCount := 2
  preprocessingIndex :=
    { toFun := fun j => ⟨11 + (j : ℕ), by
          have := j.isLt
          change 11 + (j : ℕ) < vclRound0
          simp only [vclRound0]
          omega⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  preprocessing
    | 0 => firstRowMask nodes
    | 1 => lastRowMask hn nodes

theorem computeChipVCLQ7_sat_iff
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin (computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit).rap.w → F[X]) :
    RAP.SatisfiesWithPreprocessing (computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit) P ↔
      (computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit).BindsPreprocessing P ∧
        ∀ x ∈ rowNodeSet nodes, ∀ g ∈ vclGatesQ7 n b γc ρc,
          g.eval (Reify.envOfTrace P orbit.ω x chalV pubVal) = 0 := by
  have key : ∀ (i : Fin (computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit).rap.s) (x : F),
      ((computeChipVCLQ7 hn nodes b γc ρc chalV pubVal orbit).rap.compose P i).eval x =
        ((vclGatesQ7 n b γc ρc).get i).eval (Reify.envOfTrace P orbit.ω x chalV pubVal) := by
    intro i x
    rw [Reify.compose_eval]
    exact eval_coeffToMv P orbit.ω x chalV pubVal _
  constructor
  · rintro ⟨hraw, hfixed⟩
    refine ⟨hfixed, fun x hx g hg => ?_⟩
    obtain ⟨i, hget⟩ := List.mem_iff_get.mp hg
    have hz := hraw i x hx
    rw [key i x] at hz
    rwa [← hget]
  · rintro ⟨hfixed, hall⟩
    refine ⟨?_, hfixed⟩
    intro i x hx
    rw [key i x]
    exact hall x hx _ (List.get_mem _ _)

/-- **The Q7 chip tuple** `(3, 232, 321, 4, 2)` (was `(3, 232, 339, 4, 2)` at `computeChipVCLE`). -/
theorem vclRAPQ7_fingerprint
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (b : Basis (Fin 3) F K) (γc ρc : ℕ) (chalV pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    let R := vclRAPQ7 (n := n) b γc ρc chalV pubVal orbit H
    R.w = 232 ∧ R.s = 321 ∧ R.d = 4 ∧ R.k = 2 ∧ R.e = 3 ∧ R.wRAP = ![208, 24] :=
  ⟨rfl, vclGatesQ7_length n b γc ρc, rfl, rfl, rfl, rfl⟩

/-- The deletion removes exactly `18` gates of `computeChipVCLE`. -/
theorem vclGatesQ7_deleted_count {F K : Type} [Field F] [Field K] [Algebra F K]
    (n : ℕ) (b : Basis (Fin 3) F K) (γc ρc : ℕ) :
    (vclGatesE n b γc ρc).length = (vclGatesQ7 n b γc ρc).length + 18 := by
  rw [vclGatesE_length, vclGatesQ7_length]

/-! ## 3. `frameVCL`'s coin map -/

section coins
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- Slots `0` (`α`) and `9` (`λ`) are dead (`0`); the default `0` leaves room for route (d)'s
slots `12..15`. -/
def chalKQ7 (χ : Coins frameVCL K) : ℕ → K
  | 1 => χ ⟨2, by decide⟩
  | 2 => χ ⟨8, by decide⟩
  | 3 => χ ⟨9, by decide⟩
  | 4 => χ ⟨10, by decide⟩
  | 5 => (χ ⟨2, by decide⟩)⁻¹
  | 6 => χ ⟨0, by decide⟩
  | 7 => χ ⟨4, by decide⟩
  | 8 => χ ⟨5, by decide⟩
  | 10 => χ ⟨1, by decide⟩
  | _ => 0

/-- **`chalVQ7`**: the raw `𝔽` challenge vector — limbs `3q..3q+2` of slot `q < 12` are
`coord b (chalKQ7 χ q) ·`, everything at or above `36` is `0` (as `computeChalValOfTuple`). -/
def chalVQ7 (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) : ℕ → F :=
  fun j => if j < 36 then coord b (chalKQ7 χ (j / 3)) ⟨j % 3, Nat.mod_lt j (by decide)⟩ else 0

theorem chalKQ7_zero (χ : Coins frameVCL K) : chalKQ7 χ 0 = 0 := rfl
theorem chalKQ7_nine (χ : Coins frameVCL K) : chalKQ7 χ 9 = 0 := rfl
theorem chalKQ7_eleven (χ : Coins frameVCL K) : chalKQ7 χ 11 = 0 := rfl
theorem chalKQ7_z (χ : Coins frameVCL K) : chalKQ7 χ 1 = χ ⟨2, by decide⟩ := rfl
theorem chalKQ7_zinv (χ : Coins frameVCL K) : chalKQ7 χ 5 = (chalKQ7 χ 1)⁻¹ := rfl
theorem chalKQ7_ioγ (χ : Coins frameVCL K) : chalKQ7 χ 7 = χ ioγVCL.1 := rfl
theorem chalKQ7_ioρ (χ : Coins frameVCL K) : chalKQ7 χ 8 = χ ioρVCL.1 := rfl
theorem chalKQ7_walkγ (χ : Coins frameVCL K) : chalKQ7 χ 10 = χ ⟨1, by decide⟩ := rfl
theorem chalKQ7_αC (χ : Coins frameVCL K) : chalKQ7 χ 6 = χ ⟨0, by decide⟩ := rfl

/-- The IO coin limb bases: `γc = 21` is slot `7`, `ρc = 24` is slot `8`. -/
theorem chalVQ7_io (b : Basis (Fin 3) F K) (χ : Coins frameVCL K) (k : Fin 3) :
    chalVQ7 b χ (21 + k) = coord b (χ ioγVCL.1) k ∧ chalVQ7 b χ (24 + k) = coord b (χ ioρVCL.1) k := by
  fin_cases k <;> exact ⟨rfl, rfl⟩

/-- The dead slots read `0` in every limb. -/
theorem chalVQ7_dead [FiniteDimensional F K] (b : Basis (Fin 3) F K) (χ : Coins frameVCL K)
    (k : Fin 3) : chalVQ7 b χ k = 0 ∧ chalVQ7 b χ (27 + k) = 0 := by
  fin_cases k <;> simp [chalVQ7, chalKQ7, coord]

end coins

/-- **The Q7 chip at `frameVCL` coins**: `γc = 21`, `ρc = 24`, challenge limbs `chalVQ7 b χ`. -/
def computeChipQ7
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (χ : Coins frameVCL K) (pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) :
    FixedPreprocessingRAP F :=
  computeChipVCLQ7 hn nodes b 21 24 (chalVQ7 b χ) pubVal orbit

end

end VclL.Compute
end Nock.NockVMROM.Thm54
