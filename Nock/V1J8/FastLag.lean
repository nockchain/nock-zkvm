/-
  Nock/V1J8/FastLag.lean

  **The last-row extrapolation, once per chip.**  `TabX.env` / `TabM.env` recompute the Lagrange
  weights `lagW nodes (ω · x_{n-1}) k` (n inversions each) for every gate that mentions a next-column at the last
  row: O(n^2 log n) per access.  Here the weights are computed once per table (`ellArr`, one inversion per node,
  product form), the per-column extrapolation once (`nextArr`), and the row environment reads the cache (`envF`).
  `checkCompXF = checkCompX` and `checkMF = checkM` are kernel-checked; the `@[csimp]` installation is in `FastEval`
  (which goes further: `Gold` registers); here only the equalities `checkCompX_eq_F`, `checkM_eq_F`.  No proved definition changes.
-/
import Nock.V1J8.MemJAW

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J8.FastLag

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.V1Check Nock.V1J8.Exe Nock.V1J8.CompX Nock.V1J8.MemX

/-- Lagrange weights at `z`, computed from a node array: `ell k = (∏_{j≠k}(x_k - x_j))⁻¹ · ∏_{j≠k}(z - x_j)`. -/
def ellArr {n : ℕ} (nodes : Fin n → ZMod p) (z : ZMod p) : Array (ZMod p) :=
  let xs := Array.ofFn nodes
  Array.ofFn (n := n) fun k =>
    (∏ j ∈ Finset.univ.erase k, (xs.getD k 0 - xs.getD j 0))⁻¹ * ∏ j ∈ Finset.univ.erase k, (z - xs.getD j 0)

theorem ofFn_getD {α : Type} {n : ℕ} (f : Fin n → α) (k : Fin n) (d : α) : (Array.ofFn f).getD (k : ℕ) d = f k := by
  simp [Array.getD]

theorem ellArr_getD {n : ℕ} (nodes : Fin n → ZMod p) (z : ZMod p) (k : Fin n) :
    (ellArr nodes z).getD k 0 = lagW nodes z k := by
  simp only [ellArr, ofFn_getD]
  rw [lagW, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

/-- The last-row extrapolated value of each of the first `w` columns. -/
def nextArr {n : ℕ} (nodes : Fin n → ZMod p) (ω : ZMod p) (cols : ℕ → Fin n → ZMod p) (w : ℕ) : Array (ZMod p) :=
  let z := ω * (if h : 0 < n then nodes ⟨n - 1, by omega⟩ else 0)
  let ell := ellArr nodes z
  Array.ofFn (n := w) fun j => ∑ k, cols j k * ell.getD k 0

theorem nextArr_getD {n : ℕ} (nodes : Fin n → ZMod p) (ω : ZMod p) (cols : ℕ → Fin n → ZMod p) (w : ℕ)
    (i : Fin n) (hi : ¬ (i : ℕ) + 1 < n) (j : ℕ) (hj : j < w) :
    (nextArr nodes ω cols w).getD j 0 = ∑ k, cols j k * lagW nodes (ω * nodes i) k := by
  have hn : 0 < n := by have := i.pos; omega
  have hi' : (⟨n - 1, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
  have := ofFn_getD (n := w) (fun j : Fin w => ∑ k, cols j k * lagW nodes (ω * nodes i) k) ⟨j, hj⟩ 0
  simp only [nextArr, dif_pos hn, hi', ellArr_getD]
  exact this

/-- The row environment of a compute table reading the cached extrapolation. -/
def envXF {n : ℕ} (T : TabX n) (nx : Array (ZMod p)) (i : Fin n) : Env (ZMod p) where
  trace := fun j => if j < 123 then T.cols j i else 0
  traceNext := fun j => if j < 123 then
      (if h : (i : ℕ) + 1 < n then T.cols j ⟨i + 1, h⟩ else nx.getD j 0) else 0
  chal := T.chal
  pub := T.pub

theorem envXF_eq {n : ℕ} (T : TabX n) (i : Fin n) : envXF T (nextArr T.nodes T.ω T.cols 123) i = T.env i := by
  simp only [envXF, TabX.env, Env.mk.injEq, and_true, true_and]
  funext j
  split_ifs with h1 h2
  · rfl
  · exact nextArr_getD _ _ _ _ i h2 j h1
  · rfl

def checkCompXF {n : ℕ} (T : TabX n) : Bool :=
  let nx := nextArr T.nodes T.ω T.cols 123
  (List.finRange n).all (fun i => srcX.all (srcOK (envXF T nx i))) &&
  ([(17, firstMaskE n), (18, lastMaskE n)] : List (ℕ × (Fin n → ZMod p))).all
    (fun q => (List.finRange n).all fun i => decide (T.cols q.1 i = q.2 i))

theorem checkCompX_eq_F : @checkCompX = @checkCompXF := by
  funext n T
  simp only [checkCompXF, checkCompX, envXF_eq]


section Mem
variable (Tm : ChipTemplate (ZMod p))

def envMF {n : ℕ} (T : TabM n) (nx : Array (ZMod p)) (i : Fin n) : Env (ZMod p) where
  trace := fun j => if j < Tm.width 3 then T.cols j i else 0
  traceNext := fun j => if j < Tm.width 3 then
      (if h : (i : ℕ) + 1 < n then T.cols j ⟨i + 1, h⟩ else nx.getD j 0) else 0
  chal := slotE Tm.baseCols T.chals
  pub := slotE Tm.baseCols T.pubs

theorem envMF_eq {n : ℕ} (T : TabM n) (i : Fin n) :
    envMF Tm T (nextArr T.nodes T.ω T.cols (Tm.width 3)) i = T.env Tm i := by
  simp only [envMF, TabM.env, Env.mk.injEq, and_true, true_and]
  funext j
  split_ifs with h1 h2
  · rfl
  · exact nextArr_getD _ _ _ _ i h2 j h1
  · rfl

def checkMF {n : ℕ} (T : TabM n) : Bool :=
  let nx := nextArr T.nodes T.ω T.cols (Tm.width 3)
  (List.finRange n).all (fun i => (srcM Tm).all (srcOK Tm.baseCols (envMF Tm T nx i))) &&
  T.prep.all (fun q => (List.finRange n).all fun i => decide (T.cols q.1 i = q.2 i))

theorem checkM_eq_F : @checkM = @checkMF := by
  funext Tm n T
  simp only [checkMF, checkM, envMF_eq]

end Mem


end Nock.V1J8.FastLag
