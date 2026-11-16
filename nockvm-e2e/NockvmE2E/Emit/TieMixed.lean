/-
  NockvmE2E/Emit/TieMixed.lean

  **The `K`-point twin of `mixedCompile_eval`.**  Nock's `mixedCompile_eval` is stated for `F`-valued environments only; the
  J-8 constraint polynomials are evaluated at `KC`-valued points.  Here the compiled coordinate gates are evaluated at an
  arbitrary `K`-algebra point `eA : Env K` (`evalA`; constants through `algebraMap`), and

      `Σ_k b_k · evalA eA (mixedCompile b col0 E k) = evalKK eK eA E`

  whenever `eA` carries the coordinates of `eK` (`IsCoordEnvA`).  `evalKK` is `MixedExpr.eval` with the base leaves read
  at `eA` (so `Lift g ↦ evalA eA g`).  Generic in `F K b`; no commutativity beyond `K` being a field.
-/
import NockvmE2E.Emit.Schema

set_option autoImplicit false

namespace NockvmE2E.Emit

open Nock.Reified Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Module

section Twin
variable {F K : Type*} [Field F] [Field K] [Algebra F K] {e : ℕ}

/-- a base gate at a `K`-algebra point (constants through `algebraMap`) -/
def evalA (eA : Env K) : CoeffExpr F → K
  | .const c => algebraMap F K c
  | .var .traceCur i => eA.trace i
  | .var .traceNext i => eA.traceNext i
  | .var .challenge i => eA.chal i
  | .var .publicVal i => eA.pub i
  | .add a b => evalA eA a + evalA eA b
  | .sub a b => evalA eA a - evalA eA b
  | .mul a b => evalA eA a * evalA eA b
  | .neg a => - evalA eA a
  | .pow a n => evalA eA a ^ n

/-- a mixed gate: `𝕂`-leaves at `eK`, base leaves at `eA` -/
def evalKK (eK eA : Env K) : MixedExpr F → K
  | .Var .traceCur i => eK.trace i
  | .Var .traceNext i => eK.traceNext i
  | .Var .challenge i => eK.chal i
  | .Var .publicVal i => eK.pub i
  | .Lift g => evalA eA g
  | .Scale g u => evalA eA g * evalKK eK eA u
  | .Const c => (c : K)
  | .Add x y => evalKK eK eA x + evalKK eK eA y
  | .Sub x y => evalKK eK eA x - evalKK eK eA y
  | .Neg x => - evalKK eK eA x
  | .Mul x y => evalKK eK eA x * evalKK eK eA y
  | .Pow x n => evalKK eK eA x ^ n

/-- `eA` carries the coordinates of `eK` (the `K`-point form of `IsCoordEnv`) -/
structure IsCoordEnvA (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) (eK eA : Env K) : Prop where
  trace : ∀ idx, ∑ k : Fin e, b k * eA.trace (col0 .traceCur idx + (k : ℕ)) = eK.trace idx
  traceNext : ∀ idx, ∑ k : Fin e, b k * eA.traceNext (col0 .traceNext idx + (k : ℕ)) = eK.traceNext idx
  chal : ∀ idx, ∑ k : Fin e, b k * eA.chal (col0 .challenge idx + (k : ℕ)) = eK.chal idx
  pub : ∀ idx, ∑ k : Fin e, b k * eA.pub (col0 .publicVal idx + (k : ℕ)) = eK.pub idx

theorem sum_coord_mul (b : Basis (Fin e) F K) (w : K) : ∑ k, algebraMap F K (coord b w k) * b k = w := by
  have := b.sum_repr w
  simpa [coord, Algebra.smul_def] using this

theorem sum_one (b : Basis (Fin e) F K) : ∑ k, b k * algebraMap F K (coord b (1 : K) k) = 1 := by
  have h := sum_coord_mul b (1 : K)
  calc ∑ k, b k * algebraMap F K (coord b (1 : K) k)
      = ∑ k, algebraMap F K (coord b (1 : K) k) * b k := Finset.sum_congr rfl fun k _ => mul_comm _ _
    _ = 1 := h

theorem evalA_sumList {ι : Type*} (eA : Env K) (l : List ι) (f : ι → CoeffExpr F) :
    evalA eA (CoeffExpr.sumList l f) = (l.map fun i => evalA eA (f i)).sum := by
  induction l with
  | nil => simp [CoeffExpr.sumList, evalA]
  | cons a l ih => simp [CoeffExpr.sumList, evalA] at ih ⊢; rw [ih]

theorem sum_mulVec (b : Basis (Fin e) F K) (eA : Env K) (u v : Fin e → CoeffExpr F) (x y : K)
    (hu : ∑ k, b k * evalA eA (u k) = x) (hv : ∑ k, b k * evalA eA (v k) = y) :
    ∑ k, b k * evalA eA (mulVec b u v k) = x * y := by
  have h1 : ∀ k, evalA eA (mulVec b u v k) =
      ∑ i, ∑ j, evalA eA (u i) * evalA eA (v j) * algebraMap F K (mulTensor b i j k) := by
    intro k
    simp only [mulVec, evalA_sumList, Finset.sum_map_toList, evalA]
  have h2 : ∀ i j, ∑ k, algebraMap F K (mulTensor b i j k) * b k = b i * b j :=
    fun i j => sum_coord_mul b (b i * b j)
  simp_rw [h1]
  calc ∑ k, b k * ∑ i, ∑ j, evalA eA (u i) * evalA eA (v j) * algebraMap F K (mulTensor b i j k)
      = ∑ k, ∑ i, ∑ j, b k * (evalA eA (u i) * evalA eA (v j) * algebraMap F K (mulTensor b i j k)) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ k, b k * (evalA eA (u i) * evalA eA (v j) * algebraMap F K (mulTensor b i j k)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, (b i * evalA eA (u i)) * (b j * evalA eA (v j)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have h3 : ∑ k, b k * (evalA eA (u i) * evalA eA (v j) * algebraMap F K (mulTensor b i j k)) =
            (∑ k, algebraMap F K (mulTensor b i j k) * b k) * (evalA eA (u i) * evalA eA (v j)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [h3, h2 i j]; ring
    _ = x * y := by
        rw [← hu, ← hv, Finset.sum_mul_sum]

theorem sum_powVec (b : Basis (Fin e) F K) (eA : Env K) (u : Fin e → CoeffExpr F) (x : K)
    (hu : ∑ k, b k * evalA eA (u k) = x) :
    ∀ n, ∑ k, b k * evalA eA (powVec b u n k) = x ^ n
  | 0 => by
      simp only [powVec, oneVec, evalA, pow_zero]
      exact sum_one b
  | n + 1 => by
      rw [pow_succ]
      exact sum_mulVec b eA _ u _ x (sum_powVec b eA u x hu n) hu

/-- **`mixedCompile_evalA`**: the compiled coordinate gates, summed against the basis, are the `𝕂`-gate, at any
`K`-algebra point carrying the coordinates. -/
theorem mixedCompile_evalA (b : Basis (Fin e) F K) (col0 : VarKind → ℕ → ℕ) {eK eA : Env K}
    (h : IsCoordEnvA b col0 eK eA) (E : MixedExpr F) :
    ∑ k, b k * evalA eA (mixedCompile b col0 E k) = evalKK eK eA E := by
  induction E with
  | Var kind idx =>
      cases kind
      · exact h.trace idx
      · exact h.traceNext idx
      · exact h.chal idx
      · exact h.pub idx
  | Lift g =>
      simp only [mixedCompile, evalA, evalKK]
      calc ∑ k, b k * (algebraMap F K (coord b (1 : K) k) * evalA eA g)
          = (∑ k, b k * algebraMap F K (coord b (1 : K) k)) * evalA eA g := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = evalA eA g := by rw [sum_one, one_mul]
  | Scale g u ihu =>
      simp only [mixedCompile, evalA, evalKK, ← ihu]
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  | Const c =>
      simp only [mixedCompile, evalA, evalKK, map_mul, map_intCast]
      calc ∑ k, b k * ((c : K) * algebraMap F K (coord b (1 : K) k))
          = (c : K) * ∑ k, b k * algebraMap F K (coord b (1 : K) k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = c := by rw [sum_one, mul_one]
  | Add x y ihx ihy =>
      simp only [mixedCompile, evalA, evalKK, ← ihx, ← ihy, mul_add, Finset.sum_add_distrib]
  | Sub x y ihx ihy =>
      simp only [mixedCompile, evalA, evalKK, ← ihx, ← ihy, mul_sub, Finset.sum_sub_distrib]
  | Neg x ihx =>
      simp only [mixedCompile, evalA, evalKK, ← ihx, mul_neg, Finset.sum_neg_distrib]
  | Mul x y ihx ihy =>
      exact sum_mulVec b eA _ _ _ _ ihx ihy
  | Pow x n ihx =>
      exact sum_powVec b eA _ _ ihx n

end Twin

end NockvmE2E.Emit

#print axioms NockvmE2E.Emit.mixedCompile_evalA
