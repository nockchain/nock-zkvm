import Nock.NockVMROM.Thm54.Unhosted309Chip

/-!
# V4 (a): the new gate families of `computeChipVCL`

Two families, both stated at the physical coordinate level (`CoeffExpr`), indexed by the columns of
`computeChipVCL`'s layout (`ChipVCL.lean`):

Paper: `:1728-1742` (`V_comp`), `:1456-1479`.
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Reified Module
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler

noncomputable section

/-! ## 1. The row serial at arity 1 -/

/-- The serial's physical column in `computeChipVCL`: the TAIL column `w − 1 = 220` (the layout
`layoutVCL` stub's convention; its round is `0` by `colRoundVCL`, independent of the `wRAP` split). -/
def serialCol : ℕ := 220

/-- `isFirst · S = 0` (`isFirst` is preprocessing column `11`). -/
def serialInitGate {F : Type*} [Field F] : CoeffExpr F :=
  .mul (.var .traceCur 11) (.var .traceCur serialCol)

/-- `(1 − isLast)(S(i+1) − S(i) − 1) = 0` (`isLast` is preprocessing column `12`). -/
def serialStepGate {F : Type*} [Field F] : CoeffExpr F :=
  .mul (.sub (.const 1) (.var .traceCur 12))
    (.sub (.sub (.var .traceNext serialCol) (.var .traceCur serialCol)) (.const 1))

/-- The negative-control shape: the step dropped, `+ 1 → + 0` (replica fingerprint, `Batch1710`). -/
def serialStepGateNC {F : Type*} [Field F] : CoeffExpr F :=
  .mul (.sub (.const 1) (.var .traceCur 12))
    (.sub (.sub (.var .traceNext serialCol) (.var .traceCur serialCol)) (.const 0))

def serialGates {F : Type*} [Field F] : List (CoeffExpr F) := [serialInitGate, serialStepGate]

theorem serialGates_degree {F : Type*} [Field F] : ∀ g ∈ serialGates (F := F), g.degree ≤ 2 := by
  intro g hg
  simp only [serialGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp [serialInitGate, serialStepGate, CoeffExpr.degree]

@[simp] theorem serialGates_length {F : Type*} [Field F] : (serialGates (F := F)).length = 2 := rfl

theorem serialStepGate_eval {F : Type*} [Field F] (env : Env F) :
    (serialStepGate (F := F)).eval env = 0 ↔
      env.trace 12 = 1 ∨ env.traceNext serialCol = env.trace serialCol + 1 := by
  simp only [serialStepGate, CoeffExpr.eval, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by linear_combination h)
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by linear_combination h)

theorem serialInitGate_eval {F : Type*} [Field F] (env : Env F) :
    (serialInitGate (F := F)).eval env = 0 ↔ env.trace 11 = 0 ∨ env.trace serialCol = 0 := by
  simp [serialInitGate, CoeffExpr.eval]

/-! ## 2. The lookup-inverse triple -/

/-- Coordinate `k` of `inv · den − 1`, `inv` the `𝕂`-column at base limbs `invBase..invBase+2`
(current row) and `den` the coordinate vector of the denominator. -/
def lookupInvCoord {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (invBase : ℕ) (den : Fin 3 → CoeffExpr F) (k : Fin 3) : CoeffExpr F :=
  .sub (mulVec b (fun j => .var .traceCur (invBase + (j : ℕ))) den k) (oneVec b k)

def lookupInvGates {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (invBase : ℕ) (den : Fin 3 → CoeffExpr F) : List (CoeffExpr F) :=
  List.ofFn (lookupInvCoord b invBase den)

@[simp] theorem lookupInvGates_length {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (invBase : ℕ) (den : Fin 3 → CoeffExpr F) :
    (lookupInvGates b invBase den).length = 3 := by simp [lookupInvGates]

theorem lookupInvGates_degree {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (invBase : ℕ) (den : Fin 3 → CoeffExpr F) (dd : ℕ)
    (hden : ∀ k, (den k).degree ≤ dd) :
    ∀ g ∈ lookupInvGates b invBase den, g.degree ≤ 1 + dd := by
  intro g hg
  simp only [lookupInvGates] at hg
  rw [List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  simp only [lookupInvCoord, oneVec, CoeffExpr.degree]
  refine max_le ?_ (Nat.zero_le _)
  exact degree_mulVec_le b _ den 1 dd (fun j => by simp [CoeffExpr.degree]) hden k

/-- **Soundness of the triple**: if the three coordinate gates vanish at an environment in which
`inv` and `den` are the coordinate vectors of `x` and `y`, then `x * y = 1`. -/
theorem lookupInvGates_sound {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (b : Basis (Fin 3) F K) (invBase : ℕ) (den : Fin 3 → CoeffExpr F) (envF : Env F) (x y : K)
    (hx : ∀ j : Fin 3, coord b x j = envF.trace (invBase + (j : ℕ)))
    (hy : ∀ j, coord b y j = (den j).eval envF)
    (h : ∀ g ∈ lookupInvGates b invBase den, g.eval envF = 0) : x * y = 1 := by
  apply b.repr.injective
  ext k
  have hk := h (lookupInvCoord b invBase den k) ((List.mem_ofFn ..).2 ⟨k, rfl⟩)
  simp only [lookupInvCoord, CoeffExpr.eval, sub_eq_zero] at hk
  have hm := eval_mulVec b envF (fun j => .var .traceCur (invBase + (j : ℕ))) den x y
    (fun j => by simpa [CoeffExpr.eval] using hx j) hy k
  have h1 : coord b (1 : K) k = (oneVec b k).eval envF := by simp [oneVec, CoeffExpr.eval]
  have h2 : coord b (x * y) k = coord b (1 : K) k := by rw [hm, hk, h1]
  simpa [coord] using h2

end

end VclL.Compute
end Nock.NockVMROM.Thm54
