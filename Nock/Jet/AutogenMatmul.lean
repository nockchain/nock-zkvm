/-
  Nock/Jet/AutogenMatmul.lean

  **Matmul as the first instance of the
  generic compiler.**

  * `matmul_wellTyped` (every `n`, every `p > 0`) and the faithfulness corollary
    `matmul_jetSpec_faithful` = `compile_jetSpec_faithful` applied; nothing matmul-specific is proved
    on the Nock side.
  * Toy at `n = 2`, `p = 7` (the wrap path is exercised): `toy_sem` (the template's semantics, by
    computation), `toy_holdsN` (from the generic theorem), and the direct `evalN` cross-check
    `toy_evalN` at fuel 200 (`decide +kernel`, kernel-checked), plus the same at Goldilocks on small
    entries (`toyG_evalN`).
  * Sizes: `cells` (cell nodes) of the compiled formula, kernel-checked at `n = 2` and `n = 8`
    (`matmul2_cells`, `matmul8_cells`), and of the library noun `LIB 7` (`lib_cells`).
-/
import Nock.Jet.Autogen

set_option autoImplicit false

namespace Nock.Jet.Autogen

open Nock Nock.Noun

/-- `Σ` as a left-nested `add` chain without a `const 0` seed (`const 0` only for the empty sum). -/
def sumEx {k : ℕ} : List (Ex k) → Ex k
  | [] => .const 0
  | e :: es => es.foldl .add e

def matTy (n : ℕ) : Ty := .L n (.L n .F)

def matIn (n : ℕ) : Fin 2 → Ty := fun _ => matTy n

def matmulBody (n : ℕ) : Ex 2 :=
  Ex.build ((List.range n).map fun i => Ex.build ((List.range n).map fun j =>
    sumEx ((List.range n).map fun l => .mul (.nth l (.nth i (.var 0))) (.nth j (.nth l (.var 1))))))

/-- **The matmul template**: `C = A·B mod p` on `n × n` matrices given as lists of rows. -/
def matmulT (n : ℕ) : Tpl where
  k := 2
  ax := ![12, 13]
  inTy := matIn n
  outTy := matTy n
  body := matmulBody n

theorem build_ty {p k : ℕ} {inTy : Fin k → Ty} {τ : Ty} :
    ∀ es : List (Ex k), (∀ e ∈ es, HasTy p inTy e τ) → HasTy p inTy (Ex.build es) (.L es.length τ) := by
  intro es
  induction es with
  | nil => intro _; exact HasTy.nil τ
  | cons e es ih =>
    intro h
    exact HasTy.pair (h e (by simp)) (ih fun e' he' => h e' (by simp [he']))

theorem foldl_add_ty {p k : ℕ} {inTy : Fin k → Ty} :
    ∀ (es : List (Ex k)) (acc : Ex k), HasTy p inTy acc .F → (∀ e ∈ es, HasTy p inTy e .F) →
      HasTy p inTy (es.foldl .add acc) .F := by
  intro es
  induction es with
  | nil => intro acc h _; exact h
  | cons e es ih =>
    intro acc h hes
    exact ih _ (HasTy.add h (hes e (by simp))) fun e' he' => hes e' (by simp [he'])

theorem sum_ty {p k : ℕ} (hp : 0 < p) {inTy : Fin k → Ty} (es : List (Ex k))
    (h : ∀ e ∈ es, HasTy p inTy e .F) : HasTy p inTy (sumEx es) .F := by
  cases es with
  | nil => exact HasTy.const hp
  | cons e es => exact foldl_add_ty es e (h e (by simp)) fun e' he' => h e' (by simp [he'])

/-- `matmulT n` is well typed at every modulus `p > 0` and every `n`. -/
theorem matmul_wellTyped {p : ℕ} (hp : 0 < p) (n : ℕ) : (matmulT n).WellTyped p := by
  have hA : ∀ i, i < n → HasTy p (matIn n) (.nth i (.var 0)) (.L n .F) := fun i hi =>
    HasTy.nth (HasTy.var (inTy := matIn n) 0) hi
  have hB : ∀ l, l < n → HasTy p (matIn n) (.nth l (.var 1)) (.L n .F) := fun l hl =>
    HasTy.nth (HasTy.var (inTy := matIn n) 1) hl
  have hrow : ∀ i, i < n → HasTy p (matIn n) (Ex.build ((List.range n).map fun j =>
      sumEx ((List.range n).map fun l => .mul (.nth l (.nth i (.var 0))) (.nth j (.nth l (.var 1))))))
      (.L n .F) := by
    intro i hi
    have := build_ty (p := p) (inTy := matIn n) (τ := .F) ((List.range n).map fun j =>
      sumEx ((List.range n).map fun l => .mul (.nth l (.nth i (.var 0))) (.nth j (.nth l (.var 1)))))
      (by
        intro e he
        simp only [List.mem_map, List.mem_range] at he
        obtain ⟨j, hj, rfl⟩ := he
        refine sum_ty hp _ ?_
        intro e he
        simp only [List.mem_map, List.mem_range] at he
        obtain ⟨l, hl, rfl⟩ := he
        exact HasTy.mul (HasTy.nth (hA i hi) hl) (HasTy.nth (hB l hl) hj))
    simpa using this
  have := build_ty (p := p) (inTy := matIn n) (τ := .L n .F) ((List.range n).map fun i =>
    Ex.build ((List.range n).map fun j =>
      sumEx ((List.range n).map fun l => .mul (.nth l (.nth i (.var 0))) (.nth j (.nth l (.var 1))))))
    (by
      intro e he
      simp only [List.mem_map, List.mem_range] at he
      obtain ⟨i, hi, rfl⟩ := he
      exact hrow i hi)
  simpa [Tpl.WellTyped, matmulT, matmulBody, matTy, matIn] using this

/-- **The matmul registry entry is faithful**: the generic theorem applied, at every `n`. -/
theorem matmul_jetSpec_faithful {p : ℕ} (hp : 0 < p) (n : ℕ) :
    (⟨(matmulT n).toTemplate p, compile p (matmulT n)⟩ : JetSpec).Faithful :=
  compile_jetSpec_faithful hp (matmulT n) (matmul_wellTyped hp n)

/-! ## Toy: `n = 2` -/

/-- A list noun `[x₀ [x₁ … 0]]`. -/
def lst (xs : List Noun) : Noun := xs.foldr .cell (.atom 0)

def mat (rows : List (List ℕ)) : Noun := lst (rows.map fun r => lst (r.map .atom))

/-- `A = [[1 2] [3 4]]`, `B = [[5 6] [0 1]]`; mod 7, `A·B = [[5 8] [15 22]] ≡ [[5 1] [1 1]]`. -/
def toyA : Noun := mat [[1, 2], [3, 4]]
def toyB : Noun := mat [[5, 6], [0, 1]]
def toyC : Noun := mat [[5, 1], [1, 1]]

/-- The gate subject `[battery [[A B] context]]`. -/
def toyS : Noun := .cell (.atom 0) (.cell (.cell toyA toyB) (.atom 0))

theorem toy_sem : (matmulT 2).sem 7 toyS = some toyC := by
  refine sem_eq_some_iff.2 ⟨![toyA, toyB], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [matmulT, toyS, Noun.slot]
  · intro i; fin_cases i <;> decide
  · decide

/-- **Toy `HoldsN`** of the 2×2 product, from the generic theorem. -/
theorem toy_holdsN : HoldsN ⟨toyS, compile 7 (matmulT 2), toyC⟩ :=
  compile_faithful (by norm_num) (matmulT 2) (matmul_wellTyped (by norm_num) 2) _ _ toy_sem

/-- **Direct `evalN` cross-check** at a concrete fuel (kernel evaluation). -/
theorem toy_evalN : evalN 200 toyS (compile 7 (matmulT 2)) = some toyC := by decide +kernel

/-- The same product at Goldilocks (no wrap at these entries: `[[5 8] [15 22]]`). -/
def toyCG : Noun := mat [[5, 8], [15, 22]]

theorem toyG_evalN : evalN 200 toyS (compile Nock.Field.p (matmulT 2)) = some toyCG := by
  decide +kernel

theorem toyG_holdsN : HoldsN ⟨toyS, compile Nock.Field.p (matmulT 2), toyCG⟩ := ⟨200, toyG_evalN⟩

/-- Kernel cross-check of the generic theorem's other half: the run is the template's semantics. -/
theorem toyG_sem : (matmulT 2).sem Nock.Field.p toyS = some toyCG :=
  compile_complete (by unfold Nock.Field.p; norm_num) (matmulT 2)
    (matmul_wellTyped (by unfold Nock.Field.p; norm_num) 2) 200 _ _ toyG_evalN

/-! ## Sizes -/

/-- Cell nodes of a noun (the tree size, no sharing). -/
def cells : Noun → ℕ
  | .atom _ => 0
  | .cell a b => cells a + cells b + 1

theorem lib_cells : cells (LIB 7) = 122 := by decide +kernel
theorem matmul2_cells : cells (compile 7 (matmulT 2)) = 1092 := by decide +kernel
theorem matmul8_cells : cells (compile 7 (matmulT 8)) = 57108 := by decide +kernel

end Nock.Jet.Autogen
