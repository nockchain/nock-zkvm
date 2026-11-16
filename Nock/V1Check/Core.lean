/-
  Nock/V1Check/Core.lean

  **The executable gate evaluator and the finite
  characterisation of RAP acceptance on row-interpolated traces.**  Additive; no module edited.

  * `CoeffExpr.map` / `Env.map` / `eval_map`: the evaluator over an executable field `E` agrees with the
    spec `CoeffExpr.eval` under a ring hom `φ : E →+* F`.
  * `TableData` / `checkTable`: the finite check (every gate at every row, preprocessing columns equal
    their masks at every node).  `satisfies_iff_checkTable`: for a `FixedPreprocessingRAP` whose
    constraints are `coeffToMv` of a gate list and whose trace is the Lagrange interpolant of the row
    arrays, `SatisfiesWithPreprocessing ↔ checkTable = true`.
-/
import Nock.NockVMROM.Thm54.CoordinateRAPCore
import Nock.Framework.EndpointMasks

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.V1Check

open Nock Nock.Reified Nock.Framework Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open scoped Polynomial

/-! ## 1. The evaluator agrees with the spec `eval` -/

section Eval
variable {E F : Type} [Field E] [Field F] (φ : E →+* F)

def mapC : CoeffExpr E → CoeffExpr F
  | .const c => .const (φ c)
  | .var k i => .var k i
  | .add a b => .add (mapC a) (mapC b)
  | .sub a b => .sub (mapC a) (mapC b)
  | .mul a b => .mul (mapC a) (mapC b)
  | .neg a => .neg (mapC a)
  | .pow a n => .pow (mapC a) n

def mapEnv (e : Env E) : Env F where
  trace := fun i => φ (e.trace i)
  traceNext := fun i => φ (e.traceNext i)
  chal := fun i => φ (e.chal i)
  pub := fun i => φ (e.pub i)

/-- **Evaluator agreement**: evaluating over `E` then mapping equals evaluating the mapped gate in the
mapped environment (the spec `CoeffExpr.eval` over `F`). -/
theorem eval_mapC (g : CoeffExpr E) (env : Env E) :
    φ (g.eval env) = (mapC φ g).eval (mapEnv φ env) := by
  induction g with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b ha hb => simp [CoeffExpr.eval, mapC, ha, hb]
  | sub a b ha hb => simp [CoeffExpr.eval, mapC, ha, hb]
  | mul a b ha hb => simp [CoeffExpr.eval, mapC, ha, hb]
  | neg a ha => simp [CoeffExpr.eval, mapC, ha]
  | pow a n ha => simp [CoeffExpr.eval, mapC, ha]

end Eval

/-! ## 2. Lagrange evaluation, finitely -/

section Lag
variable {F : Type} [Field F]

/-- The Lagrange weight of node `k` at the point `z`. -/
def lagW {n : ℕ} (nodes : Fin n → F) (z : F) (k : Fin n) : F :=
  ∏ j ∈ Finset.univ.erase k, (nodes k - nodes j)⁻¹ * (z - nodes j)

/-- Evaluation of the interpolant at an arbitrary point is the weighted sum of the row values. -/
theorem eval_interpolate_eq {n : ℕ} (nodes : Fin n → F) (c : Fin n → F) (z : F) :
    (Lagrange.interpolate Finset.univ nodes c).eval z = ∑ k, c k * lagW nodes z k := by
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Lagrange.basis, Polynomial.eval_prod, lagW]
  simp [Lagrange.basisDivisor, Polynomial.eval_mul]

end Lag

/-! ## 3. The finite check of a table -/

/-- **Executable table data**: nodes, orbit generator, row values per column (`cols j i`, `j < w`),
the gates (already coordinate-expanded), the coin and public limb vectors, and the verifier-fixed
columns (`prep`: column index and its required row values). -/
structure TableData (E : Type) (n : ℕ) where
  w : ℕ
  nodes : Fin n → E
  ω : E
  cols : ℕ → Fin n → E
  gates : List (CoeffExpr E)
  chal : ℕ → E
  pub : ℕ → E
  prep : List (ℕ × (Fin n → E))

namespace TableData
variable {E : Type} {n : ℕ} [Field E] [DecidableEq E]

/-- The next-row value of a row function at row `i`: the next row, or at the last row the Lagrange
extrapolation at `ω · node i` (the interpolant is not wrapped). -/
def nextVal (T : TableData E n) (c : Fin n → E) (i : Fin n) : E :=
  if h : (i : ℕ) + 1 < n then c ⟨i + 1, h⟩
  else ∑ k, c k * lagW T.nodes (T.ω * T.nodes i) k

/-- The environment at row `i`. -/
def env (T : TableData E n) (i : Fin n) : Env E where
  trace := fun j => if j < T.w then T.cols j i else 0
  traceNext := fun j => if j < T.w then T.nextVal (T.cols j) i else 0
  chal := T.chal
  pub := T.pub

/-- **The finite check**: every gate vanishes at every row; every fixed column equals its mask at
every row. -/
def checkTable (T : TableData E n) : Bool :=
  T.gates.all (fun g => (List.finRange n).all fun i => decide (g.eval (T.env i) = 0)) &&
  T.prep.all (fun p => (List.finRange n).all fun i => decide (T.cols p.1 i = p.2 i))

/-- **The ablatable check.**  `keep k` decides whether the gate at list position `k` is enforced;
`prepOn` whether the fixed (mask) columns are bound.  `checkTableF T (fun _ => true) true = checkTable T`. -/
def checkTableF (T : TableData E n) (keep : ℕ → Bool) (prepOn : Bool) : Bool :=
  (List.finRange T.gates.length).all (fun k =>
    !keep k || (List.finRange n).all fun i => decide ((T.gates.get k).eval (T.env i) = 0)) &&
  (!prepOn || T.prep.all (fun p => (List.finRange n).all fun i => decide (T.cols p.1 i = p.2 i)))

/-- **Ablated checker = the conjunction minus the disabled gates.** -/
theorem checkTableF_iff (T : TableData E n) (keep : ℕ → Bool) (prepOn : Bool) :
    T.checkTableF keep prepOn = true ↔
      (∀ k : Fin T.gates.length, keep k = true → ∀ i : Fin n, (T.gates.get k).eval (T.env i) = 0) ∧
      (prepOn = true → ∀ p ∈ T.prep, ∀ i : Fin n, T.cols p.1 i = p.2 i) := by
  simp only [checkTableF, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k hk i => ?_, fun hp p hp' i => ?_⟩
    · rcases h1 k with h | h
      · simp [hk] at h
      · exact h i
    · rcases h2 with h | h
      · simp [hp] at h
      · exact h p hp' i
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, ?_⟩
    · by_cases hk : keep k = true
      · exact Or.inr (h1 k hk)
      · exact Or.inl (by simpa using hk)
    · by_cases hp : prepOn = true
      · exact Or.inr (h2 hp)
      · exact Or.inl (by simpa using hp)

theorem checkTableF_full (T : TableData E n) : T.checkTableF (fun _ => true) true = T.checkTable := by
  apply Bool.eq_iff_iff.mpr
  rw [checkTableF_iff]
  simp only [checkTable, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq, forall_const]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun g hg i => by
      obtain ⟨k, rfl⟩ := List.get_of_mem hg
      exact h1 k i, fun p hp i => h2 p hp i⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun k i => h1 _ (List.get_mem _ _) i, fun p hp i => h2 p hp i⟩

end TableData

/-! ## 4. `SatisfiesWithPreprocessing ↔ checkTable` -/

section Main
variable {E F : Type} {n : ℕ} [Field E] [DecidableEq E] [Field F] (φ : E →+* F)

/-- **The finite characterisation.**  Let `R` be a fixed-preprocessing RAP over `F` whose constraints are
the `coeffToMv` of the `φ`-image of `T.gates`, on the row set of `φ ∘ nodes`, with generator `φ T.ω`,
whose designated fixed columns are the interpolants of `T.prep`'s masks, and let `P` be the Lagrange
interpolant of the row arrays.  With injective nodes and compute/memory adjacency, acceptance is exactly
`checkTable`. -/
theorem satisfies_iff_checkTable (T : TableData E n) (R : FixedPreprocessingRAP F)
    (P : Fin R.rap.w → F[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hw : R.rap.w = T.w)
    (hω : R.rap.ω = φ T.ω)
    (hH : R.rap.H = rowNodeSet (fun i => φ (T.nodes i)))
    (hC : List.ofFn R.rap.C =
      (T.gates.map (mapC φ)).map (coeffToMv (w := R.rap.w) (fun i => φ (T.chal i)) (fun i => φ (T.pub i))))
    (hprep : List.ofFn (fun j : Fin R.fixedCount => (((R.preprocessingColumn j : Fin R.rap.w) : ℕ), R.preprocessing j)) =
      T.prep.map (fun p => (p.1, Lagrange.interpolate Finset.univ (fun i => φ (T.nodes i)) (fun i => φ (p.2 i)))))
    (hP : ∀ j : Fin R.rap.w, P j =
      Lagrange.interpolate Finset.univ (fun i => φ (T.nodes i)) (fun i => φ (T.cols j i))) :
    RAP.SatisfiesWithPreprocessing R P ↔ T.checkTable = true := by
  classical
  have hinjF : Function.Injective (fun i => φ (T.nodes i)) := fun a b h => hinj (φ.injective h)
  have hnode : ∀ (j : Fin R.rap.w) (i : Fin n),
      (P j).eval (φ (T.nodes i)) = φ (T.cols j i) := by
    intro j i
    rw [hP j]
    exact Lagrange.eval_interpolate_at_node (fun i => φ (T.cols j i)) hinjF.injOn (Finset.mem_univ i)
  have hnext : ∀ (j : Fin R.rap.w) (i : Fin n),
      (P j).eval (R.rap.ω * φ (T.nodes i)) = φ (T.nextVal (T.cols j) i) := by
    intro j i
    rw [hω, ← map_mul]
    unfold TableData.nextVal
    split_ifs with h
    · rw [← hadj i h, hnode]
    · rw [hP j, eval_interpolate_eq, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul]
      simp [lagW, map_prod]
  have henv : ∀ i : Fin n,
      Reify.envOfTrace P R.rap.ω (φ (T.nodes i)) (fun i => φ (T.chal i)) (fun i => φ (T.pub i)) =
        mapEnv φ (T.env i) := by
    intro i
    simp only [Reify.envOfTrace, mapEnv, TableData.env]
    congr 1
    · funext j
      by_cases hj : j < R.rap.w
      · rw [dif_pos hj, if_pos (hw ▸ hj), hnode]
      · rw [dif_neg hj, if_neg (fun h => hj (hw ▸ h)), map_zero]
    · funext j
      by_cases hj : j < R.rap.w
      · rw [dif_pos hj, if_pos (hw ▸ hj), hnext]
      · rw [dif_neg hj, if_neg (fun h => hj (hw ▸ h)), map_zero]
  -- the gate half
  have hgate : R.rap.Satisfies P ↔ ∀ g ∈ T.gates, ∀ i : Fin n, g.eval (T.env i) = 0 := by
    unfold RAP.Satisfies
    constructor
    · intro h g hg i
      have hmem : coeffToMv (w := R.rap.w) (fun i => φ (T.chal i)) (fun i => φ (T.pub i)) (mapC φ g) ∈
          List.ofFn R.rap.C := by
        rw [hC]; exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩
      obtain ⟨s, hs⟩ := List.mem_ofFn.mp hmem
      have hx : φ (T.nodes i) ∈ R.rap.H := by rw [hH]; simp [rowNodeSet]
      have := h s _ hx
      rw [Reify.compose_eval, hs] at this
      have e1 := eval_coeffToMv P R.rap.ω (φ (T.nodes i)) (fun i => φ (T.chal i)) (fun i => φ (T.pub i)) (mapC φ g)
      rw [e1, henv, ← eval_mapC] at this
      exact φ.injective (by rw [this, map_zero])
    · intro h s x hx
      have hmem : R.rap.C s ∈ List.ofFn R.rap.C := List.mem_ofFn.mpr ⟨s, rfl⟩
      rw [hC] at hmem
      obtain ⟨g', hg', hgs⟩ := List.mem_map.mp hmem
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      rw [hH] at hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      rw [Reify.compose_eval, ← hgs]
      rw [eval_coeffToMv, henv, ← eval_mapC, h g hg i, map_zero]
  -- the preprocessing half
  have hbind : R.BindsPreprocessing P ↔
      ∀ p ∈ T.prep, ∀ i : Fin n, T.cols p.1 i = p.2 i := by
    unfold FixedPreprocessingRAP.BindsPreprocessing
    constructor
    · intro h p hp i
      have hmem : (p.1, Lagrange.interpolate Finset.univ (fun i => φ (T.nodes i)) (fun i => φ (p.2 i))) ∈
          List.ofFn (fun j : Fin R.fixedCount => (((R.preprocessingColumn j : Fin R.rap.w) : ℕ), R.preprocessing j)) := by
        rw [hprep]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hmem
      have h1 : ((R.preprocessingColumn j : Fin R.rap.w) : ℕ) = p.1 := congrArg Prod.fst hj
      have h2 : R.preprocessing j = Lagrange.interpolate Finset.univ (fun i => φ (T.nodes i)) (fun i => φ (p.2 i)) :=
        congrArg Prod.snd hj
      have h3 := h j
      rw [h2] at h3
      have h4 := congrArg (Polynomial.eval (φ (T.nodes i))) h3
      rw [hnode, Lagrange.eval_interpolate_at_node (fun i => φ (p.2 i)) hinjF.injOn (Finset.mem_univ i)] at h4
      have h5 := φ.injective h4
      rwa [h1] at h5
    · intro h j
      have hmem : (((R.preprocessingColumn j : Fin R.rap.w) : ℕ), R.preprocessing j) ∈
          List.ofFn (fun j : Fin R.fixedCount => (((R.preprocessingColumn j : Fin R.rap.w) : ℕ), R.preprocessing j)) :=
        List.mem_ofFn.mpr ⟨j, rfl⟩
      rw [hprep] at hmem
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hmem
      have h1 : p.1 = ((R.preprocessingColumn j : Fin R.rap.w) : ℕ) := congrArg Prod.fst hpe
      have h2 : Lagrange.interpolate Finset.univ (fun i => φ (T.nodes i)) (fun i => φ (p.2 i)) = R.preprocessing j :=
        congrArg Prod.snd hpe
      rw [← h2, hP]
      refine Lagrange.interpolate_eq_of_values_eq_on _ _ fun i _ => ?_
      rw [← h1]
      exact congrArg φ (h p hp i)
  have hchk : T.checkTable = true ↔
      (∀ g ∈ T.gates, ∀ i : Fin n, g.eval (T.env i) = 0) ∧
      (∀ p ∈ T.prep, ∀ i : Fin n, T.cols p.1 i = p.2 i) := by
    simp [TableData.checkTable, List.all_eq_true, Bool.and_eq_true]
  rw [hchk, ← hgate, ← hbind]
  exact Iff.rfl

end Main

end Nock.V1Check

#print axioms Nock.V1Check.eval_mapC
#print axioms Nock.V1Check.satisfies_iff_checkTable
#print axioms Nock.V1Check.TableData.checkTableF_iff
#print axioms Nock.V1Check.TableData.checkTableF_full
