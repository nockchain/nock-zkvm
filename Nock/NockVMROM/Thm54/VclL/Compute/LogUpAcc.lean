import Nock.NockVMROM.Thm54.VclL.Compute.FormulaLookup

/-!
# The LogUp accumulator gadget, PARAMETRIC in the IO field

.  The gadget is generic in the
IO field `Kio` and its limb count `e` (a `Basis (Fin e) F Kio`), in the column positions, and in
the per-slot activity selectors and denominators — nothing here is typed at `𝕂` or `Fin 3`, so it
carries over to whichever tower route is chosen (`Kio = 𝕂` pre-tower, `Kio = 𝕂′ = Quad δ` with
`e = 6` at the target).

* **Gates** (`accGates`): one accumulator `acc` (`e` limbs at `accBase`), the per-row term
  `t = Σ_s act_s · inv_s` over the slots feeding it (`act_s ∈ 𝔽` a state-selector sum, `inv_s` the
  slot's `Kio` inverse), the public terminal `ρ` (`e` public limbs at `pubBase`):
  `isFirst · acc = 0`, `(1 − isLast)·(acc′ − acc − t) = 0`, `isLast · (acc + t − ρ) = 0`
  (degree `2 / 3 / 3`, `accGates_degree`; with `deg act ≤ 1`).
* **Row soundness** (`accInit_sound`, `accStep_sound`, `accTerm_sound`) and **the telescope**
  (`acc_telescope`): on `N` rows with the shift `traceNext i = trace (i+1)` and the first / last
  masks, `Σ_i t_i = ρ`.

Paper: the paper (the accumulator and its terminal), `:597` (`requests` as the shared
public), `:227-229` (`𝓛_LDSE`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace LogUp

open Nock Nock.Reified Module
open Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.SVFrame

noncomputable section

/-! ## 1. Limb readers, generic in the IO field -/

section limbs
variable {F Kio : Type} [Field F] [Field Kio] [Algebra F Kio] {e : ℕ} (bio : Basis (Fin e) F Kio)

/-- The `Kio` value of `e` consecutive limbs of an `𝔽`-valued column map. -/
def limbVal (f : ℕ → F) (base : ℕ) : Kio := ∑ k : Fin e, f (base + (k : ℕ)) • bio k

theorem coord_limbVal (f : ℕ → F) (base : ℕ) (k : Fin e) :
    coord bio (limbVal bio f base) k = f (base + (k : ℕ)) := by
  show bio.repr _ k = _
  unfold limbVal
  rw [bio.repr_sum_self]

theorem limbVal_eq_of_coords (x : Kio) (f : ℕ → F) (base : ℕ)
    (h : ∀ k : Fin e, coord bio x k = f (base + (k : ℕ))) : limbVal bio f base = x := by
  apply bio.repr.injective
  ext k
  have := coord_limbVal bio f base k
  simp only [coord] at this h
  rw [this, h k]

end limbs

/-! ## 2. The gates -/

/-- A slot feeding the accumulator: its activity selector (an `𝔽` expression, degree `≤ 1`) and the
base of its `Kio` inverse limbs. -/
structure Slot (F : Type) where
  act : CoeffExpr F
  invBase : ℕ

section gates
variable {F : Type} [Field F] (e : ℕ)

/-- Coordinate `k` of the per-row term `t = Σ_s act_s · inv_s`. -/
def termCoord (slots : List (Slot F)) (k : ℕ) : CoeffExpr F :=
  CoeffExpr.sumList slots fun s => .mul s.act (.var .traceCur (s.invBase + k))

/-- `isFirst · acc_k`. -/
def accInitGate (accBase : ℕ) (k : ℕ) : CoeffExpr F :=
  .mul (.var .traceCur 11) (.var .traceCur (accBase + k))

/-- `(1 − isLast) · (acc′_k − acc_k − t_k)`. -/
def accStepGate (slots : List (Slot F)) (accBase : ℕ) (k : ℕ) : CoeffExpr F :=
  .mul (.sub (.const 1) (.var .traceCur 12))
    (.sub (.sub (.var .traceNext (accBase + k)) (.var .traceCur (accBase + k))) (termCoord slots k))

/-- `isLast · (acc_k + t_k − ρ_k)`. -/
def accTermGate (slots : List (Slot F)) (accBase pubBase : ℕ) (k : ℕ) : CoeffExpr F :=
  .mul (.var .traceCur 12)
    (.sub (.add (.var .traceCur (accBase + k)) (termCoord slots k)) (.var .publicVal (pubBase + k)))

/-- **The accumulator's gates**: `3e` coordinate gates. -/
def accGates (slots : List (Slot F)) (accBase pubBase : ℕ) : List (CoeffExpr F) :=
  (List.range e).map (accInitGate accBase) ++ (List.range e).map (accStepGate slots accBase) ++
    (List.range e).map (accTermGate slots accBase pubBase)

theorem accGates_length (slots : List (Slot F)) (accBase pubBase : ℕ) :
    (accGates e slots accBase pubBase).length = 3 * e := by
  simp [accGates]; ring

theorem termCoord_degree (slots : List (Slot F)) (hs : ∀ s ∈ slots, s.act.degree ≤ 1) (k : ℕ) :
    (termCoord slots k).degree ≤ 2 :=
  CoeffExpr.degree_sumList_le _ _ _ fun s hm => by
    simp only [CoeffExpr.degree]; have := hs s hm; omega

theorem accGates_degree (slots : List (Slot F)) (hs : ∀ s ∈ slots, s.act.degree ≤ 1)
    (accBase pubBase : ℕ) : ∀ g ∈ accGates e slots accBase pubBase, g.degree ≤ 3 := by
  intro g hg
  simp only [accGates, List.mem_append, List.mem_map, List.mem_range] at hg
  have ht := termCoord_degree slots hs
  rcases hg with (⟨k, -, rfl⟩ | ⟨k, -, rfl⟩) | ⟨k, -, rfl⟩
  · simp [accInitGate, CoeffExpr.degree]
  · simp only [accStepGate, CoeffExpr.degree]; have := ht k; omega
  · simp only [accTermGate, CoeffExpr.degree]; have := ht k; omega

end gates

/-! ## 3. Row soundness at the `Kio` level -/

section sound
variable {F Kio : Type} [Field F] [Field Kio] [Algebra F Kio] {e : ℕ} (bio : Basis (Fin e) F Kio)

/-- The `Kio` value of the per-row term: `Σ_s act_s • inv_s`. -/
def termVal (slots : List (Slot F)) (env : Env F) : Kio :=
  (slots.map fun s => s.act.eval env • limbVal bio env.trace s.invBase).sum

theorem coord_termVal (slots : List (Slot F)) (env : Env F) (k : Fin e) :
    coord bio (termVal bio slots env) k = (termCoord slots k).eval env := by
  induction slots with
  | nil => simp [termVal, termCoord, CoeffExpr.sumList, CoeffExpr.eval, coord]
  | cons s ss ih =>
      simp only [termVal, List.map_cons, List.sum_cons, termCoord, CoeffExpr.sumList,
        List.foldr_cons, CoeffExpr.eval] at ih ⊢
      have hl := coord_limbVal bio env.trace s.invBase k
      simp only [coord] at ih hl ⊢
      rw [map_add, Finsupp.add_apply, map_smul, Finsupp.smul_apply, hl, ih, smul_eq_mul]

/-- `isFirst · acc = 0` at a first row gives `acc = 0`. -/
theorem accInit_zero (slots : List (Slot F)) (accBase pubBase : ℕ) (env : Env F)
    (h : ∀ g ∈ accGates e slots accBase pubBase, g.eval env = 0) (h11 : env.trace 11 = 1) :
    limbVal bio env.trace accBase = 0 := by
  apply limbVal_eq_of_coords bio 0 env.trace accBase
  intro k
  have hg := h (accInitGate accBase k) (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.2 ⟨k, List.mem_range.2 k.isLt, rfl⟩)))
  simp only [accInitGate, CoeffExpr.eval, h11, one_mul] at hg
  rw [hg]; simp [coord]

/-- `(1 − isLast)·(acc′ − acc − t) = 0` at a non-last row: `acc′ = acc + t`. -/
theorem accStep_eq (slots : List (Slot F)) (accBase pubBase : ℕ) (env : Env F)
    (h : ∀ g ∈ accGates e slots accBase pubBase, g.eval env = 0) (h12 : env.trace 12 = 0) :
    limbVal bio env.traceNext accBase = limbVal bio env.trace accBase + termVal bio slots env := by
  apply bio.repr.injective
  ext k
  have hg := h (accStepGate slots accBase k) (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨k, List.mem_range.2 k.isLt, rfl⟩)))
  simp only [accStepGate, CoeffExpr.eval, h12, sub_zero, one_mul] at hg
  have h1 := coord_limbVal bio env.traceNext accBase k
  have h2 := coord_limbVal bio env.trace accBase k
  have h3 := coord_termVal bio slots env k
  simp only [coord] at h1 h2 h3
  simp only [map_add, Finsupp.coe_add, Pi.add_apply, h1, h2, h3]
  linear_combination hg

/-- `isLast · (acc + t − ρ) = 0` at the last row: `acc + t = ρ`. -/
theorem accTerm_eq (slots : List (Slot F)) (accBase pubBase : ℕ) (env : Env F)
    (h : ∀ g ∈ accGates e slots accBase pubBase, g.eval env = 0) (h12 : env.trace 12 = 1) :
    limbVal bio env.trace accBase + termVal bio slots env = limbVal bio env.pub pubBase := by
  apply bio.repr.injective
  ext k
  have hg := h (accTermGate slots accBase pubBase k) (List.mem_append_right _
    (List.mem_map.2 ⟨k, List.mem_range.2 k.isLt, rfl⟩))
  simp only [accTermGate, CoeffExpr.eval, h12, one_mul] at hg
  have h1 := coord_limbVal bio env.pub pubBase k
  have h2 := coord_limbVal bio env.trace accBase k
  have h3 := coord_termVal bio slots env k
  simp only [coord] at h1 h2 h3
  simp only [map_add, Finsupp.coe_add, Pi.add_apply, h1, h2, h3]
  linear_combination hg

/-- **The telescope**: an accumulator starting at `0`, stepping by `t i` on rows `< N − 1`, with
terminal `acc (N−1) + t (N−1) = ρ`, sums its terms to `ρ`. -/
theorem acc_telescope {Kio : Type} [AddCommGroup Kio] (N : ℕ) (hN : 0 < N) (acc t : ℕ → Kio)
    (ρ : Kio) (h0 : acc 0 = 0) (hstep : ∀ i, i + 1 < N → acc (i + 1) = acc i + t i)
    (hterm : acc (N - 1) + t (N - 1) = ρ) :
    ∑ i ∈ Finset.range N, t i = ρ := by
  have key : ∀ m, m < N → acc m = ∑ i ∈ Finset.range m, t i := by
    intro m
    induction m with
    | zero => intro _; simpa using h0
    | succ m ih =>
        intro hm
        rw [hstep m hm, ih (by omega), Finset.sum_range_succ]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ, ← key n (by omega)]
  simpa using hterm

/-- **The accumulator over `N` rows**: from the gates at every row env, the row shift, and the
masks, the terms sum to the public terminal. -/
theorem acc_rows (slots : List (Slot F)) (accBase pubBase : ℕ) (N : ℕ) (hN : 0 < N)
    (envs : ℕ → Env F) (hg : ∀ i < N, ∀ g ∈ accGates e slots accBase pubBase, g.eval (envs i) = 0)
    (hshift : ∀ i, i + 1 < N → ∀ j, (envs i).traceNext j = (envs (i + 1)).trace j)
    (hfirst : (envs 0).trace 11 = 1)
    (hnotLast : ∀ i, i + 1 < N → (envs i).trace 12 = 0) (hlast : (envs (N - 1)).trace 12 = 1)
    (ρ : Kio) (hρ : limbVal bio (envs (N - 1)).pub pubBase = ρ) :
    ∑ i ∈ Finset.range N, termVal bio slots (envs i) = ρ := by
  refine acc_telescope N hN (fun i => limbVal bio (envs i).trace accBase)
    (fun i => termVal bio slots (envs i)) ρ ?_ ?_ ?_
  · exact accInit_zero bio slots accBase pubBase (envs 0) (hg 0 hN) hfirst
  · intro i hi
    have h := accStep_eq bio slots accBase pubBase (envs i) (hg i (by omega)) (hnotLast i hi)
    have hs : limbVal bio (envs i).traceNext accBase = limbVal bio (envs (i + 1)).trace accBase := by
      unfold limbVal
      exact Finset.sum_congr rfl fun k _ => by rw [hshift i hi]
    exact hs ▸ h
  · rw [← hρ]
    exact accTerm_eq bio slots accBase pubBase (envs (N - 1)) (hg (N - 1) (by omega)) hlast

end sound

/-! ## 4. The LogUp step: active records form `ReqIOFacts` -/

section logup
variable {Kio : Type} [Field Kio] [DecidableEq Kio] {m : ℕ}

/-- The active records of a row family (row-major, slot order). -/
def activeRecords (N ns : ℕ) (act : ℕ → ℕ → Kio) (rec : ℕ → ℕ → Fin m → Kio) :
    List (Fin m → Kio) :=
  (List.range N).flatMap fun i =>
    (List.range ns).filterMap fun s => if act i s = 1 then some (rec i s) else none

theorem activeRecords_length_le (N ns : ℕ) (act : ℕ → ℕ → Kio) (rec : ℕ → ℕ → Fin m → Kio) :
    (activeRecords N ns act rec).length ≤ N * ns := by
  unfold activeRecords
  rw [List.length_flatMap]
  calc ((List.range N).map fun i => ((List.range ns).filterMap fun s =>
          if act i s = 1 then some (rec i s) else none).length).sum
      ≤ ((List.range N).map fun _ => ns).sum := by
        apply List.sum_le_sum
        intro i _
        exact (List.length_filterMap_le _ _).trans (by simp)
    _ = N * ns := by simp

/-- **The LogUp step**: if every row's slot term is `act • inv` with `inv · den(rec) = act`,
`act ∈ {0, 1}`, then the active records' reciprocal denominators sum to `Σ_i Σ_s act·inv`. -/
theorem row_active_inv (ns : ℕ) (i : ℕ) (act inv : ℕ → ℕ → Kio) (rec : ℕ → ℕ → Fin m → Kio)
    (den : (Fin m → Kio) → Kio)
    (hbool : ∀ i s, act i s = 0 ∨ act i s = 1)
    (hinv : ∀ i s, inv i s * den (rec i s) = act i s) :
    (((List.range ns).filterMap fun s => if act i s = 1 then some (rec i s) else none).map
        fun r => (den r)⁻¹).sum =
      ∑ s ∈ Finset.range ns, act i s * inv i s := by
  induction ns with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.filterMap_append, List.map_append, List.sum_append, ih,
        Finset.sum_range_succ]
      congr 1
      rcases hbool i n with h0 | h1
      · simp [h0]
      · have hi := hinv i n
        rw [h1] at hi
        simp [h1, eq_inv_of_mul_eq_one_left hi]

/-- **The LogUp step**: if every row's slot term is `act • inv` with `inv · den(rec) = act`,
`act ∈ {0, 1}`, then the active records' reciprocal denominators sum to `Σ_i Σ_s act·inv`. -/
theorem sum_active_inv (N ns : ℕ) (act inv : ℕ → ℕ → Kio) (rec : ℕ → ℕ → Fin m → Kio)
    (den : (Fin m → Kio) → Kio)
    (hbool : ∀ i s, act i s = 0 ∨ act i s = 1)
    (hinv : ∀ i s, inv i s * den (rec i s) = act i s) :
    ((activeRecords N ns act rec).map fun r => (den r)⁻¹).sum =
      ∑ i ∈ Finset.range N, ∑ s ∈ Finset.range ns, act i s * inv i s := by
  induction N with
  | zero => simp [activeRecords]
  | succ n ih =>
      unfold activeRecords at ih ⊢
      rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih,
        Finset.sum_range_succ, List.flatMap_singleton,
        row_active_inv ns n act inv rec den hbool hinv]

/-- **`ReqIOFacts` from the rows** (the frame's `reqFacts` shape at one accumulator). -/
def reqIOFacts_of_rows (N ns : ℕ) (act inv : ℕ → ℕ → Kio) (rec : ℕ → ℕ → Fin m → Kio)
    (den : (Fin m → Kio) → Kio) (ρ : Kio)
    (hbool : ∀ i s, act i s = 0 ∨ act i s = 1)
    (hinv : ∀ i s, inv i s * den (rec i s) = act i s)
    (hsum : ∑ i ∈ Finset.range N, ∑ s ∈ Finset.range ns, act i s * inv i s = ρ) :
    ReqIOFacts den ρ where
  records := activeRecords N ns act rec
  sum_eq := (sum_active_inv N ns act inv rec den hbool hinv).trans hsum
  ne_zero := by
    intro r hr
    unfold activeRecords at hr
    simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq] at hr
    obtain ⟨i, -, s, -, hs1, rfl⟩ := hr
    intro h0
    have := hinv i s
    rw [h0, mul_zero, hs1] at this
    exact zero_ne_one this

end logup

end

end LogUp
end VclL.Compute
end Nock.NockVMROM.Thm54
