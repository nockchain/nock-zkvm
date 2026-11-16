import Nock.NockVMROM.Thm54.VclL.Compute.AxGate
import Nock.NockVMROM.Thm54.TraceGen.GenPathRows
import Nock.NockVMROM.Thm54.P8Core.TraceGen.GenTraceConfined

/-!
# V4c item 3: `hax63 : programAxisBound < 2^63`, the completeness-side axis binder

.

* `programAxisBound t` — the largest axis the generated compute tree reads: the `ax` column's
  honest value `honestAx` (OP0 `[0 b] ↦ b`, OP9 `[9 b c] ↦ b`, else `0`), maximized over the BFS
  rows, exactly as `programLeafBound` maximizes the leaf counts.  A function of the skeletons only
  (no coin, no field).
* `rowAx_le_programAxisBound` — every row's axis is below it.
* `depthOf_le_of_lt_pow` — an axis below `2^(k+1)` has at most `k` edges.
* **`hax63_depth`** — under `hax63` every row's path has `≤ 62` edges: the premise `h62` of
  `genPathRows_ok` (the honest path row passes its gates, its 6-bit certificate `62 − k` defined).
* **`hax63_fold_exact`** — and its side bits fold back to the axis below `2^63`, so at any prime
  `q > 2^63` the path record's field accumulator equals the formula atom `b < q` exactly when the
  chain's ℕ axis is `b` (`Consumers.path_record_axis_exact`'s `hlen` premise, discharged).

Paper: `:1751` (OP0's formula tail as the NMR address), `:1738` / `:1880-1881` (OP9's
`mem_axis_3 = f_th.leaf`), `:1288-1291` (axes).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock Nock.Walk Nock.NockVMROM.Thm54.TraceGen

section bound
variable {K : Type} [Field K]

/-- **The program's axis bound**: the largest `ax` value of the generated compute rows. -/
def programAxisBound (t : NTree (GenComputeRow K)) : ℕ :=
  (bfsRows t).foldl (fun acc g => acc ⊔ honestAx g.skel) 0

/-- Every generated row's axis is below the program's axis bound. -/
theorem rowAx_le_programAxisBound (t : NTree (GenComputeRow K)) :
    ∀ g ∈ bfsRows t, honestAx g.skel ≤ programAxisBound t :=
  foldl_sup_le_of_le (bfsRows t) (fun g => honestAx g.skel) le_rfl

end bound

/-- An axis below `2^(k+1)` has at most `k` edges. -/
theorem depthOf_le_of_lt_pow : ∀ (k a : ℕ), a < 2 ^ (k + 1) → depthOf a ≤ k
  | 0, a, h => by
      have : a < 2 := by simpa using h
      simp [depthOf, axisBits_of_lt_two this]
  | k + 1, a, h => by
      by_cases h2 : 2 ≤ a
      · have hlt : a / 2 < 2 ^ (k + 1) := by
          rw [Nat.div_lt_iff_lt_mul (by norm_num)]
          calc a < 2 ^ (k + 1 + 1) := h
            _ = 2 ^ (k + 1) * 2 := by rw [pow_succ]
        have ih := depthOf_le_of_lt_pow k (a / 2) hlt
        simp only [depthOf] at ih ⊢
        rw [axisBits_of_two_le h2, List.length_append, List.length_singleton]
        omega
      · simp [depthOf, axisBits_of_lt_two (by omega : a < 2)]

section hax
variable {K : Type} [Field K]

/-- **`hax63` gives `genPathRows_ok`'s depth premise at every generated row.** -/
theorem hax63_depth (t : NTree (GenComputeRow K)) (hax63 : programAxisBound t < 2 ^ 63) :
    ∀ g ∈ bfsRows t, depthOf (honestAx g.skel) ≤ 62 := fun g hg =>
  depthOf_le_of_lt_pow 62 _ (lt_of_le_of_lt (rowAx_le_programAxisBound t g hg) hax63)

/-- **`hax63` gives T4's exactness at every generated row**: the side bits of each row's axis have
`< 63` edges and fold back to the axis; at any `q > 2^63` the path accumulator's field value is the
cast of that natural, so it equals a formula atom `b < q` iff the axis is `b`. -/
theorem hax63_fold_exact (t : NTree (GenComputeRow K)) (hax63 : programAxisBound t < 2 ^ 63)
    {q : ℕ} (hq : 2 ^ 63 < q) (g : GenComputeRow K) (hg : g ∈ bfsRows t)
    (ha : 1 ≤ honestAx g.skel) (b : ℕ) (hb : b < q)
    (h : chainAccF q (axisBits (honestAx g.skel)) = (b : ZMod q)) :
    (axisBits (honestAx g.skel)).length < 63 ∧ honestAx g.skel = b := by
  have hd := hax63_depth t hax63 g hg
  have hlen : (axisBits (honestAx g.skel)).length < 63 := by simp only [depthOf] at hd; omega
  refine ⟨hlen, ?_⟩
  have := path_record_axis_exact hq _ hlen b hb h
  rwa [axisFold_axisBits _ ha] at this

/-- The axis bound is below `2^63` whenever every row's axis is (the form a fixture checks). -/
theorem programAxisBound_le_of_rows (t : NTree (GenComputeRow K)) (B : ℕ)
    (h : ∀ g ∈ bfsRows t, honestAx g.skel ≤ B) : programAxisBound t ≤ B := by
  unfold programAxisBound
  suffices ∀ (l : List (GenComputeRow K)) (acc : ℕ), acc ≤ B → (∀ g ∈ l, honestAx g.skel ≤ B) →
      l.foldl (fun acc g => acc ⊔ honestAx g.skel) acc ≤ B from this _ 0 (Nat.zero_le _) h
  intro l
  induction l with
  | nil => intro acc hacc _; simpa using hacc
  | cons x xs ih =>
      intro acc hacc hl
      simp only [List.foldl_cons]
      exact ih _ (max_le hacc (hl x (by simp))) (fun g hg => hl g (by simp [hg]))

end hax

end VclL.Compute
end Nock.NockVMROM.Thm54
