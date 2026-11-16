/-
  Nock/RedTeam/Batch470Thm54MemoryPrefix.lean

  **The memory side: the forest prefix lemma holds; "no garbage
  outside the collision census" does NOT, and here is precisely why.**

  Brief step 5 asked to locate the priced NPR collision event and prove `memory_prefix_is_whole_forest` outside it, the argument
  being "a memory node's `lc`/`rc` is a strict sub-noun, so a cycle needs a fingerprint
  collision between a noun and a strict sub-noun".

  That argument is about GENUINE nouns.  A hostile memory row commits field elements: its
  `pt.noun : FP K` is `(size, dyck, leaf)` with no gate saying `size ∈ z^ℕ`.  The collision
  event prices `fp(n) = fp(n')` for distinct nouns `n, n'` of bounded size; a cycle whose
  vertices are not fingerprints of any noun is outside its scope and is not priced by it.

  Compiled:
  * A. `selfChild_Fmem`: a `decompose` row `N` whose right child is ITSELF and whose left child
    is a `halt` leaf `L` (`memCell N 1 = N.pt`, `childLinkMem`) passes `F_mem`, at any `z` with `z ≠ 0`, `z² ≠ 1`.  Its `pt.noun.size = 0`.
  * B. `selfChild_forces_size_zero`: CONVERSELY every `F_mem`-accepted decompose row with a
    `halt` left child and itself as right child has `pt.noun.size = 0` (from `Φ₁`,
    `size = lc.size · rc.size` with `lc.size = z`, `z ≠ 1`); so no genuine noun (size `z^λ`,
    `z ≠ 0`) is such a vertex, and the collision event never fires on it.
  * C. Hence `memory_prefix_is_whole_forest` is not a theorem of `F_mem` + the collision event;
    it needs a `pt.noun.size ≠ 0` (inverse-witness) gate on memory rows — the memory analogue
    of the compute `WF.size8/size11` conditions.
    Whether the deployed memory chip carries one is not measured here
    (`memory_size_gate_status`).
  * D. The forest prefix lemma itself is generic and landed in `Nock/WalkPrefix.lean`
    (`Walk.forestPrefixBFT_of_isForestFullBFT`, `Walk.reconForest_ForestReconGoal_prefix`):
    rows `1..prefixLenF kMem fo h` are the `kMem` roots' aggregate BFS, garbage is orphan cycles
    beyond it — the same shape as compute.  `garbage_forest_shape`: a `kroots = 1` forest with
    `fo = (0, 0, 2)` (root leaf, then `L`, then `N → (L, N)`) has the aggregate identity,
    tiling, `¬ BFSValidF`, `prefixLenF = 1`.
-/
import Nock.WalkPrefix
import Nock.NockVM

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch470

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable (FP MemRec)
open Nock.MemoryTable

section Fmem
variable {K : Type} [Field K]

/-- The halt leaf `L` with atom value `v`. -/
def leafPub (z v : K) : Pub K :=
  { st := .halt, pt := ⟨FP.atomFP z v, 0, 0⟩, lc := Cell.zero, rc := Cell.zero,
    lcSt := .halt, rcSt := .halt, mem := MemRec.zero, ipre := 0, icur := 0 }

def inpM (z : K) : Inputs K := { z := z, β := 0, γ := 0 }

def leafLbl (z v : K) : MState × DTmem K := (.halt, (inpM z, leafPub z v))

/-- The self-child vertex: `pt.noun = (0, z/(1 − z²), v/(1 − z))`.
    Form R at `λ = 1` forces a zero accumulator on a size-0 loop (`ind` unused). -/
def selfNoun (z v : K) : FP K := ⟨0, z / (1 - z * z), v / (1 - z)⟩

def selfPub (z v _ind : K) : Pub K :=
  { st := .decompose, pt := ⟨selfNoun z v, 0, 0⟩,
    lc := ⟨FP.atomFP z v, 0, 0⟩, rc := ⟨selfNoun z v, 0, 0⟩,
    lcSt := .halt, rcSt := .decompose, mem := MemRec.zero, ipre := 0, icur := 0 }

def selfLbl (z v ind : K) : MState × DTmem K := (.decompose, (inpM z, selfPub z v ind))

theorem leaf_Fmem (z v : K) : Fmem (leafLbl z v) (fun _ => none) := by
  refine ⟨rfl, ⟨verBool_holds _, ?_, ?_⟩, ?_, ?_⟩
  · simp [leafLbl, eqBlk, leafPub, inpM]
  · simp [leafLbl, interV, leafPub]
  · intro i; simp [leafLbl, fanoutMem]
  · intro i hi; simp [leafLbl, fanoutMem] at hi

/-- **A memory self-child passes `F_mem`** at `z ≠ 0`, `z² ≠ 1`: `Φ₁/Φ₂/Φ₃` (`FP.cons`) admit the
fixed point `pt = cons(z, atom v, pt)` with `size = 0`. -/
theorem selfChild_Fmem (z v ind : K) (hz : z ≠ 0) (hz2 : 1 - z * z ≠ 0) (hz1 : 1 - z ≠ 0) :
    Fmem (selfLbl z v ind)
      (fun j : Fin 2 => if (j : ℕ) = 0 then some (leafLbl z v) else some (selfLbl z v ind)) := by
  refine ⟨rfl, ⟨verBool_holds _, ?_, ?_⟩, ?_, ?_⟩
  · have hz2' : 1 - z ^ 2 ≠ 0 := by rwa [sq]
    simp only [selfLbl, eqBlk, selfPub, inpM]
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply FP.ext
      · simp [FP.cons, selfNoun]
      · simp only [FP.cons, selfNoun, FP.atomFP_size, FP.atomFP_dyck]
        field_simp
        ring
      · simp only [FP.cons, selfNoun, FP.atomFP_size, FP.atomFP_leaf]
        field_simp
        ring
    · simp [Pub.lambda]
    · simp [Pub.lambda]
    · trivial
  · simp [selfLbl, interV, selfPub]
  · intro i; fin_cases i <;> simp [selfLbl, fanoutMem]
  · intro i hi
    fin_cases i
    · simp [memCell, selfLbl, selfPub, leafLbl, leafPub]
    · simp [memCell, selfLbl, selfPub]

/-- **Converse: any `F_mem`-accepted self-child with a halt left child has `size = 0`.**  From
`Φ₁`: `pt.size = lc.size · rc.size = z · pt.size`, so `(1 − z) · pt.size = 0`. -/
theorem selfChild_forces_size_zero (lbl L : MState × DTmem K)
    (hst : lbl.1 = .decompose) (hL : L.1 = .halt)
    (hF : Fmem lbl (fun j : Fin 2 => if (j : ℕ) = 0 then some L else some lbl))
    (hFL : Fmem L (fun _ => none))
    (hz1 : lbl.2.1.z ≠ 1) (hzL : L.2.1.z = lbl.2.1.z) :
    lbl.2.2.pt.noun.size = 0 := by
  obtain ⟨hs, hV, _, hlink⟩ := hF
  obtain ⟨hsL, hVL, _, _⟩ := hFL
  have h0 := hlink 0 (by rw [hst]; decide)
  have h1 := hlink 1 (by rw [hst]; decide)
  simp only [Fin.val_zero, if_true, Option.map_some, Option.some.injEq, memCell] at h0
  simp only [Fin.val_one, Nat.one_ne_zero, if_false, Option.map_some, Option.some.injEq,
    memCell] at h1
  have hblk := hV.2.1
  rw [eqBlk, hs, hst] at hblk
  have hblkL := hVL.2.1
  rw [eqBlk, hsL, hL] at hblkL
  have hnoun := hblk.1
  rw [← h0, ← h1] at hnoun
  have hsize := congrArg FP.size hnoun
  simp only [FP.cons] at hsize
  rw [hblkL.1, hzL] at hsize
  have : (1 - lbl.2.1.z) * lbl.2.2.pt.noun.size = 0 := by linear_combination hsize
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (by linear_combination -h) hz1
  · exact h

end Fmem

/-! ## D. The forest shape `kroots = 1`, `fo = (0, 0, 2)` -/

def fo3 : ℕ → ℕ := fun i => if i = 3 then 2 else 0

theorem fo3_tiling : 1 + Sf fo3 3 = 3 := by decide

theorem fo3_not_bfsValidF : ¬ BFSValidF 1 fo3 3 := by
  intro hv
  have := hv 2 (by norm_num) (by norm_num)
  simp [Sf, fo3] at this

theorem garbage_forest_prefixLenF : prefixLenF 1 fo3 3 = 1 := by
  have h1 : 1 ≤ prefixLenF 1 fo3 3 := kroots_le_prefixLenF 1 fo3 (by norm_num)
  have h2 : prefixLenF 1 fo3 3 < 2 := by
    by_contra hge
    have hge : 2 ≤ prefixLenF 1 fo3 3 := not_lt.mp hge
    have hv := bfsValidF_prefixLenF 1 fo3 3
    have := hv 2 (by norm_num) hge
    simp [Sf, fo3] at this
  omega

section ForestWalk
variable {K : Type} [Field K]

def cur3 (R L N : K) : ℕ → K := fun i => if i = 1 then R else if i = 2 then L else
  if i = 3 then N else 0

def chld3 (L N : K) : ℕ → ℕ → K := fun i l =>
  if i = 3 ∧ l = 1 then L else if i = 3 ∧ l = 2 then N else 0

theorem sum_Icc_one_two (f : ℕ → K[X]) : ∑ k ∈ Finset.Icc 1 2, f k = f 1 + f 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self,
    Finset.sum_singleton]

/-- The forest identity (`Corr:forest`) holds for the garbage shape. -/
theorem garbage_isForestFullBFT (R L N : K) : IsForestFullBFT (cur3 R L N) (chld3 L N) fo3 1 3 := by
  unfold IsForestFullBFT forestQueueP childSumP
  simp only [nodeListP]
  have h3 : Finset.Icc (1 : ℕ) 3 = {1, 2, 3} := by decide
  have hs2 : ∑ i ∈ Finset.Icc 1 2, fo3 i = 0 := by decide
  rw [h3, Finset.Icc_self]
  simp only [fo3, cur3, chld3]
  norm_num [Sf, sum_Icc_one_two, hs2]
  ring

end ForestWalk

/-! ## C. Record -/

/-- What excludes the memory self-child: a `size ≠ 0` gate on `pt.noun`, not the collision
event.  Not measured on the deployed memory chip. -/
def memory_size_gate_status : String :=
  "pt.noun.size ≠ 0 on memory rows: not a Vmem/eqBlk clause; deployed memory chip not measured"

def collisionEventScope : String :=
  "main.tex:1188-1204 prices fp(n) = fp(n') for genuine nouns; size-0 vertices are no noun's fp"

end Nock.RedTeam.Batch470

#print axioms Nock.RedTeam.Batch470.selfChild_Fmem
#print axioms Nock.RedTeam.Batch470.selfChild_forces_size_zero
#print axioms Nock.RedTeam.Batch470.garbage_isForestFullBFT
#print axioms Nock.RedTeam.Batch470.garbage_forest_prefixLenF
