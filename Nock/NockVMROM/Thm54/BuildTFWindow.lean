/-
  Nock/NockVMROM/Thm54/BuildTFWindow.lean

  `Walk.buildTF kroots fo lbl h i` is the subtree at aggregate-BFS position `i` of the
  `kroots`-root forest with fanout column `fo`, rows `1..h`.  Every child block `[firstCF i,
  firstCF i + fo i)` is carved out of one running prefix sum, so the blocks of distinct nodes are
  disjoint and the subtree at `i` consumes pairwise distinct positions of `[i, h]`.  Hence:

  * `buildTF_size_le_of_bfsValidF` : `1 ≤ i ≤ h`, `BFSValidF` ⟹ `size (buildTF i) ≤ h + 1 - i`;
  * `buildTF_roots_size_sum_le` : `kroots ≤ h` ⟹ the root subtrees together have `≤ h` nodes;
  * `decodePre_leaves_le_size` : `(decodePre K q t).leaves ≤ t.size` (the decoder maps a node to
    at least one and at most the sum of its two children's leaves);
  * `preZNounOfEnvs_leaves_le` : under `BFSValidF kroots (preFoOfEnvs envs hM) M`, every pre-`z`
    decoded noun at `i = 1..M` has `≤ M` leaves, so the guard `leaves ≤ Λ` of `guardedPairs`
    is vacuous on the first component at `Λ ≥ M`.

  Everything is generic in `kroots`, `fo`, `lbl`, `h`.  No hypothesis beyond the stated ones.
-/
import Nock.Walk
import Nock.NockVMROM.Thm54.PreZCensusCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.Walk

open Finset

section Size

variable {LT : Type*} (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → LT) (h : ℕ)

/-- Node count of the subtree at position `i`. -/
private abbrev S (i : ℕ) : ℕ := (buildTF kroots fo lbl h i).size

/-- The size recurrence of `buildTF`: one node plus the sizes of the subtrees at its child
indices. -/
theorem buildTF_size_eq (i : ℕ) :
    (buildTF kroots fo lbl h i).size =
      1 + ((childIdxsF kroots fo h i).map (fun j => (buildTF kroots fo lbl h j).size)).sum := by
  rw [buildTF]
  simp only [NTree.size, List.map_map, List.attach_map_val]
  rfl

private theorem size_eq (i : ℕ) :
    S kroots fo lbl h i = 1 + ((childIdxsF kroots fo h i).map (S kroots fo lbl h)).sum :=
  buildTF_size_eq kroots fo lbl h i

private theorem filter_range'_le (H : ℕ) :
    ∀ (n c : ℕ), (List.range' c n).filter (fun j => decide (j < H)) =
      List.range' c (min (c + n) H - c) := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    rw [List.range'_succ, List.filter_cons, ih (c + 1)]
    by_cases hc : c < H
    · have : min (c + (n + 1)) H - c = (min (c + 1 + n) H - (c + 1)) + 1 := by omega
      rw [this, List.range'_succ]
      simp [hc]
    · have h1 : min (c + (n + 1)) H - c = 0 := by omega
      have h2 : min (c + 1 + n) H - (c + 1) = 0 := by omega
      rw [h1, h2]
      simp [hc]

private theorem list_sum_range' (f : ℕ → ℕ) :
    ∀ (n c : ℕ), ((List.range' c n).map f).sum = ∑ k ∈ Finset.Ico c (c + n), f k := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    rw [List.range'_succ, List.map_cons, List.sum_cons, ih (c + 1),
      show c + (n + 1) = c + 1 + n by omega]
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : c < c + 1 + n)]

/-- The subtree size at `i`, as one sum over the (clipped) child block. -/
private theorem size_eq_Ico (i : ℕ) (hi : 1 ≤ i) (hlt : i < firstCF kroots fo i) :
    S kroots fo lbl h i =
      1 + ∑ k ∈ Finset.Ico (firstCF kroots fo i) (min (firstCF kroots fo (i + 1)) (h + 1)),
        S kroots fo lbl h k := by
  rw [size_eq, childIdxsF]
  have hf : (List.range' (firstCF kroots fo i) (fo i)).filter
        (fun j => decide (i < j ∧ j ≤ h)) =
      (List.range' (firstCF kroots fo i) (fo i)).filter (fun j => decide (j < h + 1)) := by
    apply List.filter_congr
    intro j hj
    rw [List.mem_range'] at hj
    obtain ⟨kk, hkk, rfl⟩ := hj
    simp only [decide_eq_decide]
    omega
  rw [hf, filter_range'_le, list_sum_range', firstCF_succ kroots fo hi]
  congr 1
  set c := firstCF kroots fo i
  by_cases hc : c ≤ min (c + fo i) (h + 1)
  · rw [show c + (min (c + fo i) (h + 1) - c) = min (c + fo i) (h + 1) by omega]
  · have h1 : min (c + fo i) (h + 1) - c = 0 := by omega
    rw [h1]
    simp only [Nat.add_zero]
    rw [Finset.Ico_eq_empty_of_le (le_refl c), Finset.Ico_eq_empty (by omega)]

private theorem firstCF_mono {i j : ℕ} (hij : i ≤ j) :
    firstCF kroots fo i ≤ firstCF kroots fo j := by
  unfold firstCF
  have := Sf_mono fo (show i - 1 ≤ j - 1 by omega)
  omega

/-- Gluing two adjacent clipped blocks. -/
private theorem glue (f : ℕ → ℕ) {x y z H : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) :
    ∑ k ∈ Finset.Ico x (min y H), f k + ∑ k ∈ Finset.Ico y (min z H), f k =
      ∑ k ∈ Finset.Ico x (min z H), f k := by
  by_cases hy : y ≤ H
  · rw [min_eq_left hy]
    exact Finset.sum_Ico_consecutive f hxy (le_min hyz hy)
  · have h1 : min y H = H := min_eq_right (by omega)
    have h2 : min z H = H := min_eq_right (by omega)
    have h3 : Finset.Ico y H = ∅ := Finset.Ico_eq_empty (by omega)
    rw [h1, h2, h3]
    simp

/-- Telescoping: the children blocks of the consecutive nodes `a..e-1` form one block. -/
private theorem children_telescope (a : ℕ) :
    ∀ e, a ≤ e → e ≤ firstCF kroots fo a →
      ∑ j ∈ Finset.Ico a e,
        ∑ k ∈ Finset.Ico (firstCF kroots fo j) (min (firstCF kroots fo (j + 1)) (h + 1)),
          S kroots fo lbl h k =
      ∑ k ∈ Finset.Ico (firstCF kroots fo a) (min (firstCF kroots fo e) (h + 1)),
        S kroots fo lbl h k := by
  intro e hae
  induction e, hae using Nat.le_induction with
  | base =>
    intro _
    rw [Finset.Ico_self, Finset.sum_empty, Finset.Ico_eq_empty (by omega)]
    simp
  | succ e hae ih =>
    intro hle
    rw [Finset.sum_Ico_succ_top hae, ih (by omega)]
    exact glue (S kroots fo lbl h) (firstCF_mono kroots fo hae)
      (firstCF_mono kroots fo (Nat.le_succ e))

/-- **Block bound.**  A block `[a, e)` of positions whose first children all lie at or beyond `e`
(`e ≤ firstCF a`, which is the queue-validity inequality at `a` for the one-node block) has total
subtree size at most `h + 1 - a`. -/
theorem buildTF_block_size_le :
    ∀ (N a e : ℕ), h + 1 - a ≤ N → 1 ≤ a → e ≤ h + 1 → e ≤ firstCF kroots fo a →
      ∑ j ∈ Finset.Ico a e, (buildTF kroots fo lbl h j).size ≤ h + 1 - a := by
  intro N
  induction N with
  | zero =>
    intro a e hN ha he hec
    have : Finset.Ico a e = ∅ := Finset.Ico_eq_empty (by omega)
    rw [this]; simp
  | succ N ih =>
    intro a e hN ha he hec
    by_cases hae : e ≤ a
    · rw [Finset.Ico_eq_empty (by omega)]; simp
    · replace hae := not_le.mp hae
      have hstep : ∀ j ∈ Finset.Ico a e,
          S kroots fo lbl h j = 1 + ∑ k ∈ Finset.Ico (firstCF kroots fo j)
            (min (firstCF kroots fo (j + 1)) (h + 1)), S kroots fo lbl h k := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        refine size_eq_Ico kroots fo lbl h j (by omega) ?_
        have := firstCF_mono kroots fo (show a ≤ j by omega)
        omega
      have hsum : ∑ j ∈ Finset.Ico a e, S kroots fo lbl h j =
          (e - a) + ∑ k ∈ Finset.Ico (firstCF kroots fo a) (min (firstCF kroots fo e) (h + 1)),
            S kroots fo lbl h k := by
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
          children_telescope kroots fo lbl h a e hae.le hec]
        simp
      show ∑ j ∈ Finset.Ico a e, S kroots fo lbl h j ≤ _
      rw [hsum]
      have hca : a < firstCF kroots fo a := by omega
      have hih := ih (firstCF kroots fo a) (min (firstCF kroots fo e) (h + 1)) (by omega)
        (by unfold firstCF; omega) (min_le_right _ _)
        (le_trans (min_le_left _ _) (firstCF_mono kroots fo hec))
      have hih' : ∑ k ∈ Finset.Ico (firstCF kroots fo a) (min (firstCF kroots fo e) (h + 1)),
          S kroots fo lbl h k ≤ h + 1 - firstCF kroots fo a := hih
      omega

end Size

section Public

variable {LT : Type*} {kroots : ℕ} {fo : ℕ → ℕ} {h : ℕ} (lbl : ℕ → LT)

/-- **C3, per position.**  Under queue validity, the subtree of `buildTF` at position
`1 ≤ i ≤ h` has at most `h + 1 - i` nodes (in particular at most `h`). -/
theorem buildTF_size_le_of_bfsValidF (hvalid : BFSValidF kroots fo h) {i : ℕ}
    (hi : 1 ≤ i) (hih : i ≤ h) :
    (buildTF kroots fo lbl h i).size ≤ h + 1 - i := by
  have hv := hvalid i hi hih
  have := buildTF_block_size_le kroots fo lbl h (h + 1 - i) i (i + 1) le_rfl hi (by omega)
    (by unfold firstCF; omega)
  simpa using this

/-- **C3, per position, window form.** `size ≤ h`. -/
theorem buildTF_size_le_h_of_bfsValidF (hvalid : BFSValidF kroots fo h) {i : ℕ}
    (hi : 1 ≤ i) (hih : i ≤ h) :
    (buildTF kroots fo lbl h i).size ≤ h := by
  have := buildTF_size_le_of_bfsValidF lbl hvalid hi hih
  omega

/-- **C3, over the roots.**  The `kroots` root subtrees of `buildTF kroots fo lbl h` have at most
`h` nodes in total (`kroots ≤ h`; supplied by the tiling `kroots + Sf fo h = h`). -/
theorem buildTF_roots_size_sum_le (hk : kroots ≤ h) :
    ∑ i ∈ Finset.Icc 1 kroots, (buildTF kroots fo lbl h i).size ≤ h := by
  have := buildTF_block_size_le kroots fo lbl h (h + 1 - 1) 1 (kroots + 1) le_rfl le_rfl
    (by omega) (by unfold firstCF; simp [Sf])
  have hI : Finset.Icc 1 kroots = Finset.Ico 1 (kroots + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ico]
  rw [hI]
  simpa using this

end Public

end Nock.Walk

namespace Nock.NockVMROM.Thm54.PreSeedCensus

open Nock Nock.Walk Nock.MemoryTable Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis Nock.NockVMROM.Thm54.HostileSkeletonDecoding

/-- The pre-`z` decoder never produces more leaves than the tree has nodes. -/
theorem decodePre_leaves_le_size {F : Type} (K : Type) [Field F] [Field K] [Algebra F K]
    (q : ℕ) (t : NTree (MState × F)) : (decodePre K q t).leaves ≤ t.size := by
  induction t using decodePre.induct with
  | case1 a => simp [decodePre, NTree.size, Noun.leaves]
  | case2 _ l r ihl ihr =>
      simp only [decodePre, Noun.leaves, NTree.size, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
  | case3 _ c ih =>
      simp only [decodePre, NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  | case4 _ c ih =>
      simp only [decodePre, NTree.size, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  | case5 t h1 h2 h3 h4 =>
      rw [decodePre.eq_5 (K := K) (q := q) t h1 h2 h3 h4]
      cases t with
      | node l c => simp [Noun.leaves, NTree.size]

section OfEnvs

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {M : ℕ}

/-- **The decoded-window cell of route B (C3).**  Under queue validity of the pre-`z` fanout
column on rows `1..M`, every decoded pre-`z` noun at position `1 ≤ i ≤ M` has at most `M` leaves:
the guard `leaves ≤ Λ` of `guardedPairs` is vacuous on the pre-`z` component at `Λ ≥ M`. -/
theorem preZNounOfEnvs_leaves_le (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M)
    (hvalid : BFSValidF kroots (preFoOfEnvs envs hM) M) {i : ℕ} (hi : 1 ≤ i) (hiM : i ≤ M) :
    (preZNounOfEnvs K q kroots envs hM i).leaves ≤ M := by
  unfold preZNounOfEnvs
  exact (decodePre_leaves_le_size K q _).trans
    (buildTF_size_le_h_of_bfsValidF _ hvalid hi hiM)

/-- Every first component of the route-B census has `≤ M` leaves. -/
theorem reqPairsOfEnvs_fst_leaves_le (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M) (T : MState → ℕ → Noun)
    (hvalid : BFSValidF kroots (preFoOfEnvs envs hM) M) :
    ∀ p ∈ reqPairsOfEnvs K q kroots envs hM T, p.1.leaves ≤ M := by
  intro p hp
  unfold reqPairsOfEnvs at hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  rw [List.mem_range'_1] at hi
  exact preZNounOfEnvs_leaves_le K q kroots envs hM hvalid (by omega) (by omega)

/-- The decoded root nouns together have at most `M` leaves (`kroots ≤ M`). -/
theorem preZNounOfEnvs_roots_leaves_sum_le (K : Type) [Field K] [Algebra F K] (q kroots : ℕ)
    (envs : Fin M → Env F) (hM : 0 < M) (hk : kroots ≤ M) :
    ∑ i ∈ Finset.Icc 1 kroots, (preZNounOfEnvs K q kroots envs hM i).leaves ≤ M := by
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (buildTF_roots_size_sum_le (fo := preFoOfEnvs envs hM) (preLblOfEnvs envs hM) hk)
  exact decodePre_leaves_le_size K q _

end OfEnvs

end Nock.NockVMROM.Thm54.PreSeedCensus
