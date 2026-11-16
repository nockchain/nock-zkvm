/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ABalST.lean

  **J-9 A L7 C3 S3: row transfer**.

  * `sumT_transfer` (a): for `g` vanishing on the noun-row states `s0 / s10 / s10L / s10T`, the sum over the
    `old`-chip rows of the J-9 A twin `bfsForest [genX9T t]` of `g (rn)` is the J-8 BFS sum of
    `g (rowOfSkelX ·)`.  The one structural side condition `ChainZ g t` ("the chain child of every `s10B` row
    is `g`-null") is what the J-8 generated tree satisfies (its chain child is a `genChain`, states `s10L/s10T`).
  * `segT_F_zero`: every row of a segment chain contributes 0 (`s10S` rows are non-`old`; the lifted chain rows
    and the closing `s10T` row are `old` with `g = 0`).
  * `sum_axKey9` (b): `Σ_{rows} (axKey9 ↦ F) = Σ_{rows.filterMap axKey9} F`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AGen
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChainsRun
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABalSAx

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalST

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.Jet (Registry)
open Nock.NockVMROM.Thm54 (mapNTree mapNTree_label mapNTree_children bfsForest_mapNTree)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axKey9)
open Nock.J9A.NounAx (top)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalSAx (limbRecs list_range_sum)

/-! ## 1. DFS sums -/

theorem dfs_sum {M : Type} [AddCommMonoid M] {α : Type} (f : NTree α → M) :
    ∀ l : List (NTree α), ((dfsForest l).map f).sum = (l.map fun c => ((dfsTree c).map f).sum).sum
  | [] => by simp
  | c :: cs => by
    rw [dfsForest_cons, List.map_append, List.sum_append, dfs_sum f cs]
    simp

theorem dfsTree_map_perm {α β : Type} (f : α → β) (t : NTree α) :
    (dfsTree (mapNTree f t)).Perm ((dfsTree t).map (mapNTree f)) := by
  have h1 := dfsTree_perm_bfsForest (mapNTree f t)
  have h2 := bfsForest_mapNTree f [t]
  have h3 := (dfsTree_perm_bfsForest t).map (mapNTree f)
  simp only [List.map_cons, List.map_nil] at h2
  rw [h2] at h1
  exact h1.trans h3.symm

theorem rowOfSkelX_st (sk : SkelX) : (rowOfSkelX sk).st = sk.state := by
  cases h : sk.state <;> simp [rowOfSkelX, h]

/-! ## 2. Chains -/

theorem genChainF_states (old e : Noun) :
    ∀ (k a : ℕ), ∀ v ∈ dfsTree (genChainF old e k a),
      v.label.state = StateX.s10L ∨ v.label.state = StateX.s10T
  | 0, a, v, hv => by
    simp [genChainF, mkX, dfsTree, dfsForest] at hv
    subst hv; simp [NTree.label]
  | k + 1, a, v, hv => by
    unfold genChainF at hv
    split_ifs at hv with h2
    · simp only [mkX, dfsTree, dfsForest, List.map_cons, List.map_nil, List.append_nil,
        List.mem_cons] at hv
      rcases hv with rfl | hv
      · simp [NTree.label]
      · exact genChainF_states old e k (a / 2) v hv
    · simp [mkX, dfsTree, dfsForest] at hv
      subst hv; simp [NTree.label]

section G
variable {M : Type} [AddCommMonoid M] (g : RowNX → M)

/-- the transferred summand -/
def FF (u : NTree LX9) : M := if u.label.chip = ChipSt9.old then g u.label.rn else 0

variable (hg : ∀ r : RowNX, (r.st = StateX.s0 ∨ r.st = StateX.s10 ∨ r.st = StateX.s10L ∨ r.st = StateX.s10T) →
  g r = 0)
include hg

theorem liftT_chain_zero (old e : Noun) (k a : ℕ) :
    ((dfsTree (liftT (genChainF old e k a))).map (FF g)).sum = 0 := by
  have hp := (dfsTree_map_perm liftL (genChainF old e k a)).map (FF g)
  rw [show liftT (genChainF old e k a) = mapNTree liftL (genChainF old e k a) from rfl,
    hp.sum_eq, List.map_map]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
  have hs := genChainF_states old e k a v hv
  have : (FF g ∘ mapNTree liftL) v = g (rowOfSkelX v.label) := by
    simp [Function.comp, FF, liftL, mapNTree_label]
  rw [this]
  apply hg
  rw [rowOfSkelX_st]
  tauto

theorem segT_F_zero (n : ℕ) :
    ∀ (m : ℕ) (s e : Noun), ((dfsTree (segT n m s e)).map (FF g)).sum = 0
  | 0, s, e => by
    simp only [segT, segNode, tNode, dfsTree, dfsForest, List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, List.map_nil, List.sum_nil, List.append_nil]
    rw [show genChain s e (J9A.NounAx.segRd n 0) = genChainF s e _ _ from rfl, liftT_chain_zero g hg]
    have h0 : g (tRow (segX n 0 s) (segX n 0 e)) = 0 := hg _ (by simp [tRow])
    simp [FF, NTree.label, h0]
  | m + 1, s, e => by
    simp only [segT, segNode, dfsTree, dfsForest, List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, List.map_nil, List.sum_nil, List.append_nil]
    rw [show genChain s e (J9A.NounAx.segRd n (m + 1)) = genChainF s e _ _ from rfl,
      liftT_chain_zero g hg, segT_F_zero n m]
    simp [FF, NTree.label]

/-- The side condition: the chain child of every `s10B` node of `t` is `g`-null. -/
def ChainZ (t : NTree SkelX) : Prop :=
  ∀ u, InTree t u → (chipOf u.label).1 = ChipSt9.s10B → ∀ c ∈ u.children, c.label.state.isChain = true →
    ∀ v ∈ dfsTree c, g (rowOfSkelX v.label) = 0

theorem ChainZ.sub {t c : NTree SkelX} (h : ChainZ g t) (hc : c ∈ t.children) : ChainZ g c :=
  fun u hu => h u (InTree.sub hc hu)

theorem root_eq (k : SkelX) :
    (if (chipOf k).1 = ChipSt9.old then g (rowOfSkelX k) else 0) = g (rowOfSkelX k) := by
  by_cases h : (chipOf k).1 = ChipSt9.old
  · simp [h]
  · rw [if_neg h]
    symm
    apply hg
    rw [rowOfSkelX_st]
    unfold chipOf at h
    cases hst : k.state <;> simp [hst] at h ⊢

theorem sumT_tree (t : NTree SkelX) (hz : ChainZ g t) :
    ((dfsTree (genX9T t)).map (FF g)).sum = ((dfsTree t).map fun u => g (rowOfSkelX u.label)).sum := by
  let P : NTree SkelX → Prop := fun t => ChainZ g t →
    ((dfsTree (genX9T t)).map (FF g)).sum = ((dfsTree t).map fun u => g (rowOfSkelX u.label)).sum
  revert hz
  show P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro k ks ih hz
    have hk : (genX9T (.node k ks)) = .node ⟨rowX9 k, (chipOf k).1, (chipOf k).2, 0, rowOfSkelX k⟩
        (ks.map fun c => kid9 k c (genX9T c)) := by rw [genX9T]
    rw [hk]
    simp only [dfsTree, List.map_cons, List.sum_cons]
    rw [dfs_sum, dfs_sum, List.map_map]
    congr 1
    · simp only [FF, NTree.label]
      exact root_eq g hg k
    · congr 1
      apply List.map_congr_left
      intro c hc
      simp only [Function.comp]
      unfold kid9
      by_cases hcond : (chipOf k).1 = ChipSt9.s10B ∧ c.label.state.isChain = true
      · rw [if_pos hcond, segT_F_zero g hg]
        symm
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
        exact hz (.node k ks) (InTree.here _) hcond.1 c hc hcond.2 v hv
      · rw [if_neg hcond]
        exact ih c hc (ChainZ.sub g hg hz hc)
  · intro c hc; simp at hc
  · intro head tail ihH ihT c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihH
    · exact ihT c hc

theorem sumT_transfer (t : NTree SkelX) (hz : ChainZ g t) :
    (((bfsForest [genX9T t]).map (FF g))).sum = (((bfsForest [t]).map fun u => g (rowOfSkelX u.label))).sum := by
  rw [← ((dfsTree_perm_bfsForest (genX9T t)).map (FF g)).sum_eq,
    ← ((dfsTree_perm_bfsForest t).map fun u : NTree SkelX => g (rowOfSkelX u.label)).sum_eq]
  exact sumT_tree g hg t hz

end G

/-! ## 3. (b) keys -/

theorem sum_axKey9 {M : Type} [AddCommMonoid M] (F : Noun × ℕ → M) :
    ∀ rows : List LX9, (rows.map fun l => match axKey9 l with | some k => F k | none => 0).sum =
      ((rows.filterMap axKey9).map F).sum
  | [] => by simp
  | l :: ls => by
    rw [List.map_cons, List.sum_cons, sum_axKey9 F ls, List.filterMap_cons]
    cases h : axKey9 l <;> simp [h]

/-! ## 4. (c) the `s10S` rows -/

section C
variable {M : Type} [AddCommMonoid M] (φ : ℕ → ℕ → M)

/-- the `s10S` summand -/
def FS (u : NTree LX9) : M := if u.label.chip = ChipSt9.s10S then φ u.label.n u.label.m else 0

theorem liftT_FS_zero (c : NTree SkelX) : ((dfsTree (liftT c)).map (FS φ)).sum = 0 := by
  have hp := (dfsTree_map_perm liftL c).map (FS φ)
  rw [show liftT c = mapNTree liftL c from rfl, hp.sum_eq, List.map_map]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
  simp [Function.comp, FS, liftL, mapNTree_label]

theorem segT_FS (n : ℕ) :
    ∀ (m : ℕ) (s e : Noun), ((dfsTree (segT n m s e)).map (FS φ)).sum = ∑ i ∈ Finset.range (m + 1), φ n i
  | 0, s, e => by
    simp only [segT, segNode, tNode, dfsTree, dfsForest, List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, List.map_nil, List.sum_nil, List.append_nil]
    rw [liftT_FS_zero φ]
    simp [FS, NTree.label]
  | m + 1, s, e => by
    simp only [segT, segNode, dfsTree, dfsForest, List.map_cons, List.sum_cons, List.map_append,
      List.sum_append, List.map_nil, List.sum_nil, List.append_nil]
    rw [liftT_FS_zero φ, segT_FS n m, Finset.sum_range_succ _ (m + 1)]
    simp [FS, NTree.label, add_comm]

theorem sum_ite_count {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (S : M) (g : α → M) :
    (l.map fun c => if p c then S else g c).sum =
      (l.map fun c => if p c then 0 else g c).sum + ((l.filter fun c => decide (p c)).length) • S := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [List.filter_cons, h, ih, add_nsmul, add_assoc, add_comm, add_left_comm]

/-- the J-8-side summand: an `s10B` row stands for its whole limb chain -/
def GS (k : SkelX) : M :=
  if (chipOf k).1 = ChipSt9.s10B then ∑ i ∈ Finset.range (top (chipOf k).2 + 1), φ (chipOf k).2 i else 0

/-- side condition (discharged from the generator's shape): an `s10B` node has exactly one chain child, and
no `s10B` node lies inside a chain child. -/
def OneChain (t : NTree SkelX) : Prop :=
  ∀ u, InTree t u → (chipOf u.label).1 = ChipSt9.s10B →
    (u.children.filter fun c => decide (c.label.state.isChain = true)).length = 1 ∧
    ∀ c ∈ u.children, c.label.state.isChain = true → ∀ v ∈ dfsTree c, (chipOf v.label).1 ≠ ChipSt9.s10B

theorem OneChain.sub {t c : NTree SkelX} (h : OneChain t) (hc : c ∈ t.children) : OneChain c :=
  fun u hu => h u (InTree.sub hc hu)

theorem chipOf_ne_s10S (k : SkelX) : (chipOf k).1 ≠ ChipSt9.s10S := by
  unfold chipOf
  cases k.state <;> simp <;> split_ifs <;> simp

theorem sumS_tree (t : NTree SkelX) (hz : OneChain t) :
    ((dfsTree (genX9T t)).map (FS φ)).sum = ((dfsTree t).map fun u => GS φ u.label).sum := by
  let P : NTree SkelX → Prop := fun t => OneChain t →
    ((dfsTree (genX9T t)).map (FS φ)).sum = ((dfsTree t).map fun u => GS φ u.label).sum
  revert hz
  show P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro k ks ih hz
    have hk : (genX9T (.node k ks)) = .node ⟨rowX9 k, (chipOf k).1, (chipOf k).2, 0, rowOfSkelX k⟩
        (ks.map fun c => kid9 k c (genX9T c)) := by rw [genX9T]
    rw [hk]
    simp only [dfsTree, List.map_cons, List.sum_cons]
    rw [dfs_sum, dfs_sum, List.map_map]
    have e1 : ∀ ks' : List (NTree LX9),
        FS φ (NTree.node (⟨rowX9 k, (chipOf k).1, (chipOf k).2, 0, rowOfSkelX k⟩ : LX9) ks') = 0 := by
      intro ks'
      simp [FS, NTree.label, chipOf_ne_s10S]
    rw [e1, zero_add]
    by_cases hB : (chipOf k).1 = ChipSt9.s10B
    · obtain ⟨hcnt, hno⟩ := hz (.node k ks) (InTree.here _) hB
      have hcnt' : (ks.filter fun c => decide (c.label.state.isChain = true)).length = 1 := hcnt
      have hL : (ks.map ((fun u => ((dfsTree u).map (FS φ)).sum) ∘ fun c => kid9 k c (genX9T c))).sum =
          (ks.map fun c => if c.label.state.isChain = true then
            ∑ i ∈ Finset.range (top (chipOf k).2 + 1), φ (chipOf k).2 i
            else ((dfsTree (genX9T c)).map (FS φ)).sum).sum := by
        congr 1
        apply List.map_congr_left
        intro c hc
        simp only [Function.comp, kid9]
        by_cases hch : c.label.state.isChain = true
        · rw [if_pos ⟨hB, hch⟩, if_pos hch, segT_FS φ]
        · rw [if_neg (by tauto), if_neg hch]
      have hR : (ks.map ((fun u => ((dfsTree u).map fun u => GS φ u.label).sum))).sum =
          (ks.map fun c => if c.label.state.isChain = true then 0
            else ((dfsTree c).map fun u => GS φ u.label).sum).sum := by
        congr 1
        apply List.map_congr_left
        intro c hc
        by_cases hch : c.label.state.isChain = true
        · rw [if_pos hch]
          apply List.sum_eq_zero
          intro x hx
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
          simp [GS, hno c hc hch v hv]
        · rw [if_neg hch]
      rw [hL, hR, sum_ite_count ks _ _ (fun c => ((dfsTree (genX9T c)).map (FS φ)).sum), hcnt']
      have hG : GS φ (NTree.node k ks).label = ∑ i ∈ Finset.range (top (chipOf k).2 + 1), φ (chipOf k).2 i := by
        simp [GS, hB, NTree.label]
      have hm : (ks.map fun c => if c.label.state.isChain = true then 0
            else ((dfsTree (genX9T c)).map (FS φ)).sum).sum =
          (ks.map fun c => if c.label.state.isChain = true then 0
            else ((dfsTree c).map fun u => GS φ u.label).sum).sum := by
        congr 1
        apply List.map_congr_left
        intro c hc
        by_cases hch : c.label.state.isChain = true
        · rw [if_pos hch, if_pos hch]
        · rw [if_neg hch, if_neg hch]
          exact ih c hc (OneChain.sub hz hc)
      rw [hm, hG]
      simp [add_comm]
    · have hG : GS φ (NTree.node k ks).label = 0 := by simp [GS, hB, NTree.label]
      rw [hG, zero_add]
      congr 1
      apply List.map_congr_left
      intro c hc
      simp only [Function.comp]
      unfold kid9
      rw [if_neg (by tauto)]
      exact ih c hc (OneChain.sub hz hc)
  · intro c hc; simp at hc
  · intro head tail ihH ihT c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihH
    · exact ihT c hc

theorem sumS_transfer (t : NTree SkelX) (hz : OneChain t) :
    (((bfsForest [genX9T t]).map (FS φ))).sum = (((bfsForest [t]).map fun u => GS φ u.label)).sum := by
  rw [← ((dfsTree_perm_bfsForest (genX9T t)).map (FS φ)).sum_eq,
    ← ((dfsTree_perm_bfsForest t).map fun u : NTree SkelX => GS φ u.label).sum_eq]
  exact sumS_tree φ t hz

/-- the limb record at segment `i` (the `limbRecs` entries) -/
def limbRecAt {p : ℕ} (R n i : ℕ) : ZMod p × ZMod p × (ZMod p × ZMod p) :=
  ((R : ZMod p), (if i = top n then ((2 ^ (top n + 1) : ℕ) : ZMod p) - 1 else ((2 ^ (i + 2) : ℕ) : ZMod p) - 2),
    (0, ((n / 2 ^ (32 * i) % 2 ^ 32 : ℕ) : ZMod p)))

/-- reorder: the `limbRecs` sum is the sum over segments `0..top`. -/
theorem limbRecs_sum {p : ℕ} [Fact p.Prime] (f : ZMod p × ZMod p × (ZMod p × ZMod p) → M) (R n : ℕ) :
    ((limbRecs (p := p) R n).map f).sum = ∑ i ∈ Finset.range (top n + 1), f (limbRecAt R n i) := by
  rw [limbRecs, List.map_cons, List.sum_cons, List.map_map, Finset.sum_range_succ, add_comm]
  congr 1
  · rw [list_range_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have : i ≠ top n := (Finset.mem_range.1 hi).ne
    simp [limbRecAt, this]
  · simp [limbRecAt]

end C

/-! ## 4. The side conditions hold for generated trees -/

/-- the direct shape of a generated root: an `s10` root has the two generated children and the one chain child,
every other root has only non-chain children. -/
theorem genX_shape {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) :
    (t.label.state = StateX.s10 → ∃ a b c : NTree SkelX, t.children = [a, b, c] ∧
      a.label.state.isChain = false ∧ b.label.state.isChain = false ∧ ChainNode c) ∧
    (t.label.state ≠ StateX.s10 → ∀ k ∈ t.children, k.label.state.isChain = false) := by
  induction n, s, f using genComputeSkeletonX.induct R generalizing t r
  all_goals first | (simp_all [genComputeSkeletonX]; done) | skip
  case case32 n s ax c d tl new tr old hd hc e he ih1 ih2 =>
    simp only [genComputeSkeletonX, hc, hd, he, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨fun _ => ⟨tl, tr, _, by simp, (genX_label hc).2.2.2, (genX_label hd).2.2.2,
      chainNode_genChain he⟩, fun hne => absurd (by simp) hne⟩
  all_goals
    first
    | (simp only [genComputeSkeletonX, Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h
       refine ⟨fun h => by simp at h, fun _ k hk => ?_⟩
       simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false] at hk
       rcases hk with rfl | rfl | rfl <;> exact (genX_label (by assumption)).2.2.2)
    | skip
  all_goals
    simp only [genComputeSkeletonX, Option.some.injEq, Prod.mk.injEq, *] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨fun h => by simp at h, fun _ k hk => ?_⟩
    simp only [mkX_children, List.mem_cons, List.not_mem_nil, or_false] at hk
    try first
    | (rcases hk with rfl | rfl | rfl <;> exact (genX_label (by assumption)).2.2.2)
    | (rcases hk with rfl | rfl <;> exact (genX_label (by assumption)).2.2.2)
    | (rcases hk with rfl <;> exact (genX_label (by assumption)).2.2.2)

theorem chainNode_states {c : NTree SkelX} (hc : ChainNode c) :
    ∀ v ∈ dfsTree c, v.label.state = StateX.s10L ∨ v.label.state = StateX.s10T := by
  obtain ⟨old, e, k, a, rfl, -⟩ := hc
  exact genChainF_states old e k a

theorem chip_s10B_state {k : SkelX} (h : (chipOf k).1 = ChipSt9.s10B) : k.state = StateX.s10 := by
  unfold chipOf at h
  cases hs : k.state <;> simp [hs] at h ⊢
  all_goals split_ifs at h <;> simp_all

theorem chip_chain_ne {v : NTree SkelX}
    (hv : v.label.state = StateX.s10L ∨ v.label.state = StateX.s10T) : (chipOf v.label).1 ≠ ChipSt9.s10B := by
  intro h
  have := chip_s10B_state h
  rcases hv with hv | hv <;> rw [hv] at this <;> cases this

/-- for a generated or chain node `u` with `s10B` chip: three children, the first two non-chain, the third a
chain node. -/
theorem node_s10B {R : Registry} {t u : NTree SkelX} {n : ℕ} {s f : Noun} {r : Noun}
    (h : genX R n s f = some (t, r)) (hu : InTree t u) (hb : (chipOf u.label).1 = ChipSt9.s10B) :
    ∃ a b c : NTree SkelX, u.children = [a, b, c] ∧
      a.label.state.isChain = false ∧ b.label.state.isChain = false ∧ ChainNode c := by
  rcases genX_inTree h hu with ⟨m, hm⟩ | hch
  · exact (genX_shape hm).1 (chip_s10B_state hb)
  · exfalso
    have hu' : u ∈ dfsTree u := by cases u; simp [dfsTree]
    exact chip_chain_ne (chainNode_states hch u hu') hb

theorem oneChain_gen {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) : OneChain t := by
  intro u hu hb
  obtain ⟨a, b, c, hc, ha, hb', hch⟩ := node_s10B h hu hb
  have hcc := chainNode_isChain hch
  refine ⟨by simp [hc, ha, hb', hcc], ?_⟩
  intro x hx hxc v hv
  rw [hc] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · simp [ha] at hxc
  · simp [hb'] at hxc
  · exact chip_chain_ne (chainNode_states hch v hv)

theorem chainZ_gen {M : Type} [AddCommMonoid M] (g : RowNX → M)
    (hg : ∀ r : RowNX, (r.st = StateX.s0 ∨ r.st = StateX.s10 ∨ r.st = StateX.s10L ∨ r.st = StateX.s10T) →
      g r = 0)
    {R : Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    (h : genX R n s f = some (t, r)) : ChainZ g t := by
  intro u hu hb x hx hxc v hv
  obtain ⟨a, b, c, hc, ha, hb', hch⟩ := node_s10B h hu hb
  rw [hc] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · simp [ha] at hxc
  · simp [hb'] at hxc
  · apply hg
    rw [rowOfSkelX_st]
    rcases chainNode_states hch v hv with h | h <;> simp [h]

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABalST
