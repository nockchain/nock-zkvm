/-
  Nock/NockVMROM/Thm54/VclL/Handle/WalkTreeVS.lean

  Additive.

  Over the label language of `WalkLblVS` (`(st, row)`, encoded by the row's `(s, f, e)`, committed
  children = the row's `kids`):

  * `stVS` — the `StateSep` of `FV` (`Sleaf := fanS = 0`, `fanout := fanS`); `fv_respects` — `FV`
    reads the children only through `enc`, so `Walk_IOP_forest_final_card_of_label` applies with
    `labelOf := enc` (its `hEnc` is `id`);
  * **`cwEvent rows h`** — the compute walk event over `(α, γ) ∈ 𝕂 × 𝕂` at `kroots = 1`: the queue and
    tiling facts hold, the walk accepts with `seed = RLC^γ(label 1)·α`, `initial_count = α`, `out = 0`,
    and yet the committed rows do NOT form a single BFS tree; **`cwEvent_card`**:
    `≤ |𝕂|·h + |𝕂|·5h` (no hypothesis: the facts are in the event);
  * `goal_of_not_mem` — outside the event, the facts and the accepted walk give `ForestReconGoal`;
  * **`tree_of_goal`** — from `ForestReconGoal` at `kroots = 1`, with every row's handle values below
    the characteristic (`SmallR`, so `encT` is injective on the triples involved): one tree whose
    root label is row `1`, every node's label is some row `i ∈ [1, h]`, and every node's children
    carry exactly its `kids` triples (in order) — the `RowsOK.link` shape of `LocalVS`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVS
import Nock.NockVMROM.Thm54.WalkTilingEvents
import Nock.RedTeam.Batch478Thm54QueueGateRatioForm

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVS

open Nock Nock.Walk
open Nock.ComputeTable (State)
open Nock.NockVMROM.Thm54.VclL.Handle (VHandle)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVS
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVS

noncomputable section

section Sep
variable (K : Type) [Field K]

theorem fv_none_iff (a : State × RowVS) :
    FV (K := K) a (fun _ => none) ↔ a.1 = a.2.st ∧ fanS a.1 = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := (h2 ⟨0, by decide⟩).1
    simp only [ne_eq, not_true_eq_false, iff_false, not_lt, Nat.le_zero] at this
    exact this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j => ⟨?_, fun c hc => by cases hc⟩⟩
    simp [h2]

/-- **The `StateSep` of the compute walk at VS.** -/
def stVS : StateSep (FV (K := K)) where
  Sleaf s := fanS s = 0
  fanout := fanS
  fanout_le := fanS_le
  fanout_leaf _ h := h
  solely := by
    intro t ht
    obtain ⟨l, ch⟩ := t
    simp only [RVT] at ht
    obtain ⟨hF, -, hleaf⟩ := ht
    rw [hleaf, fv_none_iff]
    exact ⟨fun h => ⟨hF.1, h⟩, fun h => h.2⟩
  dynamic := by
    intro s d xout hF i
    exact (hF.2 i).1

/-- `FV` reads the children only through `enc`. -/
theorem fv_respects : RespectsChildLabels (FV (K := K)) (enc (K := K)) := by
  intro a xout xout' hmap hF
  refine ⟨hF.1, fun j => ⟨?_, ?_⟩⟩
  · rw [(hF.2 j).1]
    have hj := hmap j
    constructor
    · intro hne hn; rw [hn] at hj; apply hne
      cases hx : xout j with
      | none => rfl
      | some c => rw [hx] at hj; simp at hj
    · intro hne hn; rw [hn] at hj; apply hne
      cases hx : xout' j with
      | none => rfl
      | some c => rw [hx] at hj; simp at hj
  · intro c' hc'
    have hj := hmap j
    rw [hc'] at hj
    cases hx : xout j with
    | none => rw [hx] at hj; simp at hj
    | some c =>
      rw [hx] at hj
      simp only [Option.map_some, Option.some.injEq] at hj
      rw [← hj]
      exact (hF.2 j).2 c hx

end Sep

/-! ## 2. The event -/

section Event
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

open scoped Classical in
/-- **The compute walk event at VS** (`kroots = 1`): the queue/tiling facts hold and the walk accepts
with the frame's publics, yet the rows form no BFS tree. -/
def cwEvent (rows : ℕ → RowVS) (h : ℕ) : Finset (K × K) :=
  Finset.univ.filter fun p : K × K =>
    (1 + Sf (foOf rows) h = h ∧ BFSValidF 1 (foOf rows) h) ∧
    (∃ ln count acc : ℕ → K,
      WalkSat (fun i => rlc p.2 (enc (lblOf rows i))) (fun i l => rlc p.2 (enc (clabOf rows i l)))
        (foOf rows) ln count acc p.1
        (∑ i ∈ Finset.Icc 1 1, rlc p.2 (enc (lblOf rows i)) * p.1 ^ i) (p.1 ^ 1) h ∧ acc h = 0) ∧
    ¬ ForestReconGoal (stVS K) (lblOf rows) 1 h

open scoped Classical in
theorem cwEvent_card (rows : ℕ → RowVS) (h : ℕ) :
    (cwEvent (K := K) rows h).card ≤ Fintype.card K * h + Fintype.card K * (h * (6 - 1)) := by
  by_cases hyp : 1 + Sf (foOf rows) h = h ∧ BFSValidF 1 (foOf rows) h
  · have hc := Walk_IOP_forest_final_card_of_label (stVS K) (enc (K := K)) (fv_respects K)
      (enc (K := K)) (fun _ _ h => h) (lblOf rows) (clabOf rows) (foOf rows) (kroots := 1) (h := h)
      le_rfl hyp.1 hyp.2 (foOf_le rows) (fun _ _ _ => rfl) (fun i _ _ => fv_commit rows i)
    refine le_trans (Finset.card_le_card ?_) hc
    intro p hp
    simp only [cwEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2.1, hp.2.2⟩
  · have : cwEvent (K := K) rows h = ∅ := by
      ext p; simp [cwEvent, hyp]
    rw [this]; simp

theorem cwEvent_card_le (rows : ℕ → RowVS) {h H : ℕ} (hH : h ≤ H) :
    (cwEvent (K := K) rows h).card ≤ Fintype.card K * (6 * H) := by
  refine (cwEvent_card rows h).trans ?_
  have : Fintype.card K * h + Fintype.card K * (h * (6 - 1)) = Fintype.card K * (6 * h) := by ring_nf
  rw [this]
  exact Nat.mul_le_mul_left _ (by omega)

open scoped Classical in
/-- **Outside the walk event**, the facts and an accepted walk give the forest goal. -/
theorem goal_of_not_mem (rows : ℕ → RowVS) {h : ℕ} (htile : 1 + Sf (foOf rows) h = h)
    (hval : BFSValidF 1 (foOf rows) h) {α γ : K}
    (hw : ∃ ln count acc : ℕ → K,
      WalkSat (fun i => rlc γ (enc (lblOf rows i))) (fun i l => rlc γ (enc (clabOf rows i l)))
        (foOf rows) ln count acc α
        (∑ i ∈ Finset.Icc 1 1, rlc γ (enc (lblOf rows i)) * α ^ i) (α ^ 1) h ∧ acc h = 0)
    (hout : (α, γ) ∉ cwEvent (K := K) rows h) :
    ForestReconGoal (stVS K) (lblOf rows) 1 h := by
  by_contra hng
  exact hout (by simp only [cwEvent, Finset.mem_filter, Finset.mem_univ, true_and]
                 exact ⟨⟨htile, hval⟩, hw, hng⟩)

/-- The `α`-tiling set: terminal-accepting `α` on a non-tiling fanout column. -/
def tileSet (fo : ℕ → ℕ) (h : ℕ) : Finset K :=
  Finset.univ.filter fun a : K => a ^ (1 + Sf fo h) = a ^ h ∧ 1 + Sf fo h ≠ h

theorem tileSet_card (fo : ℕ → ℕ) (hfo : ∀ i, fo i ≤ 3) (h : ℕ) :
    (tileSet (K := K) fo h).card ≤ 2 * h + 2 :=
  WalkTilingEvents.card_computeTilingAlphas_le fo hfo h

end Event

/-! ## 3. Queue validity and tiling from the ratio gate -/

section Ratio
variable {K : Type} [Field K]

/-- **Queue validity** from `count ≠ ln`, no condition on `α`. -/
theorem bfs_of_walk {cur : ℕ → K} {chld : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln cnt acc : ℕ → K} {α seed : K}
    {h : ℕ} (hw : WalkSat cur chld fo ln cnt acc α seed (α ^ 1) h)
    (hne : ∀ i, 1 ≤ i → i < h → cnt i ≠ ln i) : BFSValidF 1 fo h := by
  refine Nock.RedTeam.Batch478.bfsValidF_of_ratio_gate (α := α) le_rfl ?_
  intro i hi1 hih
  have hc := count_closed hw i hi1 (le_of_lt hih)
  have hl := ln_closed hw i hi1 (le_of_lt hih)
  have := hne i hi1 hih
  rw [hc, hl, ← pow_add] at this
  exact this

/-- **The tiling** from the terminal `count = ln`, outside `tileSet`. -/
theorem tile_of_walk [Fintype K] [DecidableEq K] {cur : ℕ → K} {chld : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln cnt acc : ℕ → K} {α seed : K} {h : ℕ} (hw : WalkSat cur chld fo ln cnt acc α seed (α ^ 1) h)
    (hterm : cnt h = ln h) (hα : α ∉ tileSet fo h) : 1 + Sf fo h = h := by
  have hc := count_closed hw h hw.hpos le_rfl
  have hl := ln_closed hw h hw.hpos le_rfl
  rw [hc, hl, ← pow_add] at hterm
  by_contra hne
  exact hα (by simp only [tileSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hterm, hne⟩)

end Ratio

/-! ## 4. The tree -/

section Tree
variable {K : Type} [Field K]

/-- A triple's handle values are below `p`. -/
def SmallT (p : ℕ) (t : Trip) : Prop := t.1.2 < p ∧ t.2.1.2 < p ∧ t.2.2.2 < p

theorem smallT_trip {p : ℕ} {r : RowVS} (h : SmallR p r) : SmallT p r.trip :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem smallT_kids {p : ℕ} {r : RowVS} (h : SmallR p r) : ∀ t ∈ kids r, SmallT p t := by
  obtain ⟨hs, hf, he, h1, h2, hfh, hft, hfth, hftt, -, -, hm⟩ := h
  intro t ht
  unfold kids at ht
  split at ht <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at ht <;>
    (try rcases ht with rfl | rfl | rfl) <;> (try rcases ht with rfl | rfl) <;>
    exact ⟨by assumption, by assumption, by assumption⟩

theorem natCast_inj_lt {p : ℕ} [CharP K p] {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : K) = (b : K)) : a = b := by
  rw [CharP.natCast_eq_natCast K p] at h
  exact Nat.ModEq.eq_of_lt_of_lt h ha hb

theorem kind_inj (a b : Bool) (h : (if a then (1 : K) else 0) = (if b then 1 else 0)) : a = b := by
  cases a <;> cases b <;> simp_all

theorem encH_inj {p : ℕ} [CharP K p] {x y : VHandle} (hx : x.2 < p) (hy : y.2 < p)
    (h1 : (encH (K := K) x).1 = (encH y).1) (h2 : (encH (K := K) x).2 = (encH y).2) : x = y := by
  obtain ⟨a, n⟩ := x
  obtain ⟨b, m⟩ := y
  have hx' : n < p := hx
  have hy' : m < p := hy
  simp only [encH] at h1 h2
  rw [kind_inj a b h1, natCast_inj_lt hx' hy' h2]

/-- **`encT` is injective on small triples.** -/
theorem encT_inj {p : ℕ} [CharP K p] {t t' : Trip} (h : SmallT p t) (h' : SmallT p t')
    (he : encT (K := K) t = encT t') : t = t' := by
  have e := fun c : Fin 6 => congrFun he c
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5
  simp only [encT, Matrix.cons_val] at e0 e1 e2 e3 e4 e5
  exact Prod.ext (encH_inj h.1 h'.1 e0 e1) (Prod.ext (encH_inj h.2.1 h'.2.1 e2 e3)
    (encH_inj h.2.2 h'.2.2 e4 e5))

theorem rvt_child {F : (State × RowVS) → (Fin 3 → Option (State × RowVS)) → Prop}
    {c s : NTree (State × RowVS)} (ht : RVT F c) (hs : s ∈ c.children) : RVT F s := by
  obtain ⟨l, ch⟩ := c
  simp only [RVT] at ht
  exact ht.2.1 s hs

theorem rvt_sub {F : (State × RowVS) → (Fin 3 → Option (State × RowVS)) → Prop}
    {t u : NTree (State × RowVS)} (ht : RVT F t) (hu : InTree t u) : RVT F u := by
  induction hu with
  | here => exact ht
  | sub hs _ ih => exact ih (rvt_child ht hs)

/-- **The tree of the compute walk** (`kroots = 1`): the root is row `1`, every node is a row in
`[1, h]`, and every node's children carry exactly its `kids` triples. -/
theorem tree_of_goal (p : ℕ) [CharP K p] (rows : ℕ → RowVS) {h : ℕ} (hh : 1 ≤ h)
    (hsmall : ∀ i, 1 ≤ i → i ≤ h → SmallR p (rows i))
    (hG : ForestReconGoal (stVS K) (lblOf rows) 1 h) :
    ∃ t : NTree (State × RowVS), t.label = lblOf rows 1 ∧
      (∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ h ∧ u.label = lblOf rows i) ∧
      (∀ u, InTree t u → u.children.map (fun c => c.label.2.trip) = kids u.label.2) := by
  obtain ⟨ts, hlen, hrvt, hlab, hfan, -⟩ := hG
  obtain ⟨t, rfl⟩ : ∃ t, ts = [t] := by
    match ts, hlen with
    | [t], _ => exact ⟨t, rfl⟩
  have hmem : ∀ u, InTree t u → u ∈ bfsForest [t] := fun u hu =>
    (mem_bfsForest [t] u).mpr ⟨t, List.mem_singleton_self _, hu⟩
  have hrow : ∀ u, InTree t u → ∃ i, 1 ≤ i ∧ i ≤ h ∧ u.label = lblOf rows i := by
    intro u hu
    have hl : u.label ∈ (bfsForest [t]).map NTree.label := List.mem_map_of_mem (hmem u hu)
    rw [hlab] at hl
    obtain ⟨i, hi, hie⟩ := List.mem_map.mp hl
    rw [List.mem_range'_1] at hi
    exact ⟨i, hi.1, by omega, hie.symm⟩
  refine ⟨t, ?_, hrow, ?_⟩
  · have hb : bfsForest [t] = [t] ++ bfsForest ([t].flatMap NTree.children) :=
      bfsForest_cons_eq [t] (List.cons_ne_nil _ _)
    have hr : List.range' 1 h = 1 :: List.range' 2 (h - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
      rw [List.range'_succ]; rfl
    rw [hb, hr] at hlab
    simp only [List.singleton_append, List.map_cons, List.cons.injEq] at hlab
    exact hlab.1
  · intro u hu
    have hR : RVT (FV (K := K)) u := rvt_sub (hrvt t (List.mem_singleton_self _)) hu
    obtain ⟨i, hi1, hih, hui⟩ := hrow u hu
    have hfo : fanS u.label.1 = u.children.length := hfan u (hmem u hu)
    obtain ⟨l, ch⟩ := u
    simp only [RVT] at hR
    obtain ⟨hF, -, -⟩ := hR
    simp only [NTree.label, NTree.children] at hfo hui ⊢
    have hst : l.1 = l.2.st := hF.1
    have hlen : ch.length = (kids l.2).length := by rw [kids_length, ← hst, hfo]
    have hsl : SmallR p l.2 := by rw [hui]; exact hsmall i hi1 hih
    refine List.ext_getElem (by rw [List.length_map, hlen]) ?_
    intro j hj1 hj2
    rw [List.length_map] at hj1
    have hj3 : j < 3 := by have := fanS_le l.1; omega
    have hc := (hF.2 ⟨j, hj3⟩).2 (ch[j]).label (by
      simp [NTree.childLabel, NTree.childOpt, NTree.children, hj1])
    have hcin : InTree (NTree.node l ch) ch[j] := InTree.sub (List.getElem_mem hj1) (InTree.here _)
    obtain ⟨i', hi1', hih', hci⟩ := hrow _ (inTree_trans hu hcin)
    have hcs : SmallR p (ch[j]).label.2 := by rw [hci]; exact hsmall i' hi1' hih'
    have hk : (kids l.2).getD j trip0 = (kids l.2)[j] := by
      rw [List.getD_eq_getElem]
    rw [hk] at hc
    simp only [List.getElem_map]
    exact encT_inj (smallT_trip hcs) (smallT_kids hsl _ (List.getElem_mem _)) hc

end Tree

end

end Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVS
