/-
  Nock/NockVMROM/Thm54/VclL/Walk/WalkChain.lean

  **The chain 5-tuple from the forest walk, fed into
  VCL-L's chain soundness.**

  * `tree_inv`: along any `InTree` path of an RVT tree whose arities equal the state fanouts, every
    node carries an exported edge chain from its root's fp (`Inv`).
  * `chain_tuple_of_reconGoal`: from `ForestReconGoal` (+ its `fanout = children.length` conjunct)
    and the root gate on rows `1..kroots`, for every row `i`, side `b` and export key `k` of the
    row's fp: a root row `ρ` and an exported edge list `es` with (1) `|es| ≤ Dmax`,
    (2) `axis = axisFold sides` (no wrap), (3) fp root = `ρ`'s fp, (4) rootIdx = `ρ`'s rootIdx,
    (5) `chainEnd (fp ρ) es = target` — `PathModel.chain_record`'s five conjuncts.
  * `records_of_reconGoal` (the `path_record_genuine` twin): through the REAL `row_genuine` and
    `chain_sound_outside`, every walk record is the true slot of its root.
-/
import Nock.NockVMROM.Thm54.VclL.Walk.WalkInstance

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.WalkVCL

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.VclL
open Nock.ComputeTable (FP)

/-! ## 1. Invariant along a tree: an exported chain from the root's fp -/

section Model
variable {q : ℕ} {Kfp : Type} [Field Kfp] [DecidableEq Kfp]

theorem chainEnd_append_single (cur : FP Kfp) (es : List (Edge Kfp)) (e : Edge Kfp) :
    chainEnd cur (es ++ [e]) =
      (chainEnd cur es).bind fun c => if e.p = c then some (childOf e) else none := by
  induction es generalizing cur with
  | nil => simp [chainEnd]
  | cons a t ih =>
    simp only [List.cons_append, chainEnd]
    split_ifs
    · exact ih _
    · rfl

/-- Invariant of a node label `d` under the root label `R`. -/
def Inv (X : List (XKey Kfp)) (Dmax : ℕ) (R d : DT q Kfp) : Prop :=
  d.len.val < Dmax ∧ d.root = R.node ∧ d.ridx = R.ridx ∧
    ∃ es : List (Edge Kfp), (∀ e ∈ es, edgeKey e ∈ X) ∧ es.length = d.len.val ∧
      d.pre.val = axisFold (es.map Edge.side) ∧ chainEnd R.node es = some d.node

/-- The root gate's per-row content: prefix `1`, length `0`, fp root = own fp. -/
def RootOK (d : DT q Kfp) : Prop := d.pre = 1 ∧ d.len = 0 ∧ d.root = d.node

theorem bitZ_cast (b : Bool) : (bitZ b : ZMod q) = ((bitN b : ℕ) : ZMod q) := by
  cases b <;> simp [bitZ, bitN]

theorem val_axis [NeZero q] (p : ZMod q) (b : Bool) (hlt : 2 * p.val + bitN b < q) :
    (2 * p + bitZ b).val = 2 * p.val + bitN b := by
  have : (2 * p + bitZ b : ZMod q) = ((2 * p.val + bitN b : ℕ) : ZMod q) := by
    rw [bitZ_cast]; push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.val_natCast_of_lt hlt]

/-- **One step**: a node with the invariant and an exported key of its fp extends its chain at
side `b` to the key's `b`-target, with axis `2·pre + b` (no wrap). -/
theorem extend [NeZero q] {X : List (XKey Kfp)} {Dmax : ℕ} (hq : 2 ^ (Dmax + 1) ≤ q)
    {R d : DT q Kfp} (hI : Inv X Dmax R d) {k : XKey Kfp} (hk : k ∈ X) (hki : k.1 = d.node)
    (b : Bool) :
    ∃ es : List (Edge Kfp), (∀ e ∈ es, edgeKey e ∈ X) ∧ es.length = d.len.val + 1 ∧
      (2 * d.pre + bitZ b).val = axisFold (es.map Edge.side) ∧
      chainEnd R.node es = some (tgt k b) := by
  obtain ⟨hw, -, -, es, hesX, hlen, hpre, hend⟩ := hI
  refine ⟨es ++ [keyEdge k b], ?_, by simp [hlen], ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hesX e he
    · rw [List.mem_singleton] at he; subst he; exact hk
  · have hlt := axisFold_lt (es.map Edge.side)
    rw [List.length_map, hlen] at hlt
    have hbit : bitN b ≤ 1 := by cases b <;> simp [bitN]
    have h2 : 2 ^ (d.len.val + 1 + 1) ≤ 2 ^ (Dmax + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hlt' : 2 * d.pre.val + bitN b < q := by
      rw [pow_succ] at h2; omega
    rw [val_axis _ _ hlt', List.map_append, List.map_singleton, axisFold_append, hpre]
    cases b <;> rfl
  · rw [chainEnd_append_single, hend, Option.bind_some,
      if_pos (show (keyEdge k b).p = d.node from hki)]; rfl

theorem child_inv [NeZero q] {X : List (XKey Kfp)} {Dmax : ℕ} (hq : 2 ^ (Dmax + 1) ≤ q)
    {R d : DT q Kfp} (hI : Inv X Dmax R d) {k : XKey Kfp} (hk : k ∈ X) (hki : k.1 = d.node)
    {b : Bool} {c : LT q Kfp} (hc : ChildOK k b d c) (hcw : c.2.len.val < Dmax) :
    Inv X Dmax R c.2 := by
  obtain ⟨es, hesX, hlen, hax, hend⟩ := extend hq hI hk hki b
  obtain ⟨hn, hp, hr, hri, hl⟩ := hc
  have hdv : c.2.len.val = d.len.val + 1 := by
    have : c.2.len = ((d.len.val + 1 : ℕ) : ZMod q) := by
      rw [hl]; push_cast; rw [ZMod.natCast_zmod_val]
    rw [this, ZMod.val_natCast_of_lt]
    have h1 : Dmax < 2 ^ (Dmax + 1) :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
    have := hI.1
    omega
  exact ⟨hcw, by rw [hr, hI.2.1], by rw [hri, hI.2.2.1], es, hesX, by rw [hlen, hdv],
    by rw [hp, hax], by rw [hn, hend]⟩

theorem root_inv [NeZero q] {X : List (XKey Kfp)} {Dmax : ℕ} (hq1 : 1 < q) {d : DT q Kfp}
    (hw : d.len.val < Dmax) (hroot : RootOK d) : Inv X Dmax d d := by
  obtain ⟨hp, hl, hr⟩ := hroot
  refine ⟨hw, hr, rfl, [], by simp, by rw [hl]; simp, ?_, rfl⟩
  rw [hp, ZMod.val_one'' (by omega)]; rfl

/-- Children of a node with `children.length = fanout`: each is a `ChildOK` child of the node's
one export key. -/
theorem child_cases {X : List (XKey Kfp)} {Dmax : ℕ} (t : NTree (LT q Kfp))
    (hF : F X Dmax t.label (fun i => t.childLabel i))
    (hlen : t.children.length = fanout t.label.1) {u : NTree (LT q Kfp)} (hu : u ∈ t.children) :
    ∃ k ∈ X, k.1 = t.label.2.node ∧ ∃ b : Bool, ChildOK k b t.label.2 u.label := by
  rcases t with ⟨⟨s, d⟩, ch⟩
  simp only [NTree.label_node, NTree.children_node] at hF hlen hu ⊢
  obtain ⟨-, -, k, hk, hki, h1, h2⟩ := hF
  refine ⟨k, hk, hki, ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
  have hcl : ∀ (i : Fin 2), (i : ℕ) = j →
      (NTree.node (s, d) ch).childLabel i = some ch[j].label := by
    intro i hi
    simp [NTree.childLabel, NTree.childOpt, hi, hj]
  have pick : ∀ (b : Bool) (i : Fin 2), (i : ℕ) = j →
      OptOK k b d ((NTree.node (s, d) ch).childLabel i) → ChildOK k b d ch[j].label := by
    intro b i hi ho
    obtain ⟨c, hc, hok⟩ := ho
    rw [hcl i hi, Option.some.injEq] at hc
    rw [hc]; exact hok
  rcases s with ⟨s1, s2⟩
  have hjl : j < fanout (s1, s2) := hlen ▸ hj
  cases s1 <;> cases s2 <;> simp [fanout] at hjl h1 h2
  · subst hjl; exact ⟨true, pick true ⟨0, by norm_num⟩ rfl h2⟩
  · subst hjl; exact ⟨false, pick false ⟨0, by norm_num⟩ rfl h1⟩
  · rcases (by omega : j = 0 ∨ j = 1) with hj0 | hj1
    · subst hj0; exact ⟨false, pick false ⟨0, by norm_num⟩ rfl h1⟩
    · subst hj1; exact ⟨true, pick true ⟨1, by norm_num⟩ rfl h2⟩

theorem F_of_rvt {X : List (XKey Kfp)} {Dmax : ℕ} {t : NTree (LT q Kfp)} (h : RVT (F X Dmax) t) :
    F X Dmax t.label (fun i => t.childLabel i) := by
  rcases t with ⟨l, ch⟩; unfold RVT at h; exact h.1

/-- **Tree invariant** down any `InTree` path, given arities = state fanouts. -/
theorem tree_inv [NeZero q] {X : List (XKey Kfp)} {Dmax : ℕ} (hq : 2 ^ (Dmax + 1) ≤ q)
    {R : DT q Kfp} {t u : NTree (LT q Kfp)} (hin : InTree t u) :
    RVT (F X Dmax) t → (∀ v, InTree t v → v.children.length = fanout v.label.1) →
    Inv X Dmax R t.label.2 → Inv X Dmax R u.label.2 := by
  induction hin with
  | here => intro _ _ h; exact h
  | @sub c s v hs _ ih =>
    intro hrvt hfan hI
    have hrvts : RVT (F X Dmax) s := by
      rcases c with ⟨l, ch⟩; unfold RVT at hrvt; exact hrvt.2.1 s hs
    obtain ⟨k, hk, hki, b, hok⟩ := child_cases c (F_of_rvt hrvt) (hfan c (InTree.here c)) hs
    exact ih hrvts (fun v hv => hfan v (InTree.sub hs hv))
      (child_inv hq hI hk hki hok (F_of_rvt hrvts).1)

/-! ## 2. The chain 5-tuple from the forest -/

/-- **The chain 5-tuple at every BFS node, every side, every export key of the node's fp**. -/
theorem walk_chain_record [NeZero q] {X : List (XKey Kfp)} {Dmax : ℕ} (hq : 2 ^ (Dmax + 1) ≤ q)
    (ts : List (NTree (LT q Kfp))) (hrvt : ∀ t ∈ ts, RVT (F X Dmax) t)
    (hroot : ∀ t ∈ ts, RootOK t.label.2)
    (hfan : ∀ t ∈ bfsForest ts, fanout t.label.1 = t.children.length) :
    ∀ u ∈ bfsForest ts, ∃ r ∈ ts, ∀ k ∈ X, k.1 = u.label.2.node → ∀ b : Bool,
      ∃ es : List (Edge Kfp), (∀ e ∈ es, edgeKey e ∈ X) ∧ es.length ≤ Dmax ∧
        (2 * u.label.2.pre + bitZ b).val = axisFold (es.map Edge.side) ∧
        u.label.2.root = r.label.2.node ∧ u.label.2.ridx = r.label.2.ridx ∧
        chainEnd r.label.2.node es = some (tgt k b) := by
  have hq1 : 1 < q := lt_of_lt_of_le (Nat.one_lt_two_pow (by omega)) hq
  intro u hu
  obtain ⟨r, hr, hru⟩ := (mem_bfsForest ts u).mp hu
  have hfan' : ∀ v, InTree r v → v.children.length = fanout v.label.1 := fun v hv =>
    (hfan v ((mem_bfsForest ts v).mpr ⟨r, hr, hv⟩)).symm
  have hI0 : Inv X Dmax r.label.2 r.label.2 :=
    root_inv hq1 (F_of_rvt (hrvt r hr)).1 (hroot r hr)
  have hI := tree_inv hq hru (hrvt r hr) hfan' hI0
  refine ⟨r, hr, fun k hk hki b => ?_⟩
  obtain ⟨es, hesX, hlen, hax, hend⟩ := extend hq hI hk hki b
  exact ⟨es, hesX, by rw [hlen]; exact hI.1, hax, hI.2.1, hI.2.2.1, hend⟩

theorem lab_at {ts : List (NTree (LT q Kfp))} {lbl : ℕ → LT q Kfp} {h : ℕ}
    (hlab : (bfsForest ts).map NTree.label = (List.range' 1 h).map lbl) {j : ℕ} (hj : j < h) :
    ∃ t ∈ bfsForest ts, t.label = lbl (j + 1) ∧ (bfsForest ts)[j]? = some t := by
  have e := congrArg (fun l => l[j]?) hlab
  simp only [List.getElem?_map] at e
  rw [List.getElem?_range' hj] at e
  rcases hb : (bfsForest ts)[j]? with _ | t
  · rw [hb] at e; simp at e
  · rw [hb] at e
    refine ⟨t, List.mem_of_getElem? hb, ?_, rfl⟩
    simp only [Option.map_some, Option.some.injEq] at e
    rw [e]; congr 1; omega

/-- The forest's roots are the rows `1..kroots`. -/
theorem roots_are_rows {ts : List (NTree (LT q Kfp))} {lbl : ℕ → LT q Kfp} {kroots h : ℕ}
    (hlen : ts.length = kroots) (hk : 1 ≤ kroots)
    (hlab : (bfsForest ts).map NTree.label = (List.range' 1 h).map lbl) :
    ∀ r ∈ ts, ∃ i, 1 ≤ i ∧ i ≤ kroots ∧ r.label = lbl i := by
  have hne : ts ≠ [] := by intro e; rw [e] at hlen; simp at hlen; omega
  have hsplit := bfsForest_eq_append_flatMap ts hne
  have hlenB : (bfsForest ts).length = h := by
    have := congrArg List.length hlab; simpa using this
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  have hjB : j < (bfsForest ts).length := by
    rw [hsplit, List.length_append]; omega
  obtain ⟨t', -, hl, hg⟩ := lab_at hlab (j := j) (by omega)
  have : (bfsForest ts)[j]? = some ts[j] := by
    rw [hsplit, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  rw [this, Option.some.injEq] at hg
  exact ⟨j + 1, by omega, by omega, by rw [hg, hl]⟩

/-- **The chain 5-tuple per committed row, from `ForestReconGoal` (+ its fanout conjunct) and the
root gate on rows `1..kroots`.**  For every row `i`, side `b` and export key `k` of the row's fp
there is a root row `ρ ∈ [1, kroots]` and an exported edge list `es` with
(1) `|es| ≤ Dmax`, (2) `axis(i, b) = axisFold sides`, (3) fp root = `ρ`'s fp,
(4) rootIdx = `ρ`'s rootIdx, (5) `chainEnd (fp ρ) es = target`. -/
theorem chain_tuple_of_reconGoal [NeZero q] {X : List (XKey Kfp)} {Dmax : ℕ}
    (hq : 2 ^ (Dmax + 1) ≤ q) {lbl : ℕ → LT q Kfp} {kroots h : ℕ} (hk : 1 ≤ kroots)
    (hrootGate : ∀ i, 1 ≤ i → i ≤ kroots → RootOK (lbl i).2)
    (hG : ForestReconGoal (stateSep (q := q) X Dmax) lbl kroots h) :
    ∀ i, 1 ≤ i → i ≤ h → ∀ k ∈ X, k.1 = (lbl i).2.node → ∀ b : Bool,
      ∃ ρ, 1 ≤ ρ ∧ ρ ≤ kroots ∧ ∃ es : List (Edge Kfp), (∀ e ∈ es, edgeKey e ∈ X) ∧
        es.length ≤ Dmax ∧ (2 * (lbl i).2.pre + bitZ b).val = axisFold (es.map Edge.side) ∧
        (lbl i).2.root = (lbl ρ).2.node ∧ (lbl i).2.ridx = (lbl ρ).2.ridx ∧
        chainEnd (lbl ρ).2.node es = some (tgt k b) := by
  obtain ⟨ts, hlen, hrvt, hlab, hfan, -⟩ := hG
  have hroots := roots_are_rows hlen hk hlab
  have hroot : ∀ t ∈ ts, RootOK t.label.2 := by
    intro t ht
    obtain ⟨i, hi1, hik, he⟩ := hroots t ht
    rw [he]; exact hrootGate i hi1 hik
  intro i hi1 hih k hk hki b
  obtain ⟨u, hu, hl, -⟩ := lab_at hlab (j := i - 1) (by omega)
  have hi : i - 1 + 1 = i := by omega
  rw [hi] at hl
  rw [← hl] at hki ⊢
  obtain ⟨r, hr, hrec⟩ := walk_chain_record hq ts hrvt hroot (fun t ht => hfan t ht) u hu
  obtain ⟨ρ, hρ1, hρk, hρ⟩ := hroots r hr
  obtain ⟨es, h1, h2, h3, h4, h5, h6⟩ := hrec k hk hki b
  rw [hρ] at h4 h5 h6
  exact ⟨ρ, hρ1, hρk, es, h1, h2, h3, h4, h5, h6⟩

end Model

/-! ## 3. Fed into VCL-L's `chain_sound_outside` (the `path_record_genuine` twin) -/

section Use
variable {q : ℕ} {Kfp : Type} [Field Kfp] [Fintype Kfp] [DecidableEq Kfp] [Algebra (ZMod q) Kfp]

/-- Every key the walk consumes is exported by the cell table (what `ExportBalanced` gives the
path chip today, `edge_exported_of_balanced`). -/
def KeysExported (tb : List (CellRow q Kfp)) (X : List (XKey Kfp)) : Prop :=
  ∀ k ∈ X, ∃ c ∈ tb, c.b0.idx = k.2.2.2 ∧ c.p = k.1 ∧ c.l = k.2.1 ∧ c.r = k.2.2.1

/-- The root gate, with the root row's own consume witness: `rootIdx = cellIdx`. -/
def RootGate (X : List (XKey Kfp)) (lbl : ℕ → LT q Kfp) (kroots : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ kroots → RootOK (lbl i).2 ∧
    ∃ k ∈ X, k.1 = (lbl i).2.node ∧ (lbl i).2.ridx = (k.2.2.2 : ZMod q)

/-- Every record a row emits (side `b`, the row's own key `k`) is the true slot of its root. -/
def AllRecordsGenuine (z : Kfp) (tb : List (CellRow q Kfp)) (X : List (XKey Kfp))
    (lbl : ℕ → LT q Kfp) (h : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ h → ∀ k ∈ X, k.1 = (lbl i).2.node → ∀ b : Bool,
    ∃ (ri : ℕ) (rt nn : Noun), (lbl i).2.ridx = (ri : ZMod q) ∧
      preZNounOfTable (tb.map (·.b0)) ri = some rt ∧
      (lbl i).2.root = GlobalCarryRecognizer.enc z rt ∧
      tgt k b = GlobalCarryRecognizer.enc z nn ∧
      Noun.slot (2 * (lbl i).2.pre + bitZ b).val rt = some nn

/-- **S1 (walk side): ForestReconGoal (+ arity conjunct) + root gate + exported keys, outside
T2 ∪ the dyck-root event ⟹ every walk record is genuine**, through the REAL `row_genuine` and
`chain_sound_outside`. -/
theorem records_of_reconGoal [Fact q.Prime] (hq : 2 ^ 63 < q) {z : Kfp} (hz : z ≠ 0)
    {tb : List (CellRow q Kfp)} {vl : List (VKey Kfp)} (h : TableAccepts z tb vl)
    (hT2 : z ∉ tableBadSeeds fuelChip (tb.map (·.b0)) [])
    (hdy : z ∉ cellDyckRootSeeds fuelChip (tb.map (·.b0)))
    {X : List (XKey Kfp)} (hX : KeysExported tb X)
    {lbl : ℕ → LT q Kfp} {kroots hh : ℕ} (hk : 1 ≤ kroots) (hRG : RootGate X lbl kroots)
    (hG : ForestReconGoal (stateSep (q := q) X 62) lbl kroots hh) :
    AllRecordsGenuine z tb X lbl hh := by
  have hq' : 2 ^ (62 + 1) ≤ q := by omega
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  intro i hi1 hih k hkX hki b
  obtain ⟨ρ, hρ1, hρk, es, hesX, -, hax, hroot, hridx, hend⟩ :=
    chain_tuple_of_reconGoal hq' hk (fun j hj1 hjk => (hRG j hj1 hjk).1) hG i hi1 hih k hkX hki b
  obtain ⟨-, k0, hk0, hk0n, hk0i⟩ := hRG ρ hρ1 hρk
  obtain ⟨c, hc, hci, hcp, -, -⟩ := hX k0 hk0
  obtain ⟨L, R, hdec, hp, -⟩ := row_genuine hq hz h hc
  have hpe : (lbl ρ).2.node = GlobalCarryRecognizer.enc z (.cell L R) := by
    rw [← hk0n, ← hcp, hp]
  rw [hpe] at hend
  have hexp : ∀ e ∈ es, EdgeExported tb e := by
    intro e he
    obtain ⟨c', hc', h1, h2, h3, h4⟩ := hX _ (hesX e he)
    exact ⟨c', hc', h1, h2, h3, h4⟩
  obtain ⟨nn, hnn, hslot⟩ := chain_sound_outside hq hz h [] hT2 hdy hdec es hexp hend
  refine ⟨c.b0.idx, .cell L R, nn, ?_, hdec, by rw [hroot, hpe], hnn.symm, ?_⟩
  · rw [hridx, hk0i, hci]
  · rw [hax]; exact hslot

end Use

end Nock.NockVMROM.Thm54.VclL.WalkVCL
