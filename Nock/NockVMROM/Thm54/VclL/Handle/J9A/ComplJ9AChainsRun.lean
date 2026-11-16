/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AChainsRun.lean

  **J-9 A: the axis chains of a generated run.**  One chain per distinct `(root noun X, axis n)`; the
  consumers are the `s0B` rows on `(rn.s, n)` and the `s10B` rows on `(rn.e, n)`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChains
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AData

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains

/-! ## edit then slot -/

theorem slot_edit : ∀ a, 1 ≤ a → ∀ new old e : Noun, Noun.edit a new old = some e →
    Noun.slot a e = some new := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha new old e h
    by_cases h1 : a = 1
    · subst h1
      simp [Noun.edit] at h
      subst h
      simp [Noun.slot]
    · obtain ⟨k, hk, b, hb, rfl⟩ : ∃ k, 1 ≤ k ∧ ∃ b, b < 2 ∧ a = 2 * k + b :=
        ⟨a / 2, by omega, a % 2, by omega, by omega⟩
      rw [Nock.J9A.NounComp.edit_two_step k b new old hk hb] at h
      cases hs : Noun.slot (2 * k + (1 - b)) old with
      | none => rw [hs] at h; simp at h
      | some sib =>
        rw [hs] at h
        simp only [Option.bind_some] at h
        have h2 := ih k (by omega) hk _ _ _ h
        rw [Nock.J9A.NounComp.slot_double k b e hk hb, h2]
        have hb' : b = 0 ∨ b = 1 := by omega
        rcases hb' with rfl | rfl <;> simp

/-! ## keys, consumers -/

/-- The key `(X, n)` of an axis consumer row. -/
def axKey9 (l : LX9) : Option (Noun × ℕ) :=
  match l.chip with
  | .s0B => some (l.rn.s, l.n)
  | .s10B => some (l.rn.e, l.n)
  | _ => none

/-- The distinct keys. -/
def axKeys9 (rows : Array LX9) : List (Noun × ℕ) := (rows.toList.filterMap axKey9).dedup

/-- The consumer count of a key. -/
def muOf9 (rows : Array LX9) (k : Noun × ℕ) : ℕ := (rows.toList.filter fun l => axKey9 l = some k).length

theorem mem_axKeys9 {rows : Array LX9} {k : Noun × ℕ} :
    k ∈ axKeys9 rows ↔ ∃ l ∈ rows.toList, axKey9 l = some k := by
  simp [axKeys9, List.mem_filterMap]

theorem axKeys9_nodup (rows : Array LX9) : (axKeys9 rows).Nodup := List.nodup_dedup _

theorem muOf9_pos {rows : Array LX9} {k : Noun × ℕ} (hk : k ∈ axKeys9 rows) : 1 ≤ muOf9 rows k := by
  obtain ⟨l, hl, hlk⟩ := mem_axKeys9.1 hk
  unfold muOf9
  apply List.length_pos_of_mem (a := l)
  simp [hl, hlk]

theorem sum_ind {α : Type} [DecidableEq α] (a : α) :
    ∀ D : List α, D.Nodup → (D.map fun k => if a = k then 1 else 0).sum = if a ∈ D then 1 else 0 := by
  intro D
  induction D with
  | nil => intro _; simp
  | cons k D ih =>
    intro hD
    rw [List.nodup_cons] at hD
    simp only [List.map_cons, List.sum_cons, ih hD.2, List.mem_cons]
    by_cases hak : a = k
    · subst hak; simp [hD.1]
    · simp [hak]

theorem sum_filter_len {α β : Type} [DecidableEq α] (f : β → Option α) (D : List α) (hD : D.Nodup) :
    ∀ L : List β, (∀ l ∈ L, ∀ k, f l = some k → k ∈ D) →
      (D.map fun k => (L.filter fun l => f l = some k).length).sum = (L.filter fun l => (f l).isSome).length := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons l L ih =>
    intro hL
    have ih' := ih (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl'))
    have key : ∀ k : α, ((l :: L).filter fun l => f l = some k).length =
        (if f l = some k then 1 else 0) + (L.filter fun l => f l = some k).length := by
      intro k
      by_cases hk : f l = some k
      · simp [List.filter_cons, hk]; omega
      · simp [List.filter_cons, hk]
    simp only [key]
    rw [List.sum_map_add, ih']
    have hind : (D.map fun k => if f l = some k then 1 else 0).sum = if (f l).isSome then 1 else 0 := by
      cases hfl : f l with
      | none => simp
      | some a =>
        have := sum_ind a D hD
        have haD : a ∈ D := hL l (List.mem_cons_self ..) a hfl
        simp only [Option.some.injEq]
        rw [this]
        simp [haD]
    rw [hind]
    by_cases hs : (f l).isSome = true
    · simp [List.filter_cons, hs]; omega
    · simp [List.filter_cons, hs]

theorem sum_muOf9 (rows : Array LX9) :
    ((axKeys9 rows).map (muOf9 rows)).sum = (rows.toList.filter fun l => (axKey9 l).isSome).length := by
  have := sum_filter_len axKey9 (axKeys9 rows) (axKeys9_nodup rows) rows.toList
    (fun l hl k hk => mem_axKeys9.2 ⟨l, hl, hk⟩)
  exact this

/-! ## the chains -/

/-- **The honest axis chains of the rows**: one per distinct key. -/
def axChains9 (p nA : ℕ) [Fact (Nat.Prime p)] (H : Noun → ℕ × ℕ) (rows : Array LX9) : List (ComplJ9AAxisRows.ChainSpec (ZMod p)) :=
  (axKeys9 rows).map fun k =>
    chainOf H (decide (k.2 < p)) (idOf9 p nA H (fieldAx9 p rows) k.2) k.2 (muOf9 rows k) k.1

theorem axChains9_length (p nA : ℕ) [Fact (Nat.Prime p)] (H : Noun → ℕ × ℕ) (rows : Array LX9) :
    (axChains9 p nA H rows).length = (axKeys9 rows).length := by
  simp [axChains9]

theorem tableRows_length {F : Type} [Field F] (cs : List (ComplJ9AAxisRows.ChainSpec F)) :
    (ComplJ9AAxisRows.tableRows cs).length = (cs.map fun c => c.ls.length).sum := by
  induction cs with
  | nil => simp [ComplJ9AAxisRows.tableRows]
  | cons c cs ih =>
    simp [ComplJ9AAxisRows.tableRows, ih, ComplJ9AAxisRows.ChainSpec.rows]

theorem axChains9_table_length (p nA : ℕ) [Fact (Nat.Prime p)] (H : Noun → ℕ × ℕ) (rows : Array LX9) :
    (ComplJ9AAxisRows.tableRows (axChains9 p nA H rows)).length =
      ((axKeys9 rows).map fun k => (Nock.Atoms.limbs k.2).length).sum := by
  rw [tableRows_length]
  simp only [axChains9, List.map_map]
  rfl

section Run
variable {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}

/-- **Every key of a run is a real read** with `2^62 ≤` axis. -/
theorem axKeys9_read (h : genX R n s f = some (t, r)) {k : Noun × ℕ} (hk : k ∈ axKeys9 (rowsOfT9 t)) :
    2 ^ 62 ≤ k.2 ∧ ∃ Y, Noun.slot k.2 k.1 = some Y := by
  obtain ⟨l, hl, hlk⟩ := mem_axKeys9.1 hk
  have hsem := rowsOfT9_semN9 h l hl
  unfold axKey9 at hlk
  cases hc : l.chip <;> rw [hc] at hlk <;> simp at hlk
  · subst hlk
    simp only [SemN9, hc] at hsem
    obtain ⟨hs, hst, hft, hbig⟩ := hsem
    refine ⟨hbig, ?_⟩
    unfold RowNX.SemN at hs
    rw [hst] at hs
    obtain ⟨-, -, ax, hax, hsl⟩ := hs
    rw [hft] at hax
    have : l.n = ax := by injection hax
    rw [this]
    exact ⟨_, hsl⟩
  · subst hlk
    simp only [SemN9, hc] at hsem
    obtain ⟨hs, hst, hft, hbig⟩ := hsem
    refine ⟨hbig, ?_⟩
    unfold RowNX.SemN at hs
    rw [hst] at hs
    obtain ⟨-, -, -, -, a, ha, hed⟩ := hs
    rw [hft] at ha
    have : l.n = a := by injection ha
    rw [this]
    exact ⟨_, slot_edit a (by rw [← this]; omega) _ _ _ hed⟩

theorem axChains9_OK {p0 : ℕ} [Fact (Nat.Prime p0)] (nA : ℕ) (H : Noun → ℕ × ℕ)
    (h : genX R n s f = some (t, r)) (hpG : p0 = Nock.Atoms.p) (hH : ∀ a b, (H (.cell a b)).1 = 1) :
    ∀ c ∈ axChains9 p0 nA H (rowsOfT9 t), c.OK := by
  intro c hc
  simp only [axChains9, List.mem_map] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  obtain ⟨hbig, hY⟩ := axKeys9_read h hk
  apply chainOf_OK H _ _ _ _ _ hH _ hY
  · intro hd
    have := of_decide_eq_true hd
    rw [← hpG]; exact this
  · intro _
    rw [ZMod.ringChar_zmod_n]
    exact hp32_of_G hpG
  · have : (2 : ℕ) ^ 32 ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega

end Run

/-! ## split data -/

/-- The split values (field axis atoms), ids `nA + index`. -/
def splitVals9 (p : ℕ) (rows : Array LX9) : List ℕ := fieldAx9 p rows

section Run2
variable {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}

theorem splitVals9_range (h : genX R n s f = some (t, r)) {p : ℕ} (hpG : p = Nock.Atoms.p)
    (hax9 : ProgAxOK9A p t) : ∀ v ∈ splitVals9 p (rowsOfT9 t), 2 ^ 32 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  exact field_split_range hpG (fieldAx9_range h hax9 v hv)

end Run2

theorem idOf9_split {p nA : ℕ} {H : Noun → ℕ × ℕ} {rows : Array LX9} {k : ℕ}
    (hk : k ∈ splitVals9 p rows) :
    idOf9 p nA H (fieldAx9 p rows) k = nA + (splitVals9 p rows).idxOf k := by
  have hlt : k < p := by
    simp only [splitVals9, fieldAx9, List.mem_filter, decide_eq_true_eq] at hk
    exact hk.2
  exact idOf9_field hlt

section Axioms
/-! ## balanced read lists (C1): one chain per distinct key; limbs per distinct key / `s10B` row -/

open Nock.J9A.NounAx (top) in
/-- **The axis chains' segment reads, once per chain** (one chain per distinct key), axis `≥ 2`. -/
def axChainReadsK9 (rows : Array LX9) : List (Noun × ℕ) :=
  ((axKeys9 rows).flatMap fun k => ComplJ9AData.segReads k.2 (top k.2) k.1).filter fun q => 2 ≤ q.2

theorem walkDepthOK_axChainReadsK9 (rows : Array LX9) : ComplJ8Walk.WalkDepthOK (axChainReadsK9 rows) := by
  refine ComplJ9AData.walkDepthOK_of_lt fun x hx => ?_
  simp only [axChainReadsK9, List.mem_filter, List.mem_flatMap] at hx
  obtain ⟨⟨k, -, hl⟩, -⟩ := hx
  have h33 : (2 : ℕ) ^ 33 < 2 ^ 62 := by norm_num
  exact lt_trans (ComplJ9AData.segReads_lt _ _ _ x hl) h33

/-- **The atom-walk reads of the big axis atoms, balanced**: the limbs of each distinct key's axis (the chain's
consumer) and of each `s10B` row's atom (the `s10S` consumer). -/
def axReadsK9 (p : ℕ) (rows : Array LX9) : List (Noun × ℕ) :=
  ((axKeys9 rows).filter fun k => p ≤ k.2).flatMap (fun k => ComplJ9AData.limbReads k.2) ++
  (rows.toList.filter fun l => l.chip = .s10B ∧ p ≤ l.n).flatMap (fun l => ComplJ9AData.limbReads l.n)

theorem walkDepthOK_axReadsK9 {R : Nock.Jet.Registry} {n : ℕ} {s f : Noun} {t : NTree SkelX} {r : Noun}
    {p : ℕ} (h : genX R n s f = some (t, r)) (hax9 : ProgAxOK9A p t) :
    ComplJ8Walk.WalkDepthOK (axReadsK9 p (rowsOfT9 t)) := by
  have hcap := ComplJ9AData.bigAx9_cap h hax9
  refine ComplJ9AData.walkDepthOK_of_lt fun x hx => ?_
  simp only [axReadsK9, List.mem_append, List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hx
  have key : ∀ a, (∃ l ∈ (rowsOfT9 t).toList, (l.chip = .s0B ∨ l.chip = .s10B) ∧ l.n = a) → p ≤ a →
      ∀ y ∈ ComplJ9AData.limbReads a, y.2 < 2 ^ 62 := by
    intro a ha hp y hy
    have hmem : a ∈ bigAx9 p (rowsOfT9 t) := by
      simp only [bigAx9, List.mem_filter, decide_eq_true_eq]
      exact ⟨ComplJ9AData.mem_axAtoms9.2 ha, hp⟩
    simp only [ComplJ9AData.limbReads, List.mem_map] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ComplJ9AData.limbAxes_lt (hcap a hmem) y' hy'
  rcases hx with ⟨k, ⟨hk, hp⟩, hy⟩ | ⟨l, ⟨hl, hc, hp⟩, hy⟩
  · obtain ⟨l, hl, hlk⟩ := mem_axKeys9.1 hk
    have hn : (l.chip = .s0B ∨ l.chip = .s10B) ∧ l.n = k.2 := by
      unfold axKey9 at hlk
      cases hc : l.chip <;> rw [hc] at hlk <;> simp at hlk
      · subst hlk; exact ⟨Or.inl rfl, rfl⟩
      · subst hlk; exact ⟨Or.inr rfl, rfl⟩
    exact key k.2 ⟨l, hl, hn⟩ hp x hy
  · exact key l.n ⟨l, hl, Or.inr hc, rfl⟩ hp x hy

#print axioms slot_edit
#print axioms walkDepthOK_axChainReadsK9
#print axioms walkDepthOK_axReadsK9
#print axioms mem_axKeys9
#print axioms axKeys9_nodup
#print axioms muOf9_pos
#print axioms sum_ind
#print axioms sum_filter_len
#print axioms sum_muOf9
#print axioms axChains9_length
#print axioms tableRows_length
#print axioms axChains9_table_length
#print axioms axKeys9_read
#print axioms axChains9_OK
#print axioms splitVals9_range
#print axioms idOf9_split
end Axioms

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun
