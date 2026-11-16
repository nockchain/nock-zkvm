/-
  Nock/NockVMROM/Thm54/VclL/Chips/HonestMemGenPath.lean

  **The honest path rows from the generator.**

  `pathTable z cells reads` is the path chip's row list: one chain per DISTINCT deep read `(root, axis)`
  (`GenPathRows.pathReads` of the path-kind reads `d.preads` (SHD-A)), one row per edge `pathSteps root (axisBits axis)` (the cell left, the side taken):
  `side`, `first` / `last`, the running `len` and axis accumulator `acc = axisFold (sides so far)`, the
  multiplicity `m = reads.count` on the last row, the serials, the six certificate bits of `62 − len`, the root
  and edge fingerprints at the seed `z`.  `pathTable_baseFacts` / `pathTable_rowFacts` discharge `PathBaseFacts`
  and the row-level half of `PathMixedFacts` (root, `p_step = childOf`) for the flattened table.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemGenCell

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

open Nock
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.T0Tower
open Module
open scoped Polynomial

noncomputable section

/-! ## 1. The walk's steps -/

theorem pathSteps_length_le : ∀ (n : Noun) (bits : List Bool), (pathSteps n bits).length ≤ bits.length
  | _, [] => by simp [pathSteps]
  | .cell l r, b :: bs => by
    simp only [pathSteps, List.length_cons]
    have := pathSteps_length_le (if b then r else l) bs
    omega
  | .atom _, _ :: _ => by simp [pathSteps]

theorem pathSteps_head : ∀ (n : Noun) (bits : List Bool) (h : 0 < (pathSteps n bits).length),
    (pathSteps n bits)[0].1 = n
  | _, [], h => by simp [pathSteps] at h
  | .cell l r, b :: bs, h => by simp [pathSteps]
  | .atom _, _ :: _, h => by simp [pathSteps] at h

theorem pathSteps_next : ∀ (n : Noun) (bits : List Bool) (k : ℕ) (h : k + 1 < (pathSteps n bits).length),
    (pathSteps n bits)[k + 1].1 =
      (if (pathSteps n bits)[k].2 then tlN (pathSteps n bits)[k].1 else hdN (pathSteps n bits)[k].1)
  | _, [], k, h => by simp [pathSteps] at h
  | .cell l r, b :: bs, 0, h => by
    simp only [pathSteps] at h ⊢
    have h0 : 0 < (pathSteps (if b then r else l) bs).length := by
      simp only [List.length_cons] at h; omega
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [pathSteps_head _ _ h0]
    cases b <;> simp [hdN, tlN]
  | .cell l r, b :: bs, k + 1, h => by
    simp only [pathSteps] at h ⊢
    simp only [List.getElem_cons_succ]
    exact pathSteps_next _ _ k (by simp only [List.length_cons] at h; omega)
  | .atom _, _ :: _, k, h => by simp [pathSteps] at h

/-! ## 2. One chain's rows -/

section Chain
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **Row `k` of the chain of `steps`** (the walk from `root`), multiplicity `mult` on the last row. -/
def chainRow (z : Quad (algebraMap F K δF)) (cells : List Noun) (root : Noun) (mult : ℕ)
    (steps : List (Noun × Bool)) (k : ℕ) : PathVals F (Quad (algebraMap F K δF)) where
  side := if (steps.getD k (.atom 0, false)).2 then 1 else 0
  first := if k = 0 then 1 else 0
  last := if k + 1 = steps.length then 1 else 0
  len := ((k + 1 : ℕ) : F)
  acc := ((axisFold ((steps.map Prod.snd).take (k + 1)) : ℕ) : F)
  m := if k + 1 = steps.length then (mult : F) else 0
  cellIdx := (cells.idxOf (steps.getD k (.atom 0, false)).1 : F)
  rootIdx := (cells.idxOf root : F)
  bit := fun i => if (62 - steps.length).testBit i then 1 else 0
  root := GlobalCarryRecognizer.enc z root
  p := GlobalCarryRecognizer.enc z (steps.getD k (.atom 0, false)).1
  l := GlobalCarryRecognizer.enc z (hdN (steps.getD k (.atom 0, false)).1)
  r := GlobalCarryRecognizer.enc z (tlN (steps.getD k (.atom 0, false)).1)
  xConsInv := 0
  pProvInv := 0
  xAcc := 0
  pAcc := 0

/-- The rows of one chain. -/
def chainRows (z : Quad (algebraMap F K δF)) (cells : List Noun) (root : Noun) (mult : ℕ)
    (steps : List (Noun × Bool)) : List (PathVals F (Quad (algebraMap F K δF))) :=
  (List.range steps.length).map (chainRow δF z cells root mult steps)

/-- **The row-local facts** a path row satisfies (bits of the chain's cert, root, mixed `root_first`). -/
structure PathRowGood {F : Type} [Field F] {Q : Type} (x : PathVals F Q) : Prop where
  side_bool : x.side * (x.side - 1) = 0
  first_bool : x.first * (x.first - 1) = 0
  last_bool : x.last * (x.last - 1) = 0
  len_first : x.first * (x.len - 1) = 0
  acc_first : x.first * ((x.acc - 2) - x.side) = 0
  root_first_idx : x.first * (x.rootIdx - x.cellIdx) = 0
  cert : x.last * ((x.len + ∑ k ∈ Finset.range 6, (2 : F) ^ k * x.bit k) - 62) = 0
  m_mask : (1 - x.last) * x.m = 0
  bit_bool : ∀ k < 6, x.bit k * (x.bit k - 1) = 0

/-- The step relation between a row and its successor. -/
def PathStep (a b : PathVals F (Quad (algebraMap F K δF))) : Prop :=
  b.first = a.last ∧ (a.last = 0 →
    (b.len - a.len) - 1 = 0 ∧ (b.acc - 2 * a.acc) - b.side = 0 ∧ b.rootIdx = a.rootIdx ∧
      b.root = a.root ∧ b.p = childOf δF a)

variable {δF}

theorem chainRows_getElem (z : Quad (algebraMap F K δF)) (cells : List Noun) (root : Noun) (mult : ℕ)
    (steps : List (Noun × Bool)) {k : ℕ} (hk : k < (chainRows δF z cells root mult steps).length) :
    (chainRows δF z cells root mult steps)[k] = chainRow δF z cells root mult steps k := by
  simp [chainRows]

theorem chainRows_length (z : Quad (algebraMap F K δF)) (cells : List Noun) (root : Noun) (mult : ℕ)
    (steps : List (Noun × Bool)) : (chainRows δF z cells root mult steps).length = steps.length := by
  simp [chainRows]

end Chain

section ChainFacts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δF : F}
  [Fact (¬ IsSquare (algebraMap F K δF))] (z : Quad (algebraMap F K δF)) (cells : List Noun)
  (root : Noun) (mult : ℕ) (steps : List (Noun × Bool))

theorem axisFold_take_succ (bs : List Bool) (k : ℕ) (hk : k + 1 < bs.length) :
    axisFold (bs.take (k + 2)) = 2 * axisFold (bs.take (k + 1)) + (if bs[k + 1] then 1 else 0) := by
  have : bs.take (k + 2) = bs.take (k + 1) ++ [bs[k + 1]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  rw [this, axisFold_append]

theorem chainRow_rowGood (hroot : ∀ h : 0 < steps.length, steps[0].1 = root) (hL : steps.length ≤ 62)
    {k : ℕ} (hk : k < steps.length) :
    PathRowGood (chainRow δF z cells root mult steps k) := by
  have hg : steps.getD k (.atom 0, false) = steps[k] := List.getD_eq_getElem _ _ hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [chainRow]; split_ifs <;> simp
  · simp only [chainRow]; split_ifs <;> simp
  · simp only [chainRow]; split_ifs <;> simp
  · simp only [chainRow]; split_ifs with h
    · subst h; simp
    · simp
  · by_cases h : k = 0
    · subst h
      have hne : steps ≠ [] := by intro h; subst h; simp at hk
      obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hb : ∀ b : Bool, ((axisFold [b] : ℕ) : F) - 2 - (if b = true then 1 else 0) = 0 := by
        intro b; cases b <;> simp [axisFold] <;> norm_num
      simp only [chainRow, if_true, one_mul, List.map_cons, List.take_succ_cons, List.take_zero,
        List.getD_cons_zero]
      exact hb c.2
    · simp [chainRow, h]
  · simp only [chainRow]; split_ifs with h
    · subst h
      rw [hg, hroot hk]; simp
    · simp
  · simp only [chainRow]; split_ifs with h
    · have hbits : (62 - steps.length) < 2 ^ 6 := by omega
      have := sum_testBit_cast (F := F) 6 (62 - steps.length) hbits
      simp only [h]
      rw [← this]
      have e : (steps.length : F) + ((62 - steps.length : ℕ) : F) = 62 := by
        rw [← Nat.cast_add, show steps.length + (62 - steps.length) = 62 by omega]; norm_num
      rw [e]; simp
    · simp
  · simp only [chainRow]; split_ifs <;> simp
  · intro i _; simp only [chainRow]; split_ifs <;> simp

theorem chainRow_step (hnext : ∀ (k : ℕ) (h : k + 1 < steps.length), steps[k + 1].1 =
      (if steps[k].2 then tlN steps[k].1 else hdN steps[k].1))
    {k : ℕ} (hk : k + 1 < steps.length) :
    PathStep δF (chainRow δF z cells root mult steps k) (chainRow δF z cells root mult steps (k + 1)) := by
  have hk0 : k < steps.length := by omega
  have hg0 : steps.getD k (.atom 0, false) = steps[k] := List.getD_eq_getElem _ _ hk0
  have hg1 : steps.getD (k + 1) (.atom 0, false) = steps[k + 1] := List.getD_eq_getElem _ _ hk
  have hlast : ¬ (k + 1 = steps.length) := by omega
  refine ⟨?_, fun _ => ⟨?_, ?_, rfl, rfl, ?_⟩⟩
  · simp [chainRow, hlast]
  · simp only [chainRow]; push_cast; ring
  · simp only [chainRow]
    rw [hg1]
    have hmap : ((steps.map Prod.snd).take (k + 1 + 1)) = (steps.map Prod.snd).take (k + 2) := rfl
    rw [hmap, axisFold_take_succ (steps.map Prod.snd) k (by simpa using hk)]
    simp only [List.getElem_map]
    push_cast
    split_ifs <;> simp
  · simp only [chainRow, childOf, hg0, hg1]
    rw [hnext k hk]
    cases hs : steps[k].2
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, liftQ, map_zero, zero_mul, add_zero]
    · simp only [hs, ↓reduceIte, liftQ, map_one, one_mul, add_sub_cancel]

end ChainFacts

/-! ## 3. The whole table -/

section Table
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δF : F}
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **A good list of path rows**: row-local facts, the step relation between neighbours, the first row
starts a chain and the last row ends one. -/
def PathGood (l : List (PathVals F (Quad (algebraMap F K δF)))) : Prop :=
  (∀ x ∈ l, PathRowGood x ∧ (x.first = 1 → x.root = x.p)) ∧ List.IsChain (PathStep δF) l ∧
    (∀ y ∈ l.head?, y.first = 1) ∧ (∀ x ∈ l.getLast?, x.last = 1)

theorem PathGood.nil : PathGood (δF := δF) ([] : List (PathVals F (Quad (algebraMap F K δF)))) :=
  ⟨by simp, List.isChain_nil, by simp, by simp⟩

theorem PathGood.append {l₁ l₂ : List (PathVals F (Quad (algebraMap F K δF)))}
    (h₁ : PathGood l₁) (h₂ : PathGood l₂) : PathGood (l₁ ++ l₂) := by
  obtain ⟨a1, b1, c1, d1⟩ := h₁
  obtain ⟨a2, b2, c2, d2⟩ := h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact a1 x h
    · exact a2 x h
  · refine List.isChain_append.mpr ⟨b1, b2, fun x hx y hy => ?_⟩
    have hx1 := d1 x hx
    have hy1 := c2 y hy
    refine ⟨by rw [hx1, hy1], fun h0 => ?_⟩
    rw [hx1] at h0
    exact absurd h0 one_ne_zero
  · intro y hy
    rcases hl : l₁ with _ | ⟨a, t⟩
    · subst hl
      simp only [List.nil_append] at hy
      exact c2 y hy
    · rw [hl] at hy
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact c1 _ (by rw [hl]; rfl)
  · intro x hx
    rcases hl : l₂ with _ | ⟨a, t⟩
    · subst hl
      simp only [List.append_nil] at hx
      exact d1 x hx
    · rw [hl] at hx
      have : (l₁ ++ a :: t).getLast? = (a :: t).getLast? := by
        rw [List.getLast?_append]; simp [List.getLast?_cons]
      rw [this] at hx
      exact d2 x (by rw [hl]; exact hx)

theorem PathGood.flatMap {α : Type} (f : α → List (PathVals F (Quad (algebraMap F K δF)))) :
    ∀ (cs : List α), (∀ c ∈ cs, PathGood (f c)) → PathGood (cs.flatMap f)
  | [], _ => by simpa using PathGood.nil
  | c :: cs, h => by
    rw [List.flatMap_cons]
    exact (h c (List.mem_cons_self ..)).append
      (PathGood.flatMap f cs fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

variable (z : Quad (algebraMap F K δF)) (cells : List Noun) (root : Noun) (mult : ℕ)
  (steps : List (Noun × Bool))

theorem chainRows_good (hroot : ∀ h : 0 < steps.length, steps[0].1 = root)
    (hnext : ∀ (k : ℕ) (h : k + 1 < steps.length), steps[k + 1].1 =
      (if steps[k].2 then tlN steps[k].1 else hdN steps[k].1))
    (hL : steps.length ≤ 62) : PathGood (chainRows δF z cells root mult steps) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hk' : k < steps.length := List.mem_range.mp hk
    refine ⟨chainRow_rowGood z cells root mult steps hroot hL hk', fun hf => ?_⟩
    have h0 : k = 0 := by
      by_contra hne
      simp [chainRow, hne] at hf
    subst h0
    have hg : steps.getD 0 (.atom 0, false) = steps[0] := List.getD_eq_getElem _ _ hk'
    simp only [chainRow, hg, hroot hk']
  · rw [List.isChain_iff_getElem]
    intro i hi
    rw [chainRows_length] at hi
    rw [chainRows_getElem z cells root mult steps (by rw [chainRows_length]; omega),
      chainRows_getElem z cells root mult steps (by rw [chainRows_length]; omega)]
    exact chainRow_step z cells root mult steps hnext hi
  · intro y hy
    rcases hs : steps with _ | ⟨c, cs⟩
    · subst hs; simp [chainRows] at hy
    · subst hs
      simp only [chainRows, List.length_cons, List.range_succ_eq_map, List.map_cons, List.head?_cons,
        Option.mem_def, Option.some.injEq] at hy
      subst hy
      simp [chainRow]
  · intro x hx
    rcases hs : steps with _ | ⟨c, cs⟩
    · subst hs; simp [chainRows] at hx
    · subst hs
      have : (chainRows δF z cells root mult (c :: cs)).getLast? =
          some (chainRow δF z cells root mult (c :: cs) cs.length) := by
        simp [chainRows, List.range_succ, List.getLast?_append]
      rw [this] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      subst hx
      simp [chainRow]

end Table

section TableFacts
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] {δF : F}
  [Fact (¬ IsSquare (algebraMap F K δF))]

theorem last_cases {Q : Type} (x : PathVals F Q) (h : x.last * (x.last - 1) = 0) :
    x.last = 0 ∨ x.last = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

/-- **`PathBaseFacts` of a good list** read by position. -/
theorem pathBaseFacts_of_good (l : List (PathVals F (Quad (algebraMap F K δF)))) (hg : PathGood l)
    (dflt : PathVals F (Quad (algebraMap F K δF))) {N : ℕ} (hN : N = l.length) (i : Fin N) :
    PathBaseFacts (fun j : Fin N => l.getD j dflt) i := by
  subst hN
  obtain ⟨hrow, hchain, hhead, hlast⟩ := hg
  have hi : (i : ℕ) < l.length := i.isLt
  have hx : ∀ j (hj : j < l.length), l.getD j dflt = l[j] := fun j hj => List.getD_eq_getElem _ _ hj
  have hrg := (hrow (l[(i : ℕ)]'hi) (List.getElem_mem hi)).1
  have hstep : ∀ hi' : (i : ℕ) + 1 < l.length, PathStep δF l[(i : ℕ)] l[(i : ℕ) + 1] := fun hi' =>
    List.isChain_iff_getElem.mp hchain i hi'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (l.getD i dflt).side * _ = 0; rw [hx i hi]; exact hrg.side_bool
  · show (l.getD i dflt).first * _ = 0; rw [hx i hi]; exact hrg.first_bool
  · show (l.getD i dflt).last * _ = 0; rw [hx i hi]; exact hrg.last_bool
  · intro h0
    show (l.getD i dflt).first = 1
    rw [hx i hi]
    have h0' : (i : ℕ) = 0 := h0
    have hh : l.head? = some l[(i : ℕ)] := by
      rcases l with _ | ⟨a, t⟩
      · simp at hi
      · simp only [h0']; rfl
    exact hhead _ (by rw [hh]; rfl)
  · intro hl
    show (l.getD i dflt).last = 1
    rw [hx i hi]
    have hl' : (i : ℕ) + 1 = l.length := hl
    have : l.getLast? = some l[(i : ℕ)] := by
      rw [List.getLast?_eq_getElem?]
      have e : l.length - 1 = (i : ℕ) := by omega
      rw [e]; exact List.getElem?_eq_getElem hi
    exact hlast _ (by rw [this]; rfl)
  · intro hi'
    show (l.getD ((i : ℕ) + 1) dflt).first = (l.getD i dflt).last
    rw [hx _ hi', hx i hi]; exact (hstep hi').1
  · show (l.getD i dflt).first * _ = 0; rw [hx i hi]; exact hrg.len_first
  · intro hi'
    show (1 - (l.getD i dflt).last) * (((l.getD ((i : ℕ) + 1) dflt).len - (l.getD i dflt).len) - 1) = 0
    rw [hx _ hi', hx i hi]
    rcases last_cases _ hrg.last_bool with h | h
    · rw [h, (hstep hi').2 h |>.1]; simp
    · rw [h]; simp
  · show (l.getD i dflt).first * _ = 0; rw [hx i hi]; exact hrg.acc_first
  · intro hi'
    show (1 - (l.getD i dflt).last) * (((l.getD ((i : ℕ) + 1) dflt).acc - 2 * (l.getD i dflt).acc) -
      (l.getD ((i : ℕ) + 1) dflt).side) = 0
    rw [hx _ hi', hx i hi]
    rcases last_cases _ hrg.last_bool with h | h
    · rw [h, (hstep hi').2 h |>.2.1]; simp
    · rw [h]; simp
  · show (l.getD i dflt).first * _ = 0; rw [hx i hi]; exact hrg.root_first_idx
  · intro hi'
    show (1 - (l.getD i dflt).last) * ((l.getD ((i : ℕ) + 1) dflt).rootIdx - (l.getD i dflt).rootIdx) = 0
    rw [hx _ hi', hx i hi]
    rcases last_cases _ hrg.last_bool with h | h
    · rw [h, (hstep hi').2 h |>.2.2.1]; simp
    · rw [h]; simp
  · show (l.getD i dflt).last * _ = 0; rw [hx i hi]; exact hrg.cert
  · show (1 - (l.getD i dflt).last) * (l.getD i dflt).m = 0; rw [hx i hi]; exact hrg.m_mask
  · intro k hk
    show (l.getD i dflt).bit k * _ = 0; rw [hx i hi]; exact hrg.bit_bool k hk

/-- The row-level half of `PathMixedFacts` of a good list. -/
theorem pathMixedRows_of_good (l : List (PathVals F (Quad (algebraMap F K δF)))) (hg : PathGood l)
    (dflt : PathVals F (Quad (algebraMap F K δF))) :
    (∀ j < l.length, (l.getD j dflt).first = 1 → (l.getD j dflt).root = (l.getD j dflt).p) ∧
    (∀ j, j + 1 < l.length → (l.getD j dflt).last = 0 →
      (l.getD (j + 1) dflt).root = (l.getD j dflt).root) ∧
    (∀ j, j + 1 < l.length → (l.getD j dflt).last = 0 →
      (l.getD (j + 1) dflt).p = childOf δF (l.getD j dflt)) := by
  obtain ⟨hrow, hchain, -, -⟩ := hg
  have hx : ∀ j (hj : j < l.length), l.getD j dflt = l[j] := fun j hj => List.getD_eq_getElem _ _ hj
  have hstep : ∀ j (hj : j + 1 < l.length), PathStep δF l[j] l[j + 1] := fun j hj =>
    List.isChain_iff_getElem.mp hchain j hj
  refine ⟨fun j hj => ?_, fun j hj hl => ?_, fun j hj hl => ?_⟩
  · rw [hx j hj]; exact (hrow _ (List.getElem_mem hj)).2
  · rw [hx j (by omega), hx (j + 1) hj] at *
    exact (hstep j hj).2 hl |>.2.2.2.1
  · rw [hx j (by omega), hx (j + 1) hj] at *
    exact (hstep j hj).2 hl |>.2.2.2.2

end TableFacts

section PathTable
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- **The path chip's rows**: the chains of the distinct deep reads, flattened. -/
def pathTable (z : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ)) :
    List (PathVals F (Quad (algebraMap F K δF))) :=
  (pathReads preads).flatMap fun r =>
    chainRows δF z cells r.1 (preads.count r) (pathSteps r.1 (axisBits r.2))

variable {δF}

theorem pathTable_good (z : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ))
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) : PathGood (pathTable δF z cells preads) := by
  refine PathGood.flatMap _ _ fun r hr => ?_
  refine chainRows_good z cells r.1 _ _ (fun h => pathSteps_head _ _ h) (fun k h => pathSteps_next _ _ k h) ?_
  exact (pathSteps_length_le _ _).trans (h62 r hr)

end PathTable

/-! ## 4. The per-side export consumers (`mx` / `mx1`) -/

section Sided

/-- The path-edge export consumers with their side: parent cell and the side taken. -/
def edgeSided (preads : List (Noun × ℕ)) : List (Noun × Bool) :=
  (pathReads preads).flatMap fun r => pathSteps r.1 (axisBits r.2)

/-- The depth-1 compute lookups with their side (`axis = 2` is side `0`, `axis = 3` side `1`). -/
def shallowSided (reads : List (Noun × ℕ)) : List (Noun × Bool) :=
  (shallowReads reads).flatMap fun r => (selfCell r.1).map fun c => (c, decide (r.2 % 2 = 1))

/-- **The export consumers, with sides.** -/
def sidedConsumers (preads reads : List (Noun × ℕ)) : List (Noun × Bool) :=
  edgeSided preads ++ shallowSided reads

/-- Side-0 export consumers (`mx`). -/
def xs0 (preads reads : List (Noun × ℕ)) : List Noun :=
  ((sidedConsumers preads reads).filter fun c => !c.2).map Prod.fst

/-- Side-1 export consumers (`mx1`). -/
def xs1 (preads reads : List (Noun × ℕ)) : List Noun :=
  ((sidedConsumers preads reads).filter fun c => c.2).map Prod.fst

theorem count_fst_split (L : List (Noun × Bool)) (n : Noun) :
    (L.map Prod.fst).count n =
      (((L.filter fun c => !c.2).map Prod.fst).count n) + (((L.filter fun c => c.2).map Prod.fst).count n) := by
  induction L with
  | nil => simp
  | cons c L ih =>
    obtain ⟨m, b⟩ := c
    cases b <;> simp [List.count_cons, ih] <;> omega

theorem sidedConsumers_fst (preads reads : List (Noun × ℕ)) :
    (sidedConsumers preads reads).map Prod.fst = exportConsumers preads reads := by
  simp only [sidedConsumers, edgeSided, shallowSided, exportConsumers, edgeParents, shallowLookups,
    List.map_append, List.map_flatMap, List.map_map, Function.comp_def]
  congr 1
  simp

/-- **The per-side counts add up to the generator's single `mx`.** -/
theorem xs_count_add (preads reads : List (Noun × ℕ)) (n : Noun) :
    (xs0 preads reads).count n + (xs1 preads reads).count n = (exportConsumers preads reads).count n := by
  rw [← sidedConsumers_fst, count_fst_split]; rfl

end Sided

/-! ## 5. The m = 0 padding chain

When `pathReads preads = []` the honest path table is ONE padding chain: a one-row chain on the cell
`padCell cells` (side 0, axis 2), `first = last = 1`, `len 1`, `acc = 2`, multiplicity `m = 0`.  Its export
consume is supplied by raising that cell's export count (`edgeSidedP` / `xs0P`).  When some deep read exists
the padding is empty and everything is the old table. -/

section Pad
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δF : F)
  [Fact (¬ IsSquare (algebraMap F K δF))]

/-- The padding chain's cell: the first cell of the table (a cell whenever the table is non-empty). -/
def padCell (cells : List Noun) : Noun := cells.headD (.atom 0)

/-- The padding steps: one step `(padCell, side 0)` iff the demand has no deep read. -/
def padSteps (cells : List Noun) (preads : List (Noun × ℕ)) : List (Noun × Bool) :=
  if pathReads preads = [] then [(padCell cells, false)] else []

/-- **The path chip's rows with padding**: the old table plus the (m = 0) padding chain. -/
def pathTableP (z : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ)) :
    List (PathVals F (Quad (algebraMap F K δF))) :=
  pathTable δF z cells preads ++ chainRows δF z cells (padCell cells) 0 (padSteps cells preads)

variable {δF}

theorem padSteps_length_le (cells : List Noun) (preads : List (Noun × ℕ)) :
    (padSteps cells preads).length ≤ 1 := by
  unfold padSteps; split_ifs <;> simp

theorem padSteps_of_ne (cells : List Noun) (preads : List (Noun × ℕ)) (h : pathReads preads ≠ []) :
    padSteps cells preads = [] := if_neg h

theorem padSteps_of_eq (cells : List Noun) (preads : List (Noun × ℕ)) (h : pathReads preads = []) :
    padSteps cells preads = [(padCell cells, false)] := if_pos h

theorem pathTableP_good (z : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ))
    (h62 : ∀ r ∈ pathReads preads, depthOf r.2 ≤ 62) : PathGood (pathTableP δF z cells preads) := by
  refine (pathTable_good z cells preads h62).append ?_
  have hl := padSteps_length_le cells preads
  refine chainRows_good z cells (padCell cells) 0 (padSteps cells preads) ?_ ?_ (by omega)
  · intro h
    by_cases hp : pathReads preads = []
    · simp [padSteps_of_eq cells preads hp]
    · rw [padSteps_of_ne cells preads hp] at h; simp at h
  · intro k h; omega

/-- The padded edge consumers (with side). -/
def edgeSidedP (cells : List Noun) (preads : List (Noun × ℕ)) : List (Noun × Bool) :=
  edgeSided preads ++ padSteps cells preads

/-- The padded export consumers with sides. -/
def sidedConsumersP (cells : List Noun) (preads reads : List (Noun × ℕ)) : List (Noun × Bool) :=
  edgeSidedP cells preads ++ shallowSided reads

/-- Side-0 export consumers, padded. -/
def xs0P (cells : List Noun) (preads reads : List (Noun × ℕ)) : List Noun :=
  ((sidedConsumersP cells preads reads).filter fun c => !c.2).map Prod.fst

/-- Side-1 export consumers, padded. -/
def xs1P (cells : List Noun) (preads reads : List (Noun × ℕ)) : List Noun :=
  ((sidedConsumersP cells preads reads).filter fun c => c.2).map Prod.fst

theorem pathTableP_length (z z' : Quad (algebraMap F K δF)) (cells : List Noun) (preads : List (Noun × ℕ)) :
    (pathTableP δF z cells preads).length = (pathTableP δF z' cells preads).length := by
  simp [pathTableP, List.length_flatMap, pathTable, chainRows_length]

end Pad

end

end Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
