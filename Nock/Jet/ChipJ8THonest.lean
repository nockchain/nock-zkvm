/-
  Nock/Jet/ChipJ8THonest.lean

  **Honest full-trace acceptance of the tag-last J chip
  `jetChipJ8` over `jetTemplateJ8T`, matmul `n = 2`, `p = 1009`.**

  The trace is J-3b's `toyRowsJ`.  `jetTemplateJ8T` differs from `jetTemplateJ8` only in the keys: the
  base gates are the same list (`rfl`), the in-chip keys are `tlF` of the old ones
  (`consKT_eq`, `provKT_eq`).  So:
  * `toyT_gates` : every base gate of `jetTemplateJ8T` vanishes on every row;
  * `toyT_bal` : the existence-form balance on the tag-last keys (derived from `toy_bal`);
  * `toyT_tag_last` : every in-chip key has entry 7 in `{1, 2}`;
  * `toyRowsJ_sum_bal_fails`, `toyT_sum_bal` : FINDING + fix.  J-3b builder sets mv = 1; the SUM balance needs mv = #consumers (`rowsMv`);
    `#(rows consuming κ) = Σ mv over rows providing κ` in `ZMod 1009` (kernel, `decide`);
  * `toyT_accepted` : J-3b `Accepted` (the hypothesis of `jetChip_holds`) for the corrected rows (`rowsMv`), whose
    keys are those of the tag-last chip.
-/
import Nock.Jet.RapJetJ8
import Nock.Jet.ChipJ8Toy

set_option autoImplicit false

namespace Nock.Jet.ChipJ8T.Honest

open Nock Nock.Noun Nock.Jet Nock.Jet.Autogen Nock.Jet.Interp Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8
open Nock.NockVMROM.Thm54.CoordinateCompiler

/-- The base gates of the tag-last template are the base gates of the J chip. -/
theorem baseTransition_T (δ : ZMod 1009) : (jetTemplateJ8T δ).baseTransition = baseGatesJ := rfl

/-- Every base gate of `jetTemplateJ8T` vanishes on every row of the honest trace. -/
theorem toyT_gates (δ : ZMod 1009) : ∀ r ∈ toyRowsJ, ∀ g ∈ (jetTemplateJ8T δ).baseTransition,
    g.eval (envOf r) = 0 := toy_gates

/-- **The tag-last in-chip balance** (existence form). -/
theorem toyT_bal : ∀ r ∈ toyRowsJ, ∀ κ ∈ consKT r, ∃ r' ∈ toyRowsJ, κ ∈ provKT r' := by
  intro r hr κ hκ
  rw [consKT_eq] at hκ
  obtain ⟨κ0, hκ0, rfl⟩ := List.mem_map.mp hκ
  obtain ⟨r', hr', hp⟩ := toy_bal r hr κ0 hκ0
  exact ⟨r', hr', by rw [provKT_eq]; exact List.mem_map_of_mem hp⟩

/-- Every in-chip key of the honest trace is tag-last: length 8, entry 7 is `1` or `2` (the zero padding is
`tlF_one` / `tlF_two`). -/
theorem toyT_tag_last : ∀ r ∈ toyRowsJ, ∀ κ ∈ consKT r ++ provKT r,
    κ.length = 8 ∧ (κ.getD 7 0 = 1 ∨ κ.getD 7 0 = 2) := by
  intro r hr κ hκ
  rcases List.mem_append.mp hκ with h | h
  · rw [consKT_eq] at h
    obtain ⟨κ0, hκ0, rfl⟩ := List.mem_map.mp h
    rcases consK_shape r κ0 hκ0 with ⟨a, b, c, d, rfl⟩ | ⟨a, b, c, rfl⟩ <;> simp [tlF]
  · rw [provKT_eq] at h
    obtain ⟨κ0, hκ0, rfl⟩ := List.mem_map.mp h
    rcases provK_shape r κ0 hκ0 with ⟨a, b, c, d, rfl⟩ | ⟨a, b, c, rfl⟩ <;> simp [tlF]

/-- A key as natural numbers (the `val`s). -/
def kv (κ : List (ZMod 1009)) : List ℕ := κ.map ZMod.val

/-- **The honest provide multiplicity.**  `toyRowsJ` (J-3b's builder) sets `mv = 1` on every row; the
tagged accumulator `accT` subtracts `mv` per in-chip provide, so the SUM balance needs `mv` = the
number of consumers of the provided key.  `mvOf` is that count, `rowsMv` the corrected trace.
(`mv` is in no base gate, so the gates and the layout are untouched.) -/
def mvOf (rows : List (CRow (ZMod 1009))) (r : CRow (ZMod 1009)) : ZMod 1009 :=
  match provKT r with
  | [k] => (((rows.flatMap consKT).count k : ℕ) : ZMod 1009)
  | _ => 0

def rowsMv (rows : List (CRow (ZMod 1009))) : List (CRow (ZMod 1009)) :=
  rows.map fun r => { r with w := { r.w with mv := mvOf rows r } }

/-- Sum balance, in `ℕ` (kernel-friendly): for every in-chip key `κ`,
`#consumes(κ) ≡ Σ_rows #provides(κ) · val mv (mod 1009)`. -/
def sumBalB (rows : List (CRow (ZMod 1009))) : Bool :=
  let cs := rows.flatMap fun r => (consKT r).map kv
  let ps := rows.flatMap fun r => ((provKT r).map kv).map fun k => (k, r.w.mv.val)
  (cs ++ ps.map Prod.fst).all fun κ =>
    cs.count κ % 1009 == ((ps.filter fun q => q.1 == κ).map Prod.snd).sum % 1009

/-- Finding (`#eval`/kernel): J-3b's `mv = 1` rows do NOT satisfy the sum balance. -/
theorem toyRowsJ_sum_bal_fails : sumBalB toyRowsJ = false := by decide +kernel

/-- **The in-chip sum balance, honest (kernel, `n = 2`, `p = 1009`).** -/
theorem toyT_sum_bal : sumBalB (rowsMv toyRowsJ) = true := by decide +kernel

theorem toyT_layout : (rowsMv toyRowsJ).map CRow.pre = layoutJ8 ChipJ8.toyR [0] [0] := by
  decide +kernel

theorem toyT_gates' (δ : ZMod 1009) : ∀ r ∈ rowsMv toyRowsJ, ∀ g ∈ (jetTemplateJ8T δ).baseTransition,
    g.eval (envOf r) = 0 := by
  intro r hr g hg; revert r hr g hg; show ∀ r ∈ rowsMv toyRowsJ, ∀ g ∈ (baseGatesJ : List (CoeffExpr (ZMod 1009))), _
  decide +kernel

theorem toyT_bal' : ∀ r ∈ rowsMv toyRowsJ, ∀ κ ∈ consKT r, ∃ r' ∈ rowsMv toyRowsJ, κ ∈ provKT r' := by
  decide +kernel

/-- **Honest acceptance** (J-3b `Accepted`, the `jetChip_holds` hypothesis) of the corrected trace
over the tag-last chip: layout, bounds, unique provides, base gates (`toyT_gates'`), and the in-chip
balance, in existence form (`toyT_bal'`, with `consKT_eq`) -- the sum form is `toyT_sum_bal`. -/
theorem toyT_accepted : Accepted ChipJ8.toyR [0] [0] (rowsMv toyRowsJ) where
  lay := toyT_layout
  small := toy_small
  uniq := toy_uniq
  gate := by
    intro r hr g hg
    exact toyT_gates' 0 r hr g hg
  bal := by
    intro r hr κ hκ
    rw [consK] at hκ
    have : ∀ r' ∈ rowsMv toyRowsJ, ∀ κ ∈ consK r', ∃ r'' ∈ rowsMv toyRowsJ, κ ∈ provK r'' := by
      decide +kernel
    exact this r hr κ hκ

end Nock.Jet.ChipJ8T.Honest
