/-
  Nock/RedTeam/Batch1970Thm54WalkW1Instance.lean

  Modules (`Nock/NockVMROM/Thm54/VclL/Walk/`):
  * `WalkInstance`: `LT`, `F`, `stateSep`, `F_respects`, `enc` / `enc_det` over `𝕂` (15 entries).
  * `WalkChain`: `chain_tuple_of_reconGoal` (the chain 5-tuple from `ForestReconGoal` + its
    fanout conjunct + the root gate), `records_of_reconGoal` (via `row_genuine` +
    `chain_sound_outside`).
  * `WalkEvent`: `walk_records_card` (`≤ |𝕂|·h + |𝕂|·14h` over `𝕂 × 𝕂`, i.e. `15h/|𝕂|`, through
    `Walk_IOP_forest_final_card_of_label`), `vclWalkSummand` on `frameVCL` coins `{0, 1}` =
    `(αC, γ)` with `walkCoins_disjoint`, `records_outside_summand`.

  Negative controls (this file): each of the three `F` clauses — prefix rule, depth guard, child
  link — is shown to REJECT a concrete forged label that the variant of `F` with exactly that
  clause dropped (`Fw`, `F_iff_Fw`) ACCEPTS, together with the concrete consequence the clause
  prevents (a prefix that is not the path axis, an axis that wraps mod `q`, a record target that is
  not the chain's end).  Instance: `q = 11`, `Dmax = 2` (`2^(Dmax+1) = 8 ≤ 11`), `Kfp = ℚ`.
-/
import Nock.NockVMROM.Thm54.VclL.Walk.WalkEvent

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch1970

open Nock Nock.Walk Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.ComputeTable (FP)

/-! ## The weakened `F`: each clause behind a flag -/

section Weak
variable {q : ℕ} {Kfp : Type} [Field Kfp] [DecidableEq Kfp]

def ChildOKw (pre node : Bool) (k : XKey Kfp) (b : Bool) (d : DT q Kfp) (c : LT q Kfp) : Prop :=
  (node = true → c.2.node = tgt k b) ∧ (pre = true → c.2.pre = 2 * d.pre + bitZ b) ∧
    c.2.root = d.root ∧ c.2.ridx = d.ridx ∧ c.2.len = d.len + 1

/-- `F` with the depth guard, the prefix rule and the child link each behind a flag. -/
def Fw (guard pre node : Bool) (X : List (XKey Kfp)) (Dmax : ℕ) (l : LT q Kfp)
    (xout : Fin 2 → Option (LT q Kfp)) : Prop :=
  (guard = true → l.2.len.val < Dmax) ∧ (∀ i : Fin 2, ((i : ℕ) < fanout l.1 ↔ xout i ≠ none)) ∧
    ∃ k ∈ X, k.1 = l.2.node ∧
      (l.1.1 = true → ∃ c, xout 0 = some c ∧ ChildOKw pre node k false l.2 c) ∧
      (l.1.2 = true → ∃ c, xout (if l.1.1 then 1 else 0) = some c ∧ ChildOKw pre node k true l.2 c)

/-- The deployed `F` is `Fw` with every flag on: the controls below drop exactly one clause. -/
theorem F_iff_Fw (X : List (XKey Kfp)) (Dmax : ℕ) (l : LT q Kfp)
    (xout : Fin 2 → Option (LT q Kfp)) : F X Dmax l xout ↔ Fw true true true X Dmax l xout := by
  simp only [F, Fw, OptOK, ChildOK, ChildOKw, forall_const]

end Weak

/-! ## The concrete instance -/

abbrev n0 : FP ℚ := ⟨0, 0, 0⟩
abbrev n1 : FP ℚ := ⟨1, 1, 1⟩
abbrev n2 : FP ℚ := ⟨2, 2, 2⟩
abbrev k0 : XKey ℚ := (n0, n1, n2, 0)
abbrev X0 : List (XKey ℚ) := [k0]

/-- A root (prefix 1, len 0) continuing left only. -/
abbrev lP : LT 11 ℚ := ((true, false), ⟨n0, 1, n0, 0, 0⟩)
/-- Its honest left child. -/
abbrev cGood : LT 11 ℚ := ((false, false), ⟨n1, 2, n0, 0, 1⟩)

def xo (c : LT 11 ℚ) : Fin 2 → Option (LT 11 ℚ) := fun i => if (i : ℕ) = 0 then some c else none

theorem n1_ne_n2 : n1 ≠ n2 := by
  intro h; have := congrArg FP.size h; norm_num at this

theorem tgt_left : tgt k0 false = n1 := by simp [tgt, childOf, keyEdge]

theorem dyn_xo (c : LT 11 ℚ) :
    ∀ i : Fin 2, ((i : ℕ) < fanout lP.1 ↔ xo c i ≠ none) := by
  intro i; fin_cases i <;> simp [xo, fanout]

/-- Positive control: the honest child is accepted by the deployed `F`. -/
theorem honest_accepted : F X0 2 lP (xo cGood) := by
  refine ⟨by decide, dyn_xo cGood, k0, by simp, rfl, fun _ => ⟨cGood, rfl, ?_⟩, fun h => ?_⟩
  · refine ⟨tgt_left.symm, by decide, rfl, rfl, by decide⟩
  · exact absurd h (by decide)

/-! ### NC 1: the prefix rule -/

/-- The left child with prefix `3` instead of `2·1 + 0 = 2`. -/
abbrev cPre : LT 11 ℚ := ((false, false), ⟨n1, 3, n0, 0, 1⟩)

theorem nc_prefix_rejected : ¬ F X0 2 lP (xo cPre) := by
  rintro ⟨-, -, k, hk, -, h1, -⟩
  simp only [List.mem_singleton] at hk; subst hk
  obtain ⟨c, hc, hok⟩ := h1 rfl
  simp only [xo, Fin.isValue, Fin.val_zero, if_true, Option.some.injEq] at hc
  subst hc
  exact absurd hok.2.1 (by decide)

theorem nc_prefix_accepted_without_rule : Fw true false true X0 2 lP (xo cPre) := by
  refine ⟨fun _ => by decide, dyn_xo cPre, k0, by simp, rfl, fun _ => ⟨cPre, rfl, ?_⟩,
    fun h => absurd h (by decide)⟩
  exact ⟨fun _ => tgt_left.symm, fun h => absurd h (by decide), rfl, rfl, by decide⟩

/-- What the rule prevents: the forged prefix is not the axis of the child's chain from the root
(`[keyEdge k0 false]`, `axisFold [false] = 2`). -/
theorem nc_prefix_consequence : (cPre.2.pre).val ≠ axisFold [false] := by decide

/-! ### NC 2: the depth guard -/

/-- A leaf at `len = Dmax = 2`. -/
abbrev lDeep : LT 11 ℚ := ((false, false), ⟨n0, 7, n0, 0, 2⟩)

theorem dyn_none (l : LT 11 ℚ) (hl : l.1 = (false, false)) :
    ∀ i : Fin 2, ((i : ℕ) < fanout l.1 ↔ (fun _ : Fin 2 => (none : Option (LT 11 ℚ))) i ≠ none) := by
  intro i; rw [hl]; fin_cases i <;> simp [fanout]

theorem nc_depth_rejected : ¬ F X0 2 lDeep (fun _ => none) := by
  rintro ⟨hw, -⟩
  exact absurd hw (by decide)

theorem nc_depth_accepted_without_guard : Fw false true true X0 2 lDeep (fun _ => none) := by
  refine ⟨fun h => absurd h (by decide), dyn_none lDeep rfl, k0, by simp, rfl,
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-- What the guard prevents: one level deeper, the axis `2·7 + 1 = 15` wraps mod `q = 11`
(`extend` needs `2^(Dmax+1) ≤ q`). -/
theorem nc_depth_consequence :
    (2 * lDeep.2.pre + bitZ true).val ≠ axisFold [true, true, true] := by decide

/-! ### NC 3: the child link -/

/-- The left child carrying the RIGHT fingerprint `n2` instead of the key's left `n1`. -/
abbrev cLink : LT 11 ℚ := ((false, false), ⟨n2, 2, n0, 0, 1⟩)

theorem nc_link_rejected : ¬ F X0 2 lP (xo cLink) := by
  rintro ⟨-, -, k, hk, -, h1, -⟩
  simp only [List.mem_singleton] at hk; subst hk
  obtain ⟨c, hc, hok⟩ := h1 rfl
  simp only [xo, Fin.isValue, Fin.val_zero, if_true, Option.some.injEq] at hc
  subst hc
  exact n1_ne_n2 (tgt_left.symm.trans hok.1.symm)

theorem nc_link_accepted_without_link : Fw true true false X0 2 lP (xo cLink) := by
  refine ⟨fun _ => by decide, dyn_xo cLink, k0, by simp, rfl, fun _ => ⟨cLink, rfl, ?_⟩,
    fun h => absurd h (by decide)⟩
  exact ⟨fun h => absurd h (by decide), fun _ => by decide, rfl, rfl, by decide⟩

/-- What the link prevents: the forged child's fp is not the end of its chain from the root. -/
theorem nc_link_consequence : chainEnd n0 [keyEdge k0 false] ≠ some cLink.2.node := by
  intro h
  simp only [chainEnd, keyEdge, childOf, if_true, Bool.false_eq_true, if_false,
    Option.some.injEq] at h
  exact n1_ne_n2 h

end Nock.RedTeam.Batch1970

/-! ## Axioms -/
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.stateSep
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.F_respects
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.enc_det
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.walk_chain_record
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.chain_tuple_of_reconGoal
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.records_of_reconGoal
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.walk_records_card
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.walkEvent_card
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.walkCoins_disjoint
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.vclWalkSummand
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.vclWalkSummand_shape
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.vclWalkSummand_mem_iff
#print axioms Nock.NockVMROM.Thm54.VclL.WalkVCL.records_outside_summand
#print axioms Nock.RedTeam.Batch1970.F_iff_Fw
#print axioms Nock.RedTeam.Batch1970.honest_accepted
#print axioms Nock.RedTeam.Batch1970.nc_prefix_rejected
#print axioms Nock.RedTeam.Batch1970.nc_prefix_accepted_without_rule
#print axioms Nock.RedTeam.Batch1970.nc_prefix_consequence
#print axioms Nock.RedTeam.Batch1970.nc_depth_rejected
#print axioms Nock.RedTeam.Batch1970.nc_depth_accepted_without_guard
#print axioms Nock.RedTeam.Batch1970.nc_depth_consequence
#print axioms Nock.RedTeam.Batch1970.nc_link_rejected
#print axioms Nock.RedTeam.Batch1970.nc_link_accepted_without_link
#print axioms Nock.RedTeam.Batch1970.nc_link_consequence
