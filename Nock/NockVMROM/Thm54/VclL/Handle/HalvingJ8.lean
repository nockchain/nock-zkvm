/-
  Nock/NockVMROM/Thm54/VclL/Handle/HalvingJ8.lean

  **The `s10L` halving wrap against the walk's axis certificate.**

  **Answer: the binder alone does NOT suffice; the certificate must be narrowed by one bit.**

  * The hostile statement `Pr[AcceptsG V′ ∧ ¬ HoldsN V′.claim] ≤ …` quantifies over every `V′`; the
    `haxis` binder only feeds the honest conjunct (completeness).
  * `s10L_wrap_admitted_by_deployed_cert` (kernel, Goldilocks): the deployed depth certificate holds
    at a walk node of `len = 61`, prefix `pre₀ = 2^62 − 2^30 + 1` (a depth-61 axis), whose left
    record axis `2·pre₀ = v − 1` is the CHILD `s10L` row's sibling read for `a′ = v`, `β′ = 1` (honest
    parity), with `v = 2^63 − 2^31 + 3` the WRAPPED half of the parent's `a = 5`, `β = 0`.  All three
    `s10L` gates hold at parent and child; `HalvingOK` fails at the parent.  The honest program of
    the attack (`[10 [[5 c] d]]`) has edit/chain axes `5, 2, 1` (U: the generator twin's
    `honestAxX` is not evaluated here), far below any binder.
  * **Minimal gate change** (one gate, no column, no coin, degree 1): replace the walk twin's depth
    certificate by `len + Σ_{i<5} 2^i bᵢ + 29·b₅ − 60 = 0` and DROP the exclusion gate
    `u·b₃·b₄·b₅` (the `u = b₁b₂` gate becomes inert).
  * `halvingOK_of_child_s10L` / `halvingOK_of_child_s10T` (field level, any `2^63 + 1 < p`): once the
    child chain row's sibling read is a walk axis in `[2, 2^62)` (narrowed certificate), or the child
    is `s10T` (`a′ = 1`), the parent's `v` satisfies `HalvingOK` (`1 ≤ val v`, `2·val v + 1 < p`) —
    no parent gate is even needed.  `halvingOK_of_child_s10L_env` restates it as
    `RowSemChipX.HalvingOK` on the parent's environment.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HalvingJ8

open Nock.Reified
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX

/-! ## 1. The counterexample against the deployed certificate -/

/-- **The `s10L` wrap is admitted by the walk chip's deployed depth certificate** (Goldilocks).
Parent `s10L` (`a = 5`, `β = 0`, wrapped `v`), child `s10L` at `a′ = v` (`β′ = 1`, `v′ = pre₀`,
sibling read `ax2′ = v − 1`), and the walk node at `len = 61`, prefix `pre₀`, all six certificate
bits `0`, `u = 0`, whose left record axis `2·pre₀` IS `ax2′`: every gate holds, the record axis is a
63-bit axis, and `HalvingOK` fails at the parent. -/
theorem s10L_wrap_admitted_by_deployed_cert :
    let q := 18446744069414584321
    -- parent s10L
    let a : ZMod q := 5
    let β : ZMod q := 0
    let v : ZMod q := 9223372034707292163
    let w : ZMod q := 13835058052060938241
    let ax2 : ZMod q := 6
    -- child s10L at a' = v
    let β' : ZMod q := 1
    let v' : ZMod q := 4611686017353646081
    let w' : ZMod q := 6148914689804861441
    let ax2' : ZMod q := 9223372034707292162
    -- walk node providing the child's sibling read
    let len : ZMod q := 61
    let pre : ZMod q := 4611686017353646081
    let bits : ℕ → ZMod q := fun _ => 0
    let u : ZMod q := 0
    -- parent gates
    (a - 2 * v - β = 0 ∧ (a - 1) * w - 1 = 0 ∧ ax2 - a - 1 + 2 * β = 0) ∧
    -- child gates (v2' = a' = v)
    (v - 2 * v' - β' = 0 ∧ (v - 1) * w' - 1 = 0 ∧ ax2' - v - 1 + 2 * β' = 0) ∧
    -- the deployed depth certificate at the walk node
    (u - bits 1 * bits 2 = 0 ∧ u * bits 3 * (bits 4 * bits 5) = 0 ∧
      len + (bits 0 + 2 * bits 1 + 4 * bits 2 + 8 * bits 3 + 16 * bits 4 + 32 * bits 5) - 61 = 0) ∧
    -- the node is a depth-61 prefix; its left record axis is the child's read; a 63-bit axis
    (2 ^ 61 ≤ pre.val ∧ pre.val < 2 ^ 62 ∧ 2 * pre = ax2' ∧ ax2'.val < 2 ^ 63 ∧ 2 ^ 62 ≤ ax2'.val) ∧
    -- the wrap: the parent's v is not a / 2 and HalvingOK fails
    (v.val ≠ a.val / 2 ∧ ¬ (2 * v.val + 1 < q)) := by
  decide +kernel

/-! ## 2. The narrowed certificate -/

/-- The narrowed depth certificate's bit sum `Σ_{i<5} 2^i bᵢ + 29·b₅`. -/
def cert60 (b : ℕ → ℕ) : ℕ := b 0 + 2 * b 1 + 4 * b 2 + 8 * b 3 + 16 * b 4 + 29 * b 5

/-- **Soundness of the narrowed certificate**: boolean bits sum to at most `60`, so the gate
`len + cert60 b − 60 = 0` gives `len ≤ 60` (no exclusion gate needed). -/
theorem depthCert60_range (b : ℕ → ℕ) (hb : ∀ i, i < 6 → b i ≤ 1) : cert60 b ≤ 60 := by
  have := hb 0 (by omega); have := hb 1 (by omega); have := hb 2 (by omega)
  have := hb 3 (by omega); have := hb 4 (by omega); have := hb 5 (by omega)
  unfold cert60; omega

/-- **Completeness of the narrowed certificate**: every `n ≤ 60` has boolean bits. -/
theorem depthCert60_complete : ∀ n, n ≤ 60 → ∃ b : ℕ → ℕ, (∀ i, i < 6 → b i ≤ 1) ∧ cert60 b = n := by
  intro n hn
  by_cases h : n ≤ 31
  · refine ⟨fun i => if i < 5 then n / 2 ^ i % 2 else 0, ?_, ?_⟩
    · intro i _; dsimp only; split_ifs
      · exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
      · omega
    · simp only [cert60]; norm_num; omega
  · refine ⟨fun i => if i < 5 then (n - 29) / 2 ^ i % 2 else 1, ?_, ?_⟩
    · intro i _; dsimp only; split_ifs
      · exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
      · omega
    · simp only [cert60]; norm_num; omega

/-- **Field form**: under the narrowed gate with boolean bits, `len.val ≤ 60` (for `60 < p`). -/
theorem len_le_60_of_cert60 {p : ℕ} [Fact p.Prime] (hp : 60 < p) (len : ZMod p) (b : ℕ → ℕ)
    (hb : ∀ i, i < 6 → b i ≤ 1) (hg : len + (cert60 b : ZMod p) - 60 = 0) : len.val ≤ 60 := by
  have hc := depthCert60_range b hb
  have : len = ((60 - cert60 b : ℕ) : ZMod p) := by
    rw [Nat.cast_sub hc]; push_cast; linear_combination hg
  rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; omega

/-- The deployed certificate admits `len = 61` (bits `0`, `u = 0`), which the narrowed one rejects. -/
theorem deployed_admits_61_narrowed_rejects :
    (61 : ℕ) + (0 + 2 * 0 + 4 * 0 + 8 * 0 + 16 * 0 + 32 * 0) - 61 = 0 ∧
      ∀ b : ℕ → ℕ, (∀ i, i < 6 → b i ≤ 1) → 61 + cert60 b ≠ 60 := by
  refine ⟨rfl, fun b hb => ?_⟩
  have := depthCert60_range b hb; omega

/-! ## 3. `HalvingOK` from the child chain row under the narrowed certificate -/

section Halving
variable {p : ℕ} [Fact p.Prime]

private theorem val_nat' {n : ℕ} (hn : n < p) : ((n : ZMod p)).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]

/-- **`HalvingOK` from a child `s10L` row**: the child's `a′ = v` (`s10LEq`: `v2 = f.v`, the
child's formula handle `(0, v)` from the parent's `labAtom`), its sibling read
`ax2′ = v + 1 − 2β′` (`s10LG`), `β′` boolean, and `ax2′` a walk record axis in `[2, 2^62)` (the
narrowed certificate) give `1 ≤ val v ∧ 2·val v + 1 < p`. -/
theorem halvingOK_of_child_s10L (hp : 2 ^ 63 + 1 < p) {v ax2' β' : ZMod p}
    (hβ : β' = 0 ∨ β' = 1) (hg : ax2' - v - 1 + 2 * β' = 0)
    (hlo : 2 ≤ ax2'.val) (hhi : ax2'.val < 2 ^ 62) :
    1 ≤ v.val ∧ 2 * v.val + 1 < p := by
  set A := ax2'.val with hA
  have hax : ax2' = (A : ZMod p) := by rw [hA, ZMod.natCast_zmod_val]
  rcases hβ with rfl | rfl
  · have hv : v = ((A - 1 : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega), ← hax]; push_cast; linear_combination -hg
    rw [hv, val_nat' (by omega)]; omega
  · have hv : v = ((A + 1 : ℕ) : ZMod p) := by
      push_cast; rw [← hax]; linear_combination -hg
    rw [hv, val_nat' (by omega)]; omega

/-- **`HalvingOK` from a child `s10T` row** (`s10TEq`: `f.v = 1`, so `v = 1`). -/
theorem halvingOK_of_child_s10T (hp : 3 < p) {v : ZMod p} (hv : v = 1) :
    1 ≤ v.val ∧ 2 * v.val + 1 < p := by
  subst hv
  rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by simp, val_nat' (by omega)]; omega

/-- The env-level form: `RowSemChipX.HalvingOK` on the parent row, from the child `s10L` row's
sibling-read gate under the narrowed certificate. -/
theorem halvingOK_of_child_s10L_env (hp : 2 ^ 63 + 1 < p) {env : Env (ZMod p)} {ax2' β' : ZMod p}
    (hβ : β' = 0 ∨ β' = 1) (hg : ax2' - env.trace vX - 1 + 2 * β' = 0)
    (hlo : 2 ≤ ax2'.val) (hhi : ax2'.val < 2 ^ 62) : HalvingOK env .s10L :=
  fun _ => halvingOK_of_child_s10L hp hβ hg hlo hhi

/-- The env-level form for a child `s10T` row. -/
theorem halvingOK_of_child_s10T_env (hp : 3 < p) {env : Env (ZMod p)} (hv : env.trace vX = 1) :
    HalvingOK env .s10L :=
  fun _ => halvingOK_of_child_s10T hp hv

/-- Goldilocks meets the field premise. -/
theorem goldilocks_halving_premise : 2 ^ 63 + 1 < 18446744069414584321 := by norm_num

end Halving

end Nock.NockVMROM.Thm54.VclL.Handle.HalvingJ8
