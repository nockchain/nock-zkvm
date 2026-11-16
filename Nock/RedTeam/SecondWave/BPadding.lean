/-
  ADVERSARIAL SCRATCH B — is A2's "inert padding row" real, and does the wrap really break?
-/
import Nock.AIR

namespace Attack

open Nock Nock.ComputeTable Nock.Reified

variable {K : Type*} [Field K]

/-! ## B1.

  Every `computeAIR` row is forced by `memBlk` into `ln = ln_prev * α^{e}` with `e ∈ {1,2,3}`.
  Take the cheapest opcode `s1` (`e = 1`).  If the `.transition` gate `lnChainExpr` is demanded at
  *every* point of a cyclic `H` (which is what `airToRAP` + `RAP.Satisfies` does), then the seed
  must satisfy `seed * (α^n − 1) = 0`.  Note this holds for the padded length too: an all-`s1`
  padding tail multiplies `ln` by `α` once per padding row, so padding cannot rescue the wrap. -/

/-- `s1`'s `memBlk` third conjunct, extracted. -/
theorem s1_ln_step (inp : Inputs K) (pub : Pub K) (dec : Dec K)
    (hst : pub.state = State.s1) (h : memBlk inp pub dec) :
    pub.ln = pub.ln_prev * inp.α := by
  rw [memBlk, hst] at h
  exact h.2.2

/-- **Cyclic `ln`-chain is contradictory.**  With the per-row step `ln(k) = α·ln_prev(k)` and the
    hand-off `ln(k) = ln_prev(k+1)` demanded at *all* `n` rows of a cyclic domain, the seed obeys
    `seed·(α^n − 1) = 0`: either the line-nonce seed is `0` (killing the walk α-telescoping) or `α`
    is an `n`-th root of unity (a measure-`n/|K|` event the soundness bound does not exclude). -/
theorem cyclic_ln_chain_forces (n : ℕ) (α : K) (lnp : ℕ → K)
    (hstep : ∀ k, lnp (k + 1) = lnp k * α)
    (hwrap : lnp n = lnp 0) :
    lnp 0 * (α ^ n - 1) = 0 := by
  have key : ∀ k, lnp k = lnp 0 * α ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ m ih => rw [hstep m, ih]; ring
  have := key n
  rw [hwrap] at this
  linear_combination -this

/-! ## B2. -/

theorem no_all_zero_selector (inp : Inputs K) (op : State → K) (dec : Dec K) (consInv : K)
    (hzero : ∀ j : State, op j = 0) : ¬ SVsatFree inp op dec consInv := by
  intro h
  have h3 := h.2.1
  rw [sum09] at h3
  simp only [hzero] at h3
  norm_num at h3

/-! ## B3. -/

theorem every_row_emits_mr1 (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (h : RAPcomp inp pub dec ex) : pub.mr1.axis = 3 := by
  rw [h.2.1]

theorem mr1_axis_ne_zero (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)
    (inp : Inputs K) (pub : Pub K) (dec : Dec K) (ex : Extra K)
    (h : RAPcomp inp pub dec ex) : pub.mr1.axis ≠ 0 := by
  rw [every_row_emits_mr1 inp pub dec ex h]
  intro hz
  -- 3 = 0 ⇒ 4 = 1 ⇒ 4 = 1 in ℕ, contradiction
  have h4 : ((4 : ℕ) : K) = 1 := by push_cast; linear_combination hz
  have := hchar 4 (by norm_num) h4
  omega

end Attack
