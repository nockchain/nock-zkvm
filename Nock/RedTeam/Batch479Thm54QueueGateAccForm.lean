/-
  Nock/RedTeam/Batch479Thm54QueueGateAccForm.lean

  The client (`nockchain/hoon/common/v2/table/verifier/memory.hoon`, read at source) carries,
  on its memory table (whose `ln`/`nc`/`kvs` are the paper's `ln`/`count`/`acc_walk`):
  `%mem-kvs-ioz-system-0/1/2` (`:241-248`: `kvs·(kvsf−1) = 0`, `kvs-ioz·(kvsf−1) = 0`,
  `kvsf = kvs·kvs-ioz`, so `kvsf` is the boolean `kvs ≠ 0` with `kvs-ioz` its inverse),
  `%mem-pad-kvsf-relation` (`:252-254`: `pad·(1 − kvsf) = 0`, "kvs empty triggers padding";
  `pad = 1` on active rows, `pad = 0` on padding — `:165-190` zero the node fields where
  `1 − pad ≠ 0`), `%mem-pad-stay-pad` (`:329-331`: `(1 − pad)·pad' = 0`), the boundary
  `%mem-ln-init` `ln = z` (`:28`), and the terminal `%mem-kvs-empty` `kvs = 0` (`:60`).  Its
  `%mem-kvs-update` (`:364-`) reads `kvs' + ln·RLC(node) = kvs + nc·(children)`, so the
  client's `kvs(i)` is the pending set BEFORE row `i` is dequeued — the paper's
  `acc_walk(i−1)`.  Tree form: one `𝕂` column `acc_inv` and one gate
  `notLast · (acc(i)·acc_inv(i) − 1) = 0` beside the existing terminal `out_walk = acc(h) = 0`:
  `∀ i < h, acc(i) ≠ 0`.  (The client's COMPUTE table is a different design — `stack-kv`
  with `%stack-kv-end-0` at `compute.hoon:247`, `ln` counting DOWN on padding `:1061-1064` —
  and carries no nonzero-on-active gate for `stack-kv`; only the memory table has it.)

  Compiled here, generic:

  * A'1 `bfsValid_of_acc_nonzero` — **outside the α-event** (`IsFullBFT`, the polynomial
    identity `:2281` holding exactly), `∀ k < h, acc(k) ≠ 0` forces queue-validity: the first
    underflow row `k = prefixLen fo h` tiles (`prefixLen_tiling_of_lt`), the identity restricts
    to it (`isFullBFT_prefix`, the walk-prefix lane's lemma), and then `acc(k) = 0` by the
    closed form `:2298` (`Walk.acc_closed`).  So the gate rejects every orphan-cycle table at
    EVERY `α`, with NO extra coin event and no order condition — inside the α-event the table
    is already priced by `walkPrefixAlphaEvent`.
  * A'2 `tiling_or_overflow_of_acc_nonzero` — the acc form does NOT force the tiling by
    itself: queue-valid with `h < 1 + Sf fo h` survives iff every declared child beyond row
    `h` has `RLC^γ = 0` (`overflow_children_rlc_zero`) — the overflow branch the prefix lane
    left open (`Batch471` "second gap", `sfPrefix_or_overflow`).  The ratio form closes this
    branch for free (`Batch478::tiling_of_ratio_gate`); the acc form needs the zero-child
    exclusion (a `γ`-event on a nonzero declared vector, or a `V_comp`/`V_mem` clause on the
    zero vector).
  * D'1 `not_isFullBFT_prefix_of_cur_ne_zero`, `honest_acc_zero_is_root_event` —
    completeness is STATISTICAL, not perfect: on an honest (queue-valid, identity-holding)
    table with `cur(k+1) ≠ 0`, `acc(k) = 0` iff `α` is a root of the nonzero polynomial
    `node_list_k − node_queue_k`, of degree `≤ max k (1 + Sf fo k)`; the honest prover fails
    at those `α`, for each `k < h` — a completeness event of size `≤ Σ_{k<h} max k (1+Sf k)`,
    i.e. `O(h²)/|𝕂|`, against the paper's perfect completeness.
  * B'1 `acc_eq_zero_of_alpha_zero` — at `α = 0` every `acc(k)` is `0`: the gate rejects every
    table with `h ≥ 2`, honest ones included (as for the ratio form, `Batch478`); the
    compiler's walk coin IS `0` (`GenNockCompilesBounded.lean:447`, `:639`).
-/
import Nock.WalkPrefix

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch479

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk

section Generic
variable {K : Type*} [Field K]
variable {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ} {ln count acc : ℕ → K} {α : K} {h : ℕ}

/-! ## A'1. Queue-validity from `acc(k) ≠ 0`, outside the α-event -/

/-- **`acc(k) ≠ 0` for `k < h` plus the exact identity forces queue-validity.** -/
theorem bfsValid_of_acc_nonzero
    (hw : WalkSat cur chld' fo ln count acc α (cur 1 * α) α h)
    (hbft : IsFullBFT cur chld' fo h)
    (hacc : ∀ k, 1 ≤ k → k < h → acc k ≠ 0) :
    BFSValid fo h := by
  by_contra hnv
  have hlt : prefixLen fo h < h := prefixLen_lt_of_not_bfsValid fo hnv
  have hk1 : 1 ≤ prefixLen fo h := one_le_prefixLen fo hw.hpos
  have htile : Sf fo (prefixLen fo h) + 1 = prefixLen fo h :=
    prefixLen_tiling_of_lt fo hw.hpos hlt
  have hbk : IsFullBFT cur chld' fo (prefixLen fo h) :=
    isFullBFT_prefix (le_of_lt hlt) htile hbft
  have hacc0 : acc (prefixLen fo h) = 0 := by
    rw [acc_closed hw rfl rfl (prefixLen fo h) hk1 (le_of_lt hlt)]
    unfold IsFullBFT at hbk
    rw [hbk]; ring
  exact hacc (prefixLen fo h) hk1 hlt hacc0

/-! ## A'2. Tiling is NOT forced: the overflow branch survives -/

/-- Under the acc gate and the exact identity: either the table tiles, or the queue overflows
`h` and every declared child at a position `> h` has `RLC^γ = 0`. -/
theorem tiling_or_overflow_of_acc_nonzero
    (hw : WalkSat cur chld' fo ln count acc α (cur 1 * α) α h)
    (hbft : IsFullBFT cur chld' fo h)
    (hacc : ∀ k, 1 ≤ k → k < h → acc k ≠ 0) :
    Sf fo h + 1 = h ∨
      (h < Sf fo h + 1 ∧ ∀ j, h ≤ j + 1 → (flatBlks chld' fo h).getD j 0 = 0) := by
  have hv := bfsValid_of_acc_nonzero hw hbft hacc
  have hle : h ≤ Sf fo h + 1 := by
    have := hv h hw.hpos (le_refl h)
    have := Sf_mono fo (Nat.sub_le h 1)
    omega
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inr ⟨hlt, fun j hj => overflow_children_rlc_zero hbft hj⟩
  · exact Or.inl heq.symm

/-! ## D'1. Completeness is statistical -/

/-- On an honest table (identity at `h`, queue-valid) with `cur(k+1) ≠ 0`, the identity does
NOT hold at the proper prefix `k < h`: position `k + 1` is pending (queue-valid: `k < Sf fo k`)
and its queue entry is `cur(k+1)` (identity at `h`), while `node_list_k` has no `X^{k+1}`. -/
theorem not_isFullBFT_prefix_of_cur_ne_zero
    (hbft : IsFullBFT cur chld' fo h) (hv : BFSValid fo h) {k : ℕ}
    (hk1 : 1 ≤ k) (hkh : k < h) (hcur : cur (k + 1) ≠ 0) :
    ¬ IsFullBFT cur chld' fo k := by
  intro hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [isFullBFT_iff_getD] at hk hbft
  -- the identity at the prefix reads position `j + 2` (index `j + 1`) as `0 = queue entry`
  have e1 := hk (j + 1)
  rw [curVals_getD_ge cur (le_refl (j + 1)), List.getD_cons_succ] at e1
  -- the queue entry at that position is the same at `h` (prefix of the flattened children)
  have hjS : j < Sf fo (j + 1) := by
    have h0 := hv (j + 2) (by omega) (by omega)
    have h2 : j + 2 - 1 = j + 1 := by omega
    rw [h2] at h0
    omega
  have e2 : (flatBlks chld' fo h).getD j 0 = (flatBlks chld' fo (j + 1)).getD j 0 :=
    flatBlks_getD_prefix chld' fo (le_of_lt hkh) hjS
  -- and at `h` it equals `cur (j + 2)`
  have e3 := hbft (j + 1)
  rw [curVals_getD_lt cur hkh, List.getD_cons_succ] at e3
  apply hcur
  rw [e3, e2, ← e1]

/-- `acc(k) = 0` iff `α` is a root of `node_list_k − node_queue_k` (closed form `:2298`). -/
theorem acc_zero_iff_eval_eq
    (hw : WalkSat cur chld' fo ln count acc α (cur 1 * α) α h) {k : ℕ}
    (hk1 : 1 ≤ k) (hkh : k ≤ h) :
    acc k = 0 ↔ (nodeListP cur k).eval α = (nodeQueueP cur chld' fo k).eval α := by
  rw [acc_closed hw rfl rfl k hk1 hkh]
  constructor
  · intro heq; linear_combination -heq
  · intro heq; rw [heq]; ring

/-- **The honest completeness event of the acc gate at row `k`** has size
`≤ max k (1 + Sf fo k)` (`Walk.walk_soundness_card_max`): the honest prover is rejected at
those `α`.  Summed over `k < h` this is `O(h²)/|𝕂|`, not the paper's perfect completeness. -/
theorem honest_acc_zero_is_root_event [Fintype K] [DecidableEq K]
    (hbft : IsFullBFT cur chld' fo h) (hv : BFSValid fo h) {k : ℕ}
    (hk1 : 1 ≤ k) (hkh : k < h) (hcur : cur (k + 1) ≠ 0) :
    (Finset.univ.filter
        (fun r : K => (nodeListP cur k).eval r = (nodeQueueP cur chld' fo k).eval r)).card
      ≤ max k (1 + Sf fo k) :=
  walk_soundness_card_max (not_isFullBFT_prefix_of_cur_ne_zero hbft hv hk1 hkh hcur)

/-! ## B'1. `α = 0` rejects everything -/

theorem nodeListP_eval_zero (cur : ℕ → K) (k : ℕ) : (nodeListP cur k).eval 0 = 0 := by
  rw [nodeListP_eval]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  rw [zero_pow (by omega), mul_zero]

theorem nodeQueueP_eval_zero (cur : ℕ → K) (chld' : ℕ → ℕ → K) (fo : ℕ → ℕ) (k : ℕ) :
    (nodeQueueP cur chld' fo k).eval 0 = 0 := by
  rw [nodeQueueP_eval, mul_zero, zero_add]
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun l _ => ?_))
  rw [zero_pow (by omega), mul_zero]

/-- At `α = 0` (recognizer inputs) every accumulator value is `0`: the acc gate rejects every
table with `h ≥ 2`, honest or not. -/
theorem acc_eq_zero_of_alpha_zero
    (hw : WalkSat cur chld' fo ln count acc 0 (cur 1 * 0) 0 h) :
    ∀ k, 1 ≤ k → k ≤ h → acc k = 0 := by
  intro k hk1 hkh
  rw [acc_closed hw rfl rfl k hk1 hkh, nodeListP_eval_zero, nodeQueueP_eval_zero]
  ring

theorem alpha_zero_acc_gate_unsat
    (hw : WalkSat cur chld' fo ln count acc 0 (cur 1 * 0) 0 h) (hh : 2 ≤ h) :
    ¬ (∀ k, 1 ≤ k → k < h → acc k ≠ 0) := by
  intro hgate
  exact hgate 1 (le_refl 1) (by omega) (acc_eq_zero_of_alpha_zero hw 1 (le_refl 1) (by omega))

end Generic

/-! ## Records -/

/-- The client's memory-table gate, read at source. -/
def clientGateRecord : List (String × String) :=
  [("memory.hoon:241-248", "kvs·(kvsf−1)=0, kvs-ioz·(kvsf−1)=0, kvsf=kvs·kvs-ioz: kvsf ⟺ kvs ≠ 0"),
    ("memory.hoon:252-254", "%mem-pad-kvsf-relation: pad·(1−kvsf)=0 — active row ⟹ kvs ≠ 0"),
    ("memory.hoon:329-331", "%mem-pad-stay-pad: (1−pad)·pad'=0 — padding is a suffix"),
    ("memory.hoon:165-190", "node fields zero where 1−pad ≠ 0: pad=1 active, pad=0 padding (polarity confirmed)"),
    ("memory.hoon:60", "%mem-kvs-empty: terminal kvs = 0"),
    ("memory.hoon:364", "%mem-kvs-update: kvs(i) is the pending set BEFORE row i = paper acc_walk(i−1)"),
    ("compute.hoon:182,247,1194", "stack-kv boundary/terminal/update only; no nonzero-on-active gate; ln counts down on pad (:1061)")]

theorem clientGateRecord_length : clientGateRecord.length = 7 := by decide

/-- Side conditions of the acc form, exact. -/
def sideConditions : List (String × String) :=
  [("soundness / queue-validity", "none outside the α-event (bfsValid_of_acc_nonzero)"),
    ("soundness / tiling", "NOT forced: overflow branch with RLC-zero children survives (tiling_or_overflow_of_acc_nonzero)"),
    ("completeness", "statistical: acc(k)=0 is a root event of size ≤ max k (1+Sf k) per row (honest_acc_zero_is_root_event)"),
    ("α = 0", "rejects every h ≥ 2 (alpha_zero_acc_gate_unsat); the compiler's walk coin is 0")]

theorem sideConditions_length : sideConditions.length = 4 := by decide

end Nock.RedTeam.Batch479

#print axioms Nock.RedTeam.Batch479.bfsValid_of_acc_nonzero
#print axioms Nock.RedTeam.Batch479.tiling_or_overflow_of_acc_nonzero
#print axioms Nock.RedTeam.Batch479.not_isFullBFT_prefix_of_cur_ne_zero
#print axioms Nock.RedTeam.Batch479.honest_acc_zero_is_root_event
#print axioms Nock.RedTeam.Batch479.acc_eq_zero_of_alpha_zero
#print axioms Nock.RedTeam.Batch479.alpha_zero_acc_gate_unsat
