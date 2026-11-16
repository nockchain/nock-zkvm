/-
  Nock/RedTeam/Batch1972Thm54WalkW2Hyps.lean

  Module `VclL/Chips/RowBridgeW.lean`:
  * twins of `pathChip_rowLocal` / `pathChip_masks` / `gather_*_path` (`walkChip_rowLocal`,
    `walkChip_masks` with the third fixed column `rootMask`, `gather_chal_walk`, `gather_pub_walk`);
  * **`walkHyps_of_chip`**: `WalkVCL.WalkHyps` (all six conjuncts) and **`rootGate_of_chip`**:
    `WalkVCL.RootGate`, from `walkChip` satisfaction + preprocessing binding + node injectivity +
    adjacency + `PrimeFieldElems F` + `kroots ≤ n` + `3n < p` + `64 ≤ p`.  No coin event.
    Queue validity reuses trunk's `Batch478.bfsValidF_of_ratio_gate` (at `α = 2 ∈ ℚ`).

  Negative controls (this file), each on the gate equations the chip commits, over `ZMod 67`:
  * `nc_cert_without_exclusion`: the six certificate bits alone admit `len = −1` (bits of `62`,
    `len + Σ 2^i bᵢ = 61` holds) with `len.val = 66 > 61` — the depth guard fails; the exclusion
    gate `u·b₃b₄b₅` with `u = b₁b₂` is nonzero there, so the chip REJECTS it.
  * `nc_queue_without_inv`: a fanout column `0, 2, 0` with one root meets the counter's init, step
    and last-row gates (`q = 0, 1, 0`) and tiles (`1 + Sf = 3`) but is NOT BFS-valid; the
    `q · qinv = 1` gate fails at row `1` for every `qinv`, so the chip REJECTS it.
  * `nc_queue_without_last`: a fanout column `2, 0` with one root (`n = 2`) meets the counter's
    init and step gates (`q = 2, 1`) and the non-last `q · qinv` gate (`q₁ = 2 ≠ 0`), is BFS-valid,
    but does NOT tile (`1 + Sf = 3 ≠ 2`); only the last-row gate `isLast · q = 0` (`q₂ = 1`)
    rejects it.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.WalkAcceptW

set_option autoImplicit false

namespace Nock.RedTeam.Batch1972

open Nock.Walk
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

/-! ## NC 1: the certificate exclusion is load-bearing -/

/-- The bits of `62` (`b₀ = 0`, `b₁..b₅ = 1`). -/
def bits62 (i : ℕ) : ZMod 67 := if i = 0 then 0 else 1

theorem nc_cert_without_exclusion :
    (∀ i < 6, bits62 i * (bits62 i - 1) = 0) ∧
      ((66 : ZMod 67) + ∑ i ∈ Finset.range 6, (2 : ZMod 67) ^ i * bits62 i - 61 = 0) ∧
      ¬ ((66 : ZMod 67).val ≤ 61) ∧
      (bits62 1 * bits62 2) * bits62 3 * (bits62 4 * bits62 5) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi; unfold bits62; split_ifs <;> decide
  · simp [Finset.sum_range_succ, bits62]; decide
  · decide
  · simp [bits62]

/-! ## NC 2: the `q · qinv` gate is load-bearing (BFS validity) -/

def fo020 (i : ℕ) : ℕ := if i = 2 then 2 else 0

theorem nc_queue_without_inv :
    ((0 : ZMod 67) = (1 : ℕ) + (fo020 1 : ZMod 67) - 1) ∧
      ((1 : ZMod 67) = 0 + (fo020 2 : ZMod 67) - 1) ∧
      ((0 : ZMod 67) = 1 + (fo020 3 : ZMod 67) - 1) ∧
      1 + Sf fo020 3 = 3 ∧ ¬ BFSValidF 1 fo020 3 ∧
      ∀ x : ZMod 67, (0 : ZMod 67) * x - 1 ≠ 0 := by
  refine ⟨by simp [fo020], by simp [fo020]; norm_num, by simp [fo020], by decide, ?_, ?_⟩
  · intro hv
    have := hv 2 (by norm_num) (by norm_num)
    have h1 : Sf fo020 (2 - 1) = 0 := by decide
    omega
  · intro x; simp

/-! ## NC 3: the last-row gate is load-bearing (tiling) -/

def fo200 (i : ℕ) : ℕ := if i = 1 then 2 else 0

/-- `fo = 2, 0`, one root, `n = 2`: `q = 2, 1`; every gate but `isLast · q = 0` holds, the forest
does not tile. -/
theorem nc_queue_without_last :
    ((2 : ZMod 67) = (1 : ℕ) + (fo200 1 : ZMod 67) - 1) ∧
      ((1 : ZMod 67) = 2 + (fo200 2 : ZMod 67) - 1) ∧
      (2 : ZMod 67) ≠ 0 ∧ (1 : ZMod 67) ≠ 0 ∧
      1 + Sf fo200 2 ≠ 2 ∧ BFSValidF 1 fo200 2 := by
  refine ⟨by norm_num [fo200], by norm_num [fo200], by decide, by decide, by decide, ?_⟩
  intro i hi1 hi2
  interval_cases i <;> decide

#print axioms walkChip_rowLocal
#print axioms walkChip_masks
#print axioms gather_chal_walk
#print axioms gather_pub_walk
#print axioms walk_gates
#print axioms walk_traceNext
#print axioms walkK_traceNext
#print axioms walk_masks
#print axioms F_of_parts
#print axioms certNat_le_61
#print axioms walk_len_le
#print axioms walk_F_rows
#print axioms walk_fo_cast
#print axioms walk_q_closed
#print axioms walk_queue_ne
#print axioms walk_bfsValid
#print axioms walk_tiling
#print axioms walkHyps_of_chip
#print axioms rootGate_of_chip
#print axioms rlcW_eval
#print axioms vecAt_enc
#print axioms cur_row
#print axioms childL_row
#print axioms childR_row
#print axioms afo_cc_row
#print axioms walk_state_bits
#print axioms walk_accepts_of_chip
#print axioms records_genuine_of_chip
#print axioms nc_cert_without_exclusion
#print axioms nc_queue_without_inv
#print axioms nc_queue_without_last

end Nock.RedTeam.Batch1972
