/-
  Nock/RedTeam/Batch2903Thm54C2RowSemChip.lean

  * `rowSemX_of_chip`: a `computeChipVCLHX` row (base gates, one-hot state) whose consumed records
    are served and genuine (`RecOK`, the named memory hypothesis) satisfies `LocalVSX.RowSemX` in
    every state `0..16`, for `17 < p`, with ONE extra named hypothesis `HalvingOK` on `s10L` rows.

  **FINDING (U at the chip; compiled at the field level: `s10L_halving_wraps_goldilocks`).**  The
  `s10L` gates are `a = 2v + β`, `a ≠ 1`, `ax2 = a + 1 − 2β`, `β` boolean.  Nothing ties `β` to the
  parity of `a`: with the WRONG `β`, `v = (a − β)/2` in `𝔽` is `(a − β + p)/2`.  At Goldilocks that is
  below `2^63` for small `a` — a 63-bit axis the walk can serve — so the child chain row (formula
  `(0, v)`) can be an `s10L` row at an unrelated axis `a'`, and the pair checks agreement at `a + 1`
  instead of the sibling `a − 1`.  Witness at `p = 2^64 − 2^32 + 1`: `a = 5`, `β = 0`,
  `v = 9223372034707292163 < 2^63`, `ax2 = 6 ≠ 5 xor 1 = 4`, and the child's own sibling axis
  `v xor 1` is `< 2^63`.  Sketch (NOT compiled at the chip): `*[s [10 [[5 c] d]]]` with `*[s c] = /[5 old]`
  and `old` of depth 63 along `a'`; the chain checks `old` and `e` agree at `6`, at `2` (via `a'`'s top
  step) and along `a'`'s siblings, so `e` may differ from the true edit exactly at `a'`.  The 63-bit
  argument (`hax63_fold_exact`) does not cover it: it needs walk axes `< (p − 1)/2`, i.e. one bit
  below `2^63` at Goldilocks.  `rowSemX_of_chip` therefore carries `HalvingOK` (`2·val v + 1 < p`,
  `1 ≤ val v`) as a NAMED hypothesis.  Candidate repairs (no coin, no summand, no depth counter):
  bound the walk's axes by `2^62` (one bit of `haxis`), or `p > 2^64`, or carry the walk's `(prefix,
  bit)` in the `s10L` pair key instead of the folded axis.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX

namespace Nock.RedTeam.Batch2903

open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX

/-- **FINDING, field level**: at Goldilocks, the three `s10L` gates and `a ≠ 1` hold with `a = 5`,
`β = 0` and a WRAPPED `v` below `2^63`; the read axis `ax2 = 6` is not `5 xor 1 = 4`, `v` is not
`5 / 2`, the child's sibling axis `v xor 1` is a 63-bit axis, and `HalvingOK` fails. -/
theorem s10L_halving_wraps_goldilocks :
    let q := 18446744069414584321
    let a : ZMod q := 5
    let β : ZMod q := 0
    let v : ZMod q := 9223372034707292163
    let w : ZMod q := 13835058052060938241
    let ax2 : ZMod q := 6
    a - 2 * v - β = 0 ∧ (a - 1) * w - 1 = 0 ∧ ax2 - a - 1 + 2 * β = 0 ∧
      v.val < 2 ^ 63 ∧ v.val ≠ a.val / 2 ∧ ax2.val ≠ a.val ^^^ 1 ∧ v.val ^^^ 1 < 2 ^ 63 ∧
      ¬ (2 * v.val + 1 < q) := by
  decide +kernel

#print axioms s10L_halving_wraps_goldilocks
#print axioms rowSemX_of_chip
#print axioms differ_leaves
#print axioms sem_s4
#print axioms sem_s5
#print axioms sem_s10
#print axioms sem_s10L
#print axioms sem_s11j

end Nock.RedTeam.Batch2903
