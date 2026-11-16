/-
  Nock/RedTeam/Batch1062Thm54RepairIINonVacuity.lean

  * Tier A, `p = 769`, the canonical `α = φ 4` of order 192: `memRows = 184`, `acc ≤ 24`, so the
    signed `hwin` is `27 < 192 ∧ 184 ≤ 192` (`tierA_weakest`).
  * fib / matmul Goldilocks (`α = ω`, order `2^16`): `1277 ≤ 2^16` / `30936 ≤ 2^16`
    (`fib_weakest`, `matmul_weakest`).
  * The paper configuration: at Goldilocks `hF` caps `programFit` (hence both row counts and
    `acc + 1`) at `2^32` (`goldilocks_fit_le_of_hF`), and the primitive timestamp base has order
    `p^3 − 1 ≈ 2^192` (`goldilocksTimestampBase_order_value`), so every program `hF` admits meets
    the signed `hwin` (`goldilocks_weakest`).
  * The fit form (not signed) also holds at all four (`*_fit_window`, kept as the record of the
    comparison); `narrowing_window` / `narrowing_window_sharp`: the fit form excludes exactly the
    four orders `orderOf α ∈ {memShape, …, memShape + 3}` that the signed form admits.

  The end-to-end non-vacuity receipts at `nockCompiles` / `nockCompiles_zmod` under the new `hwin`
  are `Batch327` (`b327_*_from_nockCompiles`) and `Batch332` (the three `zmod` literals).
-/
import Nock.RedTeam.Batch327Thm54FinalShapeLiterals
import Nock.NockVMROM.Thm54.TraceGen.GenFibGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulGoldilocksResiduals
import Nock.NockVMROM.Thm54.TraceGen.GoldilocksTimestampBase

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch1062

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA GF GK
open Nock.RedTeam

-- `programFit` / `programMemShape` carry `[Fintype K] [DecidableEq K] [CharP K (ringChar K)]`
-- from their section (`GenNockCompilesCarrier.lean:82-83`); the literals need the `CharP` ones.
local instance charRingDK : CharP Batch327.DK (ringChar Batch327.DK) := ringChar.charP _
local instance charRingFK : CharP Batch327.FK (ringChar Batch327.FK) := ringChar.charP _
local instance charRingGK : CharP Batch327.GK (ringChar Batch327.GK) := ringChar.charP _

/-! ## Tier A, `p = 769`, `α = φ 4` (`orderOf = 192`) -/

theorem tierA_compRows : programCompRows (dotTree (K := Batch327.DK)) = 8 := by
  dsimp [programCompRows]
  rw [← genComputeRows_bfsForest_length DotConfig769.seedZ DotConfig769.alphaA]
  exact Batch180.dot_compRowsLen

theorem tierA_memShape :
    programMemShape DotConfig769.alphaA (dotTree (K := Batch327.DK)) = 184 := by
  rw [programMemShape_spec (lmb := MemoryTable.formRDefault) DotConfig769.seedZ]
  exact Batch180.dot_memRowsLen

theorem tierA_acc : programAcc (dotTree (K := Batch327.DK)) ≤ 24 := Batch180.dot_accAt_le

/-- `programFit = 185` at Tier A: the memory forest (184 rows) plus one. -/
theorem tierA_fit : programFit DotConfig769.alphaA (dotTree (K := Batch327.DK)) = 185 := by
  have hc := tierA_compRows
  have hm := tierA_memShape
  have ha := tierA_acc
  apply le_antisymm
  · exact max_le (max_le (by omega) (by omega)) (by omega)
  · have := programMemShape_succ_le_fit DotConfig769.alphaA (dotTree (K := Batch327.DK))
    omega

/-- **The strengthened window holds at Tier A's canonical `α`: `187 < 192`.** -/
theorem tierA_fit_window :
    programFit DotConfig769.alphaA (dotTree (K := Batch327.DK)) + 2
      < orderOf DotConfig769.alphaA := by
  rw [tierA_fit, Batch180.alphaA_order_eq_192]
  norm_num

/-- The weakest sufficient condition (what `hordM` consumes) at Tier A: `184 ≤ 192`. -/
theorem tierA_weakest :
    programAcc (dotTree (K := Batch327.DK)) + 3 < orderOf DotConfig769.alphaA ∧
      programMemShape DotConfig769.alphaA (dotTree (K := Batch327.DK))
        ≤ orderOf DotConfig769.alphaA := by
  rw [tierA_memShape, Batch180.alphaA_order_eq_192]
  have := tierA_acc
  omega

/-- The margin the fit form leaves at Tier A is five: `192 − 187`. -/
theorem tierA_margin :
    orderOf DotConfig769.alphaA -
      (programFit DotConfig769.alphaA (dotTree (K := Batch327.DK)) + 2) = 5 := by
  rw [tierA_fit, Batch180.alphaA_order_eq_192]

/-! ## Goldilocks instances (`α = ω`, `orderOf = 2^16`) -/

theorem fib_fit_window :
    programFit FibConfigGoldilocks.alphaA (fibTree (K := Batch327.FK)) + 2
      < orderOf FibConfigGoldilocks.alphaA := by
  have hord := FibConfigGoldilocks.alphaA_order
  have hcomp : programCompRows (fibTree (K := Batch327.FK)) = 33 := by
    dsimp [programCompRows]
    rw [← genComputeRows_bfsForest_length (0 : Batch327.FK) FibConfigGoldilocks.alphaA]
    exact fib_comp_rows 0 _
  have hmem : programMemShape FibConfigGoldilocks.alphaA (fibTree (K := Batch327.FK)) = 1277 :=
    fib_mem_rows 0 _
  have hacc : programAcc (fibTree (K := Batch327.FK)) ≤ 99 := fib_acc_le
  have hfit : programFit FibConfigGoldilocks.alphaA (fibTree (K := Batch327.FK)) ≤ 1278 :=
    max_le (max_le (by omega) (by omega)) (by omega)
  omega

theorem matmul_fit_window :
    programFit MatmulConfigGoldilocks.alphaA (mmTree (K := Batch327.GK)) + 2
      < orderOf MatmulConfigGoldilocks.alphaA := by
  have hord := MatmulConfigGoldilocks.alphaA_order
  have hcomp : programCompRows (mmTree (K := Batch327.GK)) = 401 := by
    dsimp [programCompRows]
    rw [← genComputeRows_bfsForest_length (0 : Batch327.GK) MatmulConfigGoldilocks.alphaA]
    exact mm_comp_rows 0 _
  have hmem : programMemShape MatmulConfigGoldilocks.alphaA (mmTree (K := Batch327.GK)) = 30936 :=
    mm_mem_rows 0 _
  have hacc : programAcc (mmTree (K := Batch327.GK)) ≤ 1203 := mm_acc_le
  have hfit : programFit MatmulConfigGoldilocks.alphaA (mmTree (K := Batch327.GK)) ≤ 30937 :=
    max_le (max_le (by omega) (by omega)) (by omega)
  omega

/-- **The signed `hwin` at fib Goldilocks** (`α = ω`, `orderOf = 2^16`): `102 < 2^16`,
`1277 ≤ 2^16`. -/
theorem fib_weakest :
    programAcc (fibTree (K := Batch327.FK)) + 3 < orderOf FibConfigGoldilocks.alphaA ∧
      programMemShape FibConfigGoldilocks.alphaA (fibTree (K := Batch327.FK))
        ≤ orderOf FibConfigGoldilocks.alphaA :=
  ⟨fib_hwin, fib_hmemOrd⟩

/-- **The signed `hwin` at matmul Goldilocks** (`α = ω`, `orderOf = 2^16`): `1206 < 2^16`,
`30936 ≤ 2^16`. -/
theorem matmul_weakest :
    programAcc (mmTree (K := Batch327.GK)) + 3 < orderOf MatmulConfigGoldilocks.alphaA ∧
      programMemShape MatmulConfigGoldilocks.alphaA (mmTree (K := Batch327.GK))
        ≤ orderOf MatmulConfigGoldilocks.alphaA :=
  ⟨mm_hwin, mm_hmemOrd⟩

/-! ## The paper configuration: Goldilocks, primitive timestamp base -/

/-- At Goldilocks, §1's `hF` (`3 · 2^orbitHeight(programFit) ∣ p − 1`) caps `programFit` at
`2^32` (`v₂(p − 1) = 32`). -/
theorem goldilocks_fit_le_of_hF (t : NTree (GenComputeRow Nock.Field.K))
    (hF : 3 * 2 ^ orbitHeight (programFit goldilocksTimestampBase t) ∣ Nock.Field.p - 1) :
    programFit goldilocksTimestampBase t ≤ 2 ^ 32 := by
  have hp : Nock.Field.p - 1 = 2 ^ 32 * 4294967295 := by rw [Nock.Field.p_eq]; norm_num
  have h2 : 2 ^ orbitHeight (programFit goldilocksTimestampBase t) ∣ Nock.Field.p - 1 :=
    (Dvd.intro_left 3 rfl).trans hF
  rw [hp] at h2
  have hcop : Nat.Coprime (2 ^ orbitHeight (programFit goldilocksTimestampBase t)) 4294967295 :=
    Nat.Coprime.pow_left _ ((Nat.prime_two.coprime_iff_not_dvd).mpr (by norm_num))
  have h32 : 2 ^ orbitHeight (programFit goldilocksTimestampBase t) ∣ 2 ^ 32 :=
    hcop.dvd_of_dvd_mul_right h2
  have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h32
  exact (le_two_pow_orbitHeight _).trans (Nat.pow_le_pow_right (by norm_num) hle)

/-- **At the paper configuration the strengthened window holds for every program `hF` admits**:
the primitive timestamp base has order `p^3 − 1 ≈ 2^192`, far above `2^32 + 2`. -/
theorem goldilocks_fit_window (t : NTree (GenComputeRow Nock.Field.K))
    (hF : 3 * 2 ^ orbitHeight (programFit goldilocksTimestampBase t) ∣ Nock.Field.p - 1) :
    programFit goldilocksTimestampBase t + 2 < orderOf goldilocksTimestampBase := by
  have := goldilocks_fit_le_of_hF t hF
  rw [goldilocksTimestampBase_order_value]
  omega

/-- **At the paper configuration the signed `hwin` holds for every program `hF` admits**
(`weakest_of_fit` of the fit window: the fit form implies the signed one). -/
theorem goldilocks_weakest (t : NTree (GenComputeRow Nock.Field.K))
    (hF : 3 * 2 ^ orbitHeight (programFit goldilocksTimestampBase t) ∣ Nock.Field.p - 1) :
    programAcc t + 3 < orderOf goldilocksTimestampBase ∧
      programMemShape goldilocksTimestampBase t ≤ orderOf goldilocksTimestampBase := by
  have h := goldilocks_fit_window t hF
  have ha := programAcc_succ_le_fit goldilocksTimestampBase t
  have hm := programMemShape_succ_le_fit goldilocksTimestampBase t
  omega

/-- The narrowing, quantified: `programFit ≥ programMemShape + 1`, so the fit form asks
`programMemShape + 4 ≤ orderOf α` where `hordM` consumes only `programMemShape ≤ orderOf α`.
With the timestamp half met, the fit form differs from the weakest form exactly on the
FOUR-element window `orderOf α ∈ {memShape, memShape + 1, memShape + 2, memShape + 3}`; any `α`
outside it is admitted by both. -/
theorem narrowing_window {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] (α : K) (t : NTree (GenComputeRow K))
    (hacc : programAcc t + 3 < orderOf α)
    (hmem : programMemShape α t ≤ orderOf α)
    (hout : ¬ (programMemShape α t ≤ orderOf α ∧ orderOf α ≤ programMemShape α t + 3)) :
    programFit α t + 2 < orderOf α := by
  have h3 : programMemShape α t + 4 ≤ orderOf α := by
    by_contra hcon
    exact hout ⟨hmem, by omega⟩
  have hc : programCompRows t + 2 < orderOf α := by
    have := programAcc_ge_compRows t
    unfold programCompRows
    omega
  have h1 : programCompRows t < orderOf α - 2 := by omega
  have h2 : programMemShape α t + 1 < orderOf α - 2 := by omega
  have h3' : programAcc t + 1 < orderOf α - 2 := by omega
  have hfit : programFit α t < orderOf α - 2 := max_lt (max_lt h1 h2) h3'
  omega

/-- The converse: inside that window the fit form fails although `hordM`'s need is met. -/
theorem narrowing_window_sharp {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] (α : K) (t : NTree (GenComputeRow K))
    (hmem : programMemShape α t ≤ orderOf α)
    (hin : orderOf α ≤ programMemShape α t + 3) :
    ¬ (programFit α t + 2 < orderOf α) := by
  have := programMemShape_succ_le_fit α t
  omega

end Nock.RedTeam.Batch1062

#print axioms Nock.RedTeam.Batch1062.tierA_fit_window
#print axioms Nock.RedTeam.Batch1062.tierA_weakest
#print axioms Nock.RedTeam.Batch1062.fib_weakest
#print axioms Nock.RedTeam.Batch1062.matmul_weakest
#print axioms Nock.RedTeam.Batch1062.goldilocks_weakest
#print axioms Nock.RedTeam.Batch1062.fib_fit_window
#print axioms Nock.RedTeam.Batch1062.matmul_fit_window
#print axioms Nock.RedTeam.Batch1062.goldilocks_fit_window
#print axioms Nock.RedTeam.Batch1062.narrowing_window
#print axioms Nock.RedTeam.Batch1062.narrowing_window_sharp
