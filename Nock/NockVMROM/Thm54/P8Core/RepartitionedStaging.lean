/-
  Nock/NockVMROM/Thm54/P8Core/RepartitionedStaging.lean

  This module sits BELOW the statement: it imports only `P8Core.DeployedStaging` (itself
  `OptimizedStrictFullPackageDefs`) and `RoundFibredSoundness`, and must not import
  `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.

  * Coins are named by role.
  * `newComputeColRound` / `newMemoryColRound` (and the role / slot maps): the column and slot
    round maps at the un-hosted compute width 309 and the memory width 205.
  * `AdaptiveEnvs`, `EnvLocal`, `readsOn_of_envLocal`, `not_mem_union_prior`: the bridge from an
    env-local bad set to `ReadsOn (D ∪ priorCoords)`, at row-environment granularity (no
    `StagedChip`).
  The compiled facts and the receipts are `Nock/RedTeam/Batch1409Thm54PartAStaging.lean`.
-/
import Nock.NockVMROM.Thm54.P8Core.DeployedStaging
import Nock.NockVMROM.Thm54.RoundFibredSoundness

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Nock.NockVMROM.Thm54.RepartitionedStaging

open Nock Nock.Reified Nock.Framework Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.Staging
open Nock.NockVMROM.Thm54.DeployedStaging Nock.NockVMROM.Thm54.RoundFibred

/-! ## 1. The chronology -/

/-- `sampledAfter := ![1,1,0,0,1,1,0,0,0,1,0,1]`: message M1 = {αM, z, a, b, c, λ} is sampled after the
base block B0, message M2 = {αC, γ, IOγ, IOpole, interPole, αW} after B1.  `M1_eq`, `M2_eq` and `moved_vs_deployed` are W-a-specific. -/
def repartitionedChronology : ChallengeChronology 3 where
  numChallenges := 12
  sampledAfter := ![1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1]

/-- The coins sampled after block 0 (message M1). -/
def M1 : Finset (Fin 12) :=
  Finset.univ.filter fun j => (repartitionedChronology.sampledAfter j : ℕ) = 0

/-- The coins sampled after block 1 (message M2). -/
def M2 : Finset (Fin 12) :=
  Finset.univ.filter fun j => (repartitionedChronology.sampledAfter j : ℕ) = 1

theorem M1_eq : M1 = {2, 3, 6, 7, 8, 10} := by decide
theorem M2_eq : M2 = {0, 1, 4, 5, 9, 11} := by decide

/-- Against `deployedChronology` (first eleven coins), exactly `αM` (2) and `λ` (10) move, from
M2 to M1. -/
theorem moved_vs_deployed :
    (Finset.univ.filter fun j : Fin 11 =>
      (deployedChronology.sampledAfter j : ℕ) ≠
        (repartitionedChronology.sampledAfter (Fin.castSucc j) : ℕ)) = {2, 10} := by decide

/-! ## 2. The round maps: compute width 309, memory width 205

Compute: the eight walk hosts are un-hosted (plain fingerprints), the walk count `W0` (cols
303..305) and walk accumulator `W1` (306..308) are appended, so every existing physical index is
preserved. -/

/-- Compute `𝕂`-role → round at the repartitioned schedule (the former hosts 6, 7, 9, 10, 18, 19,
27, 28 are round 1 now). -/
def newComputeRoleRound (r : ℕ) : ℕ :=
  if r ∈ [32, 33, 34, 35] then 2 else if r < 58 then 1 else 2

/-- Compute physical column → round at width 309. -/
def newComputeColRound (c : ℕ) : ℕ :=
  if c < 13 then 0 else if c < 202 then newComputeRoleRound ((c - 13) / 3)
  else if c < 296 then 0 else if c < 302 then 1 else if c = 302 then 0 else 2

/-- The round map as a `Fin 3`-valued schedule at width 309. -/
def newComputeRoundFin (c : Fin 309) : Fin 3 :=
  ⟨newComputeColRound c, by unfold newComputeColRound newComputeRoleRound; split_ifs <;> omega⟩

/-- Compute `𝕂` slot → after-block round (`αM` slot 0 and `λ` slot 9 are in M1 now). -/
def newComputeSlotRound (q : ℕ) : ℕ := if q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 10 then 1 else 0

/-- Memory `𝕂`-role → round: roles 3, 4, 8, 9, 13, 14 (`pw`/`counts`), 25 (`T`), 26 (`ts`) and 57
(`C'`) move from block 2 to block 1. -/
def newMemoryRoleRound (r : ℕ) : ℕ :=
  if r ∈ [3, 4, 8, 9, 13, 14, 25, 26, 57] then 1 else memoryRoleRound r

/-- Memory physical column → round at width 205 (unchanged width). -/
def newMemoryColRound (c : ℕ) : ℕ :=
  if c < 6 then 0 else if c = 153 ∨ c = 154 then 0
  else if c < 180 then newMemoryRoleRound ((c - 6) / 3) else 0

/-- The memory round map as a `Fin 3`-valued schedule at width 205. -/
def newMemoryRoundFin (c : Fin 205) : Fin 3 :=
  ⟨newMemoryColRound c, by unfold newMemoryColRound newMemoryRoleRound memoryRoleRound; split_ifs <;> omega⟩

/-- Memory slot rounds: slots 2..7 are after block 1; slot 3 is the walk coin (`αW`, M2); slot 8
(`λ`) is M1 now; slot 9 is `αW` in the "new slot" variant. -/
def newMemorySlotRound (q : ℕ) : ℕ := if (2 ≤ q ∧ q ≤ 7) ∨ q = 9 then 1 else 0

set_option maxRecDepth 20000 in
/-- The compute blocks at width 309: `[108, 168, 33]`. -/
theorem newComputeBlocks :
    ((List.finRange 3).map fun r =>
      (Finset.univ.filter fun c : Fin 309 => newComputeRoundFin c = r).card) = [108, 168, 33] := by
  decide

set_option maxRecDepth 20000 in
/-- The memory blocks at width 205: `[85, 75, 45]`. -/
theorem newMemoryBlocks :
    ((List.finRange 3).map fun r =>
      (Finset.univ.filter fun c : Fin 205 => newMemoryRoundFin c = r).card) = [85, 75, 45] := by
  decide

/-! ## 3. The generic adaptive bridge, at row-environment granularity (no `StagedChip`) -/

section Bridge
variable {n M : ℕ} {K F : Type} [Fintype K] [DecidableEq K]

/-- An adaptive prover: committed memory row environments as functions of the coin vector, each
`𝕂` role / base column reading only coins sampled strictly before its block. -/
structure AdaptiveEnvs (n M : ℕ) (K F : Type) where
  roleRound : ℕ → ℕ
  baseRound : ℕ → ℕ
  sampledAfter : Fin n → ℕ
  envK : (Fin n → K) → Fin M → Env K
  envF : (Fin n → K) → Fin M → Env F
  K_reads : ∀ r χ χ', (∀ j, sampledAfter j < roleRound r → χ j = χ' j) →
    ∀ i, (envK χ i).trace r = (envK χ' i).trace r
  F_reads : ∀ b χ χ', (∀ j, sampledAfter j < baseRound b → χ j = χ' j) →
    ∀ i, (envF χ i).trace b = (envF χ' i).trace b

/-- A bad set is *env-local* on roles `S` and base columns `B`. -/
def EnvLocal {β : Type} (S B : List ℕ) (f : (Fin M → Env K) → (Fin M → Env F) → β) : Prop :=
  ∀ eK eK' eF eF', (∀ i, ∀ r ∈ S, (eK i).trace r = (eK' i).trace r) →
    (∀ i, ∀ b ∈ B, (eF i).trace b = (eF' i).trace b) → f eK eF = f eK' eF'

/-- **Bridge.** If coin `i`'s bad set is env-local on a read set committed no later than coin `i`'s
message, and reads directly only coins in `D ∌ i`, then as a function of the coin vector it
`ReadsOn (D ∪ priorCoords)` — the premise of `cylinder_card_le` with `i ∉ dep`. -/
theorem readsOn_of_envLocal (A : AdaptiveEnvs n M K F) (i : Fin n) (S B : List ℕ) (D : Finset (Fin n))
    (bad : (Fin M → Env K) → (Fin M → Env F) → (Fin n → K) → Finset K)
    (hloc : ∀ χ, EnvLocal S B (fun eK eF => bad eK eF χ))
    (hcoin : ∀ eK eF, ReadsOn (C := K) D (bad eK eF))
    (hS : ∀ r ∈ S, A.roleRound r ≤ A.sampledAfter i) (hB : ∀ b ∈ B, A.baseRound b ≤ A.sampledAfter i) :
    ReadsOn (C := K) (D ∪ priorCoords A.sampledAfter i) (fun χ => bad (A.envK χ) (A.envF χ) χ) := by
  intro χ χ' h
  have hp : ∀ j, A.sampledAfter j < A.sampledAfter i → χ j = χ' j := fun j hj =>
    h j (Finset.mem_union_right _ (by simp [priorCoords, hj]))
  have e1 : bad (A.envK χ) (A.envF χ) χ = bad (A.envK χ') (A.envF χ') χ :=
    hloc χ _ _ _ _ (fun i' r hr => A.K_reads r χ χ' (fun j hj => hp j (lt_of_lt_of_le hj (hS r hr))) i')
      (fun i' b hb => A.F_reads b χ χ' (fun j hj => hp j (lt_of_lt_of_le hj (hB b hb))) i')
  show bad (A.envK χ) (A.envF χ) χ = bad (A.envK χ') (A.envF χ') χ'
  rw [e1]
  exact hcoin _ _ χ χ' (fun j hj => h j (Finset.mem_union_left _ hj))

theorem not_mem_union_prior (A : AdaptiveEnvs n M K F) (i : Fin n) (D : Finset (Fin n)) (hD : i ∉ D) :
    i ∉ D ∪ priorCoords A.sampledAfter i := by
  simp [hD, priorCoords]

end Bridge

end Nock.NockVMROM.Thm54.RepartitionedStaging
