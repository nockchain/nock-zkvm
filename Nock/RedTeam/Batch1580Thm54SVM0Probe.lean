/-
  Nock/RedTeam/Batch1580Thm54SVM0Probe.lean

  * **1(a)** `certAxisOfEnvs_congr`: the recovered axis `certAxisOfEnvs envs e` (the walk instance's
    `R.axis` / `CF.axB0`) reads only the row-environment trace slots `{0, 2, 5, …, 9} ∪ [202, 271)`;
    `certAxis_reads_round0`: every one of them is a round-0 column of the 309 layout
    (`newComputeColRound = 0`), none of `296 … 301` (round 1).
  * **1(b)** `compute_record_rounds`: every trace variable of every slot of every compute request
    record (`OptimizedComputeHostileAccumulator.rowRecord`, the records `rows309` sums) has mixed-layout
    round `≤ 1` and is not one of the round-2 `𝕂`-roles `32 … 35`;
    `memory_record_rounds`: the memory response record roles `19 … 26`, `57`, the `ver` role `39` and
    the base column `181` are of round `≤ 1` (`newMemoryRoleRound` / `newMemoryColRound`).
  * **The frame finding** (`compute_record_reads_lambda`, `compute_record_reads_alphaM`,
    `rowRecord309_slot6`): the compute request records are NOT functions of the compute columns: slot
    `6` of record `0` is the coin `λ` itself (compute challenge `9`, frame12 coin `10`) and slot `7` of
    record `0` is `ln_prev · αM` (challenge `0`, frame12 coin `2`).  `CompSoundnessFamily.reqRecords`
    (I0 r2) has no coin argument, so `reqFacts_records` cannot be discharged at the walk instance with
    the chip's records.  Both coins are M1 (`frame12.sampledAfter = 0`), so the IO summand's read set
    `coinsBelow (max recRound respRound)` already covers them: the repair is the coin argument, not a
    new round.
  * **1(c)** answered in the report from `PreSeedCensus.requestTargets` (`read_root` serves the root,
    `verify_child` the child, at the record's exponent `S + j + 1`, uniformly in `j`).
-/
import Nock.NockVMROM.Thm54.P8Core.SVIOCompute
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 20000

namespace Nock.RedTeam.Batch1580

open Nock Nock.Reified Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.RepartitionedStaging
open Nock.NockVMROM.Thm54.StrategyOfTracesR0 (certAxisOfEnvs)
open scoped Polynomial
open Module Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.OptimizedStrictPackage

/-! ## 1(a): the recovered axis reads round-0 columns only -/

section Axis

variable {K : Type} [Field K] {N : ℕ}

/-- The trace slots `certAxisOfEnvs` reads. -/
def certReadSet (c : ℕ) : Prop := c = 0 ∨ c = 2 ∨ (5 ≤ c ∧ c ≤ 9) ∨ (202 ≤ c ∧ c < 271)

theorem certAxis_reads_round0 (c : ℕ) (hc : certReadSet c) : newComputeColRound c = 0 := by
  unfold certReadSet at hc
  unfold newComputeColRound
  rcases hc with rfl | rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp
  · simp
  · rw [if_pos (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem certReadSet_not_round1 (c : ℕ) (hc : certReadSet c) : ¬ (296 ≤ c ∧ c < 302) := by
  unfold certReadSet at hc; omega

variable (e1 e2 : Fin N → Env K)

theorem computeArity_congr (i : Fin N) (h : ∀ c, certReadSet c → (e1 i).trace c = (e2 i).trace c) :
    DecodedLambdaEvent.computeArity (e1 i) = DecodedLambdaEvent.computeArity (e2 i) := by
  unfold DecodedLambdaEvent.computeArity
  have h0 := h 0 (by unfold certReadSet; omega)
  have h2 := h 2 (by unfold certReadSet; omega)
  have h5 := h 5 (by unfold certReadSet; omega)
  have h6 := h 6 (by unfold certReadSet; omega)
  have h7 := h 7 (by unfold certReadSet; omega)
  have h8 := h 8 (by unfold certReadSet; omega)
  have h9 := h 9 (by unfold certReadSet; omega)
  rw [h0, h2, h5, h6, h7, h8, h9]

theorem rowShift_congr (i : Fin N) (h : ∀ c, certReadSet c → (e1 i).trace c = (e2 i).trace c) :
    DecodedLambdaEvent.rowShift (e1 i) = DecodedLambdaEvent.rowShift (e2 i) := by
  unfold DecodedLambdaEvent.rowShift
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [h (265 + k) (by unfold certReadSet; omega)]

theorem rowBits_congr (i : Fin N) (h : ∀ c, certReadSet c → (e1 i).trace c = (e2 i).trace c) :
    DecodedLambdaEvent.rowBits (e1 i) = DecodedLambdaEvent.rowBits (e2 i) := by
  funext k
  unfold DecodedLambdaEvent.rowBits
  by_cases hk : 1 ≤ k ∧ k ≤ 63
  · rw [h (202 + (k - 1)) (by unfold certReadSet; omega)]
  · simp only [decide_eq_decide]
    constructor <;> intro hh <;> exact absurd ⟨hh.1, hh.2.1⟩ hk

/-- **1(a)**: `certAxisOfEnvs` is a function of the round-0 read set `certReadSet` only. -/
theorem certAxisOfEnvs_congr (h : ∀ i c, certReadSet c → (e1 i).trace c = (e2 i).trace c) (e : ℕ) :
    certAxisOfEnvs e1 e = certAxisOfEnvs e2 e := by
  have har : ∀ i, DecodedLambdaEvent.computeArity (e1 i) = DecodedLambdaEvent.computeArity (e2 i) :=
    fun i => computeArity_congr e1 e2 i (h i)
  have hpre : DecodedLambdaEvent.computePrefix e1 = DecodedLambdaEvent.computePrefix e2 := by
    funext i
    unfold DecodedLambdaEvent.computePrefix
    exact Finset.sum_congr rfl fun i' _ => har i'
  have hloc : DecodedLambdaEvent.locateExp e1 e = DecodedLambdaEvent.locateExp e2 e := by
    unfold DecodedLambdaEvent.locateExp
    rw [hpre]
    simp only [har]
  have hcert : ∀ i j, DecodedLambdaEvent.slotCert e1 i j = DecodedLambdaEvent.slotCert e2 i j := by
    intro i j
    have h0 := h i 0 (by unfold certReadSet; omega)
    have h9 := h i 9 (by unfold certReadSet; omega)
    unfold DecodedLambdaEvent.slotCert
    rw [rowShift_congr e1 e2 i (h i), rowBits_congr e1 e2 i (h i), h0, h9]
  unfold certAxisOfEnvs DecodedLambdaEvent.decodedShift DecodedLambdaEvent.decodedBits
  rw [hloc]
  rcases DecodedLambdaEvent.locateExp e2 e with _ | ⟨i, j⟩
  · rfl
  · simp only [hcert]

end Axis

/-! ## 1(b): the record roles' rounds -/

/-- Variables of an expression, as a list (decidable by evaluation). -/
def varsL : Expr → List (VarKind × ℕ)
  | .Var k i => [(k, i)]
  | .Const _ => []
  | .Add a b | .Sub a b | .Mul a b => varsL a ++ varsL b
  | .Neg a | .Pow a _ => varsL a

/-- Lookup of a variable in an environment. -/
def lookupV {K : Type} (env : Env K) : VarKind × ℕ → K
  | (.traceCur, i) => env.trace i
  | (.traceNext, i) => env.traceNext i
  | (.challenge, i) => env.chal i
  | (.publicVal, i) => env.pub i

/-- `varsL` is the read set of `Expr.eval`. -/
theorem eval_congr {K : Type} [Field K] (e : Expr) (E1 E2 : Env K)
    (h : ∀ v ∈ varsL e, lookupV E1 v = lookupV E2 v) : e.eval E1 = e.eval E2 := by
  induction e with
  | Var k i =>
      have := h (k, i) (by simp [varsL])
      cases k <;> simpa [Expr.eval, lookupV] using this
  | Const c => rfl
  | Add a b iha ihb =>
      simp only [Expr.eval]
      rw [iha fun v hv => h v (by simp [varsL, hv]), ihb fun v hv => h v (by simp [varsL, hv])]
  | Sub a b iha ihb =>
      simp only [Expr.eval]
      rw [iha fun v hv => h v (by simp [varsL, hv]), ihb fun v hv => h v (by simp [varsL, hv])]
  | Mul a b iha ihb =>
      simp only [Expr.eval]
      rw [iha fun v hv => h v (by simp [varsL, hv]), ihb fun v hv => h v (by simp [varsL, hv])]
  | Neg a iha =>
      simp only [Expr.eval]
      rw [iha fun v hv => h v (by simp [varsL, hv])]
  | Pow a n iha =>
      simp only [Expr.eval]
      rw [iha fun v hv => h v (by simp [varsL, hv])]

/-- The source expression of slot `c` of compute request record `j` (`rowRecord`'s body). -/
def recSlotExpr (j c : ℕ) : Expr :=
  (if c = 9 then sampledSlotE .traceCur (67 + 8 * j)
   else if c = 6 then sampledSlotT .traceCur (67 + 8 * j)
   else if c = 8 then sampledSlotC .traceCur (67 + 8 * j)
   else computeTraceSubst .traceCur (67 + 8 * j + c)).subst finalSampledNamespace

theorem rowRecord_eq_recSlotExpr {F K : Type} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (j : Fin 3) (c : Fin 10) :
    rowRecord env j c = (recSlotExpr j c).eval env.toSourceEnv := by
  unfold rowRecord recSlotExpr
  split_ifs <;> rfl

/-- The round of a mixed-layout trace index (`CorrectedFinalTypedEnv.toSourceEnv`): base `0..12`,
`𝕂`-roles `13..75` (role `i − 13`), certificate / `T` / `S` columns `≥ 202` physical. -/
def mixedRound (i : ℕ) : ℕ :=
  if i < 13 then 0 else if i < 76 then newComputeRoleRound (i - 13) else newComputeColRound i

/-- Round-2 `𝕂` roles `32..35` (the sampled-IO hosts) in the mixed layout. -/
def isRound2Role (i : ℕ) : Bool := decide (13 + 32 ≤ i ∧ i < 13 + 36)

/-- **1(b), compute**: every trace variable of every compute request record slot is of round `≤ 1`
and is not a round-2 role. -/
theorem compute_record_rounds :
    ∀ j < 3, ∀ c < 10, ∀ v ∈ varsL (recSlotExpr j c),
      v.1 = .traceCur → mixedRound v.2 ≤ 1 ∧ isRound2Role v.2 = false := by
  decide

/-- **1(b), memory**: the response record's roles, the `ver` role and the exponent column. -/
theorem memory_record_rounds :
    (∀ r ∈ [19, 20, 21, 22, 23, 24, 25, 26, 57, 39], newMemoryRoleRound r ≤ 1) ∧
      newMemoryColRound 181 = 0 ∧ newMemoryRoleRound 39 = 0 := by
  decide

/-! ## The frame finding: the compute records read the coins `λ` and `αM` -/

/-- Slot `6` of record `0` is the `λ` coin variable (compute challenge `9`). -/
theorem compute_record_reads_lambda : recSlotExpr 0 6 = .Var .challenge 9 := rfl

/-- Slot `7` of record `0` is `ln_prev · αM` (compute challenge `0`). -/
theorem compute_record_reads_alphaM : (VarKind.challenge, 0) ∈ varsL (recSlotExpr 0 7) := by
  decide

section At309

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [Fintype F] [DecidableEq K]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (pubVal : ℕ → F)
  (orbit : StrictOrbitDomain F 3 h) (c : OptimizedProductionChallengeTuple K F)

/-- **At the 309 chip, any trace, any row**: the committed record `0`'s slot `6` IS the tuple's `λ`.
So the records `rows309` sums are not a function of the compute columns alone. -/
theorem rowRecord309_slot6
    (Qc : Fin (Unhosted309.computeChipAt309 hn nodes b pubVal orbit c).rap.w → F[X]) (i : Fin n) :
    rowRecord (SVIO.env309 hn nodes b pubVal orbit c Qc i) 0 ⟨6, by decide⟩ = c.2.2.2.lambda := by
  rw [rowRecord_eq_recSlotExpr]
  show Expr.eval (.Var .challenge 9) _ = _
  simp only [Expr.eval]
  exact SVIO.env309_chal hn nodes b pubVal orbit c Qc i 9 (by decide)

end At309

end Nock.RedTeam.Batch1580

#print axioms Nock.RedTeam.Batch1580.certAxisOfEnvs_congr
#print axioms Nock.RedTeam.Batch1580.certAxis_reads_round0
#print axioms Nock.RedTeam.Batch1580.compute_record_rounds
#print axioms Nock.RedTeam.Batch1580.memory_record_rounds
#print axioms Nock.RedTeam.Batch1580.compute_record_reads_alphaM
#print axioms Nock.RedTeam.Batch1580.rowRecord309_slot6
