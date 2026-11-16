/-
  Nock/RedTeam/Batch589Thm54RowLevelChronology.lean

  The Form R
  names are not on live: lane objects are cited `file:line`, and local copies come from `Batch588`.

  What is compiled here:
  * §1 **The capstone samples no coin at all.**  The sampled-tuple chips (`memoryChipAt`,
    `computeChipAt`, `memoryChalValOfTuple`, `computeChalValOfTuple`, `honestTuple`) and the
    round/chronology model (`GigaChips.nockChronology`, `memorySchedule`, `memRoundOf`) are outside
    the proof closures of BOTH `nockCompiles_zmod` and `OptimizedFullStrictThm54Statement`
    (`run_cmd`, with positive controls).  At the capstone every chip coin, `λ` included, is the
    package's fixed value; the deployed memory RAP is one round (`deployed_memory_one_round`).
  * §2 **Chronology, in the tree's only round model (`GigaChips`, off-capstone).**  `mem.axis`
    (staged column `29`) is a round-0, coin-free column (`staged_axis_column_coin_free`), and the
    chronology has eight slots, none of them `λ` (`chronology_has_no_lambda_slot`).  Under F1 that
    column holds `T = λ^m`; no slot of round 0 can supply it (`r1_axis_value_unschedulable`).  Two
    repaired schedules are compiled on the live 44-column chip — `λ` with `α` (message 1, column
    `29` → round 2, widths `8/19/17`) and `λ` with `z` (message 0, column `29` → round 1, widths
    `8/20/16`) — both commit-before-sample (`repairedSchedule_msg1`, `repairedSchedule_msg0`).
  * §3 **The lane's compute `λ` gate reads the wrong coin.**  The `𝕂` coin index `9` lives at raw slots `27..29`
    (`kcoin_nine_raw_slots`).
  * §4 **One honest row, two `λ`s.**
-/
import Nock.RedTeam.Batch587Thm54RowLevelInventory
import Nock.NockVMROM.Thm54.NockGigaRAP
import Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch589

open Lean Meta Elab Command
open Nock Nock.NockVMROM.Thm54
open Nock.RedTeam.Batch588
open Module Nock.Reified StrictExtension

/-! ## §1 The capstone samples no coin -/

/-- The names whose absence from both capstone closures is asserted. -/
def sampledAndScheduled : List Name :=
  [ `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.honestTuple,
    `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage.memoryChipAt_honest_of_chalVal,
    `Nock.NockVMROM.Thm54.GigaChips.nockChronology,
    `Nock.NockVMROM.Thm54.GigaChips.memorySchedule,
    `Nock.NockVMROM.Thm54.GigaChips.memRoundOf ]

/-- Positive controls: the honest package objects the capstone does consume. -/
def capstoneControls : List Name :=
  [ `Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedMemoryRealizationAt,
    `Nock.NockVMROM.Thm54.SemanticStrategy.BindMemoryRow,
    `Nock.NockVMROM.Thm54.ExactExecution.derivedResponseIO ]

run_cmd do
  let env ← getEnv
  let roots := [Nock.RedTeam.Batch587.capstoneName, Nock.RedTeam.Batch587.statement]
  for r in roots do
    let cl := Nock.RedTeam.Batch587.closureOf env r
    for n in sampledAndScheduled do
      unless env.contains n do throwError m!"missing constant {n}"
      if cl.contains n then throwError m!"{n} IS in the closure of {r}"
  let cl := Nock.RedTeam.Batch587.closureOf env Nock.RedTeam.Batch587.capstoneName
  for n in capstoneControls do
    unless cl.contains n do throwError m!"control {n} not in the capstone closure"
  logInfo m!"§1: {sampledAndScheduled.length} sampled/scheduled objects absent from both \
    capstone closures; {capstoneControls.length} controls present"

/-- The deployed memory RAP is ONE round: every column, `T`/`C'` included, is committed in the
same block, before any coin of the model.  Honest acceptance is at the package's own coins. -/
theorem deployed_memory_one_round {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h) (kMem : ℕ) :
    (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.k = 1 :=
  (OptimizedMemoryRAP.finalMemoryRAP_fingerprint hn nodes b chalVal pubVal orbit kMem).2.2.2

/-! ## §2 Chronology in the staged model (`GigaChips`, off-capstone) -/

/-- Live: the staged memory chip's `mem.axis` column (29) is round 0 and may read no coin. -/
theorem staged_axis_column_coin_free :
    GigaChips.memRoundOf 29 = 0 ∧ GigaChips.memoryColumnChallenges 29 = ∅ := by
  refine ⟨by decide, ?_⟩
  exact GigaChips.mem_base_columns_challenge_free 29 (by decide)

/-- Live: the one chronology has eight coin slots (`α, z, a, b, c, α_C, β, γ`); `λ` is not one. -/
theorem chronology_has_no_lambda_slot : GigaChips.nockChronology.numChallenges = 8 := rfl

/-- **F1 against the schedule.**  Under F1 the honest value of column 29 is `T = λ^m`, which reads
the coin `λ`.  A round-0 column may read no coin at all (`memoryColumnChallenges 29 = ∅`), and a
coin sampled after any round is not usable at round 0. -/
theorem r1_axis_value_unschedulable (sampledAfter : Fin 9 → Fin 3) :
    ¬ ((sampledAfter 8 : ℕ) < (GigaChips.memRoundOf 29 : ℕ)) := by
  rw [staged_axis_column_coin_free.1]
  simp

def sampledAfterMsg1 : Fin 9 → Fin 3 := ![1, 0, 0, 0, 0, 1, 1, 1, 1]

/-- Repaired chronology B: `λ` is a coin of the EARLIER message, with `z, a, b, c`. -/
def sampledAfterMsg0 : Fin 9 → Fin 3 := ![1, 0, 0, 0, 0, 1, 1, 1, 0]

/-- Repaired memory schedule A: the record axis slot (`T`) moves to round 2. -/
def memRoundOfMsg1 (c : Fin 45) : Fin 3 :=
  if (c : ℕ) = 29 then 2 else GigaChips.memRoundOf c

/-- Repaired memory schedule B: the record axis slot (`T`) moves to round 1. -/
def memRoundOfMsg0 (c : Fin 45) : Fin 3 :=
  if (c : ℕ) = 29 then 1 else GigaChips.memRoundOf c

/-- Coins readable at each round, nine slots (A). -/
def colChalMsg1 : Fin 3 → Finset (Fin 9)
  | 0 => ∅
  | 1 => {1}
  | 2 => {0, 1, 6, 7, 8}

/-- Coins readable at each round, nine slots (B). -/
def colChalMsg0 : Fin 3 → Finset (Fin 9)
  | 0 => ∅
  | 1 => {1, 8}
  | 2 => {0, 1, 6, 7, 8}

/-- **Schedule A commits before it samples**, at all 45 staged columns, and column 29 may read `λ`.
    Column 35 is NOT moved
    here; whether it must move with 29 is the Option B staged-track question (off-capstone,
    deferred), not decided by this batch. -/
theorem repairedSchedule_msg1 :
    (∀ c : Fin 45, ∀ j ∈ colChalMsg1 (memRoundOfMsg1 c),
        (sampledAfterMsg1 j : ℕ) < (memRoundOfMsg1 c : ℕ)) ∧
      (8 : Fin 9) ∈ colChalMsg1 (memRoundOfMsg1 29) ∧
      ((Finset.univ.filter fun c : Fin 45 => memRoundOfMsg1 c = 0).card = 9 ∧
        (Finset.univ.filter fun c : Fin 45 => memRoundOfMsg1 c = 1).card = 19 ∧
        (Finset.univ.filter fun c : Fin 45 => memRoundOfMsg1 c = 2).card = 17) := by
  decide

/-- **Schedule B commits before it samples**, and column 29 may read `λ`. -/
theorem repairedSchedule_msg0 :
    (∀ c : Fin 45, ∀ j ∈ colChalMsg0 (memRoundOfMsg0 c),
        (sampledAfterMsg0 j : ℕ) < (memRoundOfMsg0 c : ℕ)) ∧
      (8 : Fin 9) ∈ colChalMsg0 (memRoundOfMsg0 29) ∧
      ((Finset.univ.filter fun c : Fin 45 => memRoundOfMsg0 c = 0).card = 9 ∧
        (Finset.univ.filter fun c : Fin 45 => memRoundOfMsg0 c = 1).card = 20 ∧
        (Finset.univ.filter fun c : Fin 45 => memRoundOfMsg0 c = 2).card = 16) := by
  decide

/-! ## §3 The lane's compute `λ` gate reads `coord₀(b)` -/

section ComputeCoin

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [Fintype F] [DecidableEq K] [FiniteDimensional F K]

def laneLam : CoordinateCompiler.CoeffExpr F := .var .challenge 9

theorem lane_lam_gate_reads_eqB (b : Basis (Fin 3) F K)
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) (env : Env F)
    (henv : env.chal = DeployedChipFamily.computeChalValOfTuple b c) :
    (laneLam (F := F)).eval env = CoordinateBasis.coord b c.2.2.1.eqB (0 : Fin 3) := by
  have h := DeployedChipFamily.computeChalValOfTuple_slot b c ⟨3, by decide⟩ ⟨0, by decide⟩
  simp only [laneLam, CoordinateCompiler.CoeffExpr.eval]
  rw [henv]
  simpa [DeployedChipFamily.computeKOfTuple] using h

theorem kcoin_nine_raw_slots (b : Basis (Fin 3) F K)
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) (k : Fin 3) :
    DeployedChipFamily.computeChalValOfTuple b c (27 + (k : ℕ)) =
      CoordinateBasis.coord b (DeployedChipFamily.computeKOfTuple c 9) k := by
  have h := DeployedChipFamily.computeChalValOfTuple_slot b c ⟨9, by decide⟩ k
  simpa [DeployedChipFamily.computeKOfTuple] using h

end ComputeCoin

/-! ## §4 One honest row, two `λ`s -/

section TwoLambdas

variable {K : Type*} [Field K]

noncomputable def verifyCell (lmb ts : K) : K × K :=
  (lmb ^ LpwScaleExp K * ts, lmb ^ LpwScaleExp K * ts)

/-- `decompose` with the record's subtree on side `b` (`false` = left, `true` = right), the other
side zero: `counts_P = counts + (λ−1+b)·pw`, `pw_P = λ·pw`. -/
def decCell (lmb : K) (b : Bool) (x : K × K) : K × K :=
  (x.1 + (lmb - 1 + (if b then 1 else 0)) * x.2, lmb * x.2)

/-- `read_root` residuals with the row's `(T, C')`:
`(counts − T·C'·ts, pw − λ^{n−1}·T·ts)`; both must vanish. -/
noncomputable def readResidual (lmb T C ts : K) (x : K × K) : K × K :=
  (x.1 - T * C * ts, x.2 - lmb ^ LpwScaleExp K * T * ts)

/-- Axis `3` (one step to the right child), chip `λ`, row built at `λ₀`, `ts = 1`, `𝔽_7`. -/
noncomputable def residualAxis3 (lmb lmb0 : Z7) : Z7 × Z7 :=
  readResidual lmb (LformRT lmb0 3) (LformRC lmb0 3) 1 (decCell lmb true (verifyCell lmb 1))

/-- At the chip's own `λ` the honest row closes (`λ = λ₀ = 2` and `λ = λ₀ = 3`). -/
theorem honest_row_closes_at_own_lambda :
    residualAxis3 2 2 = (0, 0) ∧ residualAxis3 3 3 = (0, 0) := by
  simp only [residualAxis3, readResidual, decCell, verifyCell, LformRT, LformRC, pwScale_Z7]
  decide

/-- **A row built at `λ₀ = 2` is rejected by the chip at `λ = 3`** — both read residuals are
nonzero.  So the honest IO is the chip's only at the coin the row was built at: at the capstone
that is the package's fixed coin (§1); on the sampled track it is the honest tuple only. -/
theorem honest_row_rejected_at_foreign_lambda :
    (residualAxis3 3 2).1 ≠ 0 ∧ (residualAxis3 3 2).2 ≠ 0 := by
  simp only [residualAxis3, readResidual, decCell, verifyCell, LformRT, LformRC, pwScale_Z7]
  decide

end TwoLambdas

end Nock.RedTeam.Batch589

#print axioms Nock.RedTeam.Batch589.deployed_memory_one_round
#print axioms Nock.RedTeam.Batch589.staged_axis_column_coin_free
#print axioms Nock.RedTeam.Batch589.chronology_has_no_lambda_slot
#print axioms Nock.RedTeam.Batch589.r1_axis_value_unschedulable
#print axioms Nock.RedTeam.Batch589.repairedSchedule_msg1
#print axioms Nock.RedTeam.Batch589.repairedSchedule_msg0
#print axioms Nock.RedTeam.Batch589.lane_lam_gate_reads_eqB
#print axioms Nock.RedTeam.Batch589.kcoin_nine_raw_slots
#print axioms Nock.RedTeam.Batch589.honest_row_closes_at_own_lambda
#print axioms Nock.RedTeam.Batch589.honest_row_rejected_at_foreign_lambda
