/-
  Nock/RedTeam/Batch440Thm54MemoryWalkLabel.lean

  **The `x^mem` label layer, receipts (twenty-first move).**

  * `childPayloadWidth = 6` = child state tag + child cell; the two declared
    child state tags are hosted at the dead sampled roles `45`/`46`; absent slots carry
    `MemoryTable.nullMStateTag = 4` (`:2064`/`:2071`/`:2079` `⊥`).
  * `labelRLC` / `childSumCC` / `selectorCM` are in-gate `MixedExpr`s over a row reader and the walk `(α, γ)`; the committed walk gates read them on the
    successor row (`nextReader`), the boundary gates on the first row (`curReader`).
  * Walk-γ is memory `𝕂` slot `7` (`DeployedChipFamily.memoryKOfTuple c 7 = gamma c.1`) — not
    compute slot `10`, not memory `4`/`5`/`6` (IO `γ`, pole, `interPole`).  JointCoins `gamma`
    is already a coordinate of the tuple: the challenge space is unchanged.
-/
import Nock.NockVMROM.Thm54.MemoryWalkLabel
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.DeployedChipFamily

set_option autoImplicit false

namespace Nock.RedTeam.Batch440

open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis

theorem label_width_six : memoryLabelWidth = 6 := memoryLabelWidth_eq
theorem child_payload_six : childPayloadWidth = 6 := childPayloadWidth_eq
theorem child_matches_label_width : childPayloadWidth = memoryLabelWidth :=
  child_payload_matches_label_width

/-- The deployed encoder width is the paper's label width (`33 → 6`). -/
theorem deployed_width_is_label_width : NodeEncoding.memoryNodeWidth = 6 :=
  NodeEncoding.memoryNode_width

theorem retired_full_row_width : NodeEncoding.memoryFullRowWidth = 37 :=
  NodeEncoding.memoryFullRow_width

theorem null_tag_four : MemoryTable.nullMStateTag = 4 := rfl

theorem null_tag_outside_states (st : MState) :
    NodeEncoding.memoryStateTag st ≠ MemoryTable.nullMStateTag := by
  cases st <;> decide

/-! ## Slots -/

theorem walk_gamma_slot : walkGammaChallengeIndex = 7 := rfl
theorem walk_alpha_slot : walkAlphaChallengeIndex = 3 := rfl

/-- The slot is disjoint from compute's walk-γ slot (`10`, a different chip) and from the memory
IO/pole slots `4`/`5`/`6`. -/
theorem walk_gamma_slot_disjoint :
    walkGammaChallengeIndex ≠ 4 ∧ walkGammaChallengeIndex ≠ 5 ∧ walkGammaChallengeIndex ≠ 6 ∧
      walkGammaChallengeIndex ≠ 3 := by
  decide

theorem deployed_slot7_is_gamma {F K : Type} [Field F] [Field K] [Fintype K] [Fintype F]
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) :
    DeployedChipFamily.memoryKOfTuple c 7 = gamma c.1 := rfl

theorem tag_hosts : childTagHostRole 0 = 45 ∧ childTagHostRole 1 = 46 := ⟨rfl, rfl⟩

/-- Fanout never exceeds the two child slots. -/
theorem fanout_le_two (st : MState) : fanoutMem st ≤ 2 := fanoutMem_le_two st

/-! ## The committed gates -/

section Gates

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem inGate_gates_committed :
    walkCount1InGate (F := F) ∈ paperKGates (K := K) (F := F) ∧
      walkAccInitInGate (F := F) ∈ paperKGates (K := K) (F := F) ∧
      walkCountStepInGate (F := F) ∈ paperKGates (K := K) (F := F) ∧
      walkAccStepInGate (F := F) ∈ paperKGates (K := K) (F := F) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (show _ ∈ paperKGates (K := K) (F := F)
     simp [paperKGates, paperKGatesCore, walkGates, walkInitGates, walkStepGates])

theorem paper_lists_agree [Fintype K] [DecidableEq K] :
    MemoryPaperFactorization.paperKGates (K := K) (F := F) = paperKGates (K := K) (F := F) :=
  MemoryPaperFactorization.paperKGates_eq_committed

theorem gate_count_unmoved : (paperKGates (K := K) (F := F)).length = 49 := paperKGates_length

theorem degree_budget : ∀ g ∈ paperKGates (K := K) (F := F), g.degree ≤ 4 := paperKGates_degree

theorem inGate_degrees :
    (walkCount1InGate (F := F)).degree ≤ 4 ∧ (walkAccInitInGate (F := F)).degree ≤ 4 ∧
      (walkCountStepInGate (F := F)).degree ≤ 4 ∧ (walkAccStepInGate (F := F)).degree ≤ 4 :=
  ⟨walkCount1InGate_degree, walkAccInitInGate_degree, walkCountStepInGate_degree,
    walkAccStepInGate_degree⟩

theorem resources_unmoved {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Module.Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) :
    (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.w = 205 ∧
      (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.s = 156 ∧
      (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.d = 4 ∧
      (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit 1).rap.k = 1 :=
  OptimizedMemoryRAP.finalMemoryRAP_fingerprint hn nodes b chalVal pubVal orbit 1

end Gates

end Nock.RedTeam.Batch440

#print axioms Nock.RedTeam.Batch440.inGate_gates_committed
#print axioms Nock.RedTeam.Batch440.degree_budget
