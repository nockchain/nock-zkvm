/-
  Nock/RedTeam/Batch466Thm54WalkAlphaRecord.lean

-- the paper
-/
import Nock.RedTeam.Batch463Thm54WalkAlphaInitialCount
import Nock.RedTeam.Batch464Thm54WalkRootEventsPriced
import Nock.RedTeam.Batch465Thm54DeployedRootLabelEqClaim
import Nock.RedTeam.Batch460Thm54ChipCloseReceipts
import Nock.RedTeam.Batch475Thm54MemoryWalkAlphaInitialCount

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch466

open Nock.RedTeam.Batch398

/-! ## Open-conjunct ledger -/

def openConjunctsBefore : List String := Nock.RedTeam.Batch398.openConjuncts
def openConjunctsAfter : List String := Nock.RedTeam.Batch398.openConjuncts

theorem openConjuncts_before_eq_after : openConjunctsBefore = openConjunctsAfter := rfl

theorem openConjuncts_after_names :
    openConjunctsAfter =
      ["memoryRows", "vmem", "mem_first_counts", "mem_first_indicator",
        "io", "computeTopology", "memoryTopology", "axisStructural",
        "rootBoundary", "structuralChecks"] := by
  decide

theorem openConjuncts_after_length : openConjunctsAfter.length = 10 :=
  Nock.RedTeam.Batch398.openConjuncts_length

/-- `chipClosedPublics` stays `0`. -/
theorem chipClosedPublics_unmoved : Nock.RedTeam.Batch403.chipClosedPublics = 0 := rfl

/-! ## Chip-level `s/f/e` ledger: `4 → 1` -/

theorem chip_sfe_ledger :
    Nock.RedTeam.Batch457.CHIP_SFE_REMAINING.length = 4 ∧
      Nock.RedTeam.Batch463.CLOSED_HERE.length = 1 ∧
      Nock.RedTeam.Batch464.CLOSED_HERE.length = 2 ∧
      Nock.RedTeam.Batch465.CHIP_SFE_REMAINING_BEFORE_H15B.length = 1 := by
  decide

/-! ## Landed theorems (compiled references, not strings) -/

def landed_initialCount := @Nock.RedTeam.Batch463.initialCount_is_coin
def landed_premise := @Nock.RedTeam.Batch463.thmWalkIOP_premise_unconditional
def landed_row0 := @Nock.RedTeam.Batch463.row0_identity_at_coin
def landed_walkSat := @Nock.RedTeam.Batch463.deployed_walkSat_at_recognizer_inputs
def landed_event := @Nock.RedTeam.Batch464.event_after_unfold
def landed_bound := @Nock.RedTeam.Batch464.bound_after_eq_before_plus_walk
def landed_figures := @Nock.RedTeam.Batch464.figure_122
def landed_root_cur := @Nock.RedTeam.Batch465.deployed_root_cur_eq_claim
def landed_root_label := @Nock.RedTeam.Batch465.deployed_root_label_eq_claim
def landed_root_label_good := @Nock.RedTeam.Batch465.deployed_root_label_eq_claim_of_good

/-! ## Record -/

/-- Resources: unmoved. -/
def resources : List (String × String) :=
  [("w", "199 / 196"), ("C.rap.s", "307"), ("M.rap.s", "140"), ("d", "4")]

/-- The bound body before/after, as the theorems state it. -/
def boundBody : List (String × String) :=
  [("before (05c2932, W4 stage 2)",
      "(p8Work + (1 + 3N(3N-1)/2))/|K| + ioWork/|K|^2 + interWork/|K|^2"),
    ("after (Batch464)",
      "(p8Work + (1 + 3N(3N-1)/2) + (3N + 1) + 9)/|K| + ioWork/|K|^2 + interWork/|K|^2")]

/-- The figures, before / after, by theorem (unmoved). -/
def figures : List (String × String × String) :=
  [("paper configuration (ioWork <= 16^65, p8Work <= 2^60)", "123", "123"),
    ("real programs 2^31 rows", "122", "122"),
    ("real programs 2^32 rows", "120", "120"),
    ("uniform-size majorant 2*hostileTotalWork", "367S^2 + 104S + 4", "367S^2 + 110S + 24")]


def checkFrozen : List (String × String) :=
  [("base 05c2932", "aac8281513bcab507de6b82d8896325aaec19d09085ce147d03dc91544dfeaee / closure 291"),
    ("after Move A", "digest moved (pinned rfl argument + docstrings); watchlist + computePublicOfTuple; closure 292"),
    ("Move A control", "computePublicOfTuple else-branch `+ 0`: exit 1, fingerprint 9841463719093856184 -> 2370672063448031595; reverted, exit 0"),
    ("after Move B", "see CENSUS-DRAFT-walk-alpha.md (digest, closure count, Move B control)")]

/-- **The memory half of Move A: LANDED**. `DeployedChipFamily.memoryPublicOfTuple` carries the coin's `initial_count = alphaM c.1 ^ kMem`
at memory publics `6..8`, the pinned `memoryChipAt` passes `familyMemoryPublic c`, and the honest identity is
`familyMemoryPublic_honest_of_chalVal` (no hypothesis beyond `h`: the chalVal agreement at walk-α slot `3`
plus the `walkChallenge` pin give `alphaM honestTuple = memoryWalkAlpha`). -/
def MEMORY_HALF_LANDED : List String :=
  ["DeployedChipFamily.memoryPublicOfTuple slots 6..8 := coord b (alphaM c.1 ^ kMem)",
    "OptimizedStrictFullPackage.familyMemoryPublic (new pinned abbrev); memoryChipAt reads it",
    "OptimizedStrictFullPackage.familyMemoryPublic_honest_of_chalVal (honest identity, generic P)",
    "FamilyComputeRows.memoryBaseEnvAt / memoryChipAt_width and FamilyMemoryRows read familyMemoryPublic c"]

theorem memory_half_landed_length : MEMORY_HALF_LANDED.length = 4 := by decide

def landed_memory_initialCount := @Nock.RedTeam.Batch475.memory_initialCount_is_coin
def landed_memory_honest := @Nock.RedTeam.Batch475.memoryChipAt_honest


def touchedProductionFiles : List String :=
  ["Nock/NockVMROM/Thm54/DeployedChipFamily.lean",
    "Nock/NockVMROM/Thm54/OptimizedStrictFullPackage.lean",
    "Nock/NockVMROM/Thm54/OptimizedStrictPackage.lean",
    "Nock/NockVMROM/Thm54/ComputeWalkRootEvents.lean",
    "Nock/NockVMROM/Thm54/GoldilocksParameters.lean",
    "Nock/NockVMROM/Thm54/RealProgramSoundness.lean",
    "Nock/NockVMROM/Thm54/HostileWorkloadMajorant.lean",
    "Nock/NockVMROM/Thm54/MemoryInternalPole.lean",
    "Nock/NockVMROM/Thm54/DistinctCensusCompleteFalseAcceptance.lean",
    "Nock/NockVMROM/Thm54/DistinctCensusFold2.lean",
    "Nock/NockVMROM/Thm54/MultiRootOptimizedAcceptance.lean",
    "Nock/NockVMROM/Thm54/OptimizedStrictFullPackageConcrete.lean",
    "Nock/NockVMROM/Thm54/IOCapstoneRedundancy.lean",
    "Nock/NockVMROM/Thm54/OptimizedHostileConfiguration.lean",
    "Nock/NockVMROM/Thm54/FamilyComputeRows.lean",
    "Nock/NockVMROM/Thm54/FamilyMemoryRows.lean",
    "Nock/NockVMROM/Thm54/DistinctCensusP8FixedField.lean",
    "Nock/FrozenClosure.lean", "frozen-pins.json"]

theorem touchedProductionFiles_length : touchedProductionFiles.length = 19 := by decide

/-- The STOPs. -/
def stops : List (String × String) :=
  [("Batch458 drop TracesBindsHyps", "rows need H1.4 join; memory half H1.4; chipClosedPublics stays 0"),
    ("Batch459 topology steps 3-4", "no queue-length gate (decision pending); (3N+1)/|K| instead of h/|K|"),
    ("honest exclusion at canonical traces", "IsFullBFT transport to the trace-only decoders not done; fixture receipts take hwalk")]

theorem stops_length : stops.length = 3 := by decide

end Nock.RedTeam.Batch466

#print axioms Nock.RedTeam.Batch466.chip_sfe_ledger
#print axioms Nock.RedTeam.Batch466.openConjuncts_after_names
