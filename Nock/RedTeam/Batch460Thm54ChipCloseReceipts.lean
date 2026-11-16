/-
  Nock/RedTeam/Batch460Thm54ChipCloseReceipts.lean

* `openConjuncts` before/after: the same 10 names (`Batch398.openConjuncts`);
    `Batch448.openConjunctsAfterVer` (7) unmoved.  `computeTopology` stays.
  * `Batch453.CHIP_SFE_REMAINING` (4) → `Batch457.CHIP_SFE_REMAINING` (4): two closed
    (`walkAccInit_eval_at_row0`, `labelRLC_eval firstReader`), two obstructions found
    (`initial_count` is the package public; the `αc` root event and the `Fin 10`
    root/claim collision are not in the consumed union).
  * `Batch455.topologyPipeline` step 2 landed (`Batch459.deployed_walkSat` at the committed
    operands, `initial_count = computeWalkAlpha`); steps 3–4 are STOPs: the deployed compute
    chip has no queue-length gate (`Walk.QGate` unreachable from `computeChipAt`, positive
    controls run), so `Sf fo h + 1 = h` / `BFSValid` are not gate-forced.
  * `Batch403.chipClosedPublics` stays `0`.

  Every chip theorem is at `rowEnvAt P c Qc` for `Qc` accepted at `computeChipAt c`; no
  honest-package object stands in for a committed trace.

  -- the paper
-/
import Nock.RedTeam.Batch457Thm54RootLabelFromChip
import Nock.RedTeam.Batch458Thm54StrategyBindsStop
import Nock.RedTeam.Batch459Thm54ComputeTopologyStop
import Nock.RedTeam.Batch448Thm54VerTransfer

set_option autoImplicit false

namespace Nock.RedTeam.Batch460

open Nock.RedTeam.Batch398

/-! ## Open-conjunct ledger -/

def openConjunctsBefore : List String := Nock.RedTeam.Batch398.openConjuncts
def openConjunctsAfter : List String := Nock.RedTeam.Batch398.openConjuncts

theorem openConjuncts_before_eq_after : openConjunctsBefore = openConjunctsAfter := rfl

theorem openConjuncts_after_length : openConjunctsAfter.length = 10 :=
  Nock.RedTeam.Batch398.openConjuncts_length

theorem openConjuncts_after_names :
    openConjunctsAfter =
      ["memoryRows", "vmem", "mem_first_counts", "mem_first_indicator",
        "io", "computeTopology", "memoryTopology", "axisStructural",
        "rootBoundary", "structuralChecks"] := by
  decide

theorem afterVer_target_unmoved : Nock.RedTeam.Batch448.openConjunctsAfterVer.length = 7 :=
  Nock.RedTeam.Batch448.openConjunctsAfterVer_length

theorem computeTopology_still_open : "computeTopology" ∈ openConjunctsAfter := by decide

/-! ## Chip-level `s/f/e` ledger -/

theorem chip_sfe_ledger :
    Nock.RedTeam.Batch453.CHIP_SFE_REMAINING.length = 4 ∧
      Nock.RedTeam.Batch457.CHIP_SFE_CLOSED.length = 2 ∧
      Nock.RedTeam.Batch457.CHIP_SFE_REMAINING.length = 4 ∧
      Nock.RedTeam.Batch403.chipClosedPublics = 0 := by
  decide

/-! ## Landed theorems (compiled references, not strings) -/

def landed_masks := @Nock.RedTeam.Batch457.masks_at_row_at
def landed_root_cur := @Nock.RedTeam.Batch457.root_cur_is_decoded_label
def landed_row0 := @Nock.RedTeam.Batch457.walkAccInit_row0_decoded
def landed_initialCount := @Nock.RedTeam.Batch457.family_initialCount_at
def landed_seed := @Nock.RedTeam.Batch457.family_seed_at
/-- Alias of `Batch457.thmWalkIOP_premise_holds` (an `iff`). -/
def landed_premise := @Nock.RedTeam.Batch457.thmWalkIOP_premise_holds
def landed_cylinder := @Nock.RedTeam.Batch457.failureUnion_alphaC_cylinder
def landed_trace_free := @Nock.RedTeam.Batch457.p8Summand_trace_free
def landed_residual := @Nock.RedTeam.Batch458.chipRootBinding_of_two_inputs
def landed_no_bfsValid := @Nock.RedTeam.Batch459.walkSat_without_bfsValid
def landed_no_tiling := @Nock.RedTeam.Batch459.walkSat_without_tiling
def landed_walkSat := @Nock.RedTeam.Batch459.deployed_walkSat
def landed_walk_out := @Nock.RedTeam.Batch459.deployed_walk_out
def landed_foW := @Nock.RedTeam.Batch459.foW_eq_foC
def landed_curW := @Nock.RedTeam.Batch459.curW_eq_lblC

theorem step2_landed : Nock.RedTeam.Batch459.step2Landed.length = 4 :=
  Nock.RedTeam.Batch459.step2Landed_length

/-! ## Record -/

/-- No `Nock/NockVMROM/Thm54/*` production file. -/
def touchedFiles : List String :=
  ["Nock/RedTeam/Batch457Thm54RootLabelFromChip.lean",
    "Nock/RedTeam/Batch458Thm54StrategyBindsStop.lean",
    "Nock/RedTeam/Batch459Thm54ComputeTopologyStop.lean",
    "Nock/RedTeam/Batch460Thm54ChipCloseReceipts.lean",
    "Nock/RedTeam.lean", "redteam-status.json", "CENSUS-DRAFT-compute-chip-close.md"]

theorem touchedFiles_length : touchedFiles.length = 7 := by decide


def checkFrozenLine : String :=
  "check-frozen: 2 digests, 2 required lines and 291 statement-closure fingerprints unchanged"

def frozenDigest : String :=
  "aac8281513bcab507de6b82d8896325aaec19d09085ce147d03dc91544dfeaee"

/-- The STOPs, by name and reason. -/
def stops : List (String × String) :=
  [("Batch457 deployed_root_label_eq_claim",
      "initial_count = computeWalkAlpha (package public), not alphaC; alphaC root event " ++
        "and Fin 10 root/claim collision not in the consumed union"),
    ("Batch458 drop TracesBindsHyps",
      "root_bindings needs Batch457's two inputs; rows need H1.4 join; memory half H1.4"),
    ("Batch459 topology steps 3-4",
      "no queue-length gate on the deployed compute chip: Sf/BFSValid not gate-forced")]

theorem stops_length : stops.length = 3 := by decide

end Nock.RedTeam.Batch460

#print axioms Nock.RedTeam.Batch460.chip_sfe_ledger
#print axioms Nock.RedTeam.Batch460.openConjuncts_after_names
