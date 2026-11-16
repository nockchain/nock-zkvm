/-
  Nock/RedTeam/Batch472Thm54WalkPrefixRecord.lean

The open
  question there was whether the IO argument (`IO.LIO` against the memory chip) rejects them. This file shows the requests are about a GENUINE noun: `loopCore = [[9 2 0 1] 0]`,
  `b = 2`, has `/[2 loopCore] = [9 2 0 1]` (`loopCore_slot`) and the honest interpreter
  diverges on `*[loopCore 9 2 0 1]` at every fuel (`loop_diverges`, `Reference.lean::evalN`). So a memory table that honestly holds `loopCore` (e.g. as the subject the honest root reads)
  answers the garbage rows' reads with TRUE slot facts; the IO argument checks slot facts, not
  reachability from the root, and does not see the orphan cycle for that reason. This does
  NOT build the full `199`-column trace: acceptance of the garbage at `computeChipAt c` as a
  whole trace stays UNCONFIRMED (the multiplicity/timestamp bookkeeping of the extra requests
  is not constructed).

  Ledger (compiled strings; the theorems are in the batch files):

-- the paper
-/
import Nock.Reference
import Nock.RedTeam.Batch468Thm54WalkPrefixAlphaEvent
import Nock.RedTeam.Batch469Thm54GarbageWitness
import Nock.RedTeam.Batch470Thm54MemoryPrefix
import Nock.RedTeam.Batch471Thm54ComputeTopologyPrefix

set_option autoImplicit false

namespace Nock.RedTeam.Batch472

open Nock

/-- `[9 2 0 1]`. -/
def loopFormula : Noun :=
  .cell (.atom 9) (.cell (.atom 2) (.cell (.atom 0) (.atom 1)))

/-- `[[9 2 0 1] 0]` — the classic self-calling core. -/
def loopCore : Noun := .cell loopFormula (.atom 0)

/-- **The slot fact the garbage row requests is TRUE:** `/[2 loopCore] = [9 2 0 1]`. -/
theorem loopCore_slot : Noun.slot 2 loopCore = some loopFormula := by
  unfold loopCore
  rw [Noun.slot]
  simp [Noun.slot]

/-- The `(a, 1, a)` read is true too. -/
theorem loopCore_slot_one : Noun.slot 1 loopCore = some loopCore := by
  simp [Noun.slot]

/-- **Honest Nock diverges on the self-caller** at every fuel. -/
theorem loop_diverges : ∀ fuel, evalN fuel loopCore loopFormula = none := by
  intro fuel
  induction fuel with
  | zero => simp [evalN]
  | succ n ih =>
    cases n with
    | zero => simp [loopFormula, evalN]
    | succ m =>
      have h01 : evalN (m + 1) loopCore (.cell (.atom 0) (.atom 1)) = some loopCore := by
        simp [evalN, Noun.slot]
      simp only [loopFormula] at ih ⊢
      rw [evalN]
      simp only [h01, loopCore_slot]
      simpa [loopFormula] using ih

/-- Per-batch status. -/
def landed : List (String × String) :=
  [("Batch467 Nock/WalkPrefix.lean", "landed: prefixLen, PrefixBFT, prefixBFT_of_isFullBFT, forest analogue"),
    ("Batch468 alpha event", "landed: walkPrefixAlphaEvent card ≤ max h (1+Sf) ≤ 1+3h; not in the union"),
    ("Batch469 garbage witness", "landed at WalkSat (every α) and F_comp; full chip trace UNCONFIRMED"),
    ("Batch470 memory side", "landed: forest prefix; F_mem self-child at size 0 (collision event does not price it)"),
    ("Batch471 topology via prefix", "step 3 landed on the prefix (hic, hseed named); step 4 STOP at AcceptedContent"),
    ("Batch472 record", "this file + CENSUS-DRAFT-walk-prefix.md")]

theorem landed_length : landed.length = 6 := by decide

def census5Addendum : String :=
  "Thm:Walk_IOP's statement (slt ∈ L_RVT, main.tex:966) survives via the prefix lemma " ++
  "(rows 1..prefixLen are the root's BFT); the proof's lemma at :2263 is false as stated; " ++
  "the h/|K| constant presupposes tiling ((3h+1)/|K| otherwise, fanout ≤ 3); the K side's " ++
  "QGate and the deployed chips' prefix route are two repairs of the same gap; the deployed " ++
  "chips carry no queue gate by user decision (Batch462 inventory)."

end Nock.RedTeam.Batch472

#print axioms Nock.RedTeam.Batch472.loopCore_slot
#print axioms Nock.RedTeam.Batch472.loop_diverges
