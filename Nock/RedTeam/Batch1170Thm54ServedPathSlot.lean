/-
  Nock/RedTeam/Batch1170Thm54ServedPathSlot.lean

  §A (link (iv)).  On the memory row envs of any trace (`envsF`), with the BFS tiling and validity
  of the memory fanout (`hSf`, `hvalid`):
  * `paths_nounAt` — every `verify` / `read` path at exponent `e` of the decoded memory tree
    `decodedMTreeOfEnvs … i` (R4's object, no atoms) is a root-relative `nounAt` path of the pre-`z`
    decoded noun `preZNounOfEnvs … i` (the served lookup's object, `decodePre (buildTF …)`), landing
    at the pre-`z` noun of a row of that state and exponent (`read` / `verify` transparent, a
    `decompose` node one left/right step; the two decoders share the `buildTF` layout:
    `childIdx i 1 = firstCF i`);
  * `slot_certAxis` — `Noun.slot (certAxis m c) = nounAt (bitsOf m c)` (`certAxis m c =
    pathAxis (bitsOf m c)`, `ServedMemoryTrace.slot_pathAxis`; the reviewer's `SlotRoute.lean`);
  * `slot_of_paths` — R4's path equation `V = R ++ bitsOf m c` at a root, with exponent-injective
    `read_root` / `verify_child` rows, gives `Noun.slot (certAxis m c) (pre-z noun of the read row)
    = some (pre-z noun of the verify row)`.
  §B (positions).  `zipT`, `pr_pos`: a positional pair `PR t T u w` (`Batch1171.PR`) of two trees of
  the same shape sits at one BFS index of both; `J_state_shape`: the C2 join has the trace tree's
  shape and states.
-/
import Nock.NockVMROM.Thm54.UniqueExponentsBridge
import Nock.NockVMROM.Thm54.PreZComputeCore
import Nock.NockVMROM.Thm54.ServedMemoryTrace
import Nock.NockVMROM.Thm54.StrategyOfTracesR0
import Nock.RedTeam.Batch1171Thm54C2InductionPositional
import Nock.NockVMROM.Thm54.P8Core.Batch1170Thm54ServedPathSlot

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1170

open Nock
open Nock.Walk
open Nock.Reified
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch554
open Nock.RedTeam.Batch1171 (PR)

/-! ## §A  Link (iv): the decoded path is the Nock `slot` -/

section PathSlot

variable {F K : Type} [Field F] [Field K] [Fintype F] [DecidableEq F] [Algebra F K] {M : ℕ}

section Generic

variable (envsK : Fin M → Env K) (envsF : Fin M → Env F) (hM : 0 < M) (kroots q : ℕ)

/-- The pre-`z` noun at 1-indexed row `i`. -/
local notation "NN" => preZNounOfEnvs K q kroots envsF hM

variable (hSf : kroots + Sf (foOfMem envsF) M = M) (hvalid : BFSValidF kroots (foOfMem envsF) M)
include hSf hvalid

end Generic

end PathSlot

/-! ## §B  Positional pairs sit at one BFS index -/

section Positions

/-! ## Zip of two trees -/

theorem mem_children_get {α : Type} (x : NTree α) (i : ℕ) (c : NTree α) (h : x.children[i]? = some c) :
    c ∈ x.children := List.mem_of_getElem? h

variable {K : Type} [Field K] {sv : MState → ℕ → Noun} {ax : ℕ → ℕ}

set_option quotPrecheck false in
local notation "J" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) sv ax

end Positions

end Nock.RedTeam.Batch1170

#print axioms Nock.RedTeam.Batch1170.paths_nounAt
#print axioms Nock.RedTeam.Batch1170.slot_of_paths
#print axioms Nock.RedTeam.Batch1170.slot_certAxis
#print axioms Nock.RedTeam.Batch1170.pr_pos
#print axioms Nock.RedTeam.Batch1170.J_state_shape
