/-
  Nock/RedTeam/Batch757Thm54HbindComputeStatement.lean

  * **(A) The statement of (iii)** (`HbindCompute T Qc z`): every active request slot `(a, j)` of
    the committed compute trace has root fingerprint `enc z (T.read_root k)` and child fingerprint
    `enc z (T.verify_child k)`, at `k = expOf a j = S(a) + j + 1`.  Record slots `0..2` / `3..5`
    are the root / child halves (`HostileRecordLists.rowRecord`, `StrategyOfTraces.recordHalfJoinOf`).
    Route A's target is `requestTargets P.strategy.skeleton` (`honestT`), a function of the package
    alone (`honestT_eq`).
  * **(B) A target read off the trace's own decode is vacuous.**  At `tgt := preZNoun` the pair
    event is EMPTY (`selfTarget_event_empty`) and the conjunct's conclusion holds with no `hbind`
    at all (`selfTarget_conjunct_free`): the census then prices nothing.  This is the shape the
    current decoder takes wherever it fills a noun by `nounByFP` of the very fingerprint being
    bound (`joinNoun pub.s` at the root, `joinFormulaDeep`'s leaves, OP0's `e`).
  * An OP9 gate call `[9 ax core]`: the core subtree's OP0 leaf `w`
    sits at depth 2, the arm-evaluation child `x` at depth 1.  In BFS order `x` precedes `w`
    (`gateCall_bfs`), so `w`'s request exponent is `5 + recordCount x` (`wExp_eq`), and it differs
    between `x = OP1` and `x = OP6` (`wExp_depends_on_x`).  Pairing `w`'s memory row with the
    honest `k`-th request therefore needs `x`'s state first; `x`'s state is the head of the arm,
    which is a lookup into a core that contains `w`'s result.  So `hbind` at `w` depends on
    `hbind` at `w`.  The same holds for OP2's third child (`:1760`, formula `= sf_evaluation_2`).
    The trace-indexed target (route B) reads the hostile `S` directly and has no such loop.
  * **(D) Rounds (rule 8(b), Q4).**  The inputs a pre-`z` target may read are round 0
    (`target_inputs_round_zero`); the fingerprints it binds are round 1 (`bound_columns_round_one`).
-/
import Nock.RedTeam.Batch742Thm54RouteBCensus
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch757

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.Framework

noncomputable section

/-! ## (A) The statement of (iii) -/

section Statement

open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Root half of a ten-slot record (slots `0..2`). -/
def recRootFP (r : Fin 10 → K) : ComputeTable.FP K := ⟨r 0, r 1, r 2⟩

/-- Child half of a ten-slot record (slots `3..5`). -/
def recChildFP (r : Fin 10 → K) : ComputeTable.FP K := ⟨r 3, r 4, r 5⟩

/-- **(iii), compute side of `hbind`.**  Every active request slot of the committed compute trace
carries the fingerprints, at `z`, of the target's root / child noun at its own exponent. -/
def HbindCompute (T : MState → ℕ → Noun) (Qc : Fin P.computeChip.rap.w → F[X]) (z : K) : Prop :=
  ∀ (a : Fin (rows P)) (j : Fin 3), activeMask (rowEnv P Qc a) j = 1 →
    recRootFP (rowRecord (rowEnv P Qc a) j) =
        GlobalCarryRecognizer.enc z (T .read_root (expOf P Qc a j)) ∧
      recChildFP (rowRecord (rowEnv P Qc a) j) =
        GlobalCarryRecognizer.enc z (T .verify_child (expOf P Qc a j))

/-- The package skeleton's request nouns. -/
abbrev honestT : MState → ℕ → Noun := requestTargets P.strategy.skeleton

/-- It is a function of the package's committed skeleton only (no trace, no coin). -/
theorem honestT_eq : honestT P = requestTargets P.optimized.commitment.skeleton := rfl

end Statement

/-! ## (B) A target read off the trace's own decode is vacuous -/

section SelfTarget

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- **The self-target event is empty**: pairing each decoded node with itself prices nothing. -/
theorem selfTarget_event_empty (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    pairEvent (K := K) P q Λ Qm (preZNoun P q Qm) = ∅ :=
  pairEvent_eq_empty_of_decoded_eq P q Λ Qm _ (fun _ _ => rfl)

/-- **…and the conjunct needs no binding there**: its conclusion is the accepted-trace bridge
`accepted_decode_eq_preZNoun`, true with no `hbind`, no window and no event. -/
theorem selfTarget_conjunct_free (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) (q i : ℕ) :
    decodeNoun q (buildTF P.optimized.family.problem.cfg.kMem (foM P (honestQm P c Qm) c)
        (lblM P (honestQm P c Qm) c) P.optimized.family.problem.cfg.memRows i) =
      preZNoun P q (honestQm P c Qm) i :=
  accepted_decode_eq_preZNoun P c Qm hsat q i

end SelfTarget

/-! ## (C) Route A's exponent alignment is circular (request numbering witness) -/

section Circular

open Nock.ComputeTable

/-- An OP9 gate call: core child `[cons [OP0 w] [OP1]]` (depth 2 leaves), arm child `x`. -/
def gateCall (x : State) : NTree State :=
  .node .s9 [.node .cons [.node .s0 [], .node .s1 []], .node x []]

/-- Row states in BFS order (the order of the compute trace and of `requestList`). -/
def bfsStates (t : NTree State) : List State := (bfsForest [t]).map NTree.label

theorem gateCall_bfs (x : State) : bfsStates (gateCall x) = [.s9, .cons, x, .s0, .s1] := by
  simp [bfsStates, gateCall, bfsForest, NTree.children, NTree.label]

def expAt (t : NTree State) (pos j : ℕ) : ℕ :=
  (((bfsStates t).take pos).map Nock.Framework.recordCount).sum + j + 1

/-- `w` (BFS position 3) asks its first request at exponent `5 + recordCount x`. -/
theorem wExp_eq (x : State) : expAt (gateCall x) 3 0 = 5 + Nock.Framework.recordCount x := by
  simp [expAt, gateCall_bfs, Nock.Framework.recordCount]
  omega

/-- **The witness**: the exponent of `w`'s request depends on the state of `x`, which BFS lists
before `w` and whose formula is read out of a core that
contains `w`'s result. -/
theorem wExp_depends_on_x :
    expAt (gateCall .s1) 3 0 = 6 ∧ expAt (gateCall .s6) 3 0 = 8 := by
  refine ⟨?_, ?_⟩ <;> simp [wExp_eq, Nock.Framework.recordCount]

end Circular

/-! ## (D) Rounds of the inputs (rule 8(b)) -/

/-- The round-0 inputs a pre-`z` target may read: compute selectors `0..10` and the carrier `S`
(column `302`); memory selectors `0..2`, `atom` (180), `reqIdx` (181). -/
theorem target_inputs_round_zero :
    (∀ c < 11, computeColRound c = 0) ∧ computeColRound 302 = 0 ∧
      memoryColRound 0 = 0 ∧ memoryColRound 1 = 0 ∧ memoryColRound 2 = 0 ∧
      memoryColRound 180 = 0 ∧ memoryColRound 181 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; simp [computeColRound, Nat.lt_trans hc (by decide : 11 < 13)]
  all_goals decide

/-- The fingerprints `hbind` binds are round 1: memory `pt.noun` (roles `0..2`, columns `6..14`)
and the served record halves (roles `19..24`, columns `63..80`). -/
theorem bound_columns_round_one :
    (∀ c, 6 ≤ c → c < 15 → memoryColRound c = 1) ∧
      (∀ c, 63 ≤ c → c < 81 → memoryColRound c = 1) := by
  refine ⟨?_, ?_⟩ <;> intro c h1 h2 <;> interval_cases c <;> decide

end

end Nock.RedTeam.Batch757

#print axioms Nock.RedTeam.Batch757.honestT_eq
#print axioms Nock.RedTeam.Batch757.selfTarget_event_empty
#print axioms Nock.RedTeam.Batch757.selfTarget_conjunct_free
#print axioms Nock.RedTeam.Batch757.gateCall_bfs
#print axioms Nock.RedTeam.Batch757.wExp_eq
#print axioms Nock.RedTeam.Batch757.wExp_depends_on_x
#print axioms Nock.RedTeam.Batch757.target_inputs_round_zero
#print axioms Nock.RedTeam.Batch757.bound_columns_round_one
