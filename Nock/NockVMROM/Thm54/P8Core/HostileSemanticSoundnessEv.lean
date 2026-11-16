/-
  Nock/NockVMROM/Thm54/P8Core/HostileSemanticSoundnessEv.lean

  Every theorem here is about traces `(Qc, Qm)` and a
  tuple `c` that are ALL FIXED: for every such triple, acceptance at the family chips and
  `c ∉ event(Qc, Qm)` give the claim.  Nothing here is a statement about a prover that chooses
  columns after seeing a coin; no `:966`-shaped / interactive soundness at the deployed
  two-message chronology is stated or implied.

  * `hostileSemanticSoundness_ev`: acceptance + `c ∉ optimizedFailureEventEv` ⟹
    `claim.Holds` (`∃ fuel, evalN fuel s f = some r`).  A thin wrapper over
    `PlacementA.holds_of_acceptance_evOnly` with the package's own `generated` / `primeField`.
  * `hostileSemanticSoundness_evalGBy_ev`, `hostileSemanticSoundness_holdsMod_ev`,
    `hostileSemanticSoundness_holdsMod_q_ev`: the guarded run, and `claim.HoldsMod (ringChar K)`
    / `claim.HoldsMod P.q` (`FieldEmbedding.noOverflow_agreeBy`).
  * `wrong_record_rejected_ev` / `one_wrong_record_rejected_ev`: negative control (b) as a
    theorem — traces serving one wrong memory record (a positional record that is not `RecOK`)
    are accepted only at tuples inside `optimizedFailureEventEv`.
-/
import Nock.NockVMROM.Thm54.P8Core.PlacementAEvOnly
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1172Thm54ServedRecordsAtTracesEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

namespace Nock.NockVMROM.Thm54.HostileSemanticSoundness

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch1024 (treeS axF svF)
open Nock.GlobalCarryRecognizer
open Nock.FieldEmbedding

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-- **The guarded run of the claim's own program returns the claimed result** at every fixed
`(c, Qc, Qm)` accepted at the family chips with `c ∉ optimizedFailureEventEv`. -/
theorem hostileSemanticSoundness_evalGBy_ev
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm)) :
    ∃ fuel, evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result ∧
      Nock.evalN fuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result := by
  obtain ⟨gfuel, G, R, fuel, r, hgen, hG, hΛG⟩ := P.generated
  exact ⟨fuel, PlacementA.holds_of_acceptance_evOnly P c Qc Qm hacc hgoodEv hax hbasis hwidth
    hgen hG hΛG P.primeField⟩

/-- **`hostileSemanticSoundness`, fixed-trace form, at the 2b-ii event**: for every fixed tuple `c`
and every fixed pair of traces accepted at the family chips `P.computeChipAt c` /
`P.memoryChipAt c`, outside `optimizedFailureEventEv` (read off the same traces), the package's
public claim holds: `∃ fuel, evalN fuel subject formula = some result`. -/
theorem hostileSemanticSoundness_ev
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm)) :
    P.optimized.verifier.raw.claim.Holds := by
  obtain ⟨fuel, -, hN⟩ := hostileSemanticSoundness_evalGBy_ev P c Qc Qm hax hbasis hwidth hacc hgoodEv
  exact ⟨fuel, hN⟩

/-- **The `HoldsMod` corollary at `ringChar K`**: the paper's finite-field semantics
(`JointSoundness.lean::P8PublicClaim.HoldsMod`, OP4 modular) of the claim, from the guarded run by
`FieldEmbedding.noOverflow_agreeBy` (inputs bounded by `skeletonBounded` at the root row). -/
theorem hostileSemanticSoundness_holdsMod_ev
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm)) :
    P.optimized.verifier.raw.claim.HoldsMod (ringChar K) := by
  obtain ⟨fuel, hG, -⟩ := hostileSemanticSoundness_evalGBy_ev P c Qc Qm hax hbasis hwidth hacc hgoodEv
  have h11 := OptimizedHostileConfiguration.eleven_lt_ringChar_of_package P
  obtain ⟨bs, bf⟩ := RootResultBridge.claimInputs_bounded P
  exact ⟨fuel, (FieldEmbedding.noOverflow_agreeBy (by omega) bs bf hG).2.1⟩

/-- The `HoldsMod` corollary at the package's own modulus `P.q` (`= ringChar K`). -/
theorem hostileSemanticSoundness_holdsMod_q_ev
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm)) :
    P.optimized.verifier.raw.claim.HoldsMod P.q := by
  rw [P.q_eq_ringChar]
  exact hostileSemanticSoundness_holdsMod_ev P c Qc Qm hax hbasis hwidth hacc hgoodEv

/-! ## Negative control (b): one wrong memory record -/

set_option quotPrecheck false
local notation "JJ" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
/-- The C2 join on the family traces at `c`, rooted at the package claim. -/
local notation "JT" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
  (treeS P c Qc).size (treeS P c Qc)
  P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula

/-- **NC (b), served-record form**: if the fixed traces serve a memory record that is not genuine
at some positional pair (`¬ Batch1172.ServedRecordsPos`), then every tuple at which they are
accepted lies in `optimizedFailureEventEv`.  Contrapositive of
`Batch1172.servedRecordsPos_of_traces_ev`; no trace-side premise. -/
theorem wrong_record_rejected_ev
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hwrong : ¬ Nock.RedTeam.Batch1172.ServedRecordsPos P c Qc Qm) :
    c ∈ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm) := by
  by_contra hgoodEv
  exact hwrong (Nock.RedTeam.Batch1172.servedRecordsPos_of_traces_ev P c Qc Qm hacc hgoodEv hax
    hbasis hwidth hgoodEv
    (PlacementA.tracesWalkHyps_of_acc_evOnly P c Qc Qm hacc hax hbasis hwidth hgoodEv)
    P.primeField)

/-- **NC (b), one explicit wrong record**: a positional node `u` of the committed compute tree,
paired with its C2-join node, and one record slot `j` whose committed root fingerprint matches,
whose root is in the window and bounded, but whose served `(axis, child)` is NOT a genuine
subtree read (`¬ (slot axis root = some child ∧ enc child = committed child)`).  Every tuple at
which such traces are accepted lies in `optimizedFailureEventEv`. -/
theorem one_wrong_record_rejected_ev
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (u : NTree ((State × DTcomp K) × ℕ)) (s f : Noun)
    (hpr : Nock.RedTeam.Batch1171.PR (treeS P c Qc) JT u (JJ u.size u s f))
    (j : Fin 3) (hj : (j : ℕ) < Nock.Framework.recordCount (JJ u.size u s f).label.state)
    (henc : enc (nprSeed c.1) ((JJ u.size u s f).label.memoryRecord j hj).root =
      (Nock.RedTeam.Batch1171.traceRec u.label j).root)
    (hl : ((JJ u.size u s f).label.memoryRecord j hj).root.leaves ≤ P.optimized.Λ)
    (hbnd : BoundedBy (ringChar K) ((JJ u.size u s f).label.memoryRecord j hj).root)
    (hbad : ¬ (Noun.slot ((JJ u.size u s f).label.memoryRecord j hj).axis
          ((JJ u.size u s f).label.memoryRecord j hj).root =
          some ((JJ u.size u s f).label.memoryRecord j hj).child ∧
        enc (nprSeed c.1) ((JJ u.size u s f).label.memoryRecord j hj).child =
          (Nock.RedTeam.Batch1171.traceRec u.label j).child)) :
    c ∈ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm) :=
  wrong_record_rejected_ev P c Qc Qm hax hbasis hwidth hacc
    (fun hok => hbad (hok u s f hpr j hj henc hl hbnd))

end Nock.NockVMROM.Thm54.HostileSemanticSoundness
