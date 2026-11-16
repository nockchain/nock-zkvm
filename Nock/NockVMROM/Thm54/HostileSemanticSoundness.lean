/-
  Nock/NockVMROM/Thm54/HostileSemanticSoundness.lean

  This module imports
  the statement file (it names `consumedFailureEvent`); the below-pin twins at
  `optimizedFailureEventEv` are `P8Core/HostileSemanticSoundnessEv.lean`
  (`consumedFailureEvent_eq_ev` is `rfl`).

  Every statement here quantifies over a tuple `c` and a
  pair of traces `(Qc, Qm)` that are FIXED together: acceptance at `c` and `c ∉ event(Qc, Qm)`
  give the claim.

  * `hostileSemanticSoundness`: `∀ c Qc Qm, DeployedAcceptanceAt P c Qc Qm →
    c ∉ P.consumedFailureEvent (honestQc P c Qc) (honestQm P c Qm) → claim.Holds`, under
    `of_package`'s three Form R hypotheses.
  * `hostileSemanticSoundness_holdsMod` / `_holdsMod_q`: `claim.HoldsMod (ringChar K)` / `P.q`.
  * `wrong_record_rejected` / `wrong_claim_rejected`: the two negative controls as theorems at the
    consumed event.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.P8Core.HostileSemanticSoundnessEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.HostileSemanticSoundness

open scoped Polynomial
open Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.TraceGen
open Nock.FieldEmbedding

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- For every fixed tuple `c` and every
fixed pair of traces accepted at the deployed family chips `P.computeChipAt c` /
`P.memoryChipAt c`, outside the consumed failure event read off the same traces, the package's
public claim holds in Nock: `∃ fuel, evalN fuel subject formula = some result`. -/
theorem hostileSemanticSoundness
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    ∀ (c : OptimizedProductionChallengeTuple K F)
      (Qc : Fin (P.computeChipAt c).rap.w → F[X])
      (Qm : Fin (P.memoryChipAt c).rap.w → F[X]),
      DeployedAcceptanceAt P c Qc Qm →
      c ∉ P.consumedFailureEvent (honestQc P c Qc) (honestQm P c Qm) →
      P.optimized.verifier.raw.claim.Holds := by
  intro c Qc Qm hacc hgood
  exact hostileSemanticSoundness_ev P c Qc Qm hax hbasis hwidth hacc
    (by rw [← P.consumedFailureEvent_eq_ev]; exact hgood)

/-- For every 309 compute
trace, memory trace and twelve-coin tuple `c` accepted by the parallel package's two chips
(`PartAStaged.AcceptanceAt309`) outside the fifteen-summand event, the package's public claim holds
in Nock — from the statement ALONE: the target's `p8` through the statement's own
`acceptance_to_target` conjunct.  No Form R hypothesis: the statement carries them.  The landed
303-chip form is the package-level, Form R form `hostileSemanticSoundness` above (the only compiled
transport is 303 ← 309, `PartAReHost.satisfies303_of_309`).  Fixed tuple and fixed traces; nothing
here states `:966` soundness at `deployedChronology`. -/
theorem hostileSemanticSoundness_pinned
    (hS : OptimizedFullStrictThm54Statement P)
    (Qc : Fin 309 → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : PartA12.OptimizedProductionChallengeTuple12 K F)
    (hacc : PartAStaged.AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ PartAStaged.consumedFailureEvent309 P Qc Qm) :
    P.optimized.verifier.raw.claim.Holds :=
  (hS.acceptance_to_target Qc Qm c hacc hgood).p8


/-- **The `HoldsMod` corollary** at `ringChar K` (the paper's finite-field semantics, OP4 modular). -/
theorem hostileSemanticSoundness_holdsMod
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.consumedFailureEvent (honestQc P c Qc) (honestQm P c Qm)) :
    P.optimized.verifier.raw.claim.HoldsMod (ringChar K) :=
  hostileSemanticSoundness_holdsMod_ev P c Qc Qm hax hbasis hwidth hacc
    (by rw [← P.consumedFailureEvent_eq_ev]; exact hgood)

/-- The `HoldsMod` corollary at the package modulus `P.q`. -/
theorem hostileSemanticSoundness_holdsMod_q
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.consumedFailureEvent (honestQc P c Qc) (honestQm P c Qm)) :
    P.optimized.verifier.raw.claim.HoldsMod P.q :=
  hostileSemanticSoundness_holdsMod_q_ev P c Qc Qm hax hbasis hwidth hacc
    (by rw [← P.consumedFailureEvent_eq_ev]; exact hgood)

/-- **NC (a) as a theorem at the consumed event**: if the program's guarded run returns
`r ≠ claim.result`, every fixed `(c, Qc, Qm)` accepted at the family chips has `c` inside
`consumedFailureEvent`. -/
theorem wrong_claim_rejected
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (hwrong : r ≠ P.optimized.verifier.raw.claim.result) :
    c ∈ P.consumedFailureEvent (honestQc P c Qc) (honestQm P c Qm) := by
  obtain ⟨gfuel, G, R, -, -, hgen, -, hΛG⟩ := P.generated
  rw [P.consumedFailureEvent_eq_ev]
  exact PlacementA.wrong_claim_rejected_evOnly P c Qc Qm hacc hax hbasis hwidth hgen hG hwrong hΛG
    P.primeField

/-- **NC (b) as a theorem at the consumed event**: traces that serve a non-genuine memory record
at some positional pair are accepted only at tuples inside `consumedFailureEvent`. -/
theorem wrong_record_rejected
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hwrong : ¬ Nock.RedTeam.Batch1172.ServedRecordsPos P c Qc Qm) :
    c ∈ P.consumedFailureEvent (honestQc P c Qc) (honestQm P c Qm) := by
  rw [P.consumedFailureEvent_eq_ev]
  exact wrong_record_rejected_ev P c Qc Qm hax hbasis hwidth hacc hwrong

end Nock.NockVMROM.Thm54.HostileSemanticSoundness
