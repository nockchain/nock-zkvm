/-
  Nock/RedTeam/Batch886Thm54Part2aNegativeControls.lean

  Standing
  rule 6: by replica fingerprint and by definitional-equality probe, never by perturbing
  production and rebuilding above the pinned file.

  * **(A) The `+0` perturbation of the lifted `FamilyEnvCore.famIOEventOf` body.**  `famIOLive` is a
    verbatim replica of the lifted body; `famIOPert` is the same with the IO coordinate's `γ` read as
    `c.2.1.1 + 0` (signature-preserving). Fingerprints: `famIOLive` vs the production constant is
    logged; `famIOPert ≠ famIOLive` is asserted (replica-vs-replica). The verbatim replica IS
    definitionally equal (positive control).
  Measured cause: the
    only structural difference is the auxiliary proof constant Lean abstracts per declaration
    (`familyQc._proof_1` vs `famIOLive._proof_1`), which `fp` hashes by name; after normalising
    `…._proof_N` names the values are identical and the `+0` perturbation still differs.

  So the doubled
    numerator stays `457S²+404S+28` and the figure theorems hold as stated: 122 at `2^31` rows,
    120 at `2^32`, 123 at the paper configuration (axioms printed below). -/
import Nock.NockVMROM.Thm54.FamilyEnvCore
import Nock.RedTeam.Batch882Thm54Part2aReplicas
import Nock.RedTeam.Batch885Thm54Part2aLiftReceipts
import Nock.RedTeam.Batch888Thm54Part2aFamIOReplica
import Nock.RedTeam.Batch881Thm54Part2aFamIOAtQD
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.GoldilocksParameters

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Lean Elab Command Meta

namespace Nock.RedTeam.Batch886

open Nock.NockVMROM.Thm54
open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open OptimizedStrictPackage
open OptimizedComputeHostileAccumulator
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeCorrectedFinal
open DeployedChipFamily
open CoordinateBasis
open CoordinateCompiler
open Module
open MonolithicRAP
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryCanonicalSatisfaction
open OptimizedComputeCollisionBound
open OptimizedMemoryCollisionAccounting

open Nock.NockVMROM.Thm54.FamilyEnvCore

noncomputable section

set_option quotPrecheck false

local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-- Verbatim replica of the lifted `FamilyEnvCore.famIOEventOf`. -/
def famIOLive (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    c.2.1 ∈ FiniteIO.IOFailureEvent (hostileRecordsAt O c (familyQm O c Qm) (familyQc O c Qc))

/-- The `+0` perturbation: the IO coordinate's `γ` read as `c.2.1.1 + 0`. -/
def famIOPert (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X]) :
    Finset (OptimizedProductionChallengeTuple K F) :=
  Finset.univ.filter fun c =>
    (c.2.1.1 + 0, c.2.1.2) ∈
      FiniteIO.IOFailureEvent (hostileRecordsAt O c (familyQm O c Qm) (familyQc O c Qc))

/-- Positive control: the verbatim replica is the lifted constant by `rfl`. -/
theorem famIOLive_eq (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X]) :
    famIOLive O Qc Qm = FamilyEnvCore.famIOEventOf O Qc Qm := rfl

/-- The perturbation is propositionally harmless (`add_zero`) — it is a pure body change, which is
what makes it a sharp control for a fingerprint / `rfl`-bridge. -/
theorem famIOPert_eq_prop (Qc : Fin (CC[O]).rap.w → F[X]) (Qm : Fin (MC[O]).rap.w → F[X]) :
    famIOPert O Qc Qm = FamilyEnvCore.famIOEventOf O Qc Qm := by
  simp only [famIOPert, add_zero, Prod.mk.eta]
  rfl

end

end Nock.RedTeam.Batch886

/-! ## A. Fingerprints and the definitional probe -/

run_cmd do
  let env ← getEnv
  let R := `Nock.RedTeam.Batch886
  let lifted := `Nock.NockVMROM.Thm54.FamilyEnvCore.famIOEventOf
  let live := Nock.RedTeam.Batch817.fp env (R ++ `famIOLive)
  let pert := Nock.RedTeam.Batch817.fp env (R ++ `famIOPert)
  let prod := Nock.RedTeam.Batch817.fp env lifted
  logInfo m!"FamilyEnvCore.famIOEventOf {prod}; famIOLive {live}; famIOPert {pert}"
  if live == prod then logInfo "famIOLive reproduces the lifted constant's fingerprint"
    else logInfo "famIOLive does NOT reproduce the lifted fingerprint (instance-path difference; the control is replica-vs-replica)"
  unless pert != live do throwError "NC (A): the +0 body perturbation did not fire (replica pair)"
  -- the definitional probe: verbatim replica ≡ lifted, perturbed replica ≢ lifted
  let some cl := env.find? lifted | throwError "lifted famIOEventOf missing"
  let some cv := env.find? (R ++ `famIOLive) | throwError "famIOLive missing"
  let some cp := env.find? (R ++ `famIOPert) | throwError "famIOPert missing"
  let lvl := cl.levelParams.map Level.param
  let vL := cl.value!.instantiateLevelParams cl.levelParams lvl
  let vV := cv.value!.instantiateLevelParams cv.levelParams lvl
  let vP := cp.value!.instantiateLevelParams cp.levelParams lvl
  let (okLive, okPert) ← liftTermElabM do
    let a ← withTransparency .default (isDefEq vV vL)
    let b ← withTransparency .default (isDefEq vP vL)
    pure (a, b)
  unless okLive do throwError "positive control: the verbatim replica is not defeq to the lifted constant"
  if okPert then throwError "NC (A): the +0 perturbation is defeq to the lifted body (the rfl bridge would NOT catch it)"
  logInfo "NC (A): +0 perturbation of the lifted famIOEventOf body fires the replica fingerprint and breaks the rfl bridge (not defeq); the verbatim replica is defeq"

/-! ## A′. The reproducing replica, fingerprinted from this second module -/

run_cmd do
  let env ← getEnv
  let R := `Nock.RedTeam.Batch888
  let prod := Nock.RedTeam.Batch817.fp env `Nock.NockVMROM.Thm54.FamilyEnvCore.famIOEventOf
  let live := Nock.RedTeam.Batch817.fp env (R ++ `famIOLive)
  let pert := Nock.RedTeam.Batch817.fp env (R ++ `famIOPert)
  logInfo m!"A′: FamilyEnvCore.famIOEventOf {prod}; Batch888.famIOLive {live}; Batch888.famIOPert {pert}"
  if live == prod then logInfo "A′: the Batch888 replica REPRODUCES the lifted fingerprint"
    else logInfo "A′: the Batch888 replica does NOT reproduce the lifted fingerprint"
  unless pert != live do throwError "NC (A′): the +0 perturbation did not fire"
  -- Why it does not reproduce (measured): the only structural difference is the name of the
  -- auxiliary proof constant Lean abstracts from the declaration (`familyQc._proof_1` in
  -- FamilyEnvCore, `famIOLive._proof_1` here); `fp` hashes constant names.  Normalising every
  -- `…._proof_N` constant to one name makes the replica's value IDENTICAL to the lifted one, and the
  -- perturbed one still different.
  let norm : Expr → Expr := fun e => e.replace fun x => match x with
    | .const n ls => if (n.toString.splitOn "._proof_").length > 1 then some (.const `auxProof ls) else none
    | _ => none
  let some cl := env.find? `Nock.NockVMROM.Thm54.FamilyEnvCore.famIOEventOf | throwError "?"
  let some cv := env.find? (R ++ `famIOLive) | throwError "?"
  let some cp := env.find? (R ++ `famIOPert) | throwError "?"
  unless cl.type == cv.type do throwError "A′: replica type differs"
  unless norm cl.value! == norm cv.value! do throwError "A′: replica differs beyond aux-proof names"
  if norm cl.value! == norm cp.value! then throwError "A′: perturbation invisible after normalisation"
  logInfo "A′: replica = lifted constant up to the auxiliary proof name (familyQc._proof_1 vs famIOLive._proof_1); the +0 perturbation differs after normalisation"

/-! ## B. -/

run_cmd do
  let env ← getEnv
  let SP := `Nock.NockVMROM.Thm54.OptimizedStrictPackage
  let FE := `Nock.NockVMROM.Thm54.FamilyEnvCore

  --.
  unless Nock.RedTeam.Batch817.fp env (SP ++ `OptimizedHostileProductionFailureEvent) == 8307282949885789412 do
    throwError "HPFE is not at its 2a re-pinned value"
  unless Nock.RedTeam.Batch817.fp env (SP ++ `OptimizedProductionFailureEvent) == 7375876556367992980 do
    throwError "OPFE is not at its 2a re-pinned value"
  for n in [`familyQc, `familyQm, `hostileRecordsAt, `rowEnvAt, `memEnvF, `memEnvK,
      `hostileRequestsAt, `hostileResponsesAt, `computeChipAt_width, `memoryChipAt_width] do
    unless env.contains (FE ++ n) do throwError m!"lifted name missing: {n}"
  logInfo "B: HPFE 217319820750748878 → 10885927128798943981 (4.35: 8307282949885789412) and OPFE 6386915887416652064 → 912960407023990049 (4.35: 7375876556367992980) read back; the lifted watchlisted names are present"

#print axioms Nock.RedTeam.Batch886.famIOLive_eq
#print axioms Nock.RedTeam.Batch886.famIOPert_eq_prop

/-! ## C. -/

#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_31
#print axioms Nock.NockVMROM.Thm54.RealProgramSoundness.hostile_soundness_for_real_programs_at_two_pow_32
#print axioms Nock.NockVMROM.Thm54.GoldilocksParameters.hostile_soundness_at_paper_configuration
#print axioms Nock.RedTeam.Batch881.replaced_457_122
#print axioms Nock.RedTeam.Batch881.replaced_457_120
#print axioms Nock.RedTeam.Batch881.famIO_term_eq_package_term
