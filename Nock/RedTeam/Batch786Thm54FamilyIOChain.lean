/-
  Nock/RedTeam/Batch786Thm54FamilyIOChain.lean

  * **(A) Reach check** (`value? No declaration of the
    `Nock.NockVMROM.Thm54.FamilyIOChain` namespace reaches `OptimizedProductionAcceptanceAt`,
    its fields `same_problem` / `p8`, `OptimizedSameProblemAt`, the target's `same_problem` /
    `p8`, or the capstone statement `OptimizedFullStrictThm54Statement` (`S`).  Positive
    controls: the package-chip originals reach the probes they are known to read
    (`optimizedFullStrict_hostile_LIO` → `S`, `same_problem`; `hz0_of_good` → `same_problem`;
    `Batch742.row_record_is_request` → `S`; `optimizedProductionAcceptanceAt_iff` → `p8`;
    `cfg_z_eq_nprSeed` → `OptimizedSameProblemAt`).  The instrument is the one `Batch742` /
    the census scratch used, run over every constant of the namespace (not a hand list).
  * **(C) Honest instance** (cheap): at the honest traces of any package, reindexed to the
    family width, the family response list **is** the package's honest ten-slot response list
    at **every** tuple `c`, and the family request list has the honest request count.
-/
import Lean
import Nock.NockVMROM.Thm54.FamilyIOChainRouteB
import Nock.RedTeam.Batch742Thm54RouteBCensus
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch786

open Lean Elab Command
open scoped Polynomial
open Polynomial
open Nock
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

/-! ## (A) Reach check -/

partial def reachNames (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if !((`Nock).isPrefixOf n) then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

def PKG : Name := `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage

def probes : Array Name := #[
  PKG ++ `OptimizedHistoricalAcceptanceAt,
  PKG ++ `OptimizedHistoricalAcceptanceAt.same_problem,
  PKG ++ `OptimizedHistoricalAcceptanceAt.p8,
  PKG ++ `OptimizedSameProblemAt,
  `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement]

def familyNs : Name := `Nock.NockVMROM.Thm54.FamilyIOChain

/-- The delivered constants: every non-internal constant of the `FamilyIOChain` namespace. -/
def delivered (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    if familyNs.isPrefixOf n && !n.isInternal then out := out.push n
  return out

run_cmd do
  let env ← getEnv
  for p in probes do
    unless env.contains p do throwError m!"probe name missing: {p}"
  -- positive controls: the instrument finds each probe where it is known to be
  let ctl : List (Name × Name) := [
    (``OptimizedHostileTimestamps.optimizedFullStrict_hostile_LIO_historical,
      PKG ++ `OptimizedHistoricalAcceptanceAt.same_problem),
    (``OptimizedHostileTimestamps.hz0_of_good, PKG ++ `OptimizedHistoricalAcceptanceAt.same_problem),
    (``Nock.RedTeam.Batch742.row_record_is_request,
      `Nock.Walk37.Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement),
    (``OptimizedFullStrictNockVMROMPackage.optimizedHistoricalAcceptanceAt_iff,
      PKG ++ `OptimizedHistoricalAcceptanceAt.p8),
    (``OptimizedHostileTimestamps.hz0_of_good, PKG ++ `OptimizedSameProblemAt),
    (``OptimizedHostileTimestamps.hostile_LIO', PKG ++ `OptimizedHistoricalAcceptanceAt)]
  for (r, p) in ctl do
    unless (reachNames env #[r]).contains p do
      throwError m!"positive control failed: {r} does not reach {p}"
  logInfo m!"Batch786 (A): {ctl.length} positive controls pass"
  let ds := delivered env
  unless ds.size ≥ 100 do throwError m!"delivered set too small: {ds.size}"
  let mut bad : Array (Name × Name) := #[]
  for d in ds do
    let r := reachNames env #[d]
    for p in probes do
      if r.contains p then bad := bad.push (d, p)
  unless bad.isEmpty do throwError m!"Batch786 (A): a twin reaches a probe: {bad}"
  logInfo m!"Batch786 (A): {ds.size} FamilyIOChain constants reach none of {probes.size} probes"
  -- the key consumers by name (must be in the delivered set)
  let keys : List Name := [``hostile_LIO'_at, ``hostile_LIO_of_good_at,
    ``hostile_timestamp_eq_at, ``hostile_requests_nodup_at, ``hostile_ln0_eq_one_at,
    ``paired_records_of_good_at, ``memory_row_bound_at, ``ts_eq_alpha_pow_natLift_at,
    ``natLift_reqIdx_window_at, ``row_record_is_request_at, ``ver_reqIdx_injective_at,
    ``request_named_by_row_at, ``nprSeed_ne_of_good_at, ``window_of_rowsBound_at,
    ``hostile_LIO_of_rowsBound_at, ``paired_records_of_rowsBound_at]
  for k in keys do
    unless ds.contains k do throwError m!"key twin missing from the delivered set: {k}"
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut axBad : Array (Name × Name) := #[]
  for d in ds do
    let axs ← liftCoreM (Lean.collectAxioms d)
    for a in axs do
      unless allowed.contains a do axBad := axBad.push (d, a)
  unless axBad.isEmpty do throwError m!"Batch786 (B): non-standard axiom: {axBad}"
  logInfo m!"Batch786 (B): {ds.size} constants use only propext / Classical.choice / Quot.sound"

/-! ## (C) Honest instance -/

section Honest

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)

/-- Reindex a package-width memory trace at the family width (as `WrapMemoryConjuncts.familyQm`). -/
noncomputable def familyQm' (Qm : Fin P.memoryChip.rap.w → F[X]) : Fin (P.memoryChipAt c).rap.w → F[X] :=
  fun j => Qm (Fin.cast (FamilyComputeRows.memoryChipAt_width P c) j)

theorem honestQm_familyQm (Qm : Fin P.memoryChip.rap.w → F[X]) :
    FamilyMemoryRows.honestQm P c (familyQm' P c Qm) = Qm := by
  funext j
  unfold FamilyMemoryRows.honestQm familyQm'
  apply congrArg Qm
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

theorem honestQc_familyQc (Qc : Fin P.computeChip.rap.w → F[X]) :
    FamilyComputeRows.honestQc P c (FamilyComputeRows.familyQc P c Qc) = Qc := by
  funext j
  unfold FamilyComputeRows.honestQc FamilyComputeRows.familyQc
  apply congrArg Qc
  exact Fin.ext (by rw [Fin.val_cast, Fin.val_cast])

/-- **Honest instance (responses).**  At the package's honest memory trace, reindexed to the
family width, the family response list is the package's honest ten-slot response list — at
every tuple `c` (memory records read trace columns only). -/
theorem family_responses_at_honest_trace :
    hostileResponsesAt P c (familyQm' P c
        (MultiRootOptimizedAcceptance.canonicalMemoryTrace P)) =
      (honestRecords10 P.optimized.family).responses := by
  rw [hostileResponsesAt_eq_package, honestQm_familyQm,
    ← OptimizedHostileIOAssembly.hostileResponses_eq_package]
  exact OptimizedHostileIOAssembly.canonical_hostileResponses P

/-- **Honest instance (request count).**  At the package's honest compute trace, reindexed to
the family width, the family request list has the honest request count — at every tuple `c`. -/
theorem family_request_count_at_honest_trace
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis) (hwidth : FormRWidth F) :
    (hostileRequestsAt P c (FamilyComputeRows.familyQc P c
        (MultiRootOptimizedAcceptance.canonicalComputeTrace P))).length =
      (honestRecords10 P.optimized.family).requests.length := by
  rw [hostileRequestsAt_length_eq, honestQc_familyQc,
    ← OptimizedHostileIOAssembly.hostileRequests_eq_package,
    OptimizedHostileIOAssembly.canonical_hostileRequests P hax hwidth]

/-! ## (D) Why `FamilyIOGood` is named: the family timestamp slot reads the coin -/

theorem family_ts_reads_coin (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (i : Fin (OptimizedComputeHostileAccumulator.rows P)) (j : Fin 3)
    (hact : OptimizedComputeHostileAccumulator.activeMask (FamilyComputeRows.rowEnvAt P c Qc i) j = 1) :
    OptimizedComputeHostileAccumulator.rowRecord (FamilyComputeRows.rowEnvAt P c Qc i) j 7 =
      OptimizedHostileTimestamps.lnPrevAt (FamilyComputeRows.rowEnvAt P c Qc i) *
        alphaM c.1 ^ ((j : ℕ) + 1) := by
  rw [OptimizedHostileTimestamps.rowRecord_ts_active _ j hact, alphaAt_rowEnvAt]

end Honest

end Nock.RedTeam.Batch786

#print axioms Nock.RedTeam.Batch786.family_responses_at_honest_trace
#print axioms Nock.RedTeam.Batch786.family_request_count_at_honest_trace
#print axioms Nock.RedTeam.Batch786.family_ts_reads_coin
#print axioms Nock.NockVMROM.Thm54.FamilyIOChain.hostile_LIO'_at
#print axioms Nock.NockVMROM.Thm54.FamilyIOChain.hostile_LIO_of_good_at
#print axioms Nock.NockVMROM.Thm54.FamilyIOChain.paired_records_of_good_at
#print axioms Nock.NockVMROM.Thm54.FamilyIOChain.ver_reqIdx_injective_at
#print axioms Nock.NockVMROM.Thm54.FamilyIOChain.window_of_rowsBound_at
