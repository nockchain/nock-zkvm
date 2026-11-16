/-
  Nock/RedTeam/Batch970Thm54Round0WrapReadSet.lean

  Additive; nothing consumes this.

  * **(A) Column rounds** (`DeployedStaging`, `decide`): the wrap's own reads are the compute
    source selectors `0..9`, the certificate block `202..270` and the memory base column `181`
    (`reqIdx`); all are round 0.  Positive control: the stored `T` (memory role 25, column `81`),
    `ts` (role 26, column `84`) and `C'` (role 57, column `177`) are round 2.
  * **(C) No `ts`, no stored `(T, C', λ)` in the specialization**: the specialized round-0 row is
    the same for any two decoded rows that differ only in `mem.ts`, `mem.axis`, `cprime?`,
    `lambda?` (`specialize_wrapR0_ignores`).  Positive control: the lifted wrap's specialization
    reads the stored axis (`lifted_specialize_reads_axis`, at `ZMod 31`).
  * **(D) Reach probe** (`allowOpaque := true`): `wrapR0OfEnvs` reaches neither `memExponent`,
    `nounByFP` nor the challenge projection `Env.chal`; positive controls: the lifted
    `wrapMemoryLabel` reaches `memExponent`, the lifted `joinNoun` reaches `nounByFP`, the lifted
    `lblMAt` reaches `Env.chal`.
  * **(E) The generic chain at `timestampOfTraces` is the lifted chain** (`rfl`), so the round-0
    strategy and the lifted strategy differ ONLY through the execution template's memory forest;
    (F) row by row, the round-0 template row is the lifted one iff the record exponent and the
    stored axis agree (`lblMR0_eq_lifted_iff`), and the forests agree when every row does
    (`memoryForest_R0_eq_lifted_of_rows`).
-/
import Lean
import Nock.NockVMROM.Thm54.StrategyOfTracesR0
import Nock.NockVMROM.Thm54.DeployedStaging
import Nock.RedTeam.Batch733Thm54DecodedLambdaSlotMapReadSet
import Nock.RedTeam.Batch509Thm54WrapSpecialize
import Nock.RedTeam.Batch916Thm54Part2bEqBlkDoubleEncode
import Nock.NockVMROM.Thm54.P8Core.Batch970Thm54Round0WrapReadSet

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Lean Elab Command

namespace Nock.RedTeam.Batch970

open Nock Nock.Walk Nock.MemoryTable Nock.ComputeTable
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.RedTeam.Batch733

noncomputable section

/-! ## (A) Column rounds -/

theorem wrap_compute_columns_round_zero :
    ∀ c, c < 10 ∨ (202 ≤ c ∧ c ≤ 270) → DeployedStaging.computeColRound c = 0 := by
  intro c hc
  rcases hc with h | ⟨h1, h2⟩
  · interval_cases c <;> decide
  · interval_cases c <;> decide

theorem wrap_memory_column_round_zero :
    DeployedStaging.memoryColRound OptimizedMemoryGateBasis.reqIdxCol = 0 := by decide

/-- Positive control: the stored `T` (role 25), `ts` (role 26) and `C'` (role 57) are round 2. -/
theorem stored_record_columns_round_two :
    DeployedStaging.memoryColRound (6 + 3 * 25) = 2 ∧
      DeployedStaging.memoryColRound (6 + 3 * 26) = 2 ∧
      DeployedStaging.memoryColRound (6 + 3 * 57) = 2 := by decide

/-! ## (B) The read-set receipt -/

section ReadSet

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
  [Fintype F] [DecidableEq F] {N M : ℕ}

theorem memRowExpOfEnvs_congr {envsF envsF' : Fin M → Env F} (hM : 0 < M)
    (h : ∀ r, (envsF r).trace OptimizedMemoryGateBasis.reqIdxCol =
      (envsF' r).trace OptimizedMemoryGateBasis.reqIdxCol) :
    memRowExpOfEnvs envsF hM = memRowExpOfEnvs envsF' hM := by
  funext i
  unfold memRowExpOfEnvs
  split_ifs <;> rw [h]

/-- **The read-set receipt.**  Two env families that agree on the compute selectors `0..9`, the
certificate block `202..270` and the memory column `181` give the same round-0 wrap at every
row, for every decoded row: no other column and no challenge is read. -/
theorem wrapR0OfEnvs_congr {envsC envsC' : Fin N → Env K} {envsF envsF' : Fin M → Env F}
    (hM : 0 < M) (hC : ComputeAgree envsC envsC')
    (hF : ∀ r, (envsF r).trace OptimizedMemoryGateBasis.reqIdxCol =
      (envsF' r).trace OptimizedMemoryGateBasis.reqIdxCol) (i : ℕ) (row : MState × DTmem K) :
    wrapR0OfEnvs envsC envsF hM i row = wrapR0OfEnvs envsC' envsF' hM i row := by
  unfold wrapR0OfEnvs
  rw [memRowExpOfEnvs_congr hM hF, certAxisOfEnvs_congr hC]

end ReadSet

section Strategy

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (O : OptimizedStrictNockVMROMPackage F K hOrb)

theorem computeEnvsR0_trace (Qc) (c c' : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.compRows) :
    (computeEnvsR0 O Qc c i).trace = (computeEnvsR0 O Qc c' i).trace := by
  unfold computeEnvsR0 FamilyEnvCore.rowEnvAt
  rw [FamilyEnvCore.gather_toSourceEnv_trace_congr O
      (FamilyEnvCore.familyQc_envTrace O Qc c _ _ _ _),
    FamilyEnvCore.gather_toSourceEnv_trace_congr O
      (FamilyEnvCore.familyQc_envTrace O Qc c' _ _ _ _)]
  rfl

theorem memoryEnvsR0_trace (Qm) (c c' : OptimizedProductionChallengeTuple K F)
    (i : Fin O.family.problem.cfg.memRows) :
    (memoryEnvsR0 O Qm c i).trace = (memoryEnvsR0 O Qm c' i).trace := rfl

/-- **No challenge, at the strategy level**: the round-0 template's metadata (record exponent and
stored axis) is the same at every challenge tuple. -/
theorem lblMR0_meta_tuple_free (Qc Qm) (c c' : OptimizedProductionChallengeTuple K F) (i : ℕ) :
    (lblMR0 O Qc Qm c i).timestamp.recordExponent =
        (lblMR0 O Qc Qm c' i).timestamp.recordExponent ∧
      (lblMR0 O Qc Qm c i).placeholder.2.2.mem.axis =
        (lblMR0 O Qc Qm c' i).placeholder.2.2.mem.axis := by
  have hF : memRowExpOfEnvs (memoryEnvsR0 O Qm c) O.family.problem.cfg.memRows_pos =
      memRowExpOfEnvs (memoryEnvsR0 O Qm c') O.family.problem.cfg.memRows_pos :=
    memRowExpOfEnvs_congr _ fun r => by rw [memoryEnvsR0_trace O Qm c c' r]
  have hC : certAxisOfEnvs (computeEnvsR0 O Qc c) = certAxisOfEnvs (computeEnvsR0 O Qc c') :=
    certAxisOfEnvs_congr fun r k _ => by rw [computeEnvsR0_trace O Qc c c' r]
  simp [lblMR0, wrapR0OfEnvs, wrapMemoryLabelR0, hF, hC]

end Strategy

/-! ## (C) The specialization reads no stored `ts` / `T` / `C'` / `λ` -/

section Ignores

variable {K : Type} [Field K]

/-- Rows that differ only in `mem.ts`, `mem.axis`, `cprime?`, `lambda?` specialize to the same
round-0 row (any state: active rows overwrite all four; inactive rows zero the record and keep
`cprime?`, which the two rows then share by hypothesis `hcp` only on inactive rows). -/
theorem specialize_wrapR0_ignores (e a : ℕ) (α lmb : K) (row : MState × DTmem K)
    (t x : K) (cp : Option K) (l : Option K)
    (hcp : memoryMemRecKind row.1 ≠ .active → cp = row.2.2.cprime?) :
    (wrapMemoryLabelR0 e a (row.1, (row.2.1,
        { row.2.2 with
          mem := { row.2.2.mem with ts := t, axis := x }
          cprime? := cp
          lambda? := l }))).specialize α lmb =
      (wrapMemoryLabelR0 e a row).specialize α lmb := by
  by_cases hact : memoryMemRecKind row.1 = .active
  · simp [wrapMemoryLabelR0, MemoryRowTemplate.specialize, MemoryRowTemplate.encodeRow,
      MemoryRowTemplate.specializeA, specializeMemRec, hact]
  · have := hcp hact
    subst this
    simp [wrapMemoryLabelR0, MemoryRowTemplate.specialize, MemoryRowTemplate.encodeRow,
      MemoryRowTemplate.specializeA, specializeMemRec, hact]

end Ignores

/-- Positive control (C): the lifted wrap's specialization reads the stored axis — at `ZMod 31`,
`λ = 3`, a `read_root` row storing `9` specializes to `27`, one storing `1` to `1`. -/
theorem lifted_specialize_reads_axis (inp : MemoryTable.Inputs (ZMod 31)) (α : ZMod 31) :
    ((StrategyOfTracesLift.wrapMemoryLabel α
        (.read_root, (inp, Batch916.reencodedRow))).specialize α 3).2.2.mem.axis ≠
      ((StrategyOfTracesLift.wrapMemoryLabel α
        (.read_root, (inp, { Batch916.reencodedRow with
          mem := { Batch916.reencodedRow.mem with axis := 1 } }))).specialize α 3).2.2.mem.axis := by
  have hact : memoryMemRecKind MState.read_root = .active := rfl
  have h27 : nockAxisOf ((27 : ℕ) : ZMod 31) = 27 :=
    nockAxisOf_natCast (by rw [ZMod.ringChar_zmod_n]; norm_num)
  have h1 : nockAxisOf ((1 : ℕ) : ZMod 31) = 1 :=
    nockAxisOf_natCast (by rw [ZMod.ringChar_zmod_n]; norm_num)
  simp only [MemoryRowTemplate.specialize, MemoryRowTemplate.encodeRow,
    MemoryRowTemplate.specializeA, StrategyOfTracesLift.wrapMemoryLabel, specializeMemRec, hact,
    if_true, decide_true, NockVM.formRRow, Batch916.reencodedRow, Batch916.honestRow]
  simp only [Nat.cast_ofNat] at h27
  simp only [Nat.cast_one] at h1
  rw [h27, h1]
  unfold formRT
  rw [show formRCertShift 27 = 4 from by decide, show formRCertShift 1 = 0 from by decide]
  decide

/-! ## (D) Reach probe -/

partial def reachSet (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work := roots
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        match ci.value? (allowOpaque := true) with
        | some v => cs := cs ++ v.getUsedConstants
        | none => pure ()
        if let .inductInfo iv := ci then cs := cs ++ iv.ctors.toArray
        work := cs.toList ++ work
  return seen

def wrapR0Names : List Name :=
  [`Nock.NockVMROM.Thm54.StrategyOfTracesR0.wrapR0OfEnvs,
   `Nock.NockVMROM.Thm54.StrategyOfTracesR0.wrapMemoryLabelR0,
   `Nock.NockVMROM.Thm54.StrategyOfTracesR0.memRowExpOfEnvs,
   `Nock.NockVMROM.Thm54.StrategyOfTracesR0.certAxisOfEnvs]

def forbidden : List Name :=
  [`Nock.NockVMROM.Thm54.StrategyOfTracesLift.memExponent,
   `Nock.NockVMROM.Thm54.StrategyOfTracesCore.memExponent,
   `Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounByFP,
   `Nock.NockVMROM.Thm54.StrategyOfTraces.nounByFP,
   `Nock.Reified.Env.chal]

run_cmd do
  let env ← getEnv
  for n in wrapR0Names ++ forbidden do
    unless (env.find? n).isSome do throwError m!"target missing: {n}"
  let cl := reachSet env wrapR0Names
  for f in forbidden do
    if cl.contains f then throwError m!"the round-0 wrap reaches {f}"
  -- positive controls
  let pw := reachSet env [`Nock.NockVMROM.Thm54.StrategyOfTracesLift.wrapMemoryLabel]
  unless pw.contains `Nock.NockVMROM.Thm54.StrategyOfTracesLift.memExponent do
    throwError "positive control: the lifted wrapMemoryLabel does not reach memExponent"
  let pj := reachSet env [`Nock.NockVMROM.Thm54.StrategyOfTracesLift.joinNoun]
  unless pj.contains `Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounByFP do
    throwError "positive control: joinNoun does not reach nounByFP"
  let pc := reachSet env [`Nock.NockVMROM.Thm54.StrategyOfTracesLift.lblMAt]
  unless pc.contains `Nock.Reified.Env.chal do
    throwError "positive control: lblMAt does not reach Env.chal"
  logInfo m!"round0_wrap_reach: the wrap's {wrapR0Names.length} constants reach {cl.size} constants, none of memExponent / nounByFP / Env.chal; the three positive controls pass"

/-! `strategyOfTracesR0`
reaches neither `memExponent` nor the lifted `wrapMemoryLabel` / `execTemplateOfTraces`; positive
control: the lifted `strategyOfTraces` reaches all three.  It DOES reach `nounByFP` (through the
skeleton `decodedSkeletonOf`) — logged, not a failure: "round 0" is a property of the memory-wrap
metadata only. -/
run_cmd do
  let env ← getEnv
  let r0 := `Nock.NockVMROM.Thm54.StrategyOfTracesR0.strategyOfTracesR0
  let lifted := `Nock.NockVMROM.Thm54.StrategyOfTracesLift.strategyOfTraces
  let bad : List Name :=
    [`Nock.NockVMROM.Thm54.StrategyOfTracesLift.memExponent,
     `Nock.NockVMROM.Thm54.StrategyOfTracesLift.wrapMemoryLabel,
     `Nock.NockVMROM.Thm54.StrategyOfTracesLift.execTemplateOfTraces]
  for n in [r0, lifted] ++ bad do
    unless (env.find? n).isSome do throwError m!"target missing: {n}"
  let cl := reachSet env [r0]
  for b in bad do
    if cl.contains b then throwError m!"strategyOfTracesR0 reaches {b}"
  let pc := reachSet env [lifted]
  for b in bad do
    unless pc.contains b do throwError m!"positive control: the lifted strategyOfTraces does not reach {b}"
  let nfp := cl.contains `Nock.NockVMROM.Thm54.StrategyOfTracesLift.nounByFP
  logInfo m!"round0_strategy_reach: strategyOfTracesR0 reaches {cl.size} constants, none of memExponent / wrapMemoryLabel / execTemplateOfTraces (positive control: the lifted strategy reaches all three); reaches nounByFP via the skeleton: {nfp}"

/-! ## (E) The generic chain at the lifted timestamp strategy is the lifted chain -/

section Receipts

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (O : OptimizedStrictNockVMROMPackage F K hOrb)

open StrategyOfTracesLift

theorem familyDataGen_eq (tag Qc Qm c h z hz α lmb) :
    familyDataGen O (timestampOfTraces O Qc Qm c h) tag Qm c z hz α lmb =
      familyDataOfTraces O tag Qc Qm c h z hz α lmb := rfl

theorem tablesGen_eq (tag Qc Qm c h z hz α lmb) :
    tablesGen O (timestampOfTraces O Qc Qm c h) tag Qc Qm c z hz α lmb =
      tablesOfTraces O tag Qc Qm c h z hz α lmb := rfl

theorem ioGen_eq (tag Qc Qm c h z hz α lmb) :
    ioGen O (timestampOfTraces O Qc Qm c h) tag Qc Qm c z hz α lmb =
      ioOfTraces O tag Qc Qm c h z hz α lmb := rfl

theorem afterAlphaMGen_eq (tag Qc Qm c h z hz α lmb) :
    afterAlphaMGen O (timestampOfTraces O Qc Qm c h) tag Qc Qm c z hz α lmb =
      afterAlphaMOfTraces O tag Qc Qm c h z hz α lmb := rfl

theorem topologyGen_eq (tag Qc Qm c h z hz α lmb) :
    topologyGen O (timestampOfTraces O Qc Qm c h) tag Qc Qm c z hz α lmb =
      topologyOfTraces O tag Qc Qm c h z hz α lmb := rfl

theorem rawVerifierGen_eq (tag Qc Qm c h) :
    rawVerifierGen O (timestampOfTraces O Qc Qm c h) tag Qc Qm c =
      rawVerifierOfTraces O tag Qc Qm c h := rfl

theorem verifierGen_eq (tag Qc Qm c h) :
    verifierGen O (timestampOfTraces O Qc Qm c h) tag Qc Qm c =
      verifierOfTraces O tag Qc Qm c h := rfl

/-- The round-0 timestamp strategy differs from the lifted one only in the execution template:
the claim and the configuration template are the lifted ones. -/
theorem timestampR0_claim_eq (Qc Qm c h) :
    (timestampOfTracesR0 O Qc Qm c h).claim = (timestampOfTraces O Qc Qm c h).claim := rfl

/-! ## (F) Row by row: where the two memory templates differ -/

/-- The lifted template's memory forest is the inverse BFS of the lifted wrap of `lblM`. -/
theorem memoryForest_lifted_eq (Qc Qm c h z) :
    (execTemplateOfTraces O Qc Qm c h z).memoryForest =
      reconForest O.family.problem.cfg.kMem (foM O Qm c)
        (fun i => wrapMemoryLabel (alphaM c.1) (lblM O Qm c i)) O.family.problem.cfg.memRows :=
  Batch509.mapNTree_reconForest _ _ _ _ _

/-- **Exactly where the templates differ, row by row**: the round-0 template row is the lifted
one iff the record exponent `natLift reqIdx` is the lifted `memExponent α ts` and the decoded slot
`axis` (the stored `T`) is the recovered `a`. -/
theorem lblMR0_eq_lifted_iff (Qc Qm c) (i : ℕ) :
    lblMR0 O Qc Qm c i = wrapMemoryLabel (alphaM c.1) (lblM O Qm c i) ↔
      (memRowExpOfEnvs (memoryEnvsR0 O Qm c) O.family.problem.cfg.memRows_pos i =
          memExponent (alphaM c.1) (lblM O Qm c i).2.2.mem.ts ∧
        (((certAxisOfEnvs (computeEnvsR0 O Qc c)
            (memRowExpOfEnvs (memoryEnvsR0 O Qm c) O.family.problem.cfg.memRows_pos i) : ℕ)
              : K) = (lblM O Qm c i).2.2.mem.axis)) := by
  constructor
  · intro h
    refine ⟨congrArg (fun T : MemoryRowTemplate (K := K) => T.timestamp.recordExponent) h,
      congrArg (fun T : MemoryRowTemplate (K := K) => T.placeholder.2.2.mem.axis) h⟩
  · rintro ⟨he, ha⟩
    simp only [lblMR0, wrapR0OfEnvs, wrapMemoryLabelR0, wrapMemoryLabel]
    rw [ha, he]

/-- The forests agree when every row does. -/
theorem memoryForest_R0_eq_lifted_of_rows (Qc Qm c h z)
    (hrow : ∀ i, lblMR0 O Qc Qm c i = wrapMemoryLabel (alphaM c.1) (lblM O Qm c i)) :
    (execTemplateOfTracesR0 O Qc Qm c h z).memoryForest =
      (execTemplateOfTraces O Qc Qm c h z).memoryForest := by
  rw [memoryForest_lifted_eq]
  exact Batch509.reconForest_eq_of_lbl _ _ _ hrow

end Receipts

end

end Nock.RedTeam.Batch970

#print axioms Nock.RedTeam.Batch970.wrapR0OfEnvs_congr
#print axioms Nock.RedTeam.Batch970.lblMR0_meta_tuple_free
#print axioms Nock.RedTeam.Batch970.specialize_wrapR0_ignores
#print axioms Nock.RedTeam.Batch970.lifted_specialize_reads_axis
#print axioms Nock.RedTeam.Batch970.lblMR0_eq_lifted_iff
#print axioms Nock.RedTeam.Batch970.memoryForest_R0_eq_lifted_of_rows
