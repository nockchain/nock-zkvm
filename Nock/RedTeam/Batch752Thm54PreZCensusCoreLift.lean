/-
  Nock/RedTeam/Batch752Thm54PreZCensusCoreLift.lean

Positive controls: the
    same walk from `PreSeedCensus` and from `StrategyOfTraces` (the two modules the core left)
    finds the pinned file.
  Positive control: the replica
    reproduces a pinned frontier fingerprint; negative control: the checker rejects a row with
    another row's hash. Theorem proof terms are hashed separately and disclosed (4 differ:
    `decodePre.eq_def` / `eq_5` / `induct` and `decodeNoun_buildTF_eq_decodePre`).
  * **(C) The env-parametric core IS the package-level census at `memoryBaseEnv`.**
    `preLbl = preLblOfEnvs`, `preZNoun = preZNounOfEnvs`, `Batch742.reqTgt = reqTgtOfEnvs`,
    `zipPairs ∘ reqTgt = reqPairsOfEnvs` (all `rfl`) and `Batch742.reqPairEvent = liftP8Failure
    (reqPairEventOfEnvs …)`, at `envs := P.memoryBaseEnv Qm`, `hM := memRows_pos`,
    `kroots := kMem`.
  * **(D)** `requestTargets` is `atom 0` at index `0` and at `halt`.
-/
import Lean
import Nock.NockVMROM.Thm54.PreZCensusCore
import Nock.RedTeam.Batch742Thm54RouteBCensus

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch752

open Lean Elab Command

/-! ## (A) Import walk -/

def importsOf (env : Environment) : Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for i in [0:env.header.moduleNames.size] do
    m := m.insert env.header.moduleNames[i]! (env.header.moduleData[i]!.imports.map (·.module))
  return m

partial def importClosure (g : Std.HashMap Name (Array Name)) (root : Name) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := [root]
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      for c in g.getD n #[] do
        unless seen.contains c do work := c :: work
  return seen

def pinnedMod : Name := `Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
def carrierMod : Name := `Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
def coreMod : Name := `Nock.NockVMROM.Thm54.PreZCensusCore

def briefImports : Array Name := #[`Nock.NockVMROM.Thm54.HostileSkeletonDecoding,
  `Nock.NockVMROM.Thm54.JointSoundness, `Nock.Walk, `Nock.NPR, `Nock.GlobalCarryRecognizer,
  `Nock.NockVMROM.Thm54.RecordCarrier, `Nock.NockVMROM.Thm54.SemanticStrategy,
  `Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis]

run_cmd do
  let env ← getEnv
  let g := importsOf env
  let direct := (g.getD coreMod #[]).filter (· != `Init)
  unless direct.size == briefImports.size && briefImports.all direct.contains do
    throwError m!"PreZCensusCore direct imports differ from the brief: {direct}"
  let cl := importClosure g coreMod
  if cl.contains pinnedMod || cl.contains carrierMod then
    throwError "STOP: PreZCensusCore reaches the pinned file or the carrier"
  for n in cl.toList do
    if (g.getD n #[]).contains pinnedMod then throwError m!"STOP: {n} imports the pinned file"
  for src in [`Nock.NockVMROM.Thm54.PreSeedCensus, `Nock.NockVMROM.Thm54.StrategyOfTraces] do
    unless (importClosure g src).contains pinnedMod do
      throwError m!"positive control failed: {src} should reach the pinned file"
  logInfo m!"PreZCensusCore: {cl.size} modules in its import closure; pinned file absent, \
    carrier absent; direct imports = the brief's eight. Positive controls (PreSeedCensus, \
    StrategyOfTraces reach the pinned file): ok"

/-! ## (B) Fingerprint identity (replica of `FrozenClosure.fingerprint`, verbatim) -/

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleFor? n with
  | some m => m
  | none => `_local

def ctorTypes (env : Environment) (ci : ConstantInfo) : Array Expr :=
  match ci with
  | .inductInfo iv =>
      iv.ctors.foldl (init := #[]) fun acc c =>
        match env.find? c with
        | some cci => acc.push cci.type
        | none => acc
  | _ => #[]

def meaningExprs (env : Environment) (n : Name) : Array Expr :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let base := #[ci.type] ++ ctorTypes env ci
    match ci with
    | .thmInfo _ => base
    | .axiomInfo _ => base
    | _ => match ci.value? (allowOpaque := true) with
           | some v => base.push v
           | none => base

def fpHash (env : Environment) (n : Name) : UInt64 :=
  (meaningExprs env n).foldl (init := (17 : UInt64)) fun acc e => mixHash acc e.hash

def proofHash (env : Environment) (n : Name) : UInt64 :=
  match env.find? n with
  | some (.thmInfo tv) => tv.value.hash
  | _ => 0

/-- ``, measured by
the same replica over the whole library at the base (78849 `Nock.*` constants). -/

def recorded : Array (String × String × UInt64 × UInt64) := #[
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodeNoun_buildTF_eq_decodePre", "Nock.NockVMROM.Thm54.PreSeedCensus.decodeNoun_buildTF_eq_decodePre", 14786420997928232343, 4059799541),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre", 11249868532285631401, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._f", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._f", 469241615524897405, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._sparseCasesOn_1", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._sparseCasesOn_1", 13095420194988522652, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._sparseCasesOn_1.else_eq", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._sparseCasesOn_1.else_eq", 2608344397796926161, 1002556507),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._sparseCasesOn_2", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._sparseCasesOn_2", 6669108917992131471, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._sparseCasesOn_2.else_eq", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._sparseCasesOn_2.else_eq", 12661309809048557208, 897110728),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._sunfold", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._sunfold", 13796491082029766230, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._unsafe_rec", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre._unsafe_rec", 4352485212620128093, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_1", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_1", 15930257602690906306, 2170296728),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_2", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_2", 6709460762565700477, 4006171802),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_3", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_3", 16671588777977559413, 3840790427),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_4", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_4", 8705073206966067996, 4000515083),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_5", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_5", 15205797516145132728, 1820058800),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_def", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.eq_def", 7436784079195087568, 1377987495),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.induct", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.induct", 10903162392282624740, 1446509502),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.match_1", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre.match_1", 81547483567691169, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre_leafList_lt", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre_leafList_lt", 4377129299833565919, 741635600),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre_leafList_lt._proof_1_10", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre_leafList_lt._proof_1_10", 11587156104477304776, 3745866646),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre_leafList_lt._simp_1_8", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre_leafList_lt._simp_1_8", 11795845109467326723, 2859177625),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodePre_leafList_lt._simp_1_9", "Nock.NockVMROM.Thm54.PreSeedCensus.decodePre_leafList_lt._simp_1_9", 840997799738035673, 1504788726),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decode_node_congr", "Nock.NockVMROM.Thm54.PreSeedCensus.decode_node_congr", 7065956464469389267, 2690726943),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds", "Nock.NockVMROM.Thm54.PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds", 17541768847998897558, 2583714596),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.guardedCensus", "Nock.NockVMROM.Thm54.PreSeedCensus.guardedCensus", 11214531059870353042, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.guardedCensus._proof_1", "Nock.NockVMROM.Thm54.PreSeedCensus.guardedCensus._proof_1", 1143389805267107726, 1248681805),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.guardedCensus._simp_2", "Nock.NockVMROM.Thm54.PreSeedCensus.guardedCensus._simp_2", 14368057795089357047, 652254238),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.guardedPairs", "Nock.NockVMROM.Thm54.PreSeedCensus.guardedPairs", 3423436599348089555, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.guardedPairs.eq_1", "Nock.NockVMROM.Thm54.PreSeedCensus.guardedPairs.eq_1", 16151758074381315092, 1735833718),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.guardedPairs_length_le", "Nock.NockVMROM.Thm54.PreSeedCensus.guardedPairs_length_le", 8986205992071245435, 1921344558),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.list_eq_of_map_natCast_eq", "Nock.NockVMROM.Thm54.PreSeedCensus.list_eq_of_map_natCast_eq", 17450494675610714381, 1058067163),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.list_eq_of_map_natCast_eq._f", "Nock.NockVMROM.Thm54.PreSeedCensus.list_eq_of_map_natCast_eq._f", 16663382070241483701, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.list_eq_of_map_natCast_eq.match_1_1", "Nock.NockVMROM.Thm54.PreSeedCensus.list_eq_of_map_natCast_eq.match_1_1", 18148255141693748652, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.mem_pairBadSeeds_iff", "Nock.NockVMROM.Thm54.PreSeedCensus.mem_pairBadSeeds_iff", 16410125656302787919, 4285458221),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.mem_pairBadSeeds_of_collision", "Nock.NockVMROM.Thm54.PreSeedCensus.mem_pairBadSeeds_of_collision", 15628286840475780786, 3141712453),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.natCast_inj_of_lt", "Nock.NockVMROM.Thm54.PreSeedCensus.natCast_inj_of_lt", 13981696372163647467, 2001923192),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.noun_eq_of_fieldNoun_eq", "Nock.NockVMROM.Thm54.PreSeedCensus.noun_eq_of_fieldNoun_eq", 3398495045950895337, 2857418940),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.pairBadSeeds", "Nock.NockVMROM.Thm54.PreSeedCensus.pairBadSeeds", 8523380660461741701, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.pairBadSeeds_card_le", "Nock.NockVMROM.Thm54.PreSeedCensus.pairBadSeeds_card_le", 15047827328021942942, 2035620213),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.pairBadSeeds_eq_empty_of_diag", "Nock.NockVMROM.Thm54.PreSeedCensus.pairBadSeeds_eq_empty_of_diag", 4259000538888676395, 2850901865),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.pairBadSeeds_eq_empty_of_diag._simp_1_1", "Nock.NockVMROM.Thm54.PreSeedCensus.pairBadSeeds_eq_empty_of_diag._simp_1_1", 5140478392145191015, 373915553),
  ("Nock.NockVMROM.Thm54.StrategyOfTraces.memoryStateOf", "Nock.NockVMROM.Thm54.StrategyOfTraces.memoryStateOf", 13906310903953858646, 0),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodeNoun_buildTF_eq_decodePre._proof_1_2", "Nock.NockVMROM.Thm54.PreSeedCensus.decodeNoun_buildTF_eq_decodePre._proof_1_3", 2161761729494012605, 27107207),
  ("Nock.NockVMROM.Thm54.PreSeedCensus.decodeNoun_buildTF_eq_decodePre._simp_1_1", "Nock.NockVMROM.Thm54.PreSeedCensus.decodeNoun_buildTF_eq_decodePre._simp_1_2", 14368057795089357047, 652254238)]

def checkRows (env : Environment) (rows : Array (String × String × UInt64 × UInt64)) :
    Except String (Nat × Array Name) := do
  let mut proofDiff : Array Name := #[]
  for (_, now, fp, ph) in rows do
    let n := now.toName
    unless (env.find? n).isSome do throw s!"missing {now}"
    unless fpHash env n == fp do throw s!"fingerprint moved: {now}"
    unless moduleOf env n == coreMod do throw s!"not in PreZCensusCore: {now}"
    unless proofHash env n == ph do proofDiff := proofDiff.push n
  return (rows.size, proofDiff)

run_cmd do
  let env ← getEnv
  unless fpHash env `Nock.NockVMROM.Thm54.OptimizedStrictPackage.pricedWalkWork ==
      18169742864994646756 do throwError "replica control failed (pricedWalkWork)"
  match checkRows env recorded with
  | .error e => throwError m!"STOP: {e}"
  | .ok (k, pd) =>
    let bad := recorded.set! 0 (recorded[0]!.1, recorded[0]!.2.1, recorded[1]!.2.2.1,
      recorded[0]!.2.2.2)
    match checkRows env bad with
    | .ok _ => throwError "negative control failed: swapped hash accepted"
    | .error _ =>
      logInfo m!"{k} moved/renamed constants: fingerprint identical, module PreZCensusCore. \
        Negative control rejected. Proof terms differing (disclosed): {pd}"

/-! ## (C) The env-parametric core at `memoryBaseEnv` is the package-level census -/

section Bridge

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.PreSeedCensus

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem preLbl_eq_ofEnvs (Qm : Fin P.memoryChip.rap.w → F[X]) :
    preLbl P Qm = preLblOfEnvs (P.memoryBaseEnv Qm)
      P.optimized.family.problem.cfg.memRows_pos := rfl

theorem preZNoun_eq_ofEnvs (q : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    preZNoun P q Qm = preZNounOfEnvs K q P.optimized.family.problem.cfg.kMem
      (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos := rfl

theorem reqTgt_eq_ofEnvs (Qm : Fin P.memoryChip.rap.w → F[X]) (T : MState → ℕ → Noun) :
    Batch742.reqTgt P Qm T = reqTgtOfEnvs (P.memoryBaseEnv Qm)
      P.optimized.family.problem.cfg.memRows_pos T := rfl

theorem zipPairs_reqTgt_eq_ofEnvs (q : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X])
    (T : MState → ℕ → Noun) :
    zipPairs P q Qm (Batch742.reqTgt P Qm T) = reqPairsOfEnvs K q
      P.optimized.family.problem.cfg.kMem (P.memoryBaseEnv Qm)
      P.optimized.family.problem.cfg.memRows_pos T := rfl


theorem reqPairEvent_eq_lift_ofEnvs (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X])
    (T : MState → ℕ → Noun) :
    Batch742.reqPairEvent (K := K) P q Λ Qm T =
      liftP8Failure (F := F) (reqPairEventOfEnvs K q P.optimized.family.problem.cfg.kMem Λ
        (P.memoryBaseEnv Qm) P.optimized.family.problem.cfg.memRows_pos T) := by
  rw [Batch742.reqPairEvent, pairEvent_eq_lift]
  rfl

end Bridge

/-! ## (D) `requestTargets` reads only the skeleton -/

open Nock.MemoryTable Nock.NockVMROM.Thm54.PreSeedCensus in
theorem requestTargets_zero (S : NockVMROM.Thm54.SemanticStrategy.SemanticSkeleton)
    (st : MState) : requestTargets S st 0 = .atom 0 := by
  cases st <;> rfl

open Nock.MemoryTable Nock.NockVMROM.Thm54.PreSeedCensus in
theorem requestTargets_halt (S : NockVMROM.Thm54.SemanticStrategy.SemanticSkeleton) (k : ℕ) :
    requestTargets S .halt k = .atom 0 := by
  cases k <;> rfl

#print axioms Nock.RedTeam.Batch752.reqPairEvent_eq_lift_ofEnvs
#print axioms Nock.NockVMROM.Thm54.PreSeedCensus.reqPairEventOfEnvs_card_le

end Nock.RedTeam.Batch752
