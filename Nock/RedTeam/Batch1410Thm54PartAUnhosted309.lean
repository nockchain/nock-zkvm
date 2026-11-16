import Nock.NockVMROM.Thm54.Unhosted309Events
import Nock.RedTeam.Batch1409Thm54PartAStaging

/-
  Nock/RedTeam/Batch1410Thm54PartAUnhosted309.lean

  **Receipts
  for the un-hosted compute chip at width 309 (`Thm54/Unhosted309*.lean`).

  * §1 **class invariance on the REAL edited sources**: L1's coarse class (`Batch1409.coarse`) of
    every one of the 94 typed compute sources at the deployed schedule equals its class at the
    repartitioned schedule, now computed on the actual 309 source list (`sources309`, with the
    seven retargeted sources as compiled, not as the design's column model) —
    `real_compute_no_class_change`; positive control: the same check with the walk columns
    mis-rounded to block 1 fires (`real_class_control`).
  * §2 **no B1 column needs an M2 coin** (honest side): the 309 encoding of every `B0 ∪ B1` cell
    is independent of the walk `count` / `acc` (`encode309_walkFree`), which live only in the
    `B2` columns `303..308` (`walk_columns_round2`); control: the deployed encoding hosts
    `count` in a `B1`-at-309 cell (`deployed_encoding_hosts_count`).
  * §3 the measured degrees, new ≤ deployed (`retargeted_degrees_le`).
  * §4 resources: `s = 418`, `w = 309 = 108 + 168 + 33` tied to L1's `newComputeBlocks`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace Nock.RedTeam.Batch1410

open Nock Nock.Reified Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.RepartitionedStaging
open Module

/-! ## 1. Class invariance on the real 309 sources -/

/-- Physical columns of a 309 typed source (the compile's read set; walk leaves read
`303 + 3j + k`). -/
def colsW : WTyped → List ℕ
  | .leaf t => typedColsC t
  | .wCur j => [303 + 3 * j.val, 304 + 3 * j.val, 305 + 3 * j.val]
  | .wNext j => [303 + 3 * j.val, 304 + 3 * j.val, 305 + 3 * j.val]
  | .add x y | .sub x y | .mul x y => colsW x ++ colsW y
  | .neg x => colsW x
  | .pow x n => if n = 0 then [] else colsW x

def slotsW : WTyped → List ℕ
  | .leaf t => typedSlots t
  | .wCur _ | .wNext _ => []
  | .add x y | .sub x y | .mul x y => slotsW x ++ slotsW y
  | .neg x => slotsW x
  | .pow x n => if n = 0 then [] else slotsW x

/-- **The 94 typed sources of the un-hosted chip, as compiled** (the deployed order of
`Batch1409.computeSources`). -/
def sources309 : List (String × WTyped) :=
  ((List.finRange 82).map fun i => (s!"core{i.val}",
      if i = packedQueueNonEmptyId then queueNonEmpty309
      else if i = packedQueueTilingId then queueTiling309
      else .leaf (correctedCoreSource i)))
  ++ ((List.finRange 3).map fun j => (s!"aux{j.val}",
      if h : j = 2 then .leaf (correctedAuxSource j)
      else .sub (.leaf (.extCur ⟨58 + j.val, by omega⟩)) (residualSource309 (aux309Idx j h))))
  ++ (endpoint2_309.zipIdx.map fun (t, k) => (s!"ep2_{k}", t))
  ++ (endpoint4_309.map fun t => ("ep4", t))
  ++ (formRLamPins.map fun t => ("lamPin", .leaf t))

theorem sources309_count : sources309.length = 94 := by decide

/-- The class of a 309 source at the repartitioned schedule. -/
def newCW (w : WTyped) : ℕ :=
  Batch1409.coarse newComputeColRound newComputeSlotRound (colsW w) (slotsW w)

/-- Every source's coarse
class at the deployed schedule (`Batch1409.oldC`, the deployed source) equals the class of its
real 309 counterpart at the repartitioned schedule. -/
theorem real_compute_no_class_change :
    ((Batch1409.computeSources.zip sources309).filterMap fun (a, b) =>
      if Batch1409.oldC a.2.2 ≠ newCW b.2 then some a.1 else none) = [] := by
  decide +kernel

/-- The names line up position by position. -/
theorem sources309_names :
    sources309.map Prod.fst = Batch1409.computeSources.map Prod.fst := by decide

/-- The seven retargeted sources, as compiled, read the walk columns and no longer read the
walk hosts *as walk values*: their column sets are contained in L1's retarget model. -/
theorem real_within_model :
    ((Batch1409.computeSources.zip sources309).filterMap fun (a, b) =>
      if (colsW b.2).all (fun c => c ∈ Batch1409.retarget a.2.1 (typedColsC a.2.2)) then none
      else some a.1) = [] := by
  decide +kernel

/-- Positive control: rounding the walk columns into block 1 (as if `count` / `acc` were committed
before the second message) changes the class of a walk source. -/
def badRound (c : ℕ) : ℕ := if 303 ≤ c then 1 else newComputeColRound c
theorem real_class_control :
    ((Batch1409.computeSources.zip sources309).filterMap fun (a, b) =>
      if Batch1409.oldC a.2.2 ≠
          Batch1409.coarse badRound newComputeSlotRound (colsW b.2) (slotsW b.2)
      then some a.1 else none) ≠ [] := by
  decide +kernel

/-! ## 2. No `B1` column needs an `M2` coin (the honest 309 encoding) -/

theorem walk_columns_round2 : ∀ c, 303 ≤ c → c < 309 → newComputeColRound c = 2 := by
  intro c h1 h2; unfold newComputeColRound; split_ifs <;> omega

section Encode
variable {F K : Type} [Field F] [Field K]
open OptimizedComputeOverlay OptimizedComputeCodec

/-- **The 309 encoding of every table cell is independent of the walk `count` / `acc`**: those
values (functions of the M2 coins `αC`, `γ`) reach only the `B2` walk columns. -/
theorem encode309_walkFree (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K)
    (ex : ComputeTable.Extra K) (v : SampledOverlayValues K) (wc wa : K) :
    sampledEncodeExtension309 pub dec ex v =
      sampledEncodeExtension309 pub dec ex
        { v with toOverlayValues := { v.toOverlayValues with walkCount := wc, walkAcc := wa } } := by
  funext i
  rcases i with ⟨r, c⟩ | i
  · simp only [sampledEncodeExtension309]
    split_ifs with h
    · rfl
    · simp only [sampledEncodeExtension]
      split_ifs with h1 h2 h3 h4 h5
      · subst h1
        have hc : c = 2 := by
          by_contra hc; exact h ⟨rfl, hc⟩
        subst hc
        simp [sampledOverlayA, fpCoordinate]
      all_goals rfl
  · rfl

theorem encode309_walk (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K)
    (ex : ComputeTable.Extra K) (v : SampledOverlayValues K) :
    (sampledEncode309 (F := F) pub dec ex v).walk = ![v.walkCount, v.walkAcc] := rfl

/-- Control: the deployed encoding hosts `count` in role-A coordinate `0`, a cell that is `B1` at
the repartitioned schedule. -/
theorem deployed_encoding_hosts_count (pub : ComputeTable.Pub K) (dec : ComputeTable.Dec K)
    (ex : ComputeTable.Extra K) (v : SampledOverlayValues K) :
    sampledEncodeExtension pub dec ex v (.inl (overlayRoleA pub.state, 0)) = v.walkCount := by
  simp [sampledEncodeExtension, sampledOverlayA, fpCoordinate]

theorem host_cells_round1 :
    ∀ r ∈ [6, 7, 9, 10, 18, 19, 27, 28], ∀ k < 3, newComputeColRound (13 + 3 * r + k) = 1 := by
  decide

end Encode

/-! ## 3. Degrees: new ≤ deployed -/

theorem retargeted_degrees_le :
    (residualSource309 0).degree ≤ (correctedFinalResidualSource 0).degree ∧
      (residualSource309 1).degree ≤ (correctedFinalResidualSource 1).degree ∧
      (lowerW finalMaskedWalkCount1_309).degree ≤
        (lowerLeaf OptimizedComputeFinalTypedLowering.finalMaskedWalkCount1).degree ∧
      (lowerW finalMaskedWalkOut309).degree ≤
        (lowerLeaf OptimizedComputeFinalTypedLowering.finalMaskedWalkOut).degree ∧
      (lowerW finalMaskedWalkAccInit309).degree ≤
        (lowerLeaf OptimizedComputeFinalTypedLowering.finalMaskedWalkAccInit).degree ∧
      queueNonEmpty309.degree ≤ (correctedFinalExtGate packedQueueNonEmptyId).degree ∧
      queueTiling309.degree ≤ (correctedFinalExtGate packedQueueTilingId).degree := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := retargeted_degrees
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := deployed_degrees
  rw [n1, n2, n3, n4, n5, n6, n7, o1, o2, o3, o4, o5, o6, o7]
  decide

/-! ## 4. Resources tied to L1's blocks -/

theorem width309_is_blocks :
    ((List.finRange 3).map fun r =>
      (Finset.univ.filter fun c : Fin 309 => newComputeRoundFin c = r).card).sum = 309 := by
  rw [newComputeBlocks]; rfl

theorem chip309_width_blocks {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) :
    (ProductionNamedComputeRAP309 hn nodes b chalVal pubVal orbit).rap.w =
      ((List.finRange 3).map fun r =>
        (Finset.univ.filter fun c : Fin 309 => newComputeRoundFin c = r).card).sum ∧
    (ProductionNamedComputeRAP309 hn nodes b chalVal pubVal orbit).rap.s = 418 := by
  refine ⟨?_, allGates309_length n b⟩
  rw [width309_is_blocks]; rfl

/-! ## 5. Each name is resolved below. -/

/-- New gate-body and codec names whose bodies carry the un-hosting. -/
def watchlistCensus : List Lean.Name :=
  [ -- the width-309 chip and gate list
    ``Unhosted309.ProductionNamedComputeRAP309, ``Unhosted309.CorrectedFinalComputeRAP309,
    ``Unhosted309.allGates309, ``Unhosted309.correctedCore309, ``Unhosted309.correctedAux309,
    ``Unhosted309.correctedCoreCoord309, ``Unhosted309.correctedAuxCoord309,
    ``Unhosted309.computeChipAt309,
    -- the typed language and its compiler/lowering
    ``Unhosted309.WTyped, ``Unhosted309.WTyped.eval, ``Unhosted309.compile309,
    ``Unhosted309.compileList309, ``Unhosted309.lower309, ``Unhosted309.lowerW,
    ``Unhosted309.lowerLeaf, ``Unhosted309.walkLimb, ``Unhosted309.walkCountCol,
    ``Unhosted309.walkAccCol,
    -- the seven retargeted gate bodies
    ``Unhosted309.finalWalkSubstInGate309, ``Unhosted309.finalWalkInitialSubst309,
    ``Unhosted309.finalWalkTerminalSubst309, ``Unhosted309.walkCountStep309,
    ``Unhosted309.walkAccStep309, ``Unhosted309.walkQueueNonEmpty309,
    ``Unhosted309.walkQueueTiling309, ``Unhosted309.finalMaskedWalkCount1_309,
    ``Unhosted309.finalMaskedWalkOut309, ``Unhosted309.finalMaskedWalkAccInit309,
    ``Unhosted309.residualSource309, ``Unhosted309.queueNonEmpty309,
    ``Unhosted309.queueTiling309, ``Unhosted309.endpoint2_309, ``Unhosted309.endpoint4_309,
    ``Unhosted309.aux309Idx,
    ``Unhosted309.gather309, ``Unhosted309.Env309.toSourceEnv, ``Unhosted309.Env309,
    ``Unhosted309.coreSemValue309, ``Unhosted309.auxSemValue309,
    ``Unhosted309.sampledEncodeExtension309, ``Unhosted309.sampledRestoreExtension309,
    ``Unhosted309.sampledEncode309, ``Unhosted309.decodeSampledOverlay309,
    ``Unhosted309.sampledDecode309, ``Unhosted309.Row309,
    -- the summand 5/8 events at 309
    ``Unhosted309.computeSourceEnv309, ``Unhosted309.computeBaseEnv309,
    ``Unhosted309.computeWalkRootEvent309, ``Unhosted309.computePrefixGammaEventOf309 ]

def watchlistCarried : List Lean.Name :=
  [ ``OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv.toSourceEnv,
    ``OptimizedComputeSemanticRealization.gatherCorrectedFinalTypedEnv,
    ``OptimizedComputeSubstitution.computeTraceSubst,
    ``OptimizedComputeOverlay.sampledEncodeExtension,
    ``OptimizedComputeOverlay.sampledRestoreExtension ]

theorem watchlistCensus_count : watchlistCensus.length = 49 ∧ watchlistCarried.length = 5 := by
  decide

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for n in watchlistCensus ++ watchlistCarried do
    unless env.contains n do
      throwError m!"watchlist census: unknown constant {n}"

end Nock.RedTeam.Batch1410

#print axioms Nock.RedTeam.Batch1410.real_compute_no_class_change
#print axioms Nock.RedTeam.Batch1410.real_within_model
#print axioms Nock.RedTeam.Batch1410.real_class_control
#print axioms Nock.RedTeam.Batch1410.encode309_walkFree
#print axioms Nock.RedTeam.Batch1410.deployed_encoding_hosts_count
#print axioms Nock.RedTeam.Batch1410.retargeted_degrees_le
#print axioms Nock.RedTeam.Batch1410.chip309_width_blocks
#print axioms Nock.NockVMROM.Thm54.Unhosted309.canonical_satisfies309
#print axioms Nock.NockVMROM.Thm54.Unhosted309.optimizedComputeRealization309
#print axioms Nock.NockVMROM.Thm54.Unhosted309.satisfies309_iff_sourceLanguage
#print axioms Nock.NockVMROM.Thm54.Unhosted309.conditional_transition_soundness309
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictPackage.OptimizedStrictNockVMROMPackage.exact_chip_resources309
#print axioms Nock.NockVMROM.Thm54.Unhosted309.computeWalkRootEvent309_congr
#print axioms Nock.NockVMROM.Thm54.Unhosted309.computePrefixGammaEventOf309_congr
#print axioms Nock.NockVMROM.Thm54.Unhosted309.summand5_readsOn
#print axioms Nock.NockVMROM.Thm54.Unhosted309.summand8_readsOn
#print axioms Nock.NockVMROM.Thm54.Unhosted309.sampledDecode309_encode309_of_vcomp
#print axioms Nock.NockVMROM.Thm54.Unhosted309.untouched_core_insensitive
#print axioms Nock.NockVMROM.Thm54.Unhosted309.retargeted_core_sensitive
