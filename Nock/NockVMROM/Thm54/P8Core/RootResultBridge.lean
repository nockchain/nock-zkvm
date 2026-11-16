/-
  Nock/NockVMROM/Thm54/P8Core/RootResultBridge.lean

  Imports only P8Core modules and below-pin production
  (`RootCheck.lean.txt` rule; this module must not import
  `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`).

  * `rootResult_bridge`: from `Batch1173`'s premise list (which already contains
    `c ∉ optimizedFailureEventEv`), the C2 join's root evaluation at the traces IS the package
    claim's result.
    - `henc`: the join root binds the S-tree root (`Batch1090.computeTreeBinds_of_chipReady` at the
      `C2ChipReady` half of `chipReady_aligned_of_traces`; its root row's evaluation slot), and
      `Batch1111.root_binds`.2.2 binds `claim.result` to the same `root.e`;
    - the root-result component of `optimizedFailureEventEv` (`rootResultEv`, the 1-pair
      `pairBadSeeds` event) and `PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds` give the
      `(leafF, dyckBits)` equality.  `OptimizedFailureEventEv.rootResult_of_not_mem` is the same
      two lines but lives ABOVE the pin (its module imports the statement file), so its body is
      inlined here, not imported;
    - leaf bounds: the built root evaluation from the honest-call window
      (`genuine_rows_le_programLeafBound` at the root of the genuine join, `hΛG`) -- NOT
      `census_window_combined`.2, whose `skeletonSizeWindowNouns` lists only OP3/4/6 subformula
      results, not the root evaluation; the claim result from the package census
      `P.optimized.census.p8` (pair `(root.evaluation, claim.result)` of `skeletonPairs`) -- NOT
      `sizeWindowBound`, for the same reason;
    - atoms below `ringChar K`: the built root evaluation is the guarded run's result `r`
      (`Batch1091.c2_aligned_eval`), bounded by `Batch1091.evalGBy_bounded`; the claim result by
      `P.skeletonBounded` at the root row and `P.q_eq_ringChar`;
    - `PreSeedCensus.noun_eq_of_fieldNoun_eq` gives the noun equality.
  * `holds_of_traces`: the same premise list, NO `hbridge`, concludes the guarded evaluation and the
    Nock evaluation of the package's own program at the claimed result.
  * `holds_exists`: the `∃ fuel` form.
  * `holds_of_acceptance`: the semantic `p8` with `h`, `bs`, `bf` dropped.
  * `wrong_claim_rejected`: the false-claim control with no trace-side premise -- a guarded run
    `r ≠ claim.result` puts EVERY accepted `(c, Qc, Qm)` in `optimizedFailureEvent ∪ optimizedFailureEventEv`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1173Thm54C2CombinedServedRecords
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

namespace Nock.NockVMROM.Thm54.RootResultBridge

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.P8EventEv
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.ComputedWindow
open Nock.NockVMROM.Thm54.TraceGen
open Nock.RedTeam.Batch1024
open Nock.RedTeam.Batch1173
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

set_option quotPrecheck false
local notation "JT" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
  (treeS P c Qc).size (treeS P c Qc)
  P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula

/-- The package claim's result: every atom below `ringChar K` (`skeletonBounded` at the root row,
`claim_eq`, `q_eq_ringChar`). -/
theorem claimResult_bounded :
    BoundedBy (ringChar K) P.optimized.verifier.raw.claim.result := by
  have hS := P.skeletonBounded.computeRows
  have hmem : P.optimized.commitment.skeleton.computeTree.label ∈
      SemanticStrategy.computeSkeletonRows P.optimized.commitment.skeleton :=
    List.mem_map.mpr ⟨_, (Walk.mem_bfsForest _ _).mpr
      ⟨_, List.mem_singleton_self _, Walk.InTree.here _⟩, rfl⟩
  have hb := List.forall_iff_forall_mem.mp hS _ hmem
  rw [← P.optimized.claim_eq, ← P.q_eq_ringChar]
  exact hb.2.2.1

/-- The package claim's result is inside the package window `Λ` (the census pair
`(root.evaluation, claim.result)` of `skeletonPairs`). -/
theorem claimResult_leaves_le :
    P.optimized.verifier.raw.claim.result.leaves ≤ P.optimized.Λ := by
  have h := P.optimized.census.p8.leaves_bounded
    (P.optimized.commitment.skeleton.computeTree.label.evaluation,
      P.optimized.commitment.skeleton.publicClaim.result)
    (by simp [BoundSemanticTrace.skeletonPairs])
  rw [← P.optimized.claim_eq]
  exact h.2

/-- **THE ROOT-RESULT BRIDGE.**  `Batch1173`'s premise list (with `c ∉ optimizedFailureEventEv`)
gives: the C2 join's root evaluation at the family traces is the package claim's result. -/
theorem rootResult_bridge
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (bs : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject)
    (bf : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    (JT).label.evaluation = P.optimized.verifier.raw.claim.result := by
  have h11 := OptimizedHostileConfiguration.eleven_lt_ringChar_of_package P
  have hq1 : 1 < ringChar K := by omega
  have hz := FamilyIOChain.nprSeed_ne_of_good_at P c Qc Qm hgood
  have hready := chipReady_aligned_of_traces P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen
    hG bs bf hΛG hF
  have hroot := Nock.RedTeam.Batch1111.root_binds P c Qc Qm hacc hgood hax hbasis hwidth
  -- (0) the built root evaluation is the guarded run's result
  have hev : (JT).label.evaluation = r :=
    Nock.RedTeam.Batch1091.c2_aligned_eval (sv := svF P c Qm) (ax := axF P c Qc) (ringChar K)
      hready.2 fuel _ r hG le_rfl
  -- (1) `henc`: the join root binds the S-tree root; `root_binds` binds the claim result there
  have hb := Nock.RedTeam.Batch1090.computeTreeBinds_of_chipReady (sv := svF P c Qm)
    (ax := axF P c Qc) hz (le_refl (treeS P c Qc).size) hready.1 hroot.1
  have hrow := hb.root
  rw [mapNTree_label] at hrow
  have he1 : bindFP (nprSeed c.1) (JT).label.evaluation (treeS P c Qc).label.1.2.2.1.e :=
    hrow.2.2.2.2.2.1
  have henc : GlobalCarryRecognizer.enc (nprSeed c.1) (JT).label.evaluation =
      GlobalCarryRecognizer.enc (nprSeed c.1) P.optimized.verifier.raw.claim.result := by
    have e2 := hroot.2.2
    unfold bindFP at he1 e2
    rw [← he1, ← e2]
  -- (2) leaf bounds, at the window `Λg = memRows ⊔ Λ`
  have hgen' := Nock.RedTeam.Batch1091.c2_aligned_genuine (sv := svF P c Qm) (ax := axF P c Qc)
    (ringChar K) hready.2 fuel (treeS P c Qc).size r hG le_rfl
  obtain ⟨-, -, hrows⟩ := genuine_rows_le_programLeafBound hgen hgen'
    (Nock.RedTeam.Batch1021.J_subject _ _ _ _) (Nock.RedTeam.Batch1021.J_formula _ _ _ _)
  have hΛ1 : (JT).label.evaluation.leaves ≤ Λg P :=
    ((hrows _ (Walk.InTree.here _)).2.2.trans hΛG).trans le_sup_right
  have hΛ2 : P.optimized.verifier.raw.claim.result.leaves ≤ Λg P :=
    (claimResult_leaves_le P).trans le_sup_right
  -- (3) outside the root-result event: field-noun equality
  have hout : c.1 ∉ rootResultEv P (honestQc P c Qc) (honestQm P c Qm) :=
    (optimizedFailureEventEv_good_components P _ _ c hgoodEv).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpub : (builtSkeletonEv P (honestQc P c Qc) (honestQm P c Qm)).publicClaim.result =
      (JT).label.evaluation := by
    show (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)).computeTree.label.evaluation = _
    rw [Nock.RedTeam.Batch1173.skeletonEv_computeTree_eq P c Qc Qm]
  have hzs : nprSeed c.1 ∉ PreSeedCensus.pairBadSeeds (K := K) (Λg P)
      [((builtSkeletonEv P (honestQc P c Qc) (honestQm P c Qm)).publicClaim.result,
        P.optimized.verifier.raw.claim.result)] := by
    intro hmem
    exact hout (by rw [rootResultEv, mem_liftSeed_iff]; exact hmem)
  rw [hpub] at hzs
  have hfn := PreSeedCensus.fieldNoun_eq_of_not_mem_pairBadSeeds hzs (by simp) hΛ1 hΛ2 henc
  -- (4) atoms below the characteristic: noun equality
  have hbr : BoundedBy (ringChar K) (JT).label.evaluation := by
    rw [hev]; exact Nock.RedTeam.Batch1091.evalGBy_bounded hq1 bs bf hG
  exact PreSeedCensus.noun_eq_of_fieldNoun_eq (bounded_leafList hbr)
    (bounded_leafList (claimResult_bounded P)) hfn

/-- **THE SEMANTIC `p8`** at the family traces: `Batch1173`'s premise list and nothing else; the
package claim's result is the guarded evaluation of its own program, and (through
`evalGBy_le_evalN`) its Nock evaluation.  No `hbridge`, no `TC.Accepts`, no `GenuineTargetAt`. -/
theorem holds_of_traces
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (bs : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject)
    (bf : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result ∧
      Nock.evalN fuel P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula =
        some P.optimized.verifier.raw.claim.result := by
  have hal := (chipReady_aligned_of_traces P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG
    bs bf hΛG hF).2
  have he : (JT).label.evaluation = r :=
    Nock.RedTeam.Batch1091.c2_aligned_eval (sv := svF P c Qm) (ax := axF P c Qc) (ringChar K) hal
      fuel _ r hG le_rfl
  have hr : r = P.optimized.verifier.raw.claim.result :=
    he.symm.trans (rootResult_bridge P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf
      hΛG hF)
  subst hr
  refine ⟨hG, ?_⟩
  have h11 := OptimizedHostileConfiguration.eleven_lt_ringChar_of_package P
  exact evalGBy_le_evalN (by omega) bs bf hG

/-- **`holds_of_traces`, `∃ fuel` form** (the paper's `Holds` via `evalGBy_le_evalN`). -/
theorem holds_exists
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (bs : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject)
    (bf : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    (∃ fuel', evalGBy (ringChar K) fuel' P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result) ∧
      ∃ fuel', Nock.evalN fuel' P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result := by
  have H := holds_of_traces P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth h hgen hG bs bf hΛG hF
  exact ⟨⟨fuel, H.1⟩, ⟨fuel, H.2⟩⟩

theorem wrong_claim_inside_events
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hW : ∀ _hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm),
      StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (hwrong : r ≠ P.optimized.verifier.raw.claim.result)
    (bs : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject)
    (bf : BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    c ∈ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm) ∪
      optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm) := by
  by_contra hc
  simp only [Finset.mem_union, not_or] at hc
  obtain ⟨hgood, hgoodEv⟩ := hc
  have H := holds_of_traces P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth (hW hgood) hgen hG bs bf
    hΛG hF
  rw [hG] at H
  exact hwrong (Option.some.inj H.1)

/-! ## Fewer premises: `h`, `bs`, `bf` derived -/

/-- The package claim's subject and formula are bounded (`skeletonBounded` at the root row). -/
theorem claimInputs_bounded :
    BoundedBy (ringChar K) P.optimized.verifier.raw.claim.subject ∧
      BoundedBy (ringChar K) P.optimized.verifier.raw.claim.formula := by
  have hS := P.skeletonBounded.computeRows
  have hmem : P.optimized.commitment.skeleton.computeTree.label ∈
      SemanticStrategy.computeSkeletonRows P.optimized.commitment.skeleton :=
    List.mem_map.mpr ⟨_, (Walk.mem_bfsForest _ _).mpr
      ⟨_, List.mem_singleton_self _, Walk.InTree.here _⟩, rfl⟩
  have hb := List.forall_iff_forall_mem.mp hS _ hmem
  rw [← P.optimized.claim_eq, ← P.q_eq_ringChar]
  exact ⟨hb.1, hb.2.1⟩

/-- The walk hypotheses at the family traces from acceptance and `c ∉ optimizedFailureEvent`
(`Batch489.tracesWalkHyps_of_deployed`, read as the lifted structure field by field). -/
theorem tracesWalkHyps_of_acc
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm)) :
    StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c := by
  have hacc' : DeployedAcceptanceAt P c (familyQc P c (honestQc P c Qc))
      (familyQm P c (honestQm P c Qm)) := by
    rw [Nock.RedTeam.Batch824.familyQc_honestQc, Nock.RedTeam.Batch824.familyQm_honestQm]
    exact hacc
  have h0 := Nock.RedTeam.Batch489.tracesWalkHyps_of_deployed P c (honestQc P c Qc)
    (honestQm P c Qm) hacc'.compute_satisfies hacc'.memory_satisfies
    (Nock.RedTeam.Batch824.memStateTagChar_of_package P) hax hbasis hwidth hacc' hgood
  exact ⟨h0.sfCompute, h0.validCompute, h0.sfMemory, h0.validMemory⟩

/-- **The semantic `p8` from acceptance**: premises = acceptance at the family chips, the two
events, `of_package`'s Form R hypotheses, the compiler's generator run and window, the program's
guarded termination, and `hF`.  `h`, `bs`, `bf` are derived. -/
theorem holds_of_acceptance
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
        P.optimized.verifier.raw.claim.formula = some P.optimized.verifier.raw.claim.result ∧
      Nock.evalN fuel P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula =
        some P.optimized.verifier.raw.claim.result :=
  holds_of_traces P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth
    (tracesWalkHyps_of_acc P c Qc Qm hacc hax hbasis hwidth hgood) hgen hG
    (claimInputs_bounded P).1 (claimInputs_bounded P).2 hΛG hF

/-- No trace-side premise. -/
theorem wrong_claim_rejected
    (hacc : DeployedAcceptanceAt P c Qc Qm)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    {gfuel : ℕ} {G : NTree (GenComputeRow K)} {R : Noun}
    (hgen : genComputeSkeleton (K := K) gfuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = .ok (G, R))
    {fuel : ℕ} {r : Noun}
    (hG : evalGBy (ringChar K) fuel P.optimized.verifier.raw.claim.subject
      P.optimized.verifier.raw.claim.formula = some r)
    (hwrong : r ≠ P.optimized.verifier.raw.claim.result)
    (hΛG : programLeafBound (airReorder G) ≤ P.optimized.Λ)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    c ∈ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm) ∪
      optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm) := by
  by_contra hc
  simp only [Finset.mem_union, not_or] at hc
  obtain ⟨hgood, hgoodEv⟩ := hc
  have H := holds_of_acceptance P c Qc Qm hacc hgood hgoodEv hax hbasis hwidth hgen hG hΛG hF
  rw [hG] at H
  exact hwrong (Option.some.inj H.1)

end Nock.NockVMROM.Thm54.RootResultBridge
