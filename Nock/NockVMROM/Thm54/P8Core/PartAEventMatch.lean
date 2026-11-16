/-
  Nock/NockVMROM/Thm54/P8Core/PartAEventMatch.lean

  Below the statement.

  `event_match`: outside the twelve-coin event `consumedFailureEvent309 P Qc Qm` (fifteen
  summands), the landed tuple `forget12 c` lies outside the LANDED consumed event
  `optimizedFailureEventEv` at the transported traces `(reHost P t Qc, reWalk P Qm c)`.

* Compute, B1 summands (1-topology, 2, 5, 8): every reader is host-insensitive on one-hot rows —
    the decoded table at indices `< 94`, the hosted child tags at the row's own state, the request
    records and activity masks; lifted to Finset
    equalities (`summand5_reHost`, `summand8_reHost`, `famIO_reHost`, `topology_reHost`).

  * Summands 7 and 10 are priced at `αW` in the twelve-coin event and at `α` in the landed one;
    both are EMPTY at the transported memory trace: tiling makes `memoryTilingEvent = ∅`, and
    `ForestVecBFT` at the view makes the forest-α event `∅` at every coin (`IsForestFullBFT` at
    the shared `γ`).
  * Summand 14 is constant; summand 15 supplied the order premise of the re-walk (step 4).

  Scope: `repartitionedChronology` and the parallel package.  -- the paper
-/
import Nock.NockVMROM.Thm54.P8Core.PartAReHost
import Nock.NockVMROM.Thm54.P8Core.PartAReWalkChip

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 300000

namespace Nock.NockVMROM.Thm54.PartAEventMatch

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.ComputeTable
open Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.Unhosted309
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.PartAReHost
open Module

noncomputable section

/-! ## 1. The decided reader facts -/

/-- Every decoded index `< 94` is host-insensitive at every state. -/
theorem decoded_insensitiveP :
    ∀ s : Fin 11, ∀ k : Fin 94,
      Insensitive (curSel s) (diffAt s) (computeTraceSubst .traceCur k) = true := by
  decide +kernel

/-- The hosted child tags at the row's own state are host-insensitive. -/
theorem tags_insensitiveP :
    ∀ s : Fin 11, ∀ j : Fin 3,
      Insensitive (curSel s) (diffAt s)
        (ComputeWalkLabel.childTagHost ComputeWalkLabel.curReader (stOfIdx s) j) = true := by
  decide +kernel

/-- The source of record slot `c` of request slot `j` (`rowRecord`). -/
def recordSrc (j : Fin 3) (c : Fin 10) : Expr :=
  if (c : ℕ) = 9 then (sampledSlotE .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else if (c : ℕ) = 6 then (sampledSlotT .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else if (c : ℕ) = 8 then (sampledSlotC .traceCur (67 + 8 * (j : ℕ))).subst finalSampledNamespace
  else (computeTraceSubst .traceCur (67 + 8 * (j : ℕ) + (c : ℕ))).subst finalSampledNamespace

theorem recordSrc_eval {F K : Type} [Field F] [Field K] [Algebra F K]
    (env : CorrectedFinalTypedEnv F K) (j : Fin 3) (c : Fin 10) :
    OptimizedComputeHostileAccumulator.rowRecord env j c = (recordSrc j c).eval env.toSourceEnv := by
  unfold OptimizedComputeHostileAccumulator.rowRecord recordSrc
  split_ifs <;> rfl

/-- The request records are host-insensitive. -/
theorem records_insensitiveP :
    ∀ s : Fin 11, ∀ j : Fin 3, ∀ c : Fin 10,
      Insensitive (curSel s) (diffAt s) (recordSrc j c) = true := by
  decide +kernel


/-! ## 2. The re-hosted and truncated rows agree off the host roles, at every coin vector -/

section Agree

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X])

/-- Re-hosted cell of the row's own state: equal to the 309 cell off the host roles of that state. -/
theorem cell_cur (i : Fin (nC P)) (c : ℕ) (hc : c < 309) (hR : isResCol c = false)
    (hH : isHostCol c = true → (c - 13) / 3 ∉ hostRolesOf (rowSt P Qc i)) :
    (reHost309 P t Qc ⟨c, hc⟩).eval (P.optimized.computeNodes i) =
      (Qc ⟨c, hc⟩).eval (P.optimized.computeNodes i) := by
  have h := e303_trace P t Qc i c hc hR hH
  simpa [envAt, envOfTrace, dif_pos hc] using h

/-- Re-hosted column off the host and residual blocks: the 309 polynomial. -/
theorem cell_poly (c : ℕ) (hc : c < 309) (hR : isResCol c = false) (hH : isHostCol c = false) :
    reHost309 P t Qc ⟨c, hc⟩ = Qc ⟨c, hc⟩ := by
  simp only [reHost309, hR, Bool.false_eq_true, if_false, preHost309, hH]

/-- A 303-wide family-or-package view of a 309 trace: columns below `303`. -/
def Trunc303 {w : ℕ} (B : Fin w → F[X]) (Q : Fin 309 → F[X]) : Prop :=
  ∀ c (h : c < w), ∃ h' : c < 303, B ⟨c, h⟩ = Q ⟨c, by omega⟩

/-- **Agreement of the deployed source rows** of two 303-wide views `B` (of `Qc`) and `B'` (of
`reHost309`), at every coin vector, off `diffAt` of the row's state. -/
theorem src303_agree {w : ℕ} (hw : w = 303) (B B' : Fin w → F[X]) (hB : Trunc303 B Qc)
    (hB' : Trunc303 B' (reHost309 P t Qc)) (cv pv : ℕ → F) (i : Fin (nC P)) :
    ∀ k j, diffAt (rowIdx P Qc i) k j = false →
      varVal (gatherCorrectedFinalTypedEnv P.optimized.basis
          (envOfTrace B' P.optimized.orbit.ω (P.optimized.computeNodes i) cv pv)).toSourceEnv k j =
        varVal (gatherCorrectedFinalTypedEnv P.optimized.basis
          (envOfTrace B P.optimized.orbit.ω (P.optimized.computeNodes i) cv pv)).toSourceEnv k j := by
  intro k j hd
  cases k
  · simp only [diffAt, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
    apply PartAStaged.landed_src_trace_congr
    intro col hcol
    unfold physOf at hcol
    have hc303 : col < 303 := by omega
    simp only [envOfTrace, dif_pos (show col < w by omega)]
    obtain ⟨_, e1⟩ := hB' col (by omega)
    obtain ⟨_, e2⟩ := hB col (by omega)
    rw [e1, e2]
    apply cell_cur P t Qc i col (by omega)
    · simp only [isResCol, decide_eq_false_iff_not]
      simp only [residualRoles, List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    · intro hh
      simp only [isHostCol, decide_eq_true_eq] at hh
      simp only [rowSt, hostRolesOf, residualRoles, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      omega
  · simp only [diffAt, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
    apply PartAStaged.landed_src_traceNext_congr
    intro col hcol
    unfold physOf at hcol
    have hc303 : col < 303 := by omega
    simp only [envOfTrace, dif_pos (show col < w by omega)]
    obtain ⟨_, e1⟩ := hB' col (by omega)
    obtain ⟨_, e2⟩ := hB col (by omega)
    rw [e1, e2, cell_poly P t Qc col (by omega)
        (by simp only [isResCol, decide_eq_false_iff_not]
            simp only [residualRoles, hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hd
            omega)
        (by simp only [isHostCol, decide_eq_false_iff_not]
            simp only [residualRoles, hostKRoles, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
            omega)]
  · rfl
  · rfl

/-- **One-hot selectors on the deployed source rows** of a 303-wide view. -/
theorem src303_matches (hone : OneHotRows P Qc) {w : ℕ} (hw : w = 303) (Q : Fin 309 → F[X])
    (hQ : ∀ j (hj : j < 11), Q ⟨j, by omega⟩ = Qc ⟨j, by omega⟩)
    (B : Fin w → F[X]) (hB : Trunc303 B Q) (cv pv : ℕ → F) (i : Fin (nC P)) :
    Matches (curSel (rowIdx P Qc i)) (gatherCorrectedFinalTypedEnv P.optimized.basis
      (envOfTrace B P.optimized.orbit.ω (P.optimized.computeNodes i) cv pv)).toSourceEnv := by
  intro k j v hσ
  cases k <;> simp only [curSel, reduceCtorEq] at hσ
  by_cases hj : j < 11
  · simp only [hj, if_true, Option.some.injEq] at hσ
    subst hσ
    have h13 : j < 13 := by omega
    have hs := hone i j hj
    simp only [selAt, dif_pos (show j < 309 by omega)] at hs
    simp only [varVal, CorrectedFinalTypedEnv.toSourceEnv, gatherCorrectedFinalTypedEnv,
      dif_pos h13, envOfTrace, dif_pos (show j < w by omega)]
    obtain ⟨_, e1⟩ := hB j (by omega)
    rw [e1, hQ j hj, hs]
    split_ifs <;> simp
  · simp [hj] at hσ

/-- The truncation is a 303-wide view of `Qc`. -/
theorem trunc_view : Trunc303 (PartAStaged.truncQc P Qc) Qc := by
  intro c h
  have hw := PartAStaged.computeWidth303 P
  exact ⟨by omega, rfl⟩

/-- `reHost` is a 303-wide view of `reHost309`. -/
theorem reHost_view : Trunc303 (reHost P t Qc) (reHost309 P t Qc) := by
  intro c h
  have hw := PartAStaged.computeWidth303 P
  exact ⟨by omega, rfl⟩

/-- The family cast of a 303-wide view is a view. -/
theorem family_view (c' : OptimizedProductionChallengeTuple K F) (A : Fin P.computeChip.rap.w → F[X])
    (Q : Fin 309 → F[X]) (hA : Trunc303 A Q) :
    Trunc303 (FamilyEnvCore.familyQc P.optimized c' A) Q := by
  intro c h
  have hw := FamilyEnvCore.computeChipAt_width P.optimized c'
  have h' : c < P.computeChip.rap.w := lt_of_lt_of_eq h hw
  obtain ⟨h1, h2⟩ := hA c h'
  exact ⟨h1, by simp only [FamilyEnvCore.familyQc]; rw [← h2]; rfl⟩

theorem reHost309_sel (j : ℕ) (hj : j < 11) :
    reHost309 P t Qc ⟨j, by omega⟩ = Qc ⟨j, by omega⟩ :=
  cell_poly P t Qc j (by omega) (by simp [isResCol]; omega) (by simp [isHostCol]; omega)

end Agree


/-! ## 3. The decoders on agreeing one-hot rows -/

section Decoders

variable {K : Type} [Field K]

theorem matches_sel {s : Fin 11} {E : Env K} (hm : Matches (curSel s) E) (j : ℕ) (hj : j < 11) :
    E.trace j = if j = (s : ℕ) then 1 else 0 := by
  have h := hm .traceCur j (if j = (s : ℕ) then 1 else 0) (by simp [curSel, hj])
  simp only [varVal] at h
  rw [h]; split_ifs <;> simp

theorem rowStateOf_of_matches {s : Fin 11} {E : Env K} (hm : Matches (curSel s) E) :
    ComputeWalkRootEvents.rowStateOf E = stOfIdx s := by
  have h := fun j hj => matches_sel hm j hj
  unfold ComputeWalkRootEvents.rowStateOf
  fin_cases s <;>
    simp [h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
      h 6 (by omega), h 7 (by omega), h 8 (by omega), h 9 (by omega), h 10 (by omega), stOfIdx]

variable {s : Fin 11} {E E' : Env K} (hm : Matches (curSel s) E) (hm' : Matches (curSel s) E')
  (hag : ∀ k j, diffAt s k j = false → varVal E k j = varVal E' k j)

include hm hm' hag in
theorem insens_eq (e : Expr) (hins : Insensitive (curSel s) (diffAt s) e = true) :
    e.eval E = e.eval E' :=
  eval_eq_of_insensitive _ _ e hins hm hm' hag

include hm hm' hag in
theorem decoded_eq (k : ℕ) (hk : k < 94) :
    (Env.ofSubst computeSubst E).trace k = (Env.ofSubst computeSubst E').trace k := by
  simp only [Env.ofSubst, computeSubst]
  exact insens_eq hm hm' hag _ (decoded_insensitiveP s ⟨k, hk⟩)

include hm hm' hag in
/-- **The decoded label, child payloads and fanout agree** on two one-hot rows agreeing off the
host roles of the row's state. -/
theorem decoders_eq :
    ComputeWalkRootEvents.rowLabelVec E = ComputeWalkRootEvents.rowLabelVec E' ∧
      (∀ l, ComputeWalkRootEvents.rowChildVec E l = ComputeWalkRootEvents.rowChildVec E' l) ∧
      ComputeWalkRootEvents.rowFanout E = ComputeWalkRootEvents.rowFanout E' := by
  have hst : ComputeWalkRootEvents.rowStateOf E = ComputeWalkRootEvents.rowStateOf E' := by
    rw [rowStateOf_of_matches hm, rowStateOf_of_matches hm']
  have hpub : ∀ b, 11 ≤ b → b + 2 < 47 →
      Nock.Reified.fpOf (Env.ofSubst computeSubst E) b =
        Nock.Reified.fpOf (Env.ofSubst computeSubst E') b := by
    intro b h1 h2
    simp only [Nock.Reified.fpOf]
    rw [decoded_eq hm hm' hag b (by omega), decoded_eq hm hm' hag (b + 1) (by omega),
      decoded_eq hm hm' hag (b + 2) (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · funext k
    fin_cases k <;>
      simp only [ComputeWalkRootEvents.rowLabelVec, ComputeWalkRootEvents.rowPub,
        Nock.Reified.pubOfState, Nock.ComputeTable.labelVecOfPub, hst,
        hpub 11 (by omega) (by omega), hpub 14 (by omega) (by omega),
        hpub 17 (by omega) (by omega)]
  · have htags : ComputeWalkRootEvents.rowTags E = ComputeWalkRootEvents.rowTags E' := by
      funext j
      simp only [ComputeWalkRootEvents.rowTags, hst]
      rw [rowStateOf_of_matches hm']
      exact insens_eq hm hm' hag _ (tags_insensitiveP s j)
    have hsf : ∀ j, Nock.ComputeTable.sfTriple (ComputeWalkRootEvents.rowPub E) j =
        Nock.ComputeTable.sfTriple (ComputeWalkRootEvents.rowPub E') j := by
      intro j
      fin_cases j <;>
        simp only [Nock.ComputeTable.sfTriple, ComputeWalkRootEvents.rowPub, Nock.Reified.pubOfState,
          hpub 20 (by omega) (by omega), hpub 23 (by omega) (by omega),
          hpub 26 (by omega) (by omega), hpub 29 (by omega) (by omega),
          hpub 32 (by omega) (by omega), hpub 35 (by omega) (by omega),
          hpub 38 (by omega) (by omega), hpub 41 (by omega) (by omega),
          hpub 44 (by omega) (by omega)]
    intro l
    unfold ComputeWalkRootEvents.rowChildVec
    match l with
    | 0 => funext k; fin_cases k <;> simp only [ComputeWalkLabel.childVecN, ComputeWalkLabel.childVec, htags, hsf 0]
    | 1 => funext k; fin_cases k <;> simp only [ComputeWalkLabel.childVecN, ComputeWalkLabel.childVec, htags, hsf 1]
    | 2 => funext k; fin_cases k <;> simp only [ComputeWalkLabel.childVecN, ComputeWalkLabel.childVec, htags, hsf 2]
    | n + 3 => rfl
  · simp only [ComputeWalkRootEvents.rowFanout, hst]

end Decoders


/-! ## 4. The compute summands at the re-hosted trace -/

section Compute

open Nock.NockVMROM.Thm54.PartAStaged
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesEv

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X])
  (hone : OneHotRows P Qc)

/-- The round-0 compute columns are neither host nor residual columns (decided). -/
theorem round0_plain : ∀ j : Fin 309, RepartitionedStaging.newComputeColRound j = 0 →
    isHostCol j = false ∧ isResCol j = false := by decide

/-- **`reHost` agrees with the 309 trace on every round-0 column.** -/
theorem agreeC0 : AgreeC309 0 (reHost309 P t Qc) Qc := by
  intro j hj
  have h := round0_plain j (by omega)
  exact cell_poly P t Qc j j.isLt h.2 h.1

/-- `reHost` is the truncation of `reHost309`. -/
theorem reHost_eq_trunc : reHost P t Qc = truncQc P (reHost309 P t Qc) := rfl

theorem w303 : P.computeChip.rap.w = 303 := computeWidth303 P

include hone in
/-- The deployed source rows of the re-hosted and the truncated traces, at any coin vector,
through any 303-wide views: matched and agreeing off the host roles. -/
theorem rows_agree {w : ℕ} (hw : w = 303) (B B' : Fin w → F[X]) (hB : Trunc303 B Qc)
    (hB' : Trunc303 B' (reHost309 P t Qc)) (cv pv : ℕ → F) (i : Fin (nC P)) :
    let E' := (gatherCorrectedFinalTypedEnv P.optimized.basis
      (envOfTrace B' P.optimized.orbit.ω (P.optimized.computeNodes i) cv pv)).toSourceEnv
    let E := (gatherCorrectedFinalTypedEnv P.optimized.basis
      (envOfTrace B P.optimized.orbit.ω (P.optimized.computeNodes i) cv pv)).toSourceEnv
    Matches (curSel (rowIdx P Qc i)) E' ∧ Matches (curSel (rowIdx P Qc i)) E ∧
      ∀ k j, diffAt (rowIdx P Qc i) k j = false → varVal E' k j = varVal E k j :=
  ⟨src303_matches P Qc hone hw _ (fun j hj => reHost309_sel P t Qc j hj) B' hB' cv pv i,
    src303_matches P Qc hone hw Qc (fun _ _ => rfl) B hB cv pv i,
    src303_agree P t Qc hw B B' hB hB' cv pv i⟩

include hone in
/-- The package source rows (`P.computeSourceEnv`). -/
theorem cenv_agree (i : Fin (nC P)) :
    Matches (curSel (rowIdx P Qc i)) (P.computeSourceEnv (reHost P t Qc) i) ∧
      Matches (curSel (rowIdx P Qc i)) (P.computeSourceEnv (truncQc P Qc) i) ∧
      ∀ k j, diffAt (rowIdx P Qc i) k j = false →
        varVal (P.computeSourceEnv (reHost P t Qc) i) k j =
          varVal (P.computeSourceEnv (truncQc P Qc) i) k j :=
  rows_agree P t Qc hone (w303 P) (truncQc P Qc) (reHost P t Qc) (trunc_view P Qc)
    (reHost_view P t Qc) P.optimized.computeChallenge P.optimized.computePublic i

include hone in
theorem cenv_decoders (i : Fin (nC P)) :
    ComputeWalkRootEvents.rowLabelVec (P.computeSourceEnv (reHost P t Qc) i) =
        ComputeWalkRootEvents.rowLabelVec (P.computeSourceEnv (truncQc P Qc) i) ∧
      (∀ l, ComputeWalkRootEvents.rowChildVec (P.computeSourceEnv (reHost P t Qc) i) l =
        ComputeWalkRootEvents.rowChildVec (P.computeSourceEnv (truncQc P Qc) i) l) ∧
      ComputeWalkRootEvents.rowFanout (P.computeSourceEnv (reHost P t Qc) i) =
        ComputeWalkRootEvents.rowFanout (P.computeSourceEnv (truncQc P Qc) i) := by
  obtain ⟨h1, h2, h3⟩ := cenv_agree P t Qc hone i
  exact decoders_eq h1 h2 h3

include hone in
/-- **Summand 5 at the re-hosted trace.** -/
theorem summand5_reHost :
    P.computeWalkRootEvent (reHost P t Qc) = P.computeWalkRootEvent (truncQc P Qc) := by
  unfold OptimizedFullStrictNockVMROMPackage.computeWalkRootEvent
  exact Unhosted309.rootEvent_congr _ (cenv_decoders P t Qc hone) (cenv_decoders P t Qc hone _).1

include hone in
/-- **Summand 8 at the re-hosted trace.** -/
theorem summand8_reHost :
    P.computePrefixGammaEventOf (reHost P t Qc) = P.computePrefixGammaEventOf (truncQc P Qc) := by
  unfold OptimizedFullStrictNockVMROMPackage.computePrefixGammaEventOf
  exact Unhosted309.prefixGamma_congr (cenv_decoders P t Qc hone)

include hone in
/-- The family compute rows at any tuple. -/
theorem fam_agree (c' : OptimizedProductionChallengeTuple K F) (i : Fin (nC P)) :
    let e' := FamilyEnvCore.rowEnvAt P.optimized c'
      (FamilyEnvCore.familyQc P.optimized c' (reHost P t Qc)) i
    let e := FamilyEnvCore.rowEnvAt P.optimized c'
      (FamilyEnvCore.familyQc P.optimized c' (truncQc P Qc)) i
    Matches (curSel (rowIdx P Qc i)) e'.toSourceEnv ∧ Matches (curSel (rowIdx P Qc i)) e.toSourceEnv ∧
      (∀ k j, diffAt (rowIdx P Qc i) k j = false → varVal e'.toSourceEnv k j = varVal e.toSourceEnv k j) ∧
      e'.baseTrace = e.baseTrace := by
  have hW : (P.computeChipAt c').rap.w = 303 :=
    (FamilyEnvCore.computeChipAt_width P.optimized c').trans (w303 P)
  obtain ⟨h1, h2, h3⟩ := rows_agree P t Qc hone hW
    (FamilyEnvCore.familyQc P.optimized c' (truncQc P Qc))
    (FamilyEnvCore.familyQc P.optimized c' (reHost P t Qc))
    (family_view P c' _ Qc (trunc_view P Qc)) (family_view P c' _ _ (reHost_view P t Qc))
    (computeChalValOfTuple P.optimized.basis c') (P.familyComputePublic c') i
  refine ⟨h1, h2, h3, ?_⟩
  funext j
  have hj := h3 .traceCur j (by simp [diffAt]; omega)
  simp only [varVal, CorrectedFinalTypedEnv.toSourceEnv, dif_pos j.isLt] at hj
  exact (algebraMap F K).injective hj

end Compute


/-! ## 5. Summands 1 (topology) and 2 (records) at the re-hosted trace -/

section Records

open Nock.NockVMROM.Thm54.PartAStaged
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ReconTreeSize
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.Walk Nock.MemoryTable

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (t : OptimizedProductionChallengeTuple K F) (Qc : Fin 309 → F[X])
  (hone : OneHotRows P Qc)

include hone in
/-- The compute request list at any tuple. -/
theorem requests_reHost (c' : OptimizedProductionChallengeTuple K F) :
    FamilyEnvCore.hostileRequestsAt P.optimized c'
        (FamilyEnvCore.familyQc P.optimized c' (reHost P t Qc)) =
      FamilyEnvCore.hostileRequestsAt P.optimized c'
        (FamilyEnvCore.familyQc P.optimized c' (truncQc P Qc)) := by
  unfold FamilyEnvCore.hostileRequestsAt
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  obtain ⟨h1, h2, h3, hbase⟩ := fam_agree P t Qc hone c' i
  have hmask := fun j => FamilyEnvCore.activeMask_congr hbase j
  have hrec : ∀ j, OptimizedComputeHostileAccumulator.rowRecord (FamilyEnvCore.rowEnvAt P.optimized c'
      (FamilyEnvCore.familyQc P.optimized c' (reHost P t Qc)) i) j =
      OptimizedComputeHostileAccumulator.rowRecord (FamilyEnvCore.rowEnvAt P.optimized c'
        (FamilyEnvCore.familyQc P.optimized c' (truncQc P Qc)) i) j := by
    intro j; funext cc
    rw [recordSrc_eval, recordSrc_eval]
    exact insens_eq h1 h2 h3 _ (records_insensitiveP _ j cc)
  unfold OptimizedComputeHostileAccumulator.rowRequests
  simp only [hmask, hrec]

include hone in
/-- **Summand 2 at the transported traces.** -/
theorem famIO_reHost {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (hM : AgreeM P 1 Qm Qm') :
    P.famIOEventOf (reHost P t Qc) Qm' = P.famIOEventOf (truncQc P Qc) Qm := by
  simp only [OptimizedFullStrictNockVMROMPackage.famIOEventOf,
    OptimizedFullStrictNockVMROMPackage.hostileRecordsAt,
    OptimizedFullStrictNockVMROMPackage.familyQm, OptimizedFullStrictNockVMROMPackage.familyQc]
  refine Finset.ext fun c' => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold FamilyEnvCore.hostileRecordsAt
  rw [requests_reHost P t Qc hone c', hostileResponsesAt_B01 P hM c']

include hone in
/-- The decoded compute table at the coin-free tuple, cut to what the labels read. -/
theorem dTrunc_reHost (i : Fin (nC P)) :
    dTrunc (decodeSource (FamilyEnvCore.rowEnvAt P.optimized coinFree
        (FamilyEnvCore.familyQc P.optimized coinFree (reHost P t Qc)) i)) =
      dTrunc (decodeSource (FamilyEnvCore.rowEnvAt P.optimized coinFree
        (FamilyEnvCore.familyQc P.optimized coinFree (truncQc P Qc)) i)) := by
  obtain ⟨h1, h2, h3, _⟩ := fam_agree P t Qc hone coinFree i
  unfold dTrunc decodeSource
  congr 1
  · funext k
    split_ifs with hk
    · exact decoded_eq h1 h2 h3 k (by omega)
    · rfl

include hone in
theorem lblC_reHost :
    lblC P.optimized (reHost P t Qc) coinFree = lblC P.optimized (truncQc P Qc) coinFree := by
  funext j
  have hAt : ∀ i, lblCAt P.optimized (reHost P t Qc) coinFree i =
      lblCAt P.optimized (truncQc P Qc) coinFree i := by
    intro i
    have hd := dTrunc_reHost P t Qc hone i
    unfold lblCAt decodeInputs decodePub decodeDec
    simp only
    rw [computeStateOf_dTrunc, inpOf_dTrunc, pubOfState_dTrunc, decOf_dTrunc,
      computeStateOf_dTrunc (decodeSource _), inpOf_dTrunc (decodeSource _),
      pubOfState_dTrunc (decodeSource _), decOf_dTrunc (decodeSource _), hd]
  unfold lblC
  split_ifs <;> exact hAt _

include hone in
theorem foC_reHost :
    foC P.optimized (reHost P t Qc) coinFree = foC P.optimized (truncQc P Qc) coinFree := by
  funext i; unfold foC; rw [lblC_reHost P t Qc hone]

/-- B0 agreement of the transported pair with the original (`reHost` touches only round-1/2
columns, `reWalk` only round-2 ones). -/
theorem agreeB0_reHost {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (hM : AgreeM P 0 Qm' Qm) :
    PartAB0.AgreeB0 P.optimized (reHost P t Qc) (truncQc P Qc) Qm' Qm :=
  agreeB0_of_trace P (agreeC0 P t Qc) hM

include hone in
/-- **The event template's compute tree at the transported pair.** -/
theorem execTemplateEv_computeTree_reHost {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hM : AgreeM P 0 Qm' Qm) (z : K) :
    (execTemplateEv P.optimized (reHost P t Qc) Qm' z).computeTree =
      (execTemplateEv P.optimized (truncQc P Qc) Qm z).computeTree := by
  have hB0 := agreeB0_reHost P t Qc hM
  by_cases ht : TracesWalkHyps P.optimized (reHost P t Qc) Qm' coinFree
  · have ht' := (PartAB0.tracesWalkHyps_congr hB0).1 ht
    rw [execTemplateEv_eq P.optimized _ _ ht z, execTemplateEv_eq P.optimized _ _ ht' z]
    show mapNTree StrategyOfTracesLift.wrapComputeLabel
        (reconTree (foC P.optimized (reHost P t Qc) coinFree) (lblC P.optimized (reHost P t Qc) coinFree)
          P.optimized.family.problem.cfg.compRows) =
      mapNTree StrategyOfTracesLift.wrapComputeLabel
        (reconTree (foC P.optimized (truncQc P Qc) coinFree) (lblC P.optimized (truncQc P Qc) coinFree)
          P.optimized.family.problem.cfg.compRows)
    rw [lblC_reHost P t Qc hone, foC_reHost P t Qc hone]
  · have ht' : ¬ TracesWalkHyps P.optimized (truncQc P Qc) Qm coinFree :=
      fun h => ht ((PartAB0.tracesWalkHyps_congr hB0).2 h)
    unfold execTemplateEv
    rw [dif_neg ht, dif_neg ht']
    rfl

/-- **The event template's projected memory forest at the transported pair.** -/
theorem execTemplateEv_memoryForest_reWalk {Qm Qm' : Fin P.memoryChip.rap.w → F[X]}
    (hM : AgreeM P 1 Qm' Qm) (d : MState × DTmem K) (z α lmb : K) :
    ((execTemplateEv P.optimized (reHost P t Qc) Qm' z).specialize α lmb).memoryForest.map
        (mapNTree (projM d)) =
      ((execTemplateEv P.optimized (truncQc P Qc) Qm z).specialize α lmb).memoryForest.map
        (mapNTree (projM d)) := by
  have hB0 := agreeB0_reHost P t Qc (agree_mono_M P hM)
  by_cases ht : TracesWalkHyps P.optimized (reHost P t Qc) Qm' coinFree
  · have ht' := (PartAB0.tracesWalkHyps_congr hB0).1 ht
    rw [execTemplateEv_eq P.optimized _ _ ht z, execTemplateEv_eq P.optimized _ _ ht' z]
    show ((reconForest P.optimized.family.problem.cfg.kMem (foM P.optimized Qm' coinFree)
          (lblMR0 P.optimized (reHost P t Qc) Qm' coinFree) P.optimized.family.problem.cfg.memRows).map
          (mapNTree (fun row => row.specialize α lmb))).map (mapNTree (projM d)) =
      ((reconForest P.optimized.family.problem.cfg.kMem (foM P.optimized Qm coinFree)
          (lblMR0 P.optimized (truncQc P Qc) Qm coinFree) P.optimized.family.problem.cfg.memRows).map
          (mapNTree (fun row => row.specialize α lmb))).map (mapNTree (projM d))
    rw [mapNTree_reconForest, mapNTree_reconForest, mapNTree_reconForest, mapNTree_reconForest,
      PartAB0.foM_congr hB0]
    congr 1
    funext j
    rw [projM_specialize_lblMR0, projM_specialize_lblMR0, lblM_proj_B01 P hM]
  · have ht' : ¬ TracesWalkHyps P.optimized (truncQc P Qc) Qm coinFree :=
      fun h => ht ((PartAB0.tracesWalkHyps_congr hB0).2 h)
    unfold execTemplateEv
    rw [dif_neg ht, dif_neg ht']
    rfl

include hone in
/-- **The P8 topology sub-event at the transported pair.** -/
theorem topology_reHost {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (hM : AgreeM P 1 Qm' Qm)
    (lmb : K) :
    specializedTopologyFailureEvent
        (OptimizedFailureEventEv.builtStrategyEv P (reHost P t Qc) Qm').verifier.raw lmb =
      specializedTopologyFailureEvent
        (OptimizedFailureEventEv.builtStrategyEv P (truncQc P Qc) Qm).verifier.raw lmb := by
  ext ω
  simp only [mem_specializedTopologyFailureEvent_iff]
  have key : ∀ hz : nprSeed ω ≠ 0,
      topologyBadGammas ((OptimizedFailureEventEv.builtStrategyEv P (reHost P t Qc) Qm').verifier.raw.afterAlphaM
        (nprSeed ω) hz (alphaM ω) lmb).familyData.base =
      topologyBadGammas ((OptimizedFailureEventEv.builtStrategyEv P (truncQc P Qc) Qm).verifier.raw.afterAlphaM
        (nprSeed ω) hz (alphaM ω) lmb).familyData.base := by
    intro hz
    obtain d := lblM P.optimized Qm coinFree 1
    apply topologyBadGammas_congr_proj _ _ d
    · exact congrArg (mapNTree fun row => row.specialize (alphaM ω))
        (execTemplateEv_computeTree_reHost P t Qc hone (agree_mono_M P hM) (nprSeed ω))
    · exact execTemplateEv_memoryForest_reWalk P t Qc hM d (nprSeed ω) (alphaM ω) lmb
  constructor
  · rintro ⟨hz, h⟩; exact ⟨hz, (key hz) ▸ h⟩
  · rintro ⟨hz, h⟩; exact ⟨hz, (key hz).symm ▸ h⟩

include hone in
/-- **Summand 1 at the transported pair.** -/
theorem p8Slot_reHost {Qm Qm' : Fin P.memoryChip.rap.w → F[X]} (hM : AgreeM P 1 Qm' Qm) :
    OptimizedFailureEventEv.p8SlotEv P (reHost P t Qc) Qm' =
      OptimizedFailureEventEv.p8SlotEv P (truncQc P Qc) Qm := by
  ext c'
  simp only [OptimizedFailureEventEv.mem_p8SlotEv_iff, PartAB0.evFailureUnion_split, Finset.mem_union]
  rw [PartAB0.p8Slot_m1Part_B0 P (agreeB0_reHost P t Qc (agree_mono_M P hM)),
    topology_reHost P t Qc hone hM]

end Records

end

noncomputable section

/-! ## 6. The memory summands at the re-walked trace; emptiness of summands 7 and 10 -/

section Memory

open Nock.NockVMROM.Thm54.PartAStaged
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.PartAReWalk
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.RedTeam.Batch489
open Nock.RedTeam.Batch490
open Nock.RedTeam.Batch501
open Nock.Walk

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (Qc : Fin 309 → F[X]) (Qm : Fin P.memoryChip.rap.w → F[X])
  (c : OptimizedProductionChallengeTuple12 K F)

/-- **The re-walk agrees with the committed memory trace on every column of round `≤ 1`.** -/
theorem agreeM_reWalk : AgreeM P 1 (reWalk P Qm c) Qm := by
  intro j hj
  apply reWalk_off
  by_contra h
  have hb : walkPhysB j = true := by simpa using h
  have hlt : (j : ℕ) < 182 := by
    simp only [walkPhysB, Bool.or_eq_true, decide_eq_true_eq] at hb; omega
  have h2 := reWalk_round2 j (List.mem_filter.2 ⟨List.mem_range.2 hlt, hb⟩)
  omega

theorem agreeM_reWalk' : AgreeM P 1 Qm (reWalk P Qm c) :=
  fun j hj => (agreeM_reWalk P Qm c j hj).symm

theorem summand4_reWalk :
    interFailurePairs (P.hostileInterRecords (reWalk P Qm c)) (P.memorySourceEnv (reWalk P Qm c))
        (P.memoryBaseEnv (reWalk P Qm c)) =
      interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) :=
  bad4_B01 P (agreeM_reWalk P Qm c)

theorem summand7_reWalk : P.memoryTilingEventOf (reWalk P Qm c) = P.memoryTilingEventOf Qm :=
  summand7_B0 P (agree_mono_M P (agreeM_reWalk P Qm c))

theorem summand9_reWalk :
    P.memoryPrefixGammaEventOf (reWalk P Qm c) = P.memoryPrefixGammaEventOf Qm := by
  obtain ⟨h1, h2, h3⟩ := menvs_B01 P (agreeM_reWalk P Qm c)
  simp only [OptimizedFullStrictNockVMROMPackage.memoryPrefixGammaEventOf,
    memoryPrefixGammaEventOfEnvs]
  rw [h1, h2, h3]

theorem summand10_reWalk :
    P.memoryForestAlphaEventOf (reWalk P Qm c) = P.memoryForestAlphaEventOf Qm := by
  obtain ⟨h1, h2, h3⟩ := menvs_B01 P (agreeM_reWalk P Qm c)
  simp only [OptimizedFullStrictNockVMROMPackage.memoryForestAlphaEventOf,
    memoryForestAlphaEventOfEnvs]
  rw [h1, h2, h3]

variable {P Qc Qm c}
variable (hacc : AcceptanceAt309 P Qc Qm c) (hgood : c ∉ consumedFailureEvent309 P Qc Qm)

include hacc hgood in
/-- The committed memory fanouts tile (summand 7 at the view, `deployed_tiling_memory`). -/
theorem tiling_committed :
    kMemP P + Sf (foOfMem (P.memoryBaseEnv Qm)) (memRowsP P) = memRowsP P := by
  have hchar : FamilyMemoryRows.MemStateTagChar F := Nock.RedTeam.Batch824.memStateTagChar_of_package P
  obtain ⟨htile, _, _, _⟩ := forest_at_view P Qc Qm c hacc hgood hchar
  rw [Sf_foOfMem_eq_foWmem P (walkView11 c) Qm]
  exact htile

include hacc hgood in
/-- **Summand 7 is empty** at the committed (hence at the re-walked) memory trace, at every coin. -/
theorem summand7_empty : P.memoryTilingEventOf Qm = ∅ := by
  unfold OptimizedFullStrictNockVMROMPackage.memoryTilingEventOf
  exact memoryTilingEvent_empty_of_tiling _ _ (tiling_committed hacc hgood)

include hacc hgood in
/-- **Summand 10 is empty** at every coin sharing `γ` with `c`: the forest-α event is the
walk-prefix α-event of the committed operands at `γ`, which `ForestVecBFT` at the view makes
`IsForestFullBFT`, hence `∅` whatever the walk coin. -/
theorem summand10_empty (ω : JointCoins K) (hγ : gamma ω = gamma c.1) :
    ω ∉ P.memoryForestAlphaEventOf Qm := by
  have hchar : FamilyMemoryRows.MemStateTagChar F := Nock.RedTeam.Batch824.memStateTagChar_of_package P
  have htile' := tiling_committed hacc hgood
  have hbft := view_isForestFullBFT P Qc Qm c hacc hgood hchar
  set t := walkView11 c with ht
  have heq : walkForestPrefixAlphaEvent
      (curOfMem (committedMemoryV (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm)) (gamma t.1))
      (chldOfMem (committedMemoryCv (P.memorySourceEnv Qm)) (gamma t.1))
      (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm)) (kMemP P) (memRowsP P) =
      walkForestPrefixAlphaEvent
        (curW P t (familyQm P t Qm)) (chldW P t (familyQm P t Qm))
        (foW P t (familyQm P t Qm)) (kMemP P) (memRowsP P) := by
    refine WalkForestPrefixAlphaEvents.walkForestPrefixAlphaEvent_congr_on
      (kMem_le_memRows P) ?_ ?_ ?_
    · intro i h1 h2
      simp only [curOfMem]
      have hV := VdM_eq_committed P t Qm i h1 h2
      have hcur : curW P t (familyQm P t Qm) i = rlc (gamma t.1) (VdM P t Qm i) := rfl
      rw [hV, hcur]
    · intro i l h1 h2
      simp only [chldOfMem]
      have hC := CvdM_eq_committed P t Qm i l h1 h2
      have hch : chldW P t (familyQm P t Qm) i l = rlc (gamma t.1) (CvdM P t Qm i l) := rfl
      rw [hC, hch]
    · intro i h1 h2
      exact foOfMem_eq_foWmem P t Qm i h1 h2
  have hempty : walkForestPrefixAlphaEvent
      (curOfMem (committedMemoryV (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm)) (gamma t.1))
      (chldOfMem (committedMemoryCv (P.memorySourceEnv Qm)) (gamma t.1))
      (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm)) (kMemP P) (memRowsP P) = ∅ := by
    rw [heq]; unfold walkForestPrefixAlphaEvent; rw [if_pos hbft]
  intro hmem
  have h := (mem_memoryForestAlphaEventOfEnvs_of_tiling
      (P.memorySourceEnv Qm) (P.memoryBaseEnv Qm) (kMemP P) htile' ω).1
    (by simpa [OptimizedFullStrictNockVMROMPackage.memoryForestAlphaEventOf] using hmem)
  have hγt : gamma ω = gamma t.1 := hγ
  rw [hγt, hempty] at h
  exact Finset.notMem_empty _ h

end Memory

/-! ## 7. The event match -/

section Match

open Nock.NockVMROM.Thm54.PartAStaged
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.PartAReWalk

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} {P : OptimizedFullStrictNockVMROMPackage F K hOrb}
  {Qc : Fin 309 → F[X]} {Qm : Fin P.memoryChip.rap.w → F[X]}
  {c : OptimizedProductionChallengeTuple12 K F}

/-- **The event match (raw traces).** Outside the twelve-coin event, the landed tuple `forget12 c`
lies outside the landed consumed event at the transported traces. -/
theorem event_match_raw (hacc : AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ consumedFailureEvent309 P Qc Qm) :
    forget12 c ∉ OptimizedFailureEventEv.optimizedFailureEventEv P
      (reHost P (forget12 c) Qc) (reWalk P Qm c) := by
  have hone : OneHotRows P Qc := (rowHyps_of_sat P (forget12 c) Qc hacc.compute_satisfies).1.hone
  have hn := Pkg12.notMem_consumedFailureEvent12 P (truncQc P Qc) Qm c hgood
  obtain ⟨h1, h2, h3, h4, h5, h6, _h7, h8, h9, _h10, h11, h12, h13, h14, _h15⟩ := hn
  have hM := agreeM_reWalk P Qm c
  have hM0 := agree_mono_M P hM
  have hC0 := agreeC0 P (forget12 c) Qc
  have hcoin : (forget12 c).1 = c.1 := rfl
  simp only [OptimizedFailureEventEv.optimizedFailureEventEv, Finset.mem_union, not_or]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [p8Slot_reHost P (forget12 c) Qc hone hM]; exact h1
  · rw [famIO_reHost P (forget12 c) Qc hone (agreeM_reWalk' P Qm c)]; exact h2
  · rw [reHost_eq_trunc, hostileRequests_length_B0 P hC0]; exact h3
  · rw [summand4_reWalk]; exact h4
  · rw [forget12_mem_liftP8, summand5_reHost P (forget12 c) Qc hone]; exact h5
  · rw [forget12_mem_liftP8, reHost_eq_trunc, summand6_B0 P hC0]; exact h6
  · rw [forget12_mem_liftP8, summand7_reWalk, summand7_empty hacc hgood]
    exact Finset.notMem_empty _
  · rw [forget12_mem_liftP8, summand8_reHost P (forget12 c) Qc hone]; exact h8
  · rw [forget12_mem_liftP8, summand9_reWalk]; exact h9
  · rw [forget12_mem_liftP8, summand10_reWalk]
    exact summand10_empty hacc hgood c.1 rfl
  · rw [reHost_eq_trunc, summand11_B0' P hC0 hM0]; exact h11
  · rw [forget12_mem_liftP8, reHost_eq_trunc, summand12_B0' P hC0 hM0]; exact h12
  · rw [forget12_mem_liftP8, reHost_eq_trunc, summand13_B0' P hC0 hM0]; exact h13
  · rw [forget12_mem_liftP8]; exact h14


theorem event_match (hacc : AcceptanceAt309 P Qc Qm c)
    (hgood : c ∉ consumedFailureEvent309 P Qc Qm) :
    forget12 c ∉ OptimizedFailureEventEv.optimizedFailureEventEv P
      (FamilyEnvCore.honestQc P.optimized (forget12 c)
        (FamilyEnvCore.familyQc P.optimized (forget12 c) (reHost P (forget12 c) Qc)))
      (FamilyEnvCore.honestQm P.optimized (forget12 c)
        (FamilyEnvCore.familyQm P.optimized (forget12 c) (reWalk P Qm c))) := by
  rw [FamilyEnvCore.honestQc_familyQc, FamilyEnvCore.honestQm_familyQm]
  exact event_match_raw hacc hgood

end Match

end

end Nock.NockVMROM.Thm54.PartAEventMatch
