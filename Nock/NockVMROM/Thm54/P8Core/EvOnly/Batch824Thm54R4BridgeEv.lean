/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch824Thm54R4BridgeEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch824Thm54R4Bridge
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch465Thm54DeployedRootLabelEqClaimEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch489Thm54FoOfEqFoWEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch490Thm54TopologyAssemblyEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch500Thm54GammaTransportEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch501Thm54MemoryTopologyEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch822Thm54R4BridgeMemoryEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.FamilyIOChainRouteBEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch824

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.FormRBridge
open Nock.RedTeam.Batch575

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

section Rows

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
include hacc

end Rows

section IO

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
  (hio : FamilyIOGood P c Qc Qm)
  (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K)
include hacc hgood hio hrb

theorem memRows_lt_ev : FamilyIOChain.memRows P < ringChar K := by
  change P.optimized.family.problem.cfg.memRows < ringChar K
  rw [P.optimized.family_cfg]; exact hrb.2

/-- **A read row's record is a located active request** whose exponent is the row's
`natLift reqIdx`, with the record's `(T, C')` slots equal to the memory row's. -/
theorem read_row_request_ev (h1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
    (k : Fin (FamilyIOChain.memRows P)) (hsel : (memEnvF P c Qm k).trace 2 = 1) :
    ∃ (a : Fin (rows P)) (j : Fin 3), activeMask (rowEnvAt P c Qc a) j = 1 ∧
      RecordCarrier.natLift ((memEnvF P c Qm k).trace reqIdxCol) = expOfAt P c Qc a j ∧
      (memEnvK P c Qm k).trace 25 = rowRecord (rowEnvAt P c Qc a) j 6 ∧
      (memEnvK P c Qm k).trace 57 = rowRecord (rowEnvAt P c Qc a) j 8 := by
  have hver := ver_of_read P c Qc Qm hacc h1 k hsel
  have hchar := OptimizedHostileConfiguration.hchar_of_package P
  obtain ⟨a, j, hact, heq⟩ := row_record_is_request_at_ev P c Qc Qm hacc hgood hio hchar
    (hKp_of_rowsBound_at P hrb) (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm)
    k hver
  have h9 := congrFun heq 9
  rw [compute_slot9_eq_expOf_at P c Qc hacc.compute_satisfies hchar a j] at h9
  have h9' : (memEnvF P c Qm k).trace reqIdxCol = ((expOfAt P c Qc a j : ℕ) : F) := by
    apply (algebraMap F K).injective
    simpa [OptimizedMemoryHostileAccumulator.rowRecord, reqIdxCol] using h9
  have hlt := expOfAt_lt_ringChar P c Qc hacc.compute_satisfies hchar
    (hKp_of_rowsBound_at P hrb) (hKreq_of_rowsBound_at P c Qc) hact
  refine ⟨a, j, hact, ?_, ?_, ?_⟩
  · rw [h9']; exact RecordCarrier.natLift_natCast hlt
  · have h6 := congrFun heq 6
    simpa [OptimizedMemoryHostileAccumulator.rowRecord] using h6
  · have h8 := congrFun heq 8
    simpa [OptimizedMemoryHostileAccumulator.rowRecord] using h8

/-- Read rows: `ts = αM ^ natLift reqIdx` and the window `≤ 3·compRows + 3`. -/
theorem read_ts_window_ev (h1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
    (k : Fin (FamilyIOChain.memRows P)) (hsel : (memEnvF P c Qm k).trace 2 = 1) :
    (memEnvK P c Qm k).trace 26 =
        alphaM c.1 ^ RecordCarrier.natLift ((memEnvF P c Qm k).trace reqIdxCol) ∧
      RecordCarrier.natLift ((memEnvF P c Qm k).trace reqIdxCol) ≤
        3 * P.optimized.family.problem.cfg.compRows + 3 := by
  have hver := ver_of_read P c Qc Qm hacc h1 k hsel
  have hw := window_of_rowsBound_at_ev P c Qc Qm hacc hgood hio hrb k hver
  exact ⟨hw.2, hw.1⟩

/-- Read or verify rows: the same, verify rows through the `intermediate` pairing
(`verify_row_inherits_at_ev`). -/
theorem ts_window_ev (h1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
    (k : Fin (FamilyIOChain.memRows P))
    (hsel : (memEnvF P c Qm k).trace 2 = 1 ∨ (memEnvF P c Qm k).trace 3 = 1) :
    (memEnvK P c Qm k).trace 26 =
        alphaM c.1 ^ RecordCarrier.natLift ((memEnvF P c Qm k).trace reqIdxCol) ∧
      RecordCarrier.natLift ((memEnvF P c Qm k).trace reqIdxCol) ≤
        3 * P.optimized.family.problem.cfg.compRows + 3 := by
  rcases hsel with hr | hv
  · exact read_ts_window_ev P c Qc Qm hacc hgood hio hrb h1 k hr
  · obtain ⟨k', hr', hidx, hts⟩ := verify_row_inherits_at_ev P c Qc Qm hacc hgood
      (memRows_lt_ev P c Qc Qm hacc hgood hio hrb) k hv
    obtain ⟨h1', h2'⟩ := read_ts_window_ev P c Qc Qm hacc hgood hio hrb h1 k' hr'
    rw [← hts, h1', hidx]
    exact ⟨rfl, by rw [← hidx]; exact h2'⟩

end IO

section Assembly

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
  (hio : FamilyIOGood P c Qc Qm)
  (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K)
  (hb : Batch823.CertBitsBoolean P c Qc)
  (h1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)
include hacc hgood hio hrb hb h1

/-- **The telescope hypotheses at the family chips.** -/
theorem telescopeRows_at_ev :
    TelescopeRows (envsFR P c Qm) P.optimized.family.problem.cfg.kMem
      (Batch822.pubR P c (honestQm P c Qm)) (Batch822.inpR P c (honestQm P c Qm))
      (alphaM c.1) c.2.2.2.lambda (FormRAxisEvent.formRN K)
      (decodedShift (envsCR P c Qc)) (decodedBits (envsCR P c Qc)) := by
  have hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c)
      (familyQm P c (honestQm P c Qm)) := by
    rw [familyQm_honestQm]; exact hacc.memory_satisfies
  have hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c)
      (familyQc P c (honestQc P c Qc)) := by
    rw [familyQc_honestQc]; exact hacc.compute_satisfies
  have hz := nprSeed_ne_of_good_at_ev P c Qc Qm hgood
  have hchar := OptimizedHostileConfiguration.hchar_of_package P
  -- the read / verify row facts, in the telescope's 1-indexed form
  have hpub : ∀ i (h : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows),
      Batch822.pubR P c (honestQm P c Qm) i = decodeMemPub P (honestQm P c Qm) c ⟨i - 1, by omega⟩ := by
    intro i h
    simp only [Batch822.pubR, Batch490.lblM_of_pos P c (honestQm P c Qm) i h.1 h.2, lblMAt]
  have hexpAt : ∀ i (h : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows),
      FormRBridge.expAt (envsFR P c Qm) i h =
        RecordCarrier.natLift ((memEnvF P c Qm (rowIx P i h)).trace reqIdxCol) := by
    intro i h
    simp only [FormRBridge.expAt, rowExp, reqIdxCol]
    rw [memEnvF_eq P c Qm i h]
  refine Batch822.telescopeRows_of_memory_ev P c (honestQm P c Qm) (honestQc P c Qc) hsatC hsatM
    (memStateTagChar_of_package P) hz hgood (FormRAxisEvent.formRN K) _ _
    FormRAxisEvent.formRN_sub_one.symm ?_ ?_ ?_
  · -- timestamps
    intro i h hst
    have hsel : (memEnvF P c Qm (rowIx P i h)).trace 2 = 1 ∨
        (memEnvF P c Qm (rowIx P i h)).trace 3 = 1 := by
      unfold FormRBridge.stAt at hst
      rcases hst with hr | hv
      · exact Or.inl (read_sel_of_state P c Qc Qm hacc (rowIx P i h) hr)
      · exact Or.inr (verify_sel_of_state P c Qc Qm hacc (rowIx P i h) hv)
    rw [hpub i h, hexpAt i h]
    exact (ts_window_ev P c Qc Qm hacc hgood hio hrb h1 (rowIx P i h) hsel).1
  · -- `T`
    intro i h hst
    unfold FormRBridge.stAt at hst
    obtain ⟨a, j, hact, hnat, h25, -⟩ := read_row_request_ev P c Qc Qm hacc hgood hio hrb h1
      (rowIx P i h) (read_sel_of_state P c Qc Qm hacc (rowIx P i h) hst)
    rw [hpub i h, hexpAt i h, hnat,
      (Batch823.decoded_eq_slotCert P c Qc hacc.compute_satisfies hchar a j hact).1]
    rw [← (Batch823.slot_values P c Qc hacc.compute_satisfies hb hchar a j hact).1, ← h25]
    rfl
  · -- `C'`
    intro i h hst
    unfold FormRBridge.stAt at hst
    obtain ⟨a, j, hact, hnat, -, h57⟩ := read_row_request_ev P c Qc Qm hacc hgood hio hrb h1
      (rowIx P i h) (read_sel_of_state P c Qc Qm hacc (rowIx P i h) hst)
    rw [hpub i h, hexpAt i h, hnat,
      (Batch823.decoded_eq_slotCert P c Qc hacc.compute_satisfies hchar a j hact).2]
    rw [← (Batch823.slot_values P c Qc hacc.compute_satisfies hb hchar a j hact).2, ← h57,
      decodeMemPub_cprime]
    rfl

/-- The decoded exponents are inside the envelope window `3N + 3`. -/
theorem expLe_at_ev :
    ∀ r, ExpLe (decodedEnvelopeDeg P.optimized.family.problem.cfg.compRows)
      (decodedMTreeOfEnvs (envsKR P c Qm) (envsFR P c Qm) P.optimized.family.problem.cfg.kMem r) := by
  refine expLe_tree (envsKR P c Qm) ?_
  intro i h hst
  have hsel : (memEnvF P c Qm (rowIx P i h)).trace 2 = 1 ∨
      (memEnvF P c Qm (rowIx P i h)).trace 3 = 1 := by
    unfold FormRBridge.stAt at hst
    rcases hst with hr | hv
    · exact Or.inl (read_sel_of_state P c Qc Qm hacc (rowIx P i h) hr)
    · exact Or.inr (verify_sel_of_state P c Qc Qm hacc (rowIx P i h) hv)
  have hw := (ts_window_ev P c Qc Qm hacc hgood hio hrb h1 (rowIx P i h) hsel).2
  simp only [FormRBridge.expAt, rowExp, decodedEnvelopeDeg]
  rw [memEnvF_eq P c Qm i h]
  exact hw

/-- **R4 — THE BRIDGE.**  (1) the accumulator gates telescope to the decoded trees' Form R
polynomials at `(αM, λ)` on every memory row; (2) every decoded root's Form R polynomial is `0`. -/
theorem r4_bridge_at_ev :
    (∀ i (h : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows),
      biv (alphaM c.1) c.2.2.2.lambda
          (formRPw (FormRAxisEvent.formRN K) (decodedShift (envsCR P c Qc))
            (decodedMTreeOfEnvs (envsKR P c Qm) (envsFR P c Qm)
              P.optimized.family.problem.cfg.kMem i)) =
        (Batch822.pubR P c (honestQm P c Qm) i).pt.indicator ∧
      biv (alphaM c.1) c.2.2.2.lambda
          (formRCounts (FormRAxisEvent.formRN K) (decodedShift (envsCR P c Qc))
            (decodedBits (envsCR P c Qc))
            (decodedMTreeOfEnvs (envsKR P c Qm) (envsFR P c Qm)
              P.optimized.family.problem.cfg.kMem i)) =
        (Batch822.pubR P c (honestQm P c Qm) i).pt.counts) ∧
    (∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem,
      decodedRootPoly (envsCR P c Qc) (envsKR P c Qm) (envsFR P c Qm)
        P.optimized.family.problem.cfg.kMem r = 0) := by
  have H := telescopeRows_at_ev P c Qc Qm hacc hgood hio hrb hb h1
  have htel := telescope (envsKR P c Qm) H
  refine ⟨htel, ?_⟩
  have hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c)
      (familyQm P c (honestQm P c Qm)) := by
    rw [familyQm_honestQm]; exact hacc.memory_satisfies
  have hout : c ∉ P.decodedLambdaEventOf (honestQc P c Qc) (honestQm P c Qm) :=
    (Nock.NockVMROM.Thm54.PlacementA.good_components_of_Ev P _ _ c hgood).2.2.2.2.2.2.2.2.2.2.1
  refine roots_zero_of_not_event (envsCR P c Qc) (envsKR P c Qm) (envsFR P c Qm)
    P.optimized.family.problem.cfg.kMem c hout (expLe_at_ev P c Qc Qm hacc hgood hio hrb hb h1) ?_
  intro r hr
  have hr' := Finset.mem_Icc.mp hr
  have hk := MemoryWalkDeployed.kMem_le P
  have hrM : 1 ≤ r ∧ r ≤ P.optimized.family.problem.cfg.memRows := by
    change P.optimized.family.problem.cfg.kMem ≤ P.optimized.family.problem.cfg.memRows at hk
    omega
  unfold decodedRootPoly
  rw [(htel r hrM).2]
  exact Batch822.root_counts_zero P c (honestQm P c Qm) hsatM r hr

/-- **R4 with the census premises: the decoded paths are valid.**  `hU` is
`FormRCore/Mtree.lean::UniqueExponents` at each decoded root tree; `hA` is
`CertInRange` in the shape U1 delivers (`decodedShift_in_range_of_U1`). -/
theorem r4_path_valid_at_ev
    (hU : ∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem,
      UniqueExponents (decodedMTreeOfEnvs (envsKR P c Qm) (envsFR P c Qm)
        P.optimized.family.problem.cfg.kMem r))
    (hA : ∀ e, decodedShift (envsCR P c Qc) e ≤ FormRAxisEvent.formRN K - 1) :
    ∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem,
      let t := decodedMTreeOfEnvs (envsKR P c Qm) (envsFR P c Qm)
        P.optimized.family.problem.cfg.kMem r
      (∀ e, readCount e t = verifyCount e t) ∧
        ∀ e, Paired e t →
          Padding (FormRAxisEvent.formRN K) (decodedShift (envsCR P c Qc) e)
              (decodedBits (envsCR P c Qc) e) ∧
            ∃ q, Batch554.rpaths e t = [q] ∧
              Batch554.vpaths e t =
                [q ++ Batch554.bitsOf (decodedShift (envsCR P c Qc) e) (decodedBits (envsCR P c Qc) e)] := by
  intro r hr
  have h0 := (r4_bridge_at_ev P c Qc Qm hacc hgood hio hrb hb h1).2 r hr
  unfold decodedRootPoly at h0
  exact (formR_counts_zero_iff (FormRAxisEvent.formRN K) (decodedShift (envsCR P c Qc))
    (decodedBits (envsCR P c Qc)) _ (hU r hr) hA).mp h0

end Assembly

end

end Nock.RedTeam.Batch824

