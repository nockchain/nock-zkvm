/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch973Thm54Round0WrapJoinEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch973Thm54Round0WrapJoin
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch465Thm54DeployedRootLabelEqClaimEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch489Thm54FoOfEqFoWEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch490Thm54TopologyAssemblyEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch500Thm54GammaTransportEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch501Thm54MemoryTopologyEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch822Thm54R4BridgeMemoryEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.FamilyIOChainRouteBEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch824Thm54R4BridgeEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.UniqueExponentsBridgeEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch973

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.ComputeTable (MemRec)
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.RedTeam.Batch575

noncomputable section

section Generic

variable {K : Type} [Field K]

end Generic

section Embed

variable {F K : Type} [Field F] [Field K] (f : F →+* K) (hf : Function.Injective f)
include hf

end Embed

section Deployed

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
  (hio : FamilyIOGood P c Qc Qm)
  (hrb : 3 * P.objects.cfg.compRows < ringChar K ∧ P.objects.cfg.memRows < ringChar K)
  (hb1 : coord P.optimized.basis (1 : K) (0 : Fin 3) ≠ 0)

include hacc hgood hio hrb hb1

/-- **A `read_root` row's stored `(T, C', ts)` are the located certificate's.** -/
theorem read_row_slots_ev (k : Fin P.optimized.family.problem.cfg.memRows)
    (hsel : (memEnvF P c Qm k).trace 2 = 1) :
    ∃ (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3),
      activeMask (rowEnvAt P c Qc a) j = 1 ∧
      expR P c Qm k = expOfAt P c Qc a j ∧
      (memEnvK P c Qm k).trace 25 = c.2.2.2.lambda ^ (slotCert (Batch824.envsCR P c Qc) a j).1 ∧
      (memEnvK P c Qm k).trace 57 =
        (C'poly (K := K) (FormRAxisEvent.formRN K) (slotCert (Batch824.envsCR P c Qc) a j).2).eval
          c.2.2.2.lambda ∧
      (memEnvK P c Qm k).trace 26 = alphaM c.1 ^ expR P c Qm k := by
  have hchar' := OptimizedHostileConfiguration.hchar_of_package P
  have hsatC := hacc.compute_satisfies
  have hver := UniqueExponentsBridge.readSel_ver_at P c Qm hacc.memory_satisfies hb1 k hsel
  obtain ⟨a, j, hact, hrec⟩ := row_record_is_request_at_ev P c Qc Qm hacc hgood hio hchar'
    (hKp_of_rowsBound_at P hrb) (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) k hver
  have hb := Batch823.certBitsBoolean_of_sat P c Qc hsatC
  obtain ⟨h6c, h8c⟩ := Batch823.slot_values P c Qc hsatC hb hchar' a j hact
  have h9 := congrFun hrec 9
  rw [compute_slot9_eq_expOf_at P c Qc hsatC hchar' a j] at h9
  have h9' : (memEnvF P c Qm k).trace reqIdxCol = ((expOfAt P c Qc a j : ℕ) : F) := by
    apply (algebraMap F K).injective
    simpa [OptimizedMemoryHostileAccumulator.rowRecord, reqIdxCol] using h9
  have hlt := expOfAt_lt_ringChar P c Qc hsatC hchar' (hKp_of_rowsBound_at P hrb)
    (hKreq_of_rowsBound_at P c Qc) hact
  have hexp : expR P c Qm k = expOfAt P c Qc a j := by
    show RecordCarrier.natLift ((memEnvF P c Qm k).trace reqIdxCol) = _
    rw [h9']; exact RecordCarrier.natLift_natCast hlt
  have h6 := congrFun hrec 6
  have h8 := congrFun hrec 8
  rw [h6c] at h6
  rw [h8c] at h8
  refine ⟨a, j, hact, hexp, ?_, ?_, ?_⟩
  · simpa [OptimizedMemoryHostileAccumulator.rowRecord] using h6
  · simpa [OptimizedMemoryHostileAccumulator.rowRecord] using h8
  · exact ts_eq_alpha_pow_natLift_at_ev P c Qc Qm hacc hgood hio hchar'
      (hKp_of_rowsBound_at P hrb) (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm) k hver

omit hio hb1 in
/-- A selector-`2` family row decodes to `read_root` (base one-hot). -/
theorem read_state_of_sel2_ev (k : Fin P.optimized.family.problem.cfg.memRows)
    (hsel : (memEnvF P c Qm k).trace 2 = 1) :
    memRowStateOf (memEnvF P c Qm k) = .read_root := by
  have hchar := Batch824.memStateTagChar_of_package P
  obtain ⟨st, hone⟩ := FamilyMemoryRows.baseOneHot_at_family P c Qm hacc.memory_satisfies k hchar
  have h2 := hone .read_root
  have hst : st = .read_root := by
    by_contra hne
    have : (memEnvF P c Qm k).trace (Nock.Reified.mopCol MState.read_root) = 0 := by
      simpa [Ne.symm hne] using h2
    rw [show Nock.Reified.mopCol MState.read_root = 2 from rfl] at this
    rw [this] at hsel
    exact zero_ne_one hsel
  rw [← Batch844.memoryStateOf_eq_memRowStateOf]
  exact (FamilyMemoryRows.memoryStateOf_eq_of_baseOneHot _ st hone).trans hst

/-- **Padding of a `read_root` row's certificate** (R4's path validity at the paired exponent). -/
theorem read_row_padding_ev (hwidth : FormRWidth F) (k : Fin P.optimized.family.problem.cfg.memRows)
    (hst : memRowStateOf (memEnvF P c Qm k) = .read_root) :
    Padding (FormRAxisEvent.formRN K) (decodedShift (Batch824.envsCR P c Qc) (expR P c Qm k))
      (decodedBits (Batch824.envsCR P c Qc) (expR P c Qm k)) := by
  have hchar := Batch824.memStateTagChar_of_package P
  have hsatM := hacc.memory_satisfies
  have hb := Batch823.certBitsBoolean_of_sat P c Qc hacc.compute_satisfies
  have hn : 2 ≤ OptimizedComputeRangeCertificate.formRN F := by
    obtain ⟨_, _, h3⟩ := hwidth
    unfold OptimizedComputeRangeCertificate.formRN
    exact Nat.lt_size.mpr (by omega)
  have hA := Batch908.hA_of_acceptance P c Qc hacc.compute_satisfies hn
  have hU : ∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem,
      UniqueExponents (decodedMTreeOfEnvs (Batch824.envsKR P c Qm) (Batch824.envsFR P c Qm)
        P.optimized.family.problem.cfg.kMem r) :=
    fun r _ => UniqueExponentsBridge.uniqueExponents_decoded_pkg_ev P c Qc Qm hacc hgood hio hrb hb1 _ r
  have hpath := Batch824.r4_path_valid_at_ev P c Qc Qm hacc hgood hio hrb hb hb1 hU hA
  have hfQm := Batch824.familyQm_honestQm P c Qm
  have hfo : ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      foOfMem (Batch824.envsFR P c Qm) i = MemoryWalkDeployed.foW P c Qm i := by
    intro i h1 h2
    have := Batch489.foOfMem_eq_foWmem P c (honestQm P c Qm) i h1 h2
    rwa [hfQm] at this
  have hα := Batch501.htileαM_of_good_ev P c (honestQc P c Qc) (honestQm P c Qm)
    (by rw [hfQm]; exact hsatM) hchar hgood
  rw [hfQm] at hα
  have ht := WalkQueueDeployed.deployed_tiling_memory P c Qm hsatM hchar hα
  have htile : P.optimized.family.problem.cfg.kMem +
      Sf (foOfMem (Batch824.envsFR P c Qm)) P.optimized.family.problem.cfg.memRows =
        P.optimized.family.problem.cfg.memRows := by
    rw [Sf_congr_le _ _ _ hfo]; exact ht
  have hv0 := WalkQueueDeployed.deployed_bfsValid_memory P c Qm hsatM hchar
  have hv : BFSValidF P.optimized.family.problem.cfg.kMem (foOfMem (Batch824.envsFR P c Qm))
      P.optimized.family.problem.cfg.memRows := by
    intro i h1 h2
    rw [Sf_congr_le _ _ _ (fun j hj1 hj2 => hfo j hj1 (by omega))]
    exact hv0 i h1 h2
  have htr : ∀ j, (Batch824.envsFR P c Qm k).trace j = (memEnvF P c Qm k).trace j :=
    fun j => (memEnvF_trace P c Qm k j).symm
  have hst' : memRowStateOf (Batch824.envsFR P c Qm k) = .read_root := by
    rw [← hst]; exact Batch733.memRowStateOf_congr (fun j _ => htr j)
  have hbal : ∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem, ∀ e,
      readCount e (decodedMTreeOfEnvs (Batch824.envsKR P c Qm) (Batch824.envsFR P c Qm)
        P.optimized.family.problem.cfg.kMem r) =
      verifyCount e (decodedMTreeOfEnvs (Batch824.envsKR P c Qm) (Batch824.envsFR P c Qm)
        P.optimized.family.problem.cfg.kMem r) :=
    fun r hr e => (hpath r hr).1 e
  obtain ⟨r, hr, hpair⟩ := Batch971.paired_of_read_row (Batch824.envsKR P c Qm)
    (Batch824.envsFR P c Qm) P.optimized.family.problem.cfg.kMem htile hv hU hbal k hst'
  have hpad := ((hpath r hr).2 _ hpair).1
  have hexp : rowExp (Batch824.envsFR P c Qm) k = expR P c Qm k := by
    unfold rowExp; rw [htr]; rfl
  rwa [hexp] at hpad

/-- **The recovered axis of a located certificate is below `p`.** -/
theorem cert_lt_ev (hwidth : FormRWidth F)
    (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hpad : Padding (FormRAxisEvent.formRN K) (slotCert (Batch824.envsCR P c Qc) a j).1
      (slotCert (Batch824.envsCR P c Qc) a j).2) :
    certAxis (slotCert (Batch824.envsCR P c Qc) a j).1 (slotCert (Batch824.envsCR P c Qc) a j).2 <
      ringChar K := by
  have hFK : ringChar F = ringChar K := Algebra.ringChar_eq F K
  have hrow : Padding (FormRAxisEvent.formRN K) (rowShift (Batch824.envsCR P c Qc a))
      (rowBits (Batch824.envsCR P c Qc a)) →
      certAxis (rowShift (Batch824.envsCR P c Qc a)) (rowBits (Batch824.envsCR P c Qc a)) <
        ringChar K := by
    intro hp
    have hE := Batch908.envsCR_embeds P c Qc
    have hs : rowShift (Batch824.envsCR P c Qc a) = rowShift (Batch908.envsFam P c Qc a) :=
      Batch908.rowShift_embed (algebraMap F K) (algebraMap F K).injective _ _
        (fun k hk => hE a (265 + k) (by unfold Batch908.ReadCols; omega))
    have hbits : rowBits (Batch824.envsCR P c Qc a) = rowBits (Batch908.envsFam P c Qc a) :=
      rowBits_embed (algebraMap F K) (algebraMap F K).injective _ _
        (fun j h1 h2 => hE a j (by unfold Batch908.ReadCols; omega))
    rw [hs, hbits] at hp ⊢
    rw [← Batch908.formRN_agree (F := F) (K := K)] at hp
    rw [← hFK]
    exact Batch972.certAxis_lt_ringChar (Batch908.envsFam P c Qc a) hwidth
      (fun g hg => (row_obligations_at P c Qc hacc.compute_satisfies a).formR99 g hg) hp
  obtain ⟨jv, hjv⟩ := j
  have h3 : (3 : ℕ) < ringChar K := by rw [← hFK]; exact hwidth.2.2
  match jv, hjv with
  | 0, _ =>
      simp only [slotCert] at hpad ⊢
      simp [certAxis]; omega
  | 1, _ =>
      simp only [slotCert] at hpad ⊢
      split_ifs at hpad ⊢
      · exact hrow hpad
      · simp [certAxis]; omega
  | 2, _ =>
      simp only [slotCert] at hpad ⊢
      split_ifs at hpad ⊢
      · exact hrow hpad
      · simp [certAxis]; omega

/-- **A `read_root` row stores exactly the encode of its recovered axis.** -/
theorem read_row_facts_ev (hwidth : FormRWidth F)
    (k : Fin P.optimized.family.problem.cfg.memRows)
    (hst : memRowStateOf (memEnvF P c Qm k) = .read_root) :
    (memEnvK P c Qm k).trace 25 = formRT c.2.2.2.lambda
        (nockAxisOf ((certAxisOfEnvs (Batch824.envsCR P c Qc) (expR P c Qm k) : ℕ) : K)) ∧
      (memEnvK P c Qm k).trace 57 = formRC c.2.2.2.lambda
        (nockAxisOf ((certAxisOfEnvs (Batch824.envsCR P c Qc) (expR P c Qm k) : ℕ) : K)) ∧
      (memEnvK P c Qm k).trace 26 = alphaM c.1 ^ expR P c Qm k := by
  have hchar' := OptimizedHostileConfiguration.hchar_of_package P
  obtain ⟨a, j, hact, hexp, h25, h57, h26⟩ :=
    read_row_slots_ev P c Qc Qm hacc hgood hio hrb hb1 k (UniqueExponentsBridge.sel2_of_read hst)
  obtain ⟨hds, hdb⟩ := Batch823.decoded_eq_slotCert P c Qc hacc.compute_satisfies hchar' a j hact
  have hpad := read_row_padding_ev P c Qc Qm hacc hgood hio hrb hb1 hwidth k hst
  have hds' : decodedShift (Batch824.envsCR P c Qc) (expR P c Qm k) =
      (slotCert (Batch824.envsCR P c Qc) a j).1 := by rw [hexp]; exact hds
  have hdb' : decodedBits (Batch824.envsCR P c Qc) (expR P c Qm k) =
      (slotCert (Batch824.envsCR P c Qc) a j).2 := by rw [hexp]; exact hdb
  rw [hds', hdb'] at hpad
  have hlt := cert_lt_ev P c Qc Qm hacc hgood hio hrb hb1 hwidth a j hpad
  unfold certAxisOfEnvs
  rw [hds', hdb', nockAxisOf_natCast hlt, Batch972.formRT_certAxis,
    Batch972.formRC_certAxis _ _ _ hpad]
  exact ⟨h25, h57, h26⟩

/-- **The same for a `verify_child` row**, through its `intermediate` partner. -/
theorem verify_row_facts_ev (hwidth : FormRWidth F)
    (k : Fin P.optimized.family.problem.cfg.memRows)
    (hst : memRowStateOf (memEnvF P c Qm k) = .verify_child) :
    (memEnvK P c Qm k).trace 25 = formRT c.2.2.2.lambda
        (nockAxisOf ((certAxisOfEnvs (Batch824.envsCR P c Qc) (expR P c Qm k) : ℕ) : K)) ∧
      (memEnvK P c Qm k).trace 57 = formRC c.2.2.2.lambda
        (nockAxisOf ((certAxisOfEnvs (Batch824.envsCR P c Qc) (expR P c Qm k) : ℕ) : K)) ∧
      (memEnvK P c Qm k).trace 26 = alphaM c.1 ^ expR P c Qm k := by
  have h3 := UniqueExponentsBridge.verify_sel_at P c Qm hacc.memory_satisfies k hst
  obtain ⟨k', hsel', hrec⟩ := UniqueExponentsBridge.verify_partner_at_ev P c Qc Qm hacc hgood hrb k h3
  have hst' := read_state_of_sel2_ev P c Qc Qm hacc hgood hrb k' hsel'
  have hf := read_row_facts_ev P c Qc Qm hacc hgood hio hrb hb1 hwidth k' hst'
  have h9 := congrFun hrec 9
  have h6 := congrFun hrec 6
  have h7 := congrFun hrec 7
  have h8 := congrFun hrec 8
  simp only [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord] at h6 h7 h8 h9
  have hr : (memEnvF P c Qm k).trace reqIdxCol = (memEnvF P c Qm k').trace reqIdxCol := by
    apply (algebraMap F K).injective
    simpa [reqIdxCol] using h9
  have hexp : expR P c Qm k = expR P c Qm k' := by
    show RecordCarrier.natLift _ = RecordCarrier.natLift _
    rw [hr]
  rw [hexp]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hf.1]; simpa using h6
  · rw [← hf.2.1]; simpa using h8
  · rw [← hf.2.2]; simpa using h7

end Deployed

end

end Nock.RedTeam.Batch973

