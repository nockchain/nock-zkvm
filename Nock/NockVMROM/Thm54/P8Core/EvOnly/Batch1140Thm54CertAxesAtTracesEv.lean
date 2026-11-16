/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch1140Thm54CertAxesAtTracesEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1140Thm54CertAxesAtTraces
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
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch973Thm54Round0WrapJoinEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch974Thm54Round0WrapJoinForestEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1011Thm54AxisViewBindsAtCoinEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1024Thm54C2BindsAtCoinEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch1111Thm54C2CombinedAtTracesEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1140

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.ComputeTable (MemRec)
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis (reqIdxCol)
open Nock.RedTeam.Batch575 (Padding)
open Nock.ComputeTable (State DTcomp)
open Nock.NockVMROM.Thm54.DeployedComputeRows (pkgHchar)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

section Generic

open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Nock.RedTeam.Batch575
open scoped Classical
variable {F : Type} [Field F]

end Generic

section Request

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
  (hα0 : alphaM c.1 ≠ 0)
include hacc hgood hax hbasis hwidth hα0

/-- **The request-to-read-row bridge.**  Every active compute request `(a, j)` has a
`read_root` memory row whose record exponent is `expOfAt a j`: the LogUp response row (`ver = 1`)
is `read_root` itself, or a `verify_child` row whose `intermediate` partner is; a padding row
(`decompose` / `halt`) stores the zero record (`eqBlk`), whose timestamp `0` cannot answer the
request's `α^e` (`α ≠ 0`). -/
theorem read_row_of_request_ev (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    ∃ k : Fin P.optimized.family.problem.cfg.memRows,
      memRowStateOf (memEnvF P c Qm k) = .read_root ∧
        Batch973.expR P c Qm k = expOfAt P c Qc a j := by
  have hio := Batch974.hio_of_hgood_ev P c Qc Qm hgood
  have hrb := P.rowsBound
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  have hchar' := OptimizedHostileConfiguration.hchar_of_package P
  have hsatC := hacc.compute_satisfies
  obtain ⟨i, hver, hrec, hidx⟩ := request_named_by_row_at_ev P c Qc Qm hacc hgood hio hchar'
    (hKp_of_rowsBound_at P hrb) (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm)
    a j hact
  have hlt := expOfAt_lt_ringChar P c Qc hsatC hchar' (hKp_of_rowsBound_at P hrb)
    (hKreq_of_rowsBound_at P c Qc) hact
  have hexpOf : ∀ k : Fin P.optimized.family.problem.cfg.memRows,
      (memEnvF P c Qm k).trace reqIdxCol = (memEnvF P c Qm i).trace reqIdxCol →
      Batch973.expR P c Qm k = expOfAt P c Qc a j := by
    intro k hk
    show RecordCarrier.natLift _ = _
    rw [hk, hidx]; exact RecordCarrier.natLift_natCast hlt
  -- the request's timestamp is `α^e ≠ 0`; a padding row's is `0`
  have hts : (memEnvK P c Qm i).trace 26 ≠ 0 := by
    have h7 := congrFun hrec 7
    rw [rowRecord_ts_at_at P c Qc hsatC hchar' (nprSeed_ne_of_good_at_ev P c Qc Qm hgood) a j hact,
      hostile_ln0_eq_one_at P c Qc hsatC, one_mul] at h7
    simp only [OptimizedMemoryHostileAccumulator.rowRecord] at h7
    intro h0
    apply pow_ne_zero (expOfAt P c Qc a j) hα0
    rw [← h7]; simpa using h0
  have hpadz : memoryMemRecKind (memRowStateOf (memEnvF P c Qm i)) = .padding →
      (memEnvK P c Qm i).trace 26 = 0 := by
    intro hk
    have htop := Batch974.decoded_topology_ev P c Qc Qm hacc hgood hax hbasis hwidth
    have hF := Batch509.fmem_of_topology P c (honestQc P c Qc) (honestQm P c Qm) _ htop
      (i.val + 1) (by omega) i.isLt
    rw [ExecOfTraces.lblM_succ] at hF
    have hst : (ExecOfTraces.lblMAt P (honestQm P c Qm) c i).2.2.st =
        (ExecOfTraces.lblMAt P (honestQm P c Qm) c i).1 := hF.1
    have hstate : (ExecOfTraces.lblMAt P (honestQm P c Qm) c i).1 =
        memRowStateOf (memEnvF P c Qm i) := Batch844.memoryStateOf_eq_memRowStateOf _
    have hm := Batch509.eqBlk_padding_mem_zero hF.2.1 (by rw [hst, hstate]; exact hk)
    have := congrArg MemRec.ts hm
    exact this
  rcases hs : memRowStateOf (memEnvF P c Qm i) with _ | _ | _ | _
  · exact absurd (hpadz (by rw [hs]; rfl)) hts
  · exact absurd (hpadz (by rw [hs]; rfl)) hts
  · exact ⟨i, hs, hexpOf i rfl⟩
  · have h3 := UniqueExponentsBridge.verify_sel_at P c Qm hacc.memory_satisfies i hs
    obtain ⟨k, hsel', hrec'⟩ := UniqueExponentsBridge.verify_partner_at_ev P c Qc Qm hacc hgood hrb i h3
    have hst' := Batch973.read_state_of_sel2_ev P c Qc Qm hacc hgood hrb k hsel'
    have h9 := congrFun hrec' 9
    simp only [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord] at h9
    have hr : (memEnvF P c Qm k).trace reqIdxCol = (memEnvF P c Qm i).trace reqIdxCol := by
      apply (algebraMap F K).injective
      simpa [reqIdxCol] using h9.symm
    exact ⟨k, hst', hexpOf k hr⟩

end Request

section Rows

variable (hsat : Framework.RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

end Rows

section RowsAcc

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
  (hα0 : alphaM c.1 ≠ 0)
include hacc hgood hax hbasis hwidth hα0

/-- The padded certificate of an active request, at the package env `envsCR`. -/
theorem request_padding_ev (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    Padding (FormRAxisEvent.formRN K) (slotCert (Batch824.envsCR P c Qc) a j).1
      (slotCert (Batch824.envsCR P c Qc) a j).2 := by
  have hio := Batch974.hio_of_hgood_ev P c Qc Qm hgood
  have hrb := P.rowsBound
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  have hchar' := OptimizedHostileConfiguration.hchar_of_package P
  obtain ⟨k, hst, hexp⟩ := read_row_of_request_ev P c Qc Qm hacc hgood hax hbasis hwidth hα0 a j hact
  have hpad := Batch973.read_row_padding_ev P c Qc Qm hacc hgood hio hrb hb1 hwidth k hst
  rw [hexp] at hpad
  obtain ⟨hds, hdb⟩ := Batch823.decoded_eq_slotCert P c Qc hacc.compute_satisfies hchar' a j hact
  rw [hds, hdb] at hpad
  exact hpad

/-- **The recovered axis of an active request is the row's certificate axis, and is below `p`**:
`certAxisOfEnvs envsCR (expOfAt a j) = certAxis (slotCert a j)` and `< ringChar K`. -/
theorem request_axis_ev (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc a j) =
        certAxis (slotCert (Batch824.envsCR P c Qc) a j).1 (slotCert (Batch824.envsCR P c Qc) a j).2 ∧
      certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc a j) < ringChar K := by
  have hio := Batch974.hio_of_hgood_ev P c Qc Qm hgood
  have hrb := P.rowsBound
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  have hchar' := OptimizedHostileConfiguration.hchar_of_package P
  obtain ⟨hds, hdb⟩ := Batch823.decoded_eq_slotCert P c Qc hacc.compute_satisfies hchar' a j hact
  have heq : certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc a j) =
      certAxis (slotCert (Batch824.envsCR P c Qc) a j).1 (slotCert (Batch824.envsCR P c Qc) a j).2 := by
    unfold certAxisOfEnvs; rw [hds, hdb]
  refine ⟨heq, ?_⟩
  rw [heq]
  exact Batch973.cert_lt_ev P c Qc Qm hacc hgood hio hrb hb1 hwidth a j
    (request_padding_ev P c Qc Qm hacc hgood hax hbasis hwidth hα0 a j hact)

/-- **The row's own certificate, at a selector-`s` row (`s = 0` or `9`)**: `slotCert` at the
row's slot is `(rowShift, rowBits)` of the family base env, and it is padded. -/
theorem row_cert_padded_ev (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hj : (j : ℕ) = 1 ∨ (j : ℕ) = 2)
    (hsel : (Batch908.envsFam P c Qc a).trace (if (j : ℕ) = 1 then 0 else 9) = 1)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    slotCert (Batch824.envsCR P c Qc) a j =
        (rowShift (Batch908.envsFam P c Qc a), rowBits (Batch908.envsFam P c Qc a)) ∧
      Padding (OptimizedComputeRangeCertificate.formRN F) (rowShift (Batch908.envsFam P c Qc a))
        (rowBits (Batch908.envsFam P c Qc a)) := by
  have hE := Batch908.envsCR_embeds P c Qc
  have hs : rowShift (Batch824.envsCR P c Qc a) = rowShift (Batch908.envsFam P c Qc a) :=
    Batch908.rowShift_embed (algebraMap F K) (algebraMap F K).injective _ _
      (fun k hk => hE a (265 + k) (by unfold Batch908.ReadCols; omega))
  have hbits : rowBits (Batch824.envsCR P c Qc a) = rowBits (Batch908.envsFam P c Qc a) :=
    Batch973.rowBits_embed (algebraMap F K) (algebraMap F K).injective _ _
      (fun j h1 h2 => hE a j (by unfold Batch908.ReadCols; omega))
  have hselK : ∀ col, (col = 0 ∨ col = 9) → (Batch908.envsFam P c Qc a).trace col = 1 →
      (Batch824.envsCR P c Qc a).trace col = 1 := by
    intro col hcol h
    rw [hE a col (by unfold Batch908.ReadCols; omega), h, map_one]
  have hslot : slotCert (Batch824.envsCR P c Qc) a j =
      (rowShift (Batch908.envsFam P c Qc a), rowBits (Batch908.envsFam P c Qc a)) := by
    obtain ⟨jv, hjv⟩ := j
    simp only at hj hsel
    rcases hj with rfl | rfl
    · simp only [if_true] at hsel
      simp only [slotCert, hselK 0 (Or.inl rfl) hsel, if_true, hs, hbits]
    · simp only [show (2 : ℕ) ≠ 1 by decide, if_false] at hsel
      simp only [slotCert, hselK 9 (Or.inr rfl) hsel, if_true, hs, hbits]
  refine ⟨hslot, ?_⟩
  have hp := request_padding_ev P c Qc Qm hacc hgood hax hbasis hwidth hα0 a j hact
  rw [hslot] at hp
  rw [Batch908.formRN_agree (F := F) (K := K)]
  exact hp

end RowsAcc

section Tree

open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1024 (treeS axF svF)

end Tree

section CertAxes

open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1024 (treeS axF svF)

variable (hsat : Framework.RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

end CertAxes

section CertAxesAcc

open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1024 (treeS axF svF)
variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
  (hα0 : alphaM c.1 ≠ 0)
include hacc hgood hax hbasis hwidth hα0

/-- `axF` reads the package env `envsCR` (`Batch974.row_identity_ev`'s congruence). -/
theorem axF_eq_ev : axF P c Qc = certAxisOfEnvs (Batch824.envsCR P c Qc) := by
  refine Batch970.certAxisOfEnvs_congr fun i col _ => ?_
  have hfam : FamilyEnvCore.familyQc P.optimized c (honestQc P c Qc) = Qc :=
    Batch824.familyQc_honestQc P c Qc
  have htr : (computeEnvsR0 P.optimized (honestQc P c Qc) c i).trace =
      (Batch824.envsCR P c Qc i).trace := by
    unfold computeEnvsR0
    rw [hfam]
    exact (Batch823.envsC_trace P c Qc i).symm
  rw [htr]

/-- The carrier `S` of row `r` is the prefix `S(r)` (`expCol_eq_prefixExp_at`, no wraparound). -/
theorem c2SAt_eq_ev (r : Fin P.optimized.family.problem.cfg.compRows) :
    c2SAt P.optimized (honestQc P c Qc) c r = prefixExpAt P c Qc r := by
  have hsatC := hacc.compute_satisfies
  have hchar' := OptimizedHostileConfiguration.hchar_of_package P
  have hrb := P.rowsBound
  have hlt := expOfAt_lt_ringChar P c Qc hsatC hchar' (hKp_of_rowsBound_at P hrb)
    (hKreq_of_rowsBound_at P c Qc) (OptimizedHostileTimestamps.activeMask_zero (rowEnvAt P c Qc r))
  have hFK : ringChar F = ringChar K := Algebra.ringChar_eq F K
  have hlt' : prefixExpAt P c Qc r < ringChar K := by
    rw [← hFK]; simp only [expOfAt] at hlt; omega
  have hfam : FamilyEnvCore.familyQc P.optimized c (honestQc P c Qc) = Qc :=
    Batch824.familyQc_honestQc P c Qc
  unfold c2SAt computeEnvsR0
  rw [hfam]
  show RecordCarrier.natLift (algebraMap F K (rowEnvAt P c Qc r).expCol) = _
  rw [expCol_eq_prefixExp_at P c Qc hsatC hchar' r r.isLt, map_natCast]
  exact RecordCarrier.natLift_natCast hlt'

theorem certAxesOK0_of_traces_ev
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c) :
    CertAxesOK0 P c Qc := by
  have hsatC := hacc.compute_satisfies
  have hFK : ringChar F = ringChar K := Algebra.ringChar_eq F K
  intro u hu
  obtain ⟨i, hi⟩ := Batch1111.label_of_inTree_S P c Qc Qm h hu
  set r := rowIdx P i with hr
  have hlab : u.label = (StrategyOfTracesLift.lblCAt P.optimized (honestQc P c Qc) c r,
      c2SAt P.optimized (honestQc P c Qc) c r) := by rw [hi, lblCS_eq]
  rw [hlab, lblCAt_eq P c Qc r, c2SAt_eq_ev P c Qc Qm hacc hgood hax hbasis hwidth hα0 r,
    axF_eq_ev P c Qc Qm hacc hgood hax hbasis hwidth hα0]
  simp only
  obtain ⟨hft, hfth⟩ := decodeDec_ft_leaf (rowEnvAt P c Qc r)
  rw [hft, hfth]
  -- the cast atom's coordinate 0
  have hcoordExt : ∀ (role : Fin 63), coord P.optimized.basis
      ((rowEnvAt P c Qc r).extTrace role) 0 =
        (Batch908.envsFam P c Qc r).trace (13 + 3 * (role : ℕ)) := by
    intro role
    have := Nock.NockVMROM.Thm54.MonolithicRAP.coord_sum_smul P.optimized.basis
      (fun k => (Batch908.envsFam P c Qc r).trace
        (OptimizedComputeCorrectedFinal.correctedFinalExtCoordIndex role k)) 0
    exact this.trans (by simp [OptimizedComputeCorrectedFinal.correctedFinalExtCoordIndex])
  have hinj : ∀ x y : ℕ, x < ringChar K → y < ringChar K → (x : F) = (y : F) → x = y := by
    intro x y hx hy hxy
    exact CharP.natCast_injOn_Iio F (ringChar F) (Set.mem_Iio.2 (hFK ▸ hx))
      (Set.mem_Iio.2 (hFK ▸ hy)) hxy
  refine ⟨fun hst => ?_, fun hst => ?_⟩
  · have hsel := rowSelector_of_state P c Qc hsatC r .s0 hst
    have hb0 : (Batch908.envsFam P c Qc r).trace 0 = 1 := by
      simpa [Nock.Reified.opCol] using base_sel_of P c Qc hsatC r .s0 .s0 hsel
    have hb9 : (Batch908.envsFam P c Qc r).trace 9 = 0 := by
      simpa [Nock.Reified.opCol] using base_sel_of P c Qc hsatC r .s0 .s9 hsel
    have hact := (activeMask_of_sel P c Qc hsatC r .s0 hsel).1 rfl
    obtain ⟨hslot, hpad⟩ := row_cert_padded_ev P c Qc Qm hacc hgood hax hbasis hwidth hα0 r 1
      (Or.inl rfl) (by simpa using hb0) hact
    obtain ⟨heq, hlt⟩ := request_axis_ev P c Qc Qm hacc hgood hax hbasis hwidth hα0 r 1 hact
    have hE : prefixExpAt P c Qc r + 2 = expOfAt P c Qc r 1 := by simp [expOfAt]
    rw [hE]
    refine ⟨fun n hn hleaf => ?_, hlt⟩
    have h136 := leaf136_eq_certAxis (Batch908.envsFam P c Qc r) hwidth
      (fun g hg => (row_obligations_at P c Qc hsatC r).formR99 g hg) hpad hb0 hb9
    have hc := hcoordExt ⟨41, by decide⟩
    rw [hleaf, coord_natCast _ hbasis] at hc
    simp only [show 13 + 3 * 41 = 136 from rfl] at hc
    have hAeq : certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc r 1) =
        certAxis (rowShift (Batch908.envsFam P c Qc r)) (rowBits (Batch908.envsFam P c Qc r)) := by
      rw [heq, hslot]
    rw [h136, ← hAeq] at hc
    exact (hinj _ _ hn hlt hc).symm
  · have hsel := rowSelector_of_state P c Qc hsatC r .s9 hst
    have hb0 : (Batch908.envsFam P c Qc r).trace 0 = 0 := by
      simpa [Nock.Reified.opCol] using base_sel_of P c Qc hsatC r .s9 .s0 hsel
    have hb9 : (Batch908.envsFam P c Qc r).trace 9 = 1 := by
      simpa [Nock.Reified.opCol] using base_sel_of P c Qc hsatC r .s9 .s9 hsel
    have hact := (activeMask_of_sel P c Qc hsatC r .s9 hsel).2 rfl
    obtain ⟨hslot, hpad⟩ := row_cert_padded_ev P c Qc Qm hacc hgood hax hbasis hwidth hα0 r 2
      (Or.inr rfl) (by simpa using hb9) hact
    obtain ⟨heq, hlt⟩ := request_axis_ev P c Qc Qm hacc hgood hax hbasis hwidth hα0 r 2 hact
    have hE : prefixExpAt P c Qc r + 3 = expOfAt P c Qc r 2 := by simp [expOfAt]
    rw [hE]
    refine ⟨fun n hn hleaf => ?_, hlt⟩
    have h145 := leaf145_eq_certAxis (Batch908.envsFam P c Qc r) hwidth
      (fun g hg => (row_obligations_at P c Qc hsatC r).formR99 g hg) hpad hb0 hb9
    have hc := hcoordExt ⟨44, by decide⟩
    rw [hleaf, coord_natCast _ hbasis] at hc
    simp only [show 13 + 3 * 44 = 145 from rfl] at hc
    have hAeq : certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc r 2) =
        certAxis (rowShift (Batch908.envsFam P c Qc r)) (rowBits (Batch908.envsFam P c Qc r)) := by
      rw [heq, hslot]
    rw [h145, ← hAeq] at hc
    exact (hinj _ _ hn hlt hc).symm

end CertAxesAcc

end

end Nock.RedTeam.Batch1140

