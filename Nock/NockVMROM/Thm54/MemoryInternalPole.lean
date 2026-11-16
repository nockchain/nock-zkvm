import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.PairedRecordCountedEvent
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.CrossRapChronology
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.BuildablePackage
import Nock.NockVMROM.Thm54.BuildableTopology
import Nock.NockVMROM.Thm54.MultiRootHonestCommitment
import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.P8Core.MemoryInternalPole
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
The new
element is the memory table's internal `intermediate` LogUp pole; the
record-RLC coin `γ` is **reused** from the sampled IO `γ` (memory challenge slot `4`).
Inserting that coordinate into the acceptance tuple is stage 2 and is **not** done here.

Paper at source: the paper.
-/

namespace Nock.NockVMROM.Thm54
namespace MemoryInternalPole

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemoryHostileAccumulator
open MemoryPaperFactorization (paper_to_deployed BaseOneHot TreeOnlyBindings
  PreprocessingMasksBoolean DeadWitnessesHonest HostedPaperRow DeployedRow)
open StrictExtension
open OptimizedStrictFullPackage
open OptimizedStrictPackage
open MultiRootOptimizedAcceptance
open MultiRootHonestCommitment
open BuildablePackage
open BuildablePackage.Concrete
open BuildableConcrete
open PairedRecordCountedEvent
open Module
open scoped Polynomial

noncomputable section
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
variable [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K] [CharP K (ringChar K)]

/-! ## Design A

* `3` — forest-walk `α`;
* `4` — sampled IO `γ` (`ioGamma`);
* `5` — sampled IO pole;
* `6` — dead fold (`I.memoryExtensionFold`).

Stage 2 puts `interPole` at **slot `6`** and retargets `poleSource` onto
`(ioGamma, interPole) = (slot 4, slot 6)`.
-/

def proposedInterPoleSlot : ℕ := 6
def proposedInterGammaSlot : ℕ := 4
def proposedChronologyPoleSlot : Fin 10 := ⟨6, by decide⟩

theorem proposedInterPoleSlot_eq : proposedInterPoleSlot = 6 := rfl
theorem proposedInterGammaSlot_eq : proposedInterGammaSlot = 4 := rfl

/-! ## (d) Pole discipline for the proposed chronology slot -/

theorem proposedChronologyPoleSlot_mem :
    proposedChronologyPoleSlot ∈ CrossRap.memInternalPoleCoins := by
  decide

theorem proposedInterPole_sampledAfter_two :
    (CrossRap.nockChronologyPole.sampledAfter proposedChronologyPoleSlot : ℕ) = 2 := by
  decide

theorem proposedInterPole_follows_mem_records
    (c : Fin 55) (hc : c ∈ CrossRap.memRecordCols) :
    (CrossRap.finMemRoundOf5 c : ℕ)
      ≤ (CrossRap.nockChronologyPole.sampledAfter proposedChronologyPoleSlot : ℕ) := by
  have hle := CrossRap.memRecordCols_round5_le_two c hc
  have h2 := proposedInterPole_sampledAfter_two
  omega

theorem proposedInterPole_is_pole_disciplined
    {L : Type*} [Field L] (S : GigaIOThirdMessage.IOPlacement3)
    (q : Nock.NockVMROM.Thm54.SegmentedRAPParams L) :
    CrossRap.PoleDisciplined (CrossRap.memoryChip5 S q) CrossRap.memRecordCols
      {proposedChronologyPoleSlot} := by
  intro c hc j hj
  have hj' : j = proposedChronologyPoleSlot := Finset.mem_singleton.mp hj
  subst hj'
  exact CrossRap.memoryChip5_is_pole_disciplined S q c hc
    proposedChronologyPoleSlot proposedChronologyPoleSlot_mem

/-! ## Env-level coins, records, aggregator -/

theorem rlc_zero (γ : K) : Walk.rlc γ (fun _ : Fin 8 => (0 : K)) = 0 := by
  simp [Walk.rlc]

theorem identity_of_perm {records : FiniteIO.PreChallengeRecords K 9} (pole γ : K)
    (h : records.requests.Perm records.responses) :
    (records.requests.map fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      (records.responses.map fun r => (pole + Walk.rlc γ r)⁻¹).sum :=
  (h.map (fun r => (pole + Walk.rlc γ r)⁻¹)).sum_eq

theorem sum_map_eq_sum_fin {α M' : Type*} [AddCommMonoid M'] (g : α → M') :
    ∀ l : List α, (l.map g).sum = ∑ i : Fin l.length, g (l.get i) := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Fin.sum_univ_succ]
      simp

theorem coe_ofFn_eq_valMultiset {n : ℕ} (a : Fin n → K) :
    (↑(List.ofFn a) : Multiset K) = SetEq.valMultiset a := by
  simp [SetEq.valMultiset, List.ofFn_eq_map, Finset.val_univ_fin]

theorem pole_ne_zero_of_not_hit_zero_record
    {records : FiniteIO.PreChallengeRecords K 10} {coins : FiniteIO.IOCoins K}
    (hhit : coins.pole ∉ FiniteIO.IOPoleHitEvent records coins.gamma)
    (hzero : (fun _ : Fin 10 => (0 : K)) ∈ records.requests ++ records.responses) :
    coins.pole ≠ 0 := by
  intro hp0
  refine hhit ?_
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun _ => 0, hzero, by rw [hp0, zero_add]; simp [Walk.rlc]⟩

theorem paper_to_deployed_of_not_hit_zero_record
    (b : Basis (Fin 3) F K) (envF : Env F) (st : MemoryTable.MState)
    (hone : BaseOneHot envF st)
    (hbind : TreeOnlyBindings (gatherEnv b memoryCol0 envF) envF)
    (hmask : PreprocessingMasksBoolean envF)
    (hdead : DeadWitnessesHonest (gatherEnv b memoryCol0 envF) st)
    (hp : HostedPaperRow b envF)
    {records : FiniteIO.PreChallengeRecords K 10}
    (hzero : rowRecord (gatherEnv b memoryCol0 envF) envF = fun _ => 0)
    (hmem : rowRecord (gatherEnv b memoryCol0 envF) envF ∈
      records.requests ++ records.responses)
    (hhit : (chipInterCoins (gatherEnv b memoryCol0 envF)).pole ∉
      FiniteIO.IOPoleHitEvent records
        (chipInterCoins (gatherEnv b memoryCol0 envF)).gamma)
    (hst : st = .decompose ∨ st = .halt) :
    DeployedRow b envF := by
  refine paper_to_deployed b envF st hone hbind hmask hdead ?_ ?_ hp
  · set envK := gatherEnv b memoryCol0 envF
    have hsrc : (MemoryPaperFactorization.poleSourceMixed (F := F)).eval envK envF =
        (poleSourceMixed (F := F)).eval envK envF := rfl
    have hps : (poleSourceMixed (F := F)).eval envK envF = (chipInterCoins envK).pole := by
      rw [poleSource_eq_compress, FiniteIO.compress, hzero]
      simp [Walk.rlc]
    rw [hsrc, hps]
    exact pole_ne_zero_of_not_hit_zero_record hhit (by simpa [hzero] using hmem)
  · intro hrv
    cases hst with
    | inl hd =>
      cases hrv with
      | inl hr => cases hd.symm.trans hr
      | inr hv => cases hd.symm.trans hv
    | inr hh =>
      cases hrv with
      | inl hr => cases hh.symm.trans hr
      | inr hv => cases hh.symm.trans hv

def interWork (M cardK : ℕ) : ℕ :=
  FiniteIO.ioFailureUnionBound 10 M M cardK

theorem honest_encRec_identity_of_paired
    (E : BuildableNockExecution F K) (pole γ : K)
    (h : RowLayout.PairedRecordLayout E.exec) :
    (((RowLayout.consumedRecordList E.exec).map NockVM.encRec).map
        fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      (((RowLayout.addedRecordList E.exec).map NockVM.encRec).map
        fun r => (pole + Walk.rlc γ r)⁻¹).sum :=
  ((h.map NockVM.encRec).map (fun r => (pole + Walk.rlc γ r)⁻¹)).sum_eq

/-! ## Live chip, accepted traces -/

section Deployed

variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
variable (Qm : Fin P.memoryChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.memoryChip Qm)
include hsat

theorem aggregator_at (i : Fin (rows P)) :
    (paperAggregator (F := F)).eval (rowEnvK P Qm i) (rowEnvF P Qm i) = 0 :=
  mixed_at P Qm hsat i _ (paperAggregator_mem P.optimized.basis)

theorem intermediate_chain_at (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvK P Qm i).trace 28 = (rowEnvK P Qm i).traceNext 27 := by
  have hc := mixed_at P Qm hsat i _ (chainMixed_mem P.optimized.basis)
  have h5 : (rowEnvF P Qm i).trace 5 = 0 := by
    rw [(masks_at P Qm hsat i).2, if_neg (by omega)]
  simp only [chainMixed, MixedExpr.eval, bcur, CoeffExpr.eval, h5, sub_zero, map_one,
    one_mul, sub_eq_zero] at hc
  exact hc

omit hsat

theorem next_ipre (i : Fin (rows P)) (hi : (i : ℕ) + 1 < rows P) :
    (rowEnvK P Qm i).traceNext 27 = (rowEnvK P Qm ⟨(i : ℕ) + 1, hi⟩).trace 27 := by
  have hadj := P.optimized.memoryOrbitAligned i hi
  simp only [rowEnvK, gatherEnv, memoryCol0]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hw : (sourceOf P).rap.w = 182 :=
    (sourceMemoryRAP_fingerprint P.optimized.basis P.optimized.memoryChallenge
      P.optimized.memoryPublic P.optimized.orbit (rowNodeSet P.optimized.memoryNodes)).1
  have hlt : 6 + 3 * 27 + (k : ℕ) < (sourceOf P).rap.w := by rw [hw]; omega
  simp only [rowEnvF, envOfTrace, dif_pos hlt]
  rw [hadj, mul_comm]

theorem rowEnvK_chal (i j : Fin (rows P)) (k : ℕ) :
    (rowEnvK P Qm i).chal k = (rowEnvK P Qm j).chal k := by
  simp [rowEnvK, gatherEnv, rowEnvF, envOfTrace]

theorem chipInterCoins_const (i j : Fin (rows P)) :
    chipInterCoins (rowEnvK P Qm i) = chipInterCoins (rowEnvK P Qm j) := by
  refine congr_arg₂ FiniteIO.IOCoins.mk (rowEnvK_chal P Qm i j 4) (rowEnvK_chal P Qm i j 6)

def traceInterCoins : FiniteIO.IOCoins K :=
  chipInterCoins (rowEnvK P Qm (firstRow P))

theorem traceInterCoins_eq (i : Fin (rows P)) :
    chipInterCoins (rowEnvK P Qm i) = traceInterCoins P Qm :=
  chipInterCoins_const P Qm i (firstRow P)

def deltaPrefix (m : ℕ) : K :=
  ∑ k ∈ Finset.range m, if h : k < rows P then rowDelta (rowEnvK P Qm ⟨k, h⟩) else 0

theorem deltaPrefix_succ (m : ℕ) (hm : m < rows P) :
    deltaPrefix P Qm (m + 1) = deltaPrefix P Qm m + rowDelta (rowEnvK P Qm ⟨m, hm⟩) := by
  simp [deltaPrefix, Finset.sum_range_succ, hm]

include hsat

theorem ipre_eq_deltaPrefix :
    ∀ (m : ℕ) (hm : m < rows P), (rowEnvK P Qm ⟨m, hm⟩).trace 27 = deltaPrefix P Qm m := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp only [deltaPrefix, Finset.range_zero, Finset.sum_empty]
      exact (hostile_intermediate_anchored P Qm hsat).1
  | succ m ih =>
      intro hm
      have hm' : m < rows P := by omega
      rw [← next_ipre P Qm ⟨m, hm'⟩ hm, ← intermediate_chain_at P Qm hsat ⟨m, hm'⟩ hm,
        deltaPrefix_succ P Qm m hm', ← ih hm']
      simp [rowDelta]

theorem hostile_intermediate_telescopes :
    ∑ i : Fin (rows P), rowDelta (rowEnvK P Qm i) = 0 := by
  have hpos := P.optimized.family.problem.cfg.memRows_pos
  have hlast : (rowEnvK P Qm (lastRow P)).trace 28 = deltaPrefix P Qm (rows P - 1 + 1) := by
    have hm : rows P - 1 < rows P := Nat.sub_lt hpos (by omega)
    have hipre := ipre_eq_deltaPrefix P Qm hsat (rows P - 1) hm
    have hΔ : rowDelta (rowEnvK P Qm (lastRow P)) =
        (rowEnvK P Qm (lastRow P)).trace 28 - (rowEnvK P Qm (lastRow P)).trace 27 := rfl
    rw [deltaPrefix_succ P Qm (rows P - 1) hm, ← hipre, lastRow, hΔ]
    ring
  rw [(hostile_intermediate_anchored P Qm hsat).2, Nat.sub_add_cancel hpos] at hlast
  have hsum : ∑ i : Fin (rows P), rowDelta (rowEnvK P Qm i) = deltaPrefix P Qm (rows P) := by
    unfold deltaPrefix
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [i.isLt]
  rw [hsum, ← hlast]

theorem selector_bool (i : Fin (rows P)) (j : Fin 4) :
    (rowEnvF P Qm i).trace j * ((rowEnvF P Qm i).trace j - 1) = 0 := by
  have hb := (row_parts P Qm hsat i).1
  have hj : bbool (bcur (j : ℕ)) ∈ baseTransitionGates P.optimized.basis := by
    simp [baseTransitionGates, paperBaseGates]
    fin_cases j <;> simp [bbool, bcur]
  have h := hb _ hj
  simpa [bbool, bcur, CoeffExpr.eval] using h

theorem selector_zero_or_one (i : Fin (rows P)) (j : Fin 4) :
    (rowEnvF P Qm i).trace j = 0 ∨ (rowEnvF P Qm i).trace j = 1 := by
  have h := selector_bool P Qm hsat i j
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem selector_sum (i : Fin (rows P)) :
    (rowEnvF P Qm i).trace 0 + (rowEnvF P Qm i).trace 1 +
      (rowEnvF P Qm i).trace 2 + (rowEnvF P Qm i).trace 3 = 1 := by
  have hb := (row_parts P Qm hsat i).1
  have hs : bsum4 VarKind.traceCur ∈ baseTransitionGates P.optimized.basis := by
    simp [baseTransitionGates, paperBaseGates]
  have h := hb _ hs
  simpa [bsum4, CoeffExpr.eval, sub_eq_zero, add_assoc] using h

/-! ## (a) Record lists and the identity -/

def hostileReads : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin (rows P) =>
    rowReadsOf (rowEnvF P Qm i) (rowEnvK P Qm i)).flatten

def hostileVerifies : List (Fin 10 → K) :=
  (List.ofFn fun i : Fin (rows P) =>
    rowVerifiesOf (rowEnvF P Qm i) (rowEnvK P Qm i)).flatten

theorem hostileReads_length_le : (hostileReads P Qm).length ≤ rows P := by
  simp only [hostileReads, List.length_flatten, List.map_ofFn]
  rw [List.sum_ofFn]
  calc ∑ i : Fin (rows P), (rowReadsOf (rowEnvF P Qm i) (rowEnvK P Qm i)).length
      ≤ ∑ _i : Fin (rows P), 1 :=
        Finset.sum_le_sum fun i _ => rowReadsOf_length_le _ _
    _ = rows P := by simp

theorem hostileVerifies_length_le : (hostileVerifies P Qm).length ≤ rows P := by
  simp only [hostileVerifies, List.length_flatten, List.map_ofFn]
  rw [List.sum_ofFn]
  calc ∑ i : Fin (rows P), (rowVerifiesOf (rowEnvF P Qm i) (rowEnvK P Qm i)).length
      ≤ ∑ _i : Fin (rows P), 1 :=
        Finset.sum_le_sum fun i _ => rowVerifiesOf_length_le _ _
    _ = rows P := by simp

def interRecordsOf : FiniteIO.PreChallengeRecords K 10 where
  requests := hostileReads P Qm
  responses := hostileVerifies P Qm

theorem interRecordsOf_lengths :
    (interRecordsOf P Qm).requests.length ≤ rows P ∧
      (interRecordsOf P Qm).responses.length ≤ rows P :=
  ⟨hostileReads_length_le P Qm hsat, hostileVerifies_length_le P Qm hsat⟩

theorem internalPoleIdentity_abstract
    (pole γ : K)
    (hagg : ∀ i : Fin (rows P),
      AggregatorAt (rowEnvK P Qm i) (rowEnvF P Qm i) pole γ)
    (hden : ∀ i : Fin (rows P), pole + Walk.rlc γ (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)) ≠ 0) :
    (∑ i : Fin (rows P),
        algebraMap F K ((rowEnvF P Qm i).trace 2) *
          (pole + Walk.rlc γ (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)))⁻¹) =
      ∑ i : Fin (rows P),
        algebraMap F K ((rowEnvF P Qm i).trace 3) *
          (pole + Walk.rlc γ (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)))⁻¹ := by
  have htel := hostile_intermediate_telescopes P Qm hsat
  have hΔ : ∀ i : Fin (rows P),
      rowDelta (rowEnvK P Qm i) =
        (algebraMap F K ((rowEnvF P Qm i).trace 2) -
          algebraMap F K ((rowEnvF P Qm i).trace 3)) *
          (pole + Walk.rlc γ (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)))⁻¹ :=
    fun i => delta_eq_signed_inv _ _ pole γ (hagg i) (hden i)
  have htel' : ∑ i, ((algebraMap F K ((rowEnvF P Qm i).trace 2) -
        algebraMap F K ((rowEnvF P Qm i).trace 3)) *
        (pole + Walk.rlc γ (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)))⁻¹) = 0 := by
    simpa [hΔ] using htel
  simp only [sub_mul] at htel'
  rw [Finset.sum_sub_distrib] at htel'
  exact sub_eq_zero.mp htel'

theorem internalPoleIdentity
    (hpole : ∀ i : Fin (rows P), (poleSourceMixed (F := F)).eval (rowEnvK P Qm i) (rowEnvF P Qm i) ≠ 0) :
    (∑ i : Fin (rows P),
        algebraMap F K ((rowEnvF P Qm i).trace 2) *
          ((poleSourceMixed (F := F)).eval (rowEnvK P Qm i) (rowEnvF P Qm i))⁻¹) =
      ∑ i : Fin (rows P),
        algebraMap F K ((rowEnvF P Qm i).trace 3) *
          ((poleSourceMixed (F := F)).eval (rowEnvK P Qm i) (rowEnvF P Qm i))⁻¹ := by
  have hagg : ∀ i : Fin (rows P),
      AggregatorAt (rowEnvK P Qm i) (rowEnvF P Qm i)
        (traceInterCoins P Qm).pole (traceInterCoins P Qm).gamma := by
    intro i
    have := aggregatorAt_of_paperAggregator (rowEnvK P Qm i) (rowEnvF P Qm i)
      (aggregator_at P Qm hsat i)
    rwa [traceInterCoins_eq P Qm i] at this
  have hden : ∀ i : Fin (rows P),
      (traceInterCoins P Qm).pole +
        Walk.rlc (traceInterCoins P Qm).gamma (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)) ≠ 0 := by
    intro i
    have h := hpole i
    rw [poleSource_eq_compress] at h
    rw [traceInterCoins_eq P Qm i] at h
    simpa [FiniteIO.compress] using h
  have h := internalPoleIdentity_abstract P Qm hsat
    (traceInterCoins P Qm).pole (traceInterCoins P Qm).gamma hagg hden
  convert h using 1 <;> simp_rw [poleSource_eq_compress, traceInterCoins_eq P Qm,
    FiniteIO.compress]

theorem rowReadsOf_sum (i : Fin (rows P)) (pole γ : K) :
    ((rowReadsOf (rowEnvF P Qm i) (rowEnvK P Qm i)).map
        fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      algebraMap F K ((rowEnvF P Qm i).trace 2) *
        (pole + Walk.rlc γ (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)))⁻¹ := by
  have h01 := selector_zero_or_one P Qm hsat i ⟨2, by decide⟩
  unfold rowReadsOf
  rcases h01 with h0 | h1
  · simp [h0, map_zero]
  · simp [h1, map_one]

theorem rowVerifiesOf_sum (i : Fin (rows P)) (pole γ : K) :
    ((rowVerifiesOf (rowEnvF P Qm i) (rowEnvK P Qm i)).map
        fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      algebraMap F K ((rowEnvF P Qm i).trace 3) *
        (pole + Walk.rlc γ (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)))⁻¹ := by
  have h01 := selector_zero_or_one P Qm hsat i ⟨3, by decide⟩
  unfold rowVerifiesOf
  rcases h01 with h0 | h1
  · simp [h0, map_zero]
  · simp [h1, map_one]

theorem internalPoleIdentity_lists
    (pole γ : K)
    (hagg : ∀ i : Fin (rows P),
      AggregatorAt (rowEnvK P Qm i) (rowEnvF P Qm i) pole γ)
    (hden : ∀ i : Fin (rows P), pole + Walk.rlc γ (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)) ≠ 0) :
    ((hostileReads P Qm).map fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      ((hostileVerifies P Qm).map fun r => (pole + Walk.rlc γ r)⁻¹).sum := by
  have h1 : ((hostileReads P Qm).map fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      ∑ i : Fin (rows P),
        ((rowReadsOf (rowEnvF P Qm i) (rowEnvK P Qm i)).map
          fun r => (pole + Walk.rlc γ r)⁻¹).sum := by
    simp [hostileReads, List.map_flatten, List.map_ofFn, List.sum_ofFn, List.sum_flatten]
  have h2 : ((hostileVerifies P Qm).map fun r => (pole + Walk.rlc γ r)⁻¹).sum =
      ∑ i : Fin (rows P),
        ((rowVerifiesOf (rowEnvF P Qm i) (rowEnvK P Qm i)).map
          fun r => (pole + Walk.rlc γ r)⁻¹).sum := by
    simp [hostileVerifies, List.map_flatten, List.map_ofFn, List.sum_ofFn, List.sum_flatten]
  rw [h1, h2]
  have h := internalPoleIdentity_abstract P Qm hsat pole γ hagg hden
  convert h using 1
  · simp_rw [rowReadsOf_sum P Qm hsat _ pole γ]
  · simp_rw [rowVerifiesOf_sum P Qm hsat _ pole γ]

/-! ## (c) Card bound at `(M, M)` -/

theorem interWork_le :
    (FiniteIO.IOFailureEvent (interRecordsOf P Qm)).card
      ≤ interWork (rows P) (Fintype.card K) := by
  refine le_trans (FiniteIO.IOFailureEvent_card_le (interRecordsOf P Qm)) ?_
  exact OptimizedStrictPackage.ioFailureUnionBound_mono₂ 10
    (interRecordsOf P Qm).requests.length (interRecordsOf P Qm).responses.length
    (rows P) (rows P) (Fintype.card K)
    (hostileReads_length_le P Qm hsat) (hostileVerifies_length_le P Qm hsat)

/-! ## (b) Compressed and record-level permutations -/

omit hsat

include hsat

theorem internalPole_compressed_perm
    (pole γ : K)
    (hagg : ∀ i : Fin (rows P),
      AggregatorAt (rowEnvK P Qm i) (rowEnvF P Qm i) pole γ)
    (hden : ∀ i : Fin (rows P), pole + Walk.rlc γ (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)) ≠ 0)
    (hn1 : (hostileReads P Qm).length < ringChar K)
    (hn2 : (hostileVerifies P Qm).length < ringChar K)
    (hlog : pole ∉ FiniteIO.IOLogDerivEvent (interRecordsOf P Qm) γ) :
    ((hostileReads P Qm).map (Walk.rlc γ)).Perm
      ((hostileVerifies P Qm).map (Walk.rlc γ)) := by
  classical
  set records := interRecordsOf P Qm
  set coins : FiniteIO.IOCoins K := ⟨γ, pole⟩
  have hend_list := internalPoleIdentity_lists P Qm hsat pole γ hagg hden
  have hend : (∑ i, (coins.pole + FiniteIO.reqVals records coins.gamma i)⁻¹) =
      ∑ j, (coins.pole + FiniteIO.respVals records coins.gamma j)⁻¹ := by
    have e1 := FiniteIO.sum_fin_get (hostileReads P Qm)
      (fun r => (pole + Walk.rlc γ r)⁻¹)
    have e2 := FiniteIO.sum_fin_get (hostileVerifies P Qm)
      (fun r => (pole + Walk.rlc γ r)⁻¹)
    rw [← e1, ← e2] at hend_list
    dsimp [records, coins, FiniteIO.reqVals, FiniteIO.respVals, interRecordsOf]
    exact hend_list
  have hhit : coins.pole ∉ FiniteIO.IOPoleHitEvent records coins.gamma := by
    intro hmem
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨v, hv, hz⟩ := hmem
    have hv' : v ∈ hostileReads P Qm ∨ v ∈ hostileVerifies P Qm := by
      simpa [records, interRecordsOf, List.mem_append] using hv
    have hex : ∃ i, rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i) = v := by
      rcases hv' with h | h
      · simp only [hostileReads, List.mem_flatten, List.mem_ofFn] at h
        obtain ⟨l, ⟨i, rfl⟩, hl⟩ := h
        unfold rowReadsOf at hl; split_ifs at hl with hs
        · simp at hl; exact ⟨i, hl.symm⟩
        · simp at hl
      · simp only [hostileVerifies, List.mem_flatten, List.mem_ofFn] at h
        obtain ⟨l, ⟨i, rfl⟩, hl⟩ := h
        unfold rowVerifiesOf at hl; split_ifs at hl with hs
        · simp at hl; exact ⟨i, hl.symm⟩
        · simp at hl
    obtain ⟨i, hi⟩ := hex
    exact (hden i) (by simpa [hi] using hz)
  have hdA := req_denom_ne_of_not_hit coins hhit
  have hdB := resp_denom_ne_of_not_hit coins hhit
  have hfrac := FiniteIO.frac_identity_of_pole_identity records coins hdA hdB hend
    (by simpa [records, coins] using hlog)
  have hmse :
      (∏ i, (Polynomial.X + Polynomial.C (FiniteIO.reqVals records coins.gamma i)))
        = ∏ j, (Polynomial.X + Polynomial.C (FiniteIO.respVals records coins.gamma j)) :=
    (SetEq.mse_ldse_general (p := ringChar K) hn1 hn2 _ _).mpr hfrac
  have hms :
      ((records.requests.map (Walk.rlc γ) : List K) : Multiset K)
        = ((records.responses.map (Walk.rlc γ) : List K) : Multiset K) := by
    refine (IO.prodXaddC_ms_inj _ _).mp ?_
    rw [← denomP_eq_ms_prod, ← denomP_eq_ms_prod]
    simpa [FiniteIO.denomP, FiniteIO.reqVals, FiniteIO.respVals, coins] using hmse
  exact Multiset.coe_eq_coe.mp (by simpa [records, interRecordsOf] using hms)

/-- `hpole` / per-row `hden` is derived from
`pole ∉ IOPoleHitEvent` (the `hgood` / `hfail` half).  `hγ` and `hlog`
are the other two components of `IOFailureEvent`. -/
theorem internalPole_multiset_eq
    (pole γ : K)
    (hagg : ∀ i : Fin (rows P),
      AggregatorAt (rowEnvK P Qm i) (rowEnvF P Qm i) pole γ)
    (hfail : (γ, pole) ∉ FiniteIO.IOFailureEvent (interRecordsOf P Qm))
    (hn1 : (hostileReads P Qm).length < ringChar K)
    (hn2 : (hostileVerifies P Qm).length < ringChar K)
    (hden : ∀ i : Fin (rows P), pole + Walk.rlc γ (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)) ≠ 0) :
    (hostileReads P Qm).Perm (hostileVerifies P Qm) := by
  have hγ : γ ∉ FiniteIO.IORLCCollisionEvent (interRecordsOf P Qm) := fun h =>
    hfail ((FiniteIO.mem_IOFailureEvent_iff).2 (Or.inl h))
  have hlog : pole ∉ FiniteIO.IOLogDerivEvent (interRecordsOf P Qm) γ := fun h =>
    hfail ((FiniteIO.mem_IOFailureEvent_iff).2 (Or.inr (Or.inr h)))
  have hcomp := internalPole_compressed_perm P Qm hsat pole γ hagg hden hn1 hn2 hlog
  refine PairedRecordCountedEvent.perm_of_perm_map_of_injOn (Walk.rlc γ) ?_ hcomp
  intro u hu v hv heq
  exact FiniteIO.rlc_inj_of_not_collision hγ hu hv heq

/-- Active-row `hden` from the priced pole-hit event.  Halt / decompose rows
keep an explicit `hden` (F-A-1 discharges it from a zero-record hit). -/
theorem hden_of_not_hit_of_mem
    (pole γ : K)
    (hhit : pole ∉ FiniteIO.IOPoleHitEvent (interRecordsOf P Qm) γ)
    (i : Fin (rows P))
    (hmem : rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i) ∈
      (interRecordsOf P Qm).requests ++ (interRecordsOf P Qm).responses) :
    pole + Walk.rlc γ (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)) ≠ 0 := by
  intro h0
  apply hhit
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i), hmem, h0⟩

end Deployed

/-! ## (f) Fixtures -/

section Fixture73
set_option maxRecDepth 100000

open ConcreteStrictPackage

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

theorem package73_internalPoleIdentity
    (hmore : BuildableAxisWitness.LaterSeedZeros concreteExecution)
    (hpole : ∀ i : Fin (rows (package73 hmore)),
      (poleSourceMixed (F := F73)).eval (rowEnvK (package73 hmore) (canonicalMemoryTrace (package73 hmore)) i)
        (rowEnvF (package73 hmore) (canonicalMemoryTrace (package73 hmore)) i) ≠ 0) :
    (∑ i : Fin (rows (package73 hmore)),
        algebraMap F73 K73cubic
          ((rowEnvF (package73 hmore) (canonicalMemoryTrace (package73 hmore)) i).trace 2) *
          ((poleSourceMixed (F := F73)).eval (rowEnvK (package73 hmore) (canonicalMemoryTrace (package73 hmore)) i)
        (rowEnvF (package73 hmore) (canonicalMemoryTrace (package73 hmore)) i))⁻¹) =
      ∑ i : Fin (rows (package73 hmore)),
        algebraMap F73 K73cubic
          ((rowEnvF (package73 hmore) (canonicalMemoryTrace (package73 hmore)) i).trace 3) *
          ((poleSourceMixed (F := F73)).eval (rowEnvK (package73 hmore) (canonicalMemoryTrace (package73 hmore)) i)
        (rowEnvF (package73 hmore) (canonicalMemoryTrace (package73 hmore)) i))⁻¹ :=
  internalPoleIdentity (package73 hmore) (canonicalMemoryTrace (package73 hmore))
    (canonicalMemoryTrace_satisfies (package73 hmore) hmore
        (ConcreteStrictPackage.execution_cprimeCoherent ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha)) hpole

theorem concreteExecution_logup_mass_balanced :
    (((GenericHonestData.memoryPubRows concreteExecution.exec).filter
        (fun p => decide (p.st = MemoryTable.MState.read_root))).map
        (fun p => (MemoryTable.pole concreteExecution.cfg.challenges.memoryInputs p.mem p.cprime)⁻¹)).sum =
      (((GenericHonestData.memoryPubRows concreteExecution.exec).filter
            (fun p => decide (p.st = MemoryTable.MState.verify_child))).map
          (fun p => (MemoryTable.pole concreteExecution.cfg.challenges.memoryInputs p.mem p.cprime)⁻¹)).sum :=
  GenericHonestData.execution_logup_mass_balanced concreteExecution

end Fixture73

section Fixture97
set_option maxRecDepth 100000

open OptimizedStrictNonterminalConcrete

local instance prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

theorem packageM_internalPoleIdentity
    (hmoreM : BuildableAxisWitness.LaterSeedZeros MultiRootServedFixture.multiRootExecution)
    (hpole : ∀ i : Fin (rows (packageM hmoreM)),
      (poleSourceMixed (F := F97)).eval (rowEnvK (packageM hmoreM) (canonicalMemoryTrace (packageM hmoreM)) i)
        (rowEnvF (packageM hmoreM) (canonicalMemoryTrace (packageM hmoreM)) i) ≠ 0) :
    (∑ i : Fin (rows (packageM hmoreM)),
        algebraMap F97 K97cubic
          ((rowEnvF (packageM hmoreM) (canonicalMemoryTrace (packageM hmoreM)) i).trace 2) *
          ((poleSourceMixed (F := F97)).eval (rowEnvK (packageM hmoreM) (canonicalMemoryTrace (packageM hmoreM)) i)
        (rowEnvF (packageM hmoreM) (canonicalMemoryTrace (packageM hmoreM)) i))⁻¹) =
      ∑ i : Fin (rows (packageM hmoreM)),
        algebraMap F97 K97cubic
          ((rowEnvF (packageM hmoreM) (canonicalMemoryTrace (packageM hmoreM)) i).trace 3) *
          ((poleSourceMixed (F := F97)).eval (rowEnvK (packageM hmoreM) (canonicalMemoryTrace (packageM hmoreM)) i)
        (rowEnvF (packageM hmoreM) (canonicalMemoryTrace (packageM hmoreM)) i))⁻¹ :=
  internalPoleIdentity (packageM hmoreM) (canonicalMemoryTrace (packageM hmoreM))
    (canonicalMemoryTrace_satisfies (packageM hmoreM) hmoreM
        MultiRootServedFixture.execS_cprimeCoherent) hpole

theorem multiRootExecution_logup_mass_balanced :
    (((GenericHonestData.memoryPubRows MultiRootServedFixture.multiRootExecution.exec).filter
        (fun p => decide (p.st = MemoryTable.MState.read_root))).map
        (fun p => (MemoryTable.pole
          MultiRootServedFixture.multiRootExecution.cfg.challenges.memoryInputs p.mem p.cprime)⁻¹)).sum =
      (((GenericHonestData.memoryPubRows MultiRootServedFixture.multiRootExecution.exec).filter
            (fun p => decide (p.st = MemoryTable.MState.verify_child))).map
          (fun p => (MemoryTable.pole
            MultiRootServedFixture.multiRootExecution.cfg.challenges.memoryInputs p.mem p.cprime)⁻¹)).sum :=
  GenericHonestData.execution_logup_mass_balanced
    MultiRootServedFixture.multiRootExecution

end Fixture97


section PairedRecords
open OptimizedHostileTimestamps
open OptimizedStrictFullPackage

variable {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
variable (Qc : Fin P.computeChip.rap.w → F[X])
variable (Qm : Fin P.memoryChip.rap.w → F[X])
variable (c : OptimizedProductionChallengeTuple K F)

set_option maxRecDepth 20000 in
theorem rowEnvF_eq_memoryBaseEnv (i : Fin (rows P)) :
    rowEnvF P Qm i = P.memoryBaseEnv Qm i := rfl

theorem rowEnvK_eq_memorySourceEnv (i : Fin (rows P)) :
    rowEnvK P Qm i = P.memorySourceEnv Qm i := by
  unfold rowEnvK OptimizedFullStrictNockVMROMPackage.memorySourceEnv
  rw [memorySourceTemplate_col0]
  rfl

theorem rowRecord_eq_memorySourceEnv_trace (i : Fin (rows P)) :
    rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i) =
      OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
        (P.memoryBaseEnv Qm i) := by
  simp only [rowRecord]
  rw [rowEnvK_eq_memorySourceEnv, rowEnvF_eq_memoryBaseEnv]

theorem hostileReads_eq_interReads :
    hostileReads P Qm = P.hostileInterReads Qm := by
  unfold hostileReads rowReadsOf
    OptimizedFullStrictNockVMROMPackage.hostileInterReads
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_))
  rw [rowEnvF_eq_memoryBaseEnv, rowEnvK_eq_memorySourceEnv]
  rfl

theorem hostileVerifies_eq_interVerifies :
    hostileVerifies P Qm = P.hostileInterVerifies Qm := by
  unfold hostileVerifies rowVerifiesOf
    OptimizedFullStrictNockVMROMPackage.hostileInterVerifies
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_))
  rw [rowEnvF_eq_memoryBaseEnv, rowEnvK_eq_memorySourceEnv]
  rfl

theorem interRecordsOf_eq_hostileInterRecords :
    interRecordsOf P Qm = P.hostileInterRecords Qm := by
  simp only [interRecordsOf, OptimizedFullStrictNockVMROMPackage.hostileInterRecords]
  rw [hostileReads_eq_interReads, hostileVerifies_eq_interVerifies]

/-- All-row pole-hit from the priced `interFailurePairs`. -/
theorem allRow_not_hit_of_interFailure
    (hinter : (c.2.1.1, c.2.2.2.interPole) ∉
      interFailurePairs (P.hostileInterRecords Qm) (P.memorySourceEnv Qm)
        (P.memoryBaseEnv Qm)) :
    c.2.2.2.interPole ∉
      FiniteIO.IOPoleHitEvent
        ⟨List.ofFn (fun i : Fin (rows P) =>
            rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)), []⟩
        c.2.1.1 := by
  intro hhit
  apply hinter
  refine Finset.mem_union.mpr (Or.inr ?_)
  have hrec :
      List.ofFn (fun i : Fin (rows P) => rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)) =
        List.ofFn (fun i : Fin (rows P) =>
          OptimizedMemoryHostileAccumulator.rowRecord (P.memorySourceEnv Qm i)
            (P.memoryBaseEnv Qm i)) := by
    refine congrArg List.ofFn (funext fun i => ?_)
    exact rowRecord_eq_memorySourceEnv_trace (P := P) Qm i
  simp only [allRowPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hrec] at hhit
  exact hhit

theorem hden_of_allRow_not_hit
    (hhit : c.2.2.2.interPole ∉
      FiniteIO.IOPoleHitEvent
        ⟨List.ofFn (fun i : Fin (rows P) =>
            rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)), []⟩
        c.2.1.1)
    (i : Fin (rows P)) :
    c.2.2.2.interPole + Walk.rlc c.2.1.1 (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)) ≠ 0 := by
  intro h0
  apply hhit
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i), ?_, h0⟩
  simp [List.mem_ofFn]

/-- At any accepted `(Qc, Qm, c)` outside the consumed failure
event, the memory table's committed `read_root` records are a permutation of its
`verify_child` records.  `hpole` is gone: `pole ≠ 0` / `hden`
are derived from `c ∉ optimizedFailureEvent` (the all-row pole-hit half of
`interFailurePairs`). -/
theorem optimizedFullStrict_paired_records
    (S : OptimizedFullStrictThm54Statement P)
    (hacc : P.OptimizedHistoricalAcceptanceAt Qc Qm c)
    (hgood : c ∉ P.optimizedFailureEvent Qc Qm)
    (hK : rows P < ringChar K) :
    (hostileReads P Qm).Perm (hostileVerifies P Qm) := by
  have hsat := hacc.memory_satisfies
  have hc := P.optimizedFailureEvent_good_components Qc Qm c hgood
  have hinter := hc.2.2.2.1
  have hfail : (c.2.1.1, c.2.2.2.interPole) ∉
      FiniteIO.IOFailureEvent (interRecordsOf P Qm) := by
    intro h
    apply hinter
    refine Finset.mem_union.mpr (Or.inl ?_)
    rwa [interRecordsOf_eq_hostileInterRecords] at h
  have hagg : ∀ i : Fin (rows P),
      AggregatorAt (rowEnvK P Qm i) (rowEnvF P Qm i)
        c.2.2.2.interPole c.2.1.1 := by
    intro i
    have hpin := hacc.memory_intermediate_pole i
    have hγ := (hacc.memory_sampled_coins i).1
    have happ := aggregatorAt_of_paperAggregator (rowEnvK P Qm i) (rowEnvF P Qm i)
      (aggregator_at P Qm hsat i)
    have hcoins : chipInterCoins (rowEnvK P Qm i) =
        ⟨c.2.1.1, c.2.2.2.interPole⟩ := by
      simp [chipInterCoins, rowEnvK]
      constructor
      · exact hγ
      · exact hpin
    simpa [hcoins] using happ
  have hhitAll := allRow_not_hit_of_interFailure P Qm c hinter
  have hden : ∀ i : Fin (rows P),
      c.2.2.2.interPole + Walk.rlc c.2.1.1 (rowRecord (rowEnvK P Qm i) (rowEnvF P Qm i)) ≠ 0 :=
    hden_of_allRow_not_hit P Qm c hhitAll
  have hn1 : (hostileReads P Qm).length < ringChar K :=
    lt_of_le_of_lt (hostileReads_length_le P Qm hsat) hK
  have hn2 : (hostileVerifies P Qm).length < ringChar K :=
    lt_of_le_of_lt (hostileVerifies_length_le P Qm hsat) hK
  exact internalPole_multiset_eq P Qm hsat c.2.2.2.interPole c.2.1.1
    hagg hfail hn1 hn2 hden

end PairedRecords

end
end MemoryInternalPole
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.internalPoleIdentity
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.internalPoleIdentity_lists
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.internalPole_compressed_perm
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.internalPole_multiset_eq
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.optimizedFullStrict_paired_records
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.interWork_le
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.proposedInterPole_is_pole_disciplined
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.pole_ne_zero_of_not_hit_zero_record
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.paper_to_deployed_of_not_hit_zero_record
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.identity_of_perm
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.package73_internalPoleIdentity
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.packageM_internalPoleIdentity
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.concreteExecution_logup_mass_balanced
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.multiRootExecution_logup_mass_balanced
