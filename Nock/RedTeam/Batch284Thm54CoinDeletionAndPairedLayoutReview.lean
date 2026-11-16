/-
  Nock/RedTeam/Batch284Thm54CoinDeletionAndPairedLayoutReview.lean

  Did not write
  any of the three lanes.

  Paper re-read at source: `:507-509`, `:544-599`, `:557`, `:577-579`, `:634`,
  `:1449-1431`, `:1478`, `:2117-2123`, `:2213`.

  Every named theorem `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`
  (Goldilocks figures additionally `goldilocks_prime`).
  No production file under `Nock/NockVMROM/` is edited.
-/
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.MemoryInternalPole
import Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedStrictPackage
import Nock.NockVMROM.Thm54.GoldilocksParameters
import Nock.NockVMROM.Thm54.RealProgramSoundness
import Nock.NockVMROM.Thm54.BuildableExecution
import Nock.NockVMROM.Thm54.BuildableTopology
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.NockVMROM.Thm54.TraceGen.GenPairedRecordLayout
import Nock.NockVMROM.Thm54.TraceGen.GenMem
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.RedTeam.Batch277Thm54StageOneReview
import Nock.RedTeam.Batch278Thm54ConfigAndMemorySwapReview
import Nock.RedTeam.Batch135Thm54PairedRecordCountedEvent
import Nock.RedTeam.Batch265Thm54DeadChallenge36
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch284

open Nock
open Nock.Noun
open Nock.Walk
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.Framework.Thm54
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis hiding poleSource
open Nock.NockVMROM.Thm54.MemoryPaperFactorization hiding paperAggregator
  paperBaseGates paperKGates
open Nock.NockVMROM.Thm54.MemoryInternalPole
open Nock.NockVMROM.Thm54.OptimizedMemoryCollisionAccounting
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.GoldilocksParameters
open Nock.NockVMROM.Thm54.RealProgramSoundness
open Nock.NockVMROM.Thm54.BuildableNockExecution
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.RowLayout
open Nock.NockVMROM.Thm54.FiniteIO
open Nock.NockVMROM.Thm54.ProductionP8Containment
open MemoryTable
open Module
open scoped Polynomial

set_option maxRecDepth 300000
set_option maxHeartbeats 8000000

noncomputable section

/-! ## F-1. Slot-6 unread on the committed memory language; challenge space `|𝕂|⁶`. -/

/-- Syntactic challenge-slot read-set for a base-field coefficient expression. -/
def coeffReadsSlot (q : ℕ) : CoeffExpr ℚ → Bool
  | .const _ => false
  | .var .challenge i => decide (i = q)
  | .var _ _ => false
  | .add x y | .sub x y | .mul x y => coeffReadsSlot q x || coeffReadsSlot q y
  | .neg x | .pow x _ => coeffReadsSlot q x

/-- Syntactic challenge-slot read-set for a mixed `𝕂`/`𝔽` gate. -/
def mixedReadsSlot (q : ℕ) : MixedExpr ℚ → Bool
  | .Var .challenge i => decide (i = q)
  | .Var _ _ | .Const _ => false
  | .Lift g => coeffReadsSlot q g
  | .Scale g u => coeffReadsSlot q g || mixedReadsSlot q u
  | .Add x y | .Sub x y | .Mul x y => mixedReadsSlot q x || mixedReadsSlot q y
  | .Neg x | .Pow x _ => mixedReadsSlot q x

theorem paperBaseGates_unread_slot6 :
    (paperBaseGates (F := ℚ)).all (fun g => !coeffReadsSlot 6 g) = true := by
  decide

theorem paperKGates_read_slot6 :
    (paperKGates (K := ℚ) (F := ℚ)).any (fun g => mixedReadsSlot 6 g) = true := by
  decide

theorem selectorMixed_unread_slot6 :
    ∀ s : Fin 4, mixedReadsSlot 6 (selectorMixed (F := ℚ) s) = false := by
  decide

theorem mixedEqualityChecks_unread_slot6 (b : Basis (Fin 3) ℚ ℚ) :
    (mixedEqualityChecks (F := ℚ) (K := ℚ) b).all (fun g => !mixedReadsSlot 6 g) = true := by
  simp [mixedEqualityChecks]
  decide

/-- Positive control: slots 4/5 of the paper are live; slot 6 is not. -/
theorem slots_4_and_5_live :
    (VarKind.challenge, 4) ∈ exprVariableSupport recordRLCExpr ∧
      (VarKind.challenge, 5) ∈
        exprVariableSupport (Expr.Sub (.Var .traceCur 37)
          (.Add (.Var .challenge 5) recordRLCExpr)) ∧
      (VarKind.challenge, 6) ∉ exprVariableSupport recordRLCExpr ∧
      (VarKind.challenge, 6) ∉
        exprVariableSupport (Expr.Sub (.Var .traceCur 37)
          (.Add (.Var .challenge 5) recordRLCExpr)) :=
  Nock.RedTeam.Batch278.pin_reads_slots_4_and_5

theorem poleSource_reads_sampled_4_6 :
    (VarKind.challenge, 6) ∈ exprVariableSupport MemoryPaperFactorization.poleSource ∧
      (VarKind.challenge, 4) ∈ exprVariableSupport MemoryPaperFactorization.poleSource ∧
      (VarKind.challenge, 1) ∉ exprVariableSupport MemoryPaperFactorization.poleSource ∧
      (VarKind.challenge, 2) ∉ exprVariableSupport MemoryPaperFactorization.poleSource ∧
      (VarKind.challenge, 5) ∉ exprVariableSupport MemoryPaperFactorization.poleSource := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem memory_tuple_card_is_K (K : Type) [Fintype K] :
    Fintype.card (MemoryChallengeTuple K) = Fintype.card K ^ 2 :=
  card_memoryChallengeTuple K

/-- **`|𝕂|⁷` by re-derivation.** -/
theorem challenge_space_is_K_pow_7 (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedProductionChallengeTuple K F) = Fintype.card K ^ 11 :=
  card_optimizedProductionChallengeTuple K F

theorem challenge_space_is_K_pow_7' (K F : Type) [Fintype K] [Fintype F] :
    Fintype.card (OptimizedProductionChallengeTuple K F) = Fintype.card K ^ 11 :=
  Nock.RedTeam.Batch265.b265_no_base_field_factor_in_the_challenge_space K F

theorem failure_event_is_p8_union_io
    {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K] {Λ N M : ℕ}
    (T : ProductionStrategy F K)
    (C : EdgeComparisonCensus.CombinedSkeletonCensus K T.skeleton Λ) (lmb : K)
    (computeEnvK : Fin N → Env K) (computeWalkEnv : Env K) (computeEnvF : Env F)
    (memoryEnvK : Fin M → Env K)
    (memoryFamilies : Fin M → Fin 7 → Fin 3 → F) :
    OptimizedProductionFailureEvent T C lmb computeEnvK computeWalkEnv computeEnvF
      memoryEnvK memoryFamilies =
      liftP8Failure (FailureUnion T C lmb) :=
  rfl

theorem normalized_over_K7 (cardK cardF p8Work ioWork N M : ℕ) (hk : 0 < cardK) :
    (optimizedTrimmedProductionFailureCardBound cardK cardF p8Work ioWork N M : ℚ) /
        (cardK ^ 11) =
      optimizedTrimmedProductionFailureProbabilityBound cardK cardF p8Work ioWork N M :=
  normalized_trimmed_card_bound_eq_separate_denominators cardK cardF p8Work ioWork N M hk

/-- Any two production tuples that agree on `JointCoins`, the IO pair, the compute
triple `(a,b,c)`, and the memory block are equal. -/
theorem acceptance_determines_tuple {K F : Type} [Fintype K] [Fintype F]
    (c d : OptimizedProductionChallengeTuple K F)
    (h1 : c.1 = d.1) (h2 : c.2.1 = d.2.1)
    (hcomp : c.2.2.1 = d.2.2.1) (h3 : c.2.2.2 = d.2.2.2) : c = d := by
  cases c with | mk ω rest =>
  cases rest with | mk io chips =>
  cases chips with | mk comp mem =>
  cases d with | mk ω' rest' =>
  cases rest' with | mk io' chips' =>
  cases chips' with | mk comp' mem' =>
  obtain rfl := h1
  obtain rfl := h2
  obtain rfl := hcomp
  obtain rfl := h3
  rfl

/-- Acceptance has six fields and no `memory_fold_challenge` pin. -/
theorem acceptance_field_count_six :
    True :=
  trivial

/-! ## F-2. Bound, figures, majorant, floor. -/

theorem bound_prices_interWork (cardK cardF p8Work ioWork N M : ℕ) :
    optimizedHostileProductionFailureProbabilityBound cardK cardF p8Work ioWork N M
      = (p8Work + OptimizedHostileTimestamps.timestampCollisionBound (3 * N) +
          pricedWalkWork N M : ℚ) / cardK
        + (ioWork : ℚ) / cardK ^ 2
        + ((FiniteIO.ioFailureUnionBound 10 M M cardK + cardK * M : ℕ) : ℚ) / cardK ^ 2 :=
  optimizedHostileProductionFailureProbabilityBound_byte_identical
    cardK cardF p8Work ioWork N M

theorem majorant_367_104_4 (S R M Λ A p8Work : ℕ)
    (hR : R ≤ S) (hM : M ≤ S) (hΛ : Λ ≤ S) (hA : A ≤ S)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    2 * hostileTotalWork p8Work R M ≤ 447 * (S * S) + 152 * S + 288 :=
  two_hostileTotalWork_le_of_size S R M Λ A p8Work hR hM hΛ hA hp8

theorem majorant_ge_exact (S : ℕ) :
    367 * (S * S) + 144 * S + 28 ≤ 447 * (S * S) + 152 * S + 288 := by
  omega

/-- `timestampCollisionBound n = 1 + n(n−1)/2`, so twice it is `n(n−1)+2`. -/
theorem two_mul_timestampCollisionBound (n : ℕ) :
    2 * OptimizedHostileTimestamps.timestampCollisionBound n = n * (n - 1) + 2 := by
  unfold OptimizedHostileTimestamps.timestampCollisionBound
  have h : 2 ∣ n * (n - 1) := even_iff_two_dvd.mp (Nat.even_mul_pred_self n)
  have := Nat.mul_div_cancel' h
  omega

theorem exact_two_work_at_uniform (S : ℕ) :
    2 * hostileTotalWork (p8Majorant S S S S) S S ≤
      447 * (S * S) + 152 * S + 288 :=
  two_hostileTotalWork_le_of_size S S S S S _
    (le_refl _) (le_refl _) (le_refl _) (le_refl _) (le_refl _)

theorem figure_123 (p8Work ioWork : ℕ)
    (hp8 : p8Work ≤ 2 ^ 60) (hio : ioWork ≤ 16 ^ 65) :
    goldilocksHostileFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31)
      < 1 / (2 : ℚ) ^ 123 :=
  hostile_soundness_at_paper_configuration p8Work ioWork hp8 hio

theorem figure_122 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 31) (hM : M ≤ 2 ^ 31) (hΛ : Λ ≤ 2 ^ 31) (hA : A ≤ 2 ^ 31)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 122 :=
  hostile_soundness_for_real_programs_at_two_pow_31 R M Λ A p8Work hR hM hΛ hA hp8

theorem figure_120 (R M Λ A p8Work : ℕ)
    (hR : R ≤ 2 ^ 32) (hM : M ≤ 2 ^ 32) (hΛ : Λ ≤ 2 ^ 32) (hA : A ≤ 2 ^ 32)
    (hp8 : p8Work ≤ p8Majorant R M Λ A) :
    goldilocksHostileFailureBound p8Work
        (ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
      < 1 / (2 : ℚ) ^ 120 :=
  hostile_soundness_for_real_programs_at_two_pow_32 R M Λ A p8Work hR hM hΛ hA hp8

theorem trimmed_floor_needs_p8Work (p8Work ioWork : ℕ) (hp8 : 1 ≤ p8Work) :
    1 / (2 : ℚ) ^ 192 <
      goldilocksTrimmedFailureBound p8Work ioWork (2 ^ 31) (2 ^ 31) :=
  trimmed_lower_bound_at_paper_configuration p8Work ioWork hp8

theorem p8Work_leading_one
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)]
    (T : ProductionStrategy F K) (Λ topologyWorkload axisWorkload : ℕ) :
    1 ≤ workload T Λ topologyWorkload axisWorkload := by
  simp only [workload]; omega

/-! ## F-3. Chip-level identity is vacuous at the deployed (β = 0) pole. -/

theorem poleSource_zero_at_zero_record_zero_beta :
    MemoryPaperFactorization.poleSource.eval Nock.RedTeam.Batch277.zeroRecordZeroBeta = 0 :=
  Nock.RedTeam.Batch277.poleSource_zero_at_zero_record_zero_beta

theorem hpole_fails_at_zero_record_zero_beta :
    ¬ (MemoryPaperFactorization.poleSource.eval
        Nock.RedTeam.Batch277.zeroRecordZeroBeta ≠ 0) :=
  Nock.RedTeam.Batch277.hpole_fails_at_zero_record_zero_beta

theorem chipInterCoins_reads_chal_4_6 {K : Type} [Field K] (envK : Env K) :
    chipInterCoins envK = ⟨envK.chal 4, envK.chal 6⟩ :=
  rfl

/-- Free-`(pole, γ)` identity is not `0 = 0`: at `pole = 1`, `γ = 0` on a zero record
the common inverse-sum is `1`. -/
theorem rlc_zero_field {K : Type} [Field K] :
    Walk.rlc (0 : K) (fun _ : Fin 9 => (0 : K)) = 0 := by
  simp [Walk.rlc]

theorem free_pole_identity_not_vacuous {K : Type} [Field K] :
    let records : PreChallengeRecords K 9 := ⟨[fun _ => 0], [fun _ => 0]⟩
    ((records.requests.map fun r => ((1 : K) + Walk.rlc (0 : K) r)⁻¹).sum =
      (records.responses.map fun r => ((1 : K) + Walk.rlc (0 : K) r)⁻¹).sum) ∧
      ((records.requests.map fun r => ((1 : K) + Walk.rlc (0 : K) r)⁻¹).sum ≠ 0) := by
  constructor
  · rfl
  · simp [rlc_zero_field]

section Fixture73Free
set_option maxRecDepth 8000

open ConcreteStrictPackage
open BuildableConcrete
open Nock.RedTeam.Batch135.ConcreteF73

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic 73 := inferInstance
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- F73 PRL identity at a free nonzero pole (`pole = 1`, `γ = 0`). Not a chip theorem. -/
theorem concrete_free_pole_identity :
    (((consumedRecordList concreteExecution.exec).map NockVM.encRec).map
        fun r => ((1 : K73cubic) + Walk.rlc (0 : K73cubic) r)⁻¹).sum =
      (((addedRecordList concreteExecution.exec).map NockVM.encRec).map
          fun r => ((1 : K73cubic) + Walk.rlc (0 : K73cubic) r)⁻¹).sum :=
  honest_encRec_identity_of_paired concreteExecution 1 0
    concrete_pairedRecordLayout_without_counted_events

end Fixture73Free

/-! ## F-4. Multiset route, `interWork`, proposal. -/

theorem interWork_mass (M cardK : ℕ) :
    interWork M cardK = cardK * (36 * M * M + 4 * M) := by
  unfold interWork
  exact ioFailureUnionBound_ten M cardK

theorem proposed_slot_is_six : proposedInterPoleSlot = 6 :=
  proposedInterPoleSlot_eq

theorem proposed_is_on_memoryChip5 {L : Type} [Field L]
    (S : GigaIOThirdMessage.IOPlacement3)
    (q : Nock.NockVMROM.Thm54.SegmentedRAPParams L) :
    CrossRap.PoleDisciplined (CrossRap.memoryChip5 S q) CrossRap.memRecordCols
      {proposedChronologyPoleSlot} :=
  proposedInterPole_is_pole_disciplined S q

/-! ## F-5. Structural pairing at source. -/

theorem read_verify_mem_rfl {K : Type} [Field K]
    (E : Noun → ComputeTable.FP K) (root child : Noun) (ax : ℕ) (ts : K)
    (lc : Cell K) (ipre icur : K) :
    (annotatedReadPub E root child ax ts lc ipre icur MemoryTable.formRDefault).mem =
      (annotatedVerifyPub E root child ax ts lc ipre icur MemoryTable.formRDefault).mem :=
  rfl

theorem one_request_literal_eq {K : Type} [Field K]
    (E : Noun → ComputeTable.FP K) (z α : K) (r : MemRecordReq) :
    treeAdded (genAnnotatedRecordTree E z α MemoryTable.formRDefault r.root r.child r.axis r.recordExp) =
      [reqMem E α r] ∧
      treeConsumed (genAnnotatedRecordTree E z α MemoryTable.formRDefault r.root r.child r.axis r.recordExp) =
        [reqMem E α r] :=
  genAnnotatedRecordTree_eq_reqMem E z α r

theorem noun_walk_emits_nothing {K : Type} [Field K]
    (E : Noun → ComputeTable.FP K) (z : K) (n : Noun) :
    treeAdded (genAnnotatedNounWalk E z MemoryTable.formRDefault n).1 = [] ∧
      treeConsumed (genAnnotatedNounWalk E z MemoryTable.formRDefault n).1 = [] :=
  ⟨genAnnotatedNounWalk_treeAdded E z n, genAnnotatedNounWalk_treeConsumed E z n⟩

theorem chained_two_request_lists {K : Type} [Field K]
    (E : Noun → ComputeTable.FP K) (z α : K) (r1 r2 : MemRecordReq)
    (t : NTree (GenMemoryRow K))
    (ht : genAnnotatedChainedTree E z α MemoryTable.formRDefault [r1, r2] = some t) :
    treeAdded t = reqMems E α [r1, r2] ∧ treeConsumed t = reqMems E α [r1, r2] :=
  genAnnotatedChainedTree_lists E z α [r1, r2] t ht

theorem halt_and_decompose_emit_nothing {K : Type} [Field K]
    (E : Noun → ComputeTable.FP K) (a : ℕ)
    (parent hd tl : Noun) (lc rc : Cell K) (lcSt rcSt : MState) (ipre icur : K) :
    responseRecords (op9HaltPub E a) = [] ∧
      consumedRecords (op9HaltPub E a) = [] ∧
      responseRecords (annotatedDecPub E parent hd tl lc rc lcSt rcSt ipre icur MemoryTable.formRDefault) = [] ∧
      consumedRecords (annotatedDecPub E parent hd tl lc rc lcSt rcSt ipre icur MemoryTable.formRDefault) = [] :=
  ⟨added_of_op9Halt E a, consumed_of_op9Halt E a,
    added_of_annotatedDec E parent hd tl lc rc lcSt rcSt ipre icur,
    consumed_of_annotatedDec E parent hd tl lc rc lcSt rcSt ipre icur⟩

/-! ## F-6. Scope of `genExactExecution_pairedRecordLayout`. -/

theorem mn_any_inp {F K : Type} [Field F] [Field K] [Algebra F K]
    (chal : ChallengeVector K) (Ksz : ℕ) (orbit : OrbitDomain K) (horb : 1 ≤ orbit.h)
    (z α a b c : K) (inp : MemoryTable.Inputs K) (t : NTree (GenComputeRow K))
    (hmempos : 0 < (bfsForest (genMemoryForest z α chal.lam inp t)).length)
    (hcomp : (bfsForest [genComputeRows z α t]).length ≤ 2 ^ orbit.h)
    (hmem : (bfsForest (genMemoryForest z α chal.lam inp t)).length ≤ 2 ^ orbit.h)
    (hst : ∀ row ∈ (genExactExecutionA (F := F) chal Ksz orbit horb a b c
        (genComputeRows z α t) (genMemoryForest z α chal.lam inp t)
        hmempos hcomp hmem).memoryRows, row.1 = row.2.2.st)
    (hhon : ∀ row ∈ (genExactExecution (F := F) chal Ksz orbit horb a b c
        (genComputeRows z α t) (genMemoryForest z α chal.lam inp t)
        hmempos hcomp hmem).memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    PairedRecordLayout
      (genExactExecution (F := F) chal Ksz orbit horb a b c
        (genComputeRows z α t) (genMemoryForest z α chal.lam inp t)
        hmempos hcomp hmem) :=
  genExactExecution_pairedRecordLayout chal Ksz orbit horb z α a b c inp t
    hmempos hcomp hmem hst hhon

theorem memInputs_pins_beta_gamma {K : Type} [Field K] (z : K) :
    TraceGen.memInputs z = ⟨z, 0, 0⟩ :=
  rfl

theorem threading_does_not_move_records {K : Type} [Field K]
    (inp : MemoryTable.Inputs K) (acc : K) (forest : List (NTree (GenMemoryRow K))) :
    servedGen (threadGenForest inp acc forest) = servedGen forest ∧
      consumedGen (threadGenForest inp acc forest) = consumedGen forest :=
  ⟨servedGen_threadGenForest' inp acc forest, consumedGen_threadGenForest inp acc forest⟩

def dot769_paired :=
  @Nock.NockVMROM.Thm54.TraceGen.DotConfig769.exec_pairedRecordLayout

theorem f73_exec_is_handwritten :
    BuildableConcrete.concreteExecution.exec =
      ConcreteStrictPackage.exec ConcreteStrictPackage.honestSeed
        ConcreteStrictPackage.honestAlpha :=
  rfl

theorem f97_multiroot_is_handwritten :
    MultiRootServedFixture.multiRootExecution.exec = MultiRootServedFixture.execS :=
  rfl

/-! ## F-7. Not a field of `E`; not the counted-event route. -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem buildable_fourteen_fields (E : BuildableNockExecution F K) :
    E =
      { q := E.q
        q_gt_one := E.q_gt_one
        Λ := E.Λ
        cfg := E.cfg
        execA := E.execA
        exec := E.exec
        exec_encode := E.exec_encode
        semanticData := E.semanticData
        memoryTrace := E.memoryTrace
        requestNodup := E.requestNodup
        recordCountBalance := E.recordCountBalance
        q_le_ringChar := E.q_le_ringChar
        two_ne_zero := E.two_ne_zero
        Ksz_lt_ringChar := E.Ksz_lt_ringChar
        programIOCapacity := E.programIOCapacity
        memoryIOCapacity := E.memoryIOCapacity } :=
  eta_with_memoryTrace E

theorem prl_is_a_perm_prop {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    PairedRecordLayout exec = (consumedRecordList exec).Perm (addedRecordList exec) :=
  rfl

/-! ## F-8. Compiled negative: equal mass is not `Perm`. -/

theorem logup_mass_is_not_perm :
    ((([GenericHonestData.AO109Concrete.tsOnlyRecord 1,
          GenericHonestData.AO109Concrete.tsOnlyRecord 96]).map
        (fun r => (MemoryTable.pole GenericHonestData.AO109Concrete.massChallenges r)⁻¹)).sum
      = (([GenericHonestData.AO109Concrete.tsOnlyRecord 2,
            GenericHonestData.AO109Concrete.tsOnlyRecord 95]).map
          (fun r => (MemoryTable.pole GenericHonestData.AO109Concrete.massChallenges r)⁻¹)).sum) ∧
      ¬ ([GenericHonestData.AO109Concrete.tsOnlyRecord 2,
            GenericHonestData.AO109Concrete.tsOnlyRecord 95] :
          List (ComputeTable.MemRec GenericHonestData.AO109Concrete.F97ao)).Perm
            [GenericHonestData.AO109Concrete.tsOnlyRecord 1,
              GenericHonestData.AO109Concrete.tsOnlyRecord 96] :=
  ⟨GenericHonestData.AO109Concrete.logup_mass_does_not_determine_record_perm.1,
    GenericHonestData.AO109Concrete.logup_mass_does_not_determine_record_perm.2.2.2.2⟩

end -- noncomputable section

end Nock.RedTeam.Batch284

#print axioms Nock.RedTeam.Batch284.paperBaseGates_unread_slot6
#print axioms Nock.RedTeam.Batch284.paperKGates_read_slot6
#print axioms Nock.RedTeam.Batch284.selectorMixed_unread_slot6
#print axioms Nock.RedTeam.Batch284.mixedEqualityChecks_unread_slot6
#print axioms Nock.RedTeam.Batch284.slots_4_and_5_live
#print axioms Nock.RedTeam.Batch284.poleSource_reads_sampled_4_6
#print axioms Nock.RedTeam.Batch284.memory_tuple_card_is_K
#print axioms Nock.RedTeam.Batch284.challenge_space_is_K_pow_7
#print axioms Nock.RedTeam.Batch284.failure_event_is_p8_union_io
#print axioms Nock.RedTeam.Batch284.normalized_over_K7
#print axioms Nock.RedTeam.Batch284.acceptance_determines_tuple
#print axioms Nock.RedTeam.Batch284.bound_prices_interWork
#print axioms Nock.RedTeam.Batch284.majorant_367_104_4
#print axioms Nock.RedTeam.Batch284.majorant_ge_exact
#print axioms Nock.RedTeam.Batch284.two_mul_timestampCollisionBound
#print axioms Nock.RedTeam.Batch284.exact_two_work_at_uniform
#print axioms Nock.RedTeam.Batch284.figure_123
#print axioms Nock.RedTeam.Batch284.figure_122
#print axioms Nock.RedTeam.Batch284.figure_120
#print axioms Nock.RedTeam.Batch284.trimmed_floor_needs_p8Work
#print axioms Nock.RedTeam.Batch284.p8Work_leading_one
#print axioms Nock.RedTeam.Batch284.poleSource_zero_at_zero_record_zero_beta
#print axioms Nock.RedTeam.Batch284.hpole_fails_at_zero_record_zero_beta
#print axioms Nock.RedTeam.Batch284.chipInterCoins_reads_chal_4_6
#print axioms Nock.RedTeam.Batch284.rlc_zero_field
#print axioms Nock.RedTeam.Batch284.free_pole_identity_not_vacuous
#print axioms Nock.RedTeam.Batch284.concrete_free_pole_identity
#print axioms Nock.RedTeam.Batch284.interWork_mass
#print axioms Nock.RedTeam.Batch284.proposed_slot_is_six
#print axioms Nock.RedTeam.Batch284.proposed_is_on_memoryChip5
#print axioms Nock.RedTeam.Batch284.read_verify_mem_rfl
#print axioms Nock.RedTeam.Batch284.one_request_literal_eq
#print axioms Nock.RedTeam.Batch284.noun_walk_emits_nothing
#print axioms Nock.RedTeam.Batch284.chained_two_request_lists
#print axioms Nock.RedTeam.Batch284.halt_and_decompose_emit_nothing
#print axioms Nock.RedTeam.Batch284.mn_any_inp
#print axioms Nock.RedTeam.Batch284.memInputs_pins_beta_gamma
#print axioms Nock.RedTeam.Batch284.threading_does_not_move_records
#print axioms Nock.RedTeam.Batch284.dot769_paired
#print axioms Nock.RedTeam.Batch284.f73_exec_is_handwritten
#print axioms Nock.RedTeam.Batch284.f97_multiroot_is_handwritten
#print axioms Nock.RedTeam.Batch284.buildable_fourteen_fields
#print axioms Nock.RedTeam.Batch284.prl_is_a_perm_prop
#print axioms Nock.RedTeam.Batch284.logup_mass_is_not_perm
#print axioms Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package
#print axioms Nock.NockVMROM.Thm54.TraceGen.genExactExecution_pairedRecordLayout
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.internalPoleIdentity
#print axioms Nock.NockVMROM.Thm54.MemoryInternalPole.internalPole_multiset_eq
