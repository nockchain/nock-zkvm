/-
  The statement-visible cores
  of the compute and memory families (no Kfp, Key, RecordView, SeedSpec, tree), plus the IO layer
  (also free of Kfp).  Additive; no existing module changed.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.SVFrameG

open Nock Nock.Framework Nock.Walk Nock.ComputeTable Nock.MemoryTable Nock.FieldEmbedding
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open scoped Polynomial

/-- The statement-visible part of a compute family. -/
structure CompCore (F K Kio : Type) [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    [Fintype F] [Field Kio] (Φ : CoinFrame) (hC : ℕ) (S : MemShape) (C : TableSpec) (nAcc : ℕ) where
  Msg0 : Type
  chip : VerifierData F K hC S → Msg0 → (Fin nAcc → Kio) → Coins Φ K → FixedPreprocessingRAP F
  chip_width : ∀ V x ρ χ, (chip V x ρ χ).rap.w = C.width
  reqBound : VerifierData F K hC S → Fin nAcc → ℕ
  summands : VerifierData F K hC S → Msg0 →
    List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))
  Honest : Type
  honestV : Honest → VerifierData F K hC S
  honestQ : Honest → Coins Φ K → Fin C.width → F[X]
  honestReq : Honest → Coins Φ K → Fin nAcc → Kio
  honest_staged : ∀ H, StagedCols Φ C.colRound (honestQ H)
  honestBad : Honest → List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))

/-- The statement-visible part of a memory family. -/
structure MemCore (F K Kio : Type) [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    [Fintype F] [Field Kio] (Φ : CoinFrame) (hC : ℕ) (S : MemShape) (C : TableSpec) (nAcc : ℕ) where
  Msg0 : Type
  Msg2 : Type
  chip : ∀ (V : VerifierData F K hC S) (t : Fin S.k), Msg0 → (Fin nAcc → Kio) → Msg2 →
    Coins Φ K → FixedPreprocessingRAP F
  chip_width : ∀ V t x ρ y χ, (chip V t x ρ y χ).rap.w = (S.table t).width
  internalBound : VerifierData F K hC S → Fin nAcc → ℕ
  summands : VerifierData F K hC S → Msg0 →
    List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))
  Honest : Type
  honestV : Honest → VerifierData F K hC S
  honestQ : Honest → Coins Φ K → ∀ t : Fin S.k, Fin (S.table t).width → F[X]
  honestReq : Honest → Coins Φ K → Fin nAcc → Kio
  honest_staged : ∀ H t, StagedCols Φ (S.table t).colRound (fun χ => honestQ H χ t)
  honestBad : Honest → List (BadSummand Φ K (Traces F C S) (TracesStaged Φ C S))

/-! ## The IO layer: exactly the fields `ioSummand` reads -/

/-- The compute side of the IO layer. -/
structure CompIO (F K Kio : Type) [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    [Fintype F] [Field Kio] (Φ : CoinFrame) (hC : ℕ) (S : MemShape) (C : TableSpec) (nAcc : ℕ)
    {m : Fin nAcc → ℕ} (I : IOCoinSpec Φ K Kio) extends CompCore F K Kio Φ hC S C nAcc where
  reqRecords : VerifierData F K hC S → Msg0 → (Fin C.width → F[X]) → Coins Φ K →
    ∀ a : Fin nAcc, List (Fin (m a) → Kio)
  recRound : ℕ
  recRound_le_io : ∀ i ∈ I.dep, recRound ≤ Φ.sampledAfter i
  reqRecords_round : ∀ V x Q Q' (χ χ' : Coins Φ K), (∀ j, C.colRound j ≤ recRound → Q j = Q' j) →
    (∀ i : Fin Φ.n, Φ.sampledAfter i < recRound → χ i = χ' i) →
    reqRecords V x Q χ = reqRecords V x Q' χ'

/-- The memory side of the IO layer. -/
structure MemIO (F K Kio : Type) [Field F] [Field K] [Algebra F K] [Fintype K] [DecidableEq K]
    [Fintype F] [Field Kio] (Φ : CoinFrame) (hC : ℕ) (S : MemShape) (C : TableSpec) (nAcc : ℕ)
    {m : Fin nAcc → ℕ} (I : IOCoinSpec Φ K Kio) extends MemCore F K Kio Φ hC S C nAcc where
  respBound : VerifierData F K hC S → Fin nAcc → ℕ
  internal : VerifierData F K hC S → Msg0 → (∀ t : Fin S.k, Fin (S.table t).width → F[X]) →
    Coins Φ K → ∀ a : Fin nAcc, List (Fin (m a) → Kio)
  respRecords : VerifierData F K hC S → Msg0 → (∀ t : Fin S.k, Fin (S.table t).width → F[X]) →
    Coins Φ K → ∀ a : Fin nAcc, List ((Fin (m a) → Kio) × F)
  respRound : ℕ
  respRound_le_io : ∀ i ∈ I.dep, respRound ≤ Φ.sampledAfter i
  respRecords_round : ∀ V x Q Q' (χ χ' : Coins Φ K),
    (∀ t j, (S.table t).colRound j ≤ respRound → Q t j = Q' t j) →
    (∀ i : Fin Φ.n, Φ.sampledAfter i < respRound → χ i = χ' i) →
    respRecords V x Q χ = respRecords V x Q' χ'
  internal_round : ∀ V x Q Q' (χ χ' : Coins Φ K),
    (∀ t j, (S.table t).colRound j ≤ respRound → Q t j = Q' t j) →
    (∀ i : Fin Φ.n, Φ.sampledAfter i < respRound → χ i = χ' i) →
    internal V x Q χ = internal V x Q' χ'

end Nock.NockVMROM.Thm54.SVFrameG
