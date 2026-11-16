import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.Batch1172Thm54ServedRecordsAtTraces
import Nock.NockVMROM.Thm54.P8Core.Batch823Thm54R4BridgeCompute

/-! Index and seed-slot identities for compute chip data `D : ChipData F K h`: the family seed publics agree with the coordinates of `seedOfClaim`, the row-index and label agreements (`rowIdxD`, `lblCS_eqD`, `lblCAt_eqD`), the honest polynomial assignment `honestQ`, and the arity and prefix agreements `computeArity_eqD`, `computePrefix_eqD`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.NockVMROM.Thm54.SVCompute

open scoped Polynomial
open Polynomial
open Nock Nock.Reified Nock.Framework Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.CoordinateBasis

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {h : ℕ}
  (D : ChipData F K h) (L : ChipLayout F K h)
  (c : OptimizedProductionChallengeTuple K F) (Qh : Fin L.w → F[X])

/-! ## The seed wiring -/

/-- Family publics `3..5` are the `𝔽`-coordinates of `seedOfClaim`. -/
theorem family_seed_slotsD (k : Fin 3) :
    computePublicOfTuple D.basis D.claim D.pub c (3 + (k : ℕ)) =
      coord D.basis (seedOfClaim D.claim c) k :=
  computePublicOfTuple_seed_coord D.basis D.claim D.pub c k

/-! ## The row index of a 1-indexed label -/

/-- The 0-indexed row of a 1-indexed label (`lblC`'s off-range convention). -/
def rowIdxD (D : ChipData F K h) (i : ℕ) : Fin D.N :=
  if hi : i - 1 < D.N then ⟨i - 1, hi⟩ else ⟨0, D.hN⟩

theorem lblCS_eqD (i : ℕ) :
    lblCSD D L c Qh i =
      (lblCAtD D L c Qh (rowIdxD D i), c2SAtD D L c Qh (rowIdxD D i)) := by
  unfold lblCSD lblCD rowIdxD
  split_ifs <;> rfl

/-- The decoded label of row `r` reads the family row env. -/
theorem lblCAt_eqD (r : Fin D.N) :
    lblCAtD D L c Qh r =
      (StrategyOfTracesLift.computeStateOf
          (StrategyOfTracesLift.decodeSource (rowEnvAtD D c (famQ D L c Qh) r)),
        (StrategyOfTracesLift.decodeInputs (rowEnvAtD D c (famQ D L c Qh) r),
          StrategyOfTracesLift.decodePub (rowEnvAtD D c (famQ D L c Qh) r)
            (StrategyOfTracesLift.computeStateOf
              (StrategyOfTracesLift.decodeSource (rowEnvAtD D c (famQ D L c Qh) r))),
          StrategyOfTracesLift.decodeDec (rowEnvAtD D c (famQ D L c Qh) r))) := rfl

/-- The first component of the label sequence at index `m + 1` is the state decoded from the family row environment of row `m`. -/
theorem lblCS_succ_fstD (m : ℕ) (hm : m < D.N) :
    (lblCSD D L c Qh (m + 1)).1.1 =
      StrategyOfTracesLift.computeStateOf
        (StrategyOfTracesLift.decodeSource (rowEnvAtD D c (famQ D L c Qh) ⟨m, hm⟩)) := by
  rw [lblCS_eqD, lblCAt_eqD]
  have : rowIdxD D (m + 1) = ⟨m, hm⟩ := by
    unfold rowIdxD; rw [dif_pos (by omega)]; rfl
  rw [this]

/-! ## The exponent locator at the family chip -/

/-- The honest-width trace of a family trace (`honestQc`). -/
def honestQ (D : ChipData F K h) (L : ChipLayout F K h)
    (c : OptimizedProductionChallengeTuple K F) (Q : Fin (chipOf D L c).rap.w → F[X]) :
    Fin L.w → F[X] :=
  fun j => Q (Fin.cast (chipOf_w D L c).symm j)

theorem famQ_honestQ (Q : Fin (chipOf D L c).rap.w → F[X]) :
    famQ D L c (honestQ D L c Q) = Q := rfl

/-- The package compute env the decoded event reads, at the family trace. -/
abbrev envsCD (Q : Fin (chipOf D L c).rap.w → F[X]) : Fin D.N → Env K :=
  computeSourceEnvD D (honestQ D L c Q)

theorem envsC_traceD (Q : Fin (chipOf D L c).rap.w → F[X]) (a : Fin D.N) :
    (envsCD D L c Q a).trace = (rowEnvAtD D c Q a).toSourceEnv.trace := by
  have := familyRow_trace_eqD D L c (honestQ D L c Q) a
  rw [famQ_honestQ] at this
  exact this.symm

variable (Q : Fin (chipOf D L c).rap.w → F[X]) (RF : RowFacts D L c Q)
  (hchar : ∀ n : ℕ, n ≤ 11 → (n : K) = 1 → n = 1)

include RF hchar

theorem computeArity_eqD (a : Fin D.N) :
    computeArity (envsCD D L c Q a) = rowArity (rowEnvAtD D c Q a) := by
  obtain ⟨s, hsel⟩ := source_selector_atD RF hchar a
  rw [rowArity_eq_arity_atD a s hsel]
  have ht := envsC_traceD D L c Q a
  have s0 := hsel .s0; have s2 := hsel .s2; have s5 := hsel .s5; have s6 := hsel .s6
  have s7 := hsel .s7; have s8 := hsel .s8; have s9 := hsel .s9
  simp only [Nock.Reified.opCol, ComputeTable.opSel] at s0 s2 s5 s6 s7 s8 s9
  unfold computeArity
  rw [ht]
  cases s <;> simp [s0, s2, s5, s6, s7, s8, s9, OptimizedHostileTimestamps.arity]

theorem computePrefix_eqD (a : Fin D.N) :
    computePrefix (envsCD D L c Q) a = prefixExpAtD D c Q a := by
  unfold computePrefix prefixExpAtD
  have hg : ∀ i : Fin D.N,
      computeArity (envsCD D L c Q i) =
        (fun k => if hk : k < D.N then rowArity (rowEnvAtD D c Q ⟨k, hk⟩) else 0) (i : ℕ) := by
    intro i
    rw [computeArity_eqD D L c Q RF hchar i]
    simp [i.isLt]
  rw [Finset.sum_filter]
  simp_rw [hg]
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < (a : ℕ) then
    (if hk : k < D.N then rowArity (rowEnvAtD D c Q ⟨k, hk⟩) else 0) else 0) D.N]
  rw [← Finset.sum_filter]
  have hfil : (Finset.range D.N).filter (fun k => k < (a : ℕ)) = Finset.range a := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; have := a.isLt; omega
  rw [hfil]

end

end Nock.NockVMROM.Thm54.SVCompute
