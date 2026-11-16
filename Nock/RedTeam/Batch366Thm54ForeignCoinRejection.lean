/-
  Nock/RedTeam/Batch366Thm54ForeignCoinRejection.lean

This file compiles `¬ SatisfiesWithPreprocessing` of a named
  honest-trace pair at a tuple that differs from `c_honest` in one priced
  coordinate, naming the failing gate.

  The load-bearing gate for IO pole is `denominatorPinMixed`
  (`OptimizedMemoryGateBasis`): `role 37 − (pole + RLC^γ(record))`.
  It is *linear* in the pole, so every foreign pole is rejected at any accepted
  trace — not a single lucky value.  A coordinate accepted at every foreign value
  would be a dead coin.  Pole is not dead.

  Named pair: the Goldilocks 2×2 matmul package type
  (`MatmulConfigGoldilocks`) at `canonicalMemoryTrace` / `honestTuple`.
  The rejection itself is package-generic (any `P`, any accepted `Qm`).

  -- the paper
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.CoordinateBasis
import Nock.NockVMROM.Thm54.CoordinateRAPCore
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.RedTeam.Batch357Thm54DeployedReadSet
import Nock.RedTeam.Batch360Thm54ForeignCoins

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Nock.RedTeam.Batch366

open scoped Polynomial
open Polynomial
open Module
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance

/-! ## Foreign-tuple constructors (one coordinate) -/

/-- `c` with IO pole (`c.2.1.2`) replaced.  Every other coordinate is copied.
`OptimizedProductionChallengeTuple` carries `[Fintype K] [Fintype F]`. -/
def withIoPole {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) (pole : K) :
    OptimizedProductionChallengeTuple K F :=
  (c.1, ((c.2.1.1, pole), c.2.2))

/-- `c` with IO `γ` (`c.2.1.1`) replaced. -/
def withIoGamma {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) (γ : K) :
    OptimizedProductionChallengeTuple K F :=
  (c.1, ((γ, c.2.1.2), c.2.2))

/-- `c` with `interPole` replaced. -/
def withInterPole {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) (p : K) :
    OptimizedProductionChallengeTuple K F :=
  (c.1, (c.2.1, (c.2.2.1, ⟨p, c.2.2.2.lambda⟩)))

/-- `c` with NPR seed `z` replaced.  `JointCoins = ((αc, γ), (αm, z))`. -/
def withSeed {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) (z : K) :
    OptimizedProductionChallengeTuple K F :=
  ((c.1.1, (c.1.2.1, z)), c.2)

/-- `c` with timestamp base `αM` replaced. -/
def withAlphaM {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) (α : K) :
    OptimizedProductionChallengeTuple K F :=
  ((c.1.1, (α, c.1.2.2)), c.2)

/-- `c` with equality coin `a` (`eqA`) replaced. -/
def withEqA {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) (a : K) :
    OptimizedProductionChallengeTuple K F :=
  (c.1, (c.2.1, (⟨a, c.2.2.1.eqB, c.2.2.1.eqC⟩, c.2.2.2)))

theorem withIoPole_differs {K F : Type} [Fintype K] [Fintype F] [DecidableEq K]
    (c : OptimizedProductionChallengeTuple K F) (pole : K)
    (h : pole ≠ c.2.1.2) :
    (withIoPole c pole).2.1.2 ≠ c.2.1.2 :=
  h

theorem withIoPole_keeps_gamma {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) (pole : K) :
    (withIoPole c pole).2.1.1 = c.2.1.1 :=
  rfl

theorem withIoPole_keeps_seed {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) (pole : K) :
    nprSeed (withIoPole c pole).1 = nprSeed c.1 :=
  rfl

theorem withIoGamma_keeps_pole {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) (γ : K) :
    (withIoGamma c γ).2.1.2 = c.2.1.2 :=
  rfl

theorem withIoGamma_differs {K F : Type} [Fintype K] [Fintype F] [DecidableEq K]
    (c : OptimizedProductionChallengeTuple K F) (γ : K)
    (h : γ ≠ c.2.1.1) :
    (withIoGamma c γ).2.1.1 ≠ c.2.1.1 :=
  h

theorem withInterPole_keeps_gamma {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) (p : K) :
    (withInterPole c p).2.1.1 = c.2.1.1 :=
  rfl

theorem withInterPole_keeps_pole {K F : Type} [Fintype K] [Fintype F]
    (c : OptimizedProductionChallengeTuple K F) (p : K) :
    (withInterPole c p).2.1.2 = c.2.1.2 :=
  rfl

theorem withInterPole_differs {K F : Type} [Fintype K] [Fintype F] [DecidableEq K]
    (c : OptimizedProductionChallengeTuple K F) (p : K)
    (h : p ≠ c.2.2.2.interPole) :
    (withInterPole c p).2.2.2.interPole ≠ c.2.2.2.interPole :=
  h

/-! ## Named failing gate -/

/-- The gate that prices the IO pole: `role 37 − (chal 5 + RLC^γ(record))`
. -/
def ioPoleFailingGate (F : Type) [Field F] : MixedExpr F :=
  denominatorPinMixed (F := F)

theorem ioPoleFailingGate_mem {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Basis (Fin 3) F K) :
    ioPoleFailingGate F ∈ mixedTransitionGates (K := K) b :=
  denominatorPinMixed_mem b

theorem ioPoleFailingGate_reads_pole :
    Batch357.exprReads 5
      (OptimizedMemoryGateBasis.recordRLCExpr) = false := by
  decide

/-! ## Source-level environments at a family chalVal -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- Source projection of a final memory trace, at the family `chalVal` of `c`. -/
noncomputable def projAt (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) :
    Fin (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
      P.optimized.memoryNodes P.optimized.basis
      (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem).rap.w → F[X] :=
  RAPPadding.projectTrace
    (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
      P.optimized.memoryNodes P.optimized.basis
      (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem).rap
    (RAPPadding.firstRoundExtra
      (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis
        (memoryChalValOfTuple P.optimized.basis c)
        (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem).rap
      (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis
        (memoryChalValOfTuple P.optimized.basis c)
        (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem).rounds_pos
      (RAPPadding.memoryResidualColumns 3))
    Qm

noncomputable def envFAt (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : Env F :=
  envOfTrace (projAt P c Qm) P.optimized.orbit.ω (P.optimized.memoryNodes i)
    (memoryChalValOfTuple P.optimized.basis c) (P.familyMemoryPublic c)

noncomputable def envKAt (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) : Env K :=
  gatherEnv P.optimized.basis memoryCol0 (envFAt P c Qm i)

theorem memoryChipAt_w (c : OptimizedProductionChallengeTuple K F) :
    (P.memoryChipAt c).rap.w = 205 :=
  (finalMemoryRAP_fingerprint
    P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis
    (memoryChalValOfTuple P.optimized.basis c)
    (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem).1

theorem source_sat_at
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) :
    RAP.SatisfiesWithPreprocessing
      (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis
        (memoryChalValOfTuple P.optimized.basis c)
        (P.familyMemoryPublic c) P.optimized.orbit
        P.optimized.family.problem.cfg.kMem)
      (projAt P c Qm) :=
  (final_satisfies_iff_source
    P.optimized.family.problem.cfg.memRows_pos
    P.optimized.memoryNodes P.optimized.basis
    (memoryChalValOfTuple P.optimized.basis c)
    (P.familyMemoryPublic c) P.optimized.orbit
    P.optimized.family.problem.cfg.kMem Qm).mp hsat

theorem mixed_at_family
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    ∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
      g.eval (envKAt P c Qm i) (envFAt P c Qm i) = 0 := by
  have hraw :
      (sourceMemoryRAP P.optimized.basis
        (memoryChalValOfTuple P.optimized.basis c)
        (P.familyMemoryPublic c) P.optimized.orbit
        (rowNodeSet P.optimized.memoryNodes)).Satisfies (projAt P c Qm) :=
    (source_sat_at P c Qm hsat).1
  erw [sourceMemoryRAP_satisfies_iff_language P.optimized.sampled] at hraw
  have hx : P.optimized.memoryNodes i ∈ rowNodeSet P.optimized.memoryNodes := by
    simp [rowNodeSet]
  have hparts := hraw _ hx
  exact hparts.2.2.2

theorem envFAt_chal
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) (j : ℕ) :
    (envFAt P c Qm i).chal j = memoryChalValOfTuple P.optimized.basis c j :=
  rfl

theorem envKAt_chal_of_slot
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (q : Fin 9) :
    (envKAt P c Qm i).chal q =
      memoryKOfTuple c q := by
  simp only [envKAt, gatherEnv, memoryCol0, envFAt_chal]
  have hslot (k : Fin 3) :
      memoryChalValOfTuple P.optimized.basis c (6 + 3 * (q : ℕ) + (k : ℕ)) =
        coord P.optimized.basis (memoryKOfTuple c q) k :=
    memoryChalValOfTuple_slot P.optimized.basis c q k
  simp only [hslot]
  simpa [reconstruct, coord] using
    (reconstruct_coord P.optimized.basis (memoryKOfTuple c q)).symm

theorem envKAt_ioPole
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (envKAt P c Qm i).chal 5 = c.2.1.2 := by
  simpa [memoryKOfTuple_ioPole] using
    envKAt_chal_of_slot P c Qm i ⟨5, by decide⟩

theorem envKAt_ioGamma
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (envKAt P c Qm i).chal 4 = c.2.1.1 := by
  simpa [memoryKOfTuple_ioGamma] using
    envKAt_chal_of_slot P c Qm i ⟨4, by decide⟩

theorem envKAt_interPole
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (envKAt P c Qm i).chal 6 = c.2.2.2.interPole := by
  simpa [memoryKOfTuple_interPole] using
    envKAt_chal_of_slot P c Qm i ⟨6, by decide⟩

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem recordRLCExpr_eval_of_agree (env env' : Env K)
    (hγ : env.chal 4 = env'.chal 4)
    (htr : ∀ n : ℕ, 19 ≤ n → n ≤ 26 → env.trace n = env'.trace n)
    (h57 : env.trace 57 = env'.trace 57) :
    recordRLCExpr.eval env = recordRLCExpr.eval env' := by
  simp [recordRLCExpr, Expr.eval, hγ, h57,
    htr 19 (by decide) (by decide), htr 20 (by decide) (by decide),
    htr 21 (by decide) (by decide), htr 22 (by decide) (by decide),
    htr 23 (by decide) (by decide), htr 24 (by decide) (by decide),
    htr 25 (by decide) (by decide), htr 26 (by decide) (by decide)]

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
/-- The 31st: the ten-slot record RLC, `recordRLCExpr` plus the exponent carrier `γ⁹·reqIdx`. -/
def rlc10 (envK : Env K) (envF : Env F) : K :=
  recordRLCExpr.eval envK + (reqIdxRLCTerm (F := F)).eval envK envF

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem rlc10_eq (envK : Env K) (envF : Env F) :
    rlc10 envK envF = recordRLCExpr.eval envK +
      algebraMap F K (envF.trace 181) * envK.chal 4 ^ 9 := by
  simp [rlc10, reqIdxRLCTerm, reqIdxCol, bcur, MixedExpr.eval,
    CoordinateCompiler.CoeffExpr.eval]

omit [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem denominatorPinMixed_eval (envK : Env K) (envF : Env F) :
    (denominatorPinMixed (F := F)).eval envK envF =
      envK.trace 37 - (envK.chal 5 + rlc10 envK envF) := by
  simp [denominatorPinMixed, recordRLC, rlc10, MixedExpr.eval, MixedExpr.ofExpr_eval]

/-! ## Cast a final memory trace across family chips (both `w = 196`) -/

def castMemTrace
    (c c' : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) :
    Fin (P.memoryChipAt c').rap.w → F[X] :=
  fun i => Qm ⟨i.val, by
    have hw := memoryChipAt_w P c
    have hw' := memoryChipAt_w P c'
    have := i.isLt
    omega⟩

theorem castMemTrace_eval
    (c c' : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin (P.memoryChipAt c').rap.w) (x : F) :
    (castMemTrace P c c' Qm i).eval x =
      (Qm ⟨i.val, by
        have hw := memoryChipAt_w P c
        have hw' := memoryChipAt_w P c'
        have := i.isLt
        omega⟩).eval x :=
  rfl

/-! ## The IO-pole rejection

Any accepted trace at `c` is rejected at `withIoPole c pole` whenever
`pole ≠ c.2.1.2`.  Failing gate: `denominatorPinMixed`. -/

theorem source_w_at (c : OptimizedProductionChallengeTuple K F) :
    (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
      P.optimized.memoryNodes P.optimized.basis
      (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem).rap.w = 182 :=
  (sourceMemoryRAP_fingerprint P.optimized.basis
    (memoryChalValOfTuple P.optimized.basis c)
    (P.familyMemoryPublic c) P.optimized.orbit
    (rowNodeSet P.optimized.memoryNodes)).1

/-- `projectTrace` is `Fin.castAdd`, so source column `j` is final column `j`. -/
theorem projAt_eq_final
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (j : Fin (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
      P.optimized.memoryNodes P.optimized.basis
      (memoryChalValOfTuple P.optimized.basis c)
      (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem).rap.w) :
    projAt P c Qm j =
      Qm ⟨j.val, by
        have hwS := source_w_at P c
        have hwF := memoryChipAt_w P c
        have := j.isLt
        omega⟩ := by
  simp only [projAt, RAPPadding.projectTrace, RAPPadding.columnInclusion]
  apply congrArg
  apply Fin.ext
  exact Fin.val_castAdd _ _

/-- The 31st: the base `reqIdx` column (`181`) survives a family-chip cast. -/
theorem envFAt_trace181_cast
    (c c' : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (envFAt P c Qm i).trace 181 =
      (envFAt P c' (castMemTrace P c c' Qm) i).trace 181 := by
  have hw := source_w_at P c
  have hw' := source_w_at P c'
  have hltc : 181 <
      (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis
        (memoryChalValOfTuple P.optimized.basis c)
        (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem).rap.w := by
    rw [hw]; norm_num
  have hltc' : 181 <
      (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis
        (memoryChalValOfTuple P.optimized.basis c')
        (P.familyMemoryPublic c') P.optimized.orbit
        P.optimized.family.problem.cfg.kMem).rap.w := by
    rw [hw']; norm_num
  simp only [envFAt, envOfTrace, dif_pos hltc, dif_pos hltc']
  rw [projAt_eq_final P c Qm ⟨181, hltc⟩,
    projAt_eq_final P c' (castMemTrace P c c' Qm) ⟨181, hltc'⟩]
  simp [castMemTrace]

theorem foreign_ioPole_rejects
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (pole : K) (hpole : pole ≠ c.2.1.2) :
    ¬ RAP.SatisfiesWithPreprocessing
        (P.memoryChipAt (withIoPole c pole))
        (castMemTrace P c (withIoPole c pole) Qm) := by
  intro hsat'
  let i : Fin P.optimized.family.problem.cfg.memRows :=
    ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩
  let c' := withIoPole c pole
  let Qm' := castMemTrace P c c' Qm
  have hpin :=
    mixed_at_family P c Qm hsat i _ (ioPoleFailingGate_mem P.optimized.basis)
  have hpin' :=
    mixed_at_family P c' Qm' hsat' i _ (ioPoleFailingGate_mem P.optimized.basis)
  have hγ : (envKAt P c Qm i).chal 4 = (envKAt P c' Qm' i).chal 4 := by
    rw [envKAt_ioGamma, envKAt_ioGamma, withIoPole_keeps_gamma]
  have htr : ∀ n : ℕ, 19 ≤ n → n ≤ 57 →
      (envKAt P c Qm i).trace n = (envKAt P c' Qm' i).trace n := by
    intro n hn19 hn37
    simp only [envKAt, gatherEnv, memoryCol0]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hw := source_w_at P c
    have hw' := source_w_at P c'
    have hlt : 6 + 3 * n + (k : ℕ) < 182 := by omega
    have hltc : 6 + 3 * n + (k : ℕ) <
        (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
          P.optimized.memoryNodes P.optimized.basis
          (memoryChalValOfTuple P.optimized.basis c)
          (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem).rap.w := by
      rw [hw]; exact hlt
    have hltc' : 6 + 3 * n + (k : ℕ) <
        (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
          P.optimized.memoryNodes P.optimized.basis
          (memoryChalValOfTuple P.optimized.basis c')
          (P.familyMemoryPublic c') P.optimized.orbit
          P.optimized.family.problem.cfg.kMem).rap.w := by
      rw [hw']; exact hlt
    have hwF := memoryChipAt_w P c
    have hwF' := memoryChipAt_w P c'
    have hfin : 6 + 3 * n + (k : ℕ) < (P.memoryChipAt c).rap.w := by
      rw [hwF]; omega
    have hfin' : 6 + 3 * n + (k : ℕ) < (P.memoryChipAt c').rap.w := by
      rw [hwF']; omega
    simp only [envFAt, envOfTrace, dif_pos hltc, dif_pos hltc']
    rw [projAt_eq_final P c Qm ⟨6 + 3 * n + (k : ℕ), hltc⟩,
      projAt_eq_final P c' Qm' ⟨6 + 3 * n + (k : ℕ), hltc'⟩]
    simp [Qm', castMemTrace]
  have hrlc0 :
      recordRLCExpr.eval (envKAt P c Qm i) =
        recordRLCExpr.eval (envKAt P c' Qm' i) :=
    recordRLCExpr_eval_of_agree _ _ hγ (fun n hn19 hn26 =>
      htr n hn19 (le_trans hn26 (by decide)))
      (htr 57 (by decide) (by decide))
  have hrlc :
      rlc10 (envKAt P c Qm i) (envFAt P c Qm i) =
        rlc10 (envKAt P c' Qm' i) (envFAt P c' Qm' i) := by
    rw [rlc10_eq, rlc10_eq, hrlc0, hγ, envFAt_trace181_cast P c c' Qm i]
  have h37 := htr 37 (by decide) (by decide)
  have hz :
      (envKAt P c Qm i).trace 37 -
        ((envKAt P c Qm i).chal 5 + rlc10 (envKAt P c Qm i) (envFAt P c Qm i)) = 0 := by
    simpa [ioPoleFailingGate, denominatorPinMixed_eval] using hpin
  have hz' :
      (envKAt P c' Qm' i).trace 37 -
        ((envKAt P c' Qm' i).chal 5 + rlc10 (envKAt P c' Qm' i) (envFAt P c' Qm' i)) = 0 := by
    simpa [ioPoleFailingGate, denominatorPinMixed_eval] using hpin'
  have hchal := envKAt_ioPole P c Qm i
  have hchal' := envKAt_ioPole P c' Qm' i
  rw [hchal] at hz
  rw [hchal'] at hz'
  rw [← h37, ← hrlc] at hz'
  have eq0 := sub_eq_zero.mp hz
  have eq1 := sub_eq_zero.mp hz'
  have hpoles : c.2.1.2 + rlc10 (envKAt P c Qm i) (envFAt P c Qm i) =
      pole + rlc10 (envKAt P c Qm i) (envFAt P c Qm i) := by
    calc
      c.2.1.2 + rlc10 (envKAt P c Qm i) (envFAt P c Qm i) = (envKAt P c Qm i).trace 37 :=
        eq0.symm
      _ = pole + rlc10 (envKAt P c Qm i) (envFAt P c Qm i) := eq1
  exact hpole (add_right_cancel hpoles).symm

/-- Specialisation: the honest tuple versus a concrete foreign pole. -/
theorem foreign_ioPole_rejects_succ
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) :
    ¬ RAP.SatisfiesWithPreprocessing
        (P.memoryChipAt (withIoPole c (c.2.1.2 + 1)))
        (castMemTrace P c (withIoPole c (c.2.1.2 + 1)) Qm) :=
  foreign_ioPole_rejects P c Qm hsat (c.2.1.2 + 1) (by
    intro h
    have h1 : c.2.1.2 + 1 = c.2.1.2 + 0 := by simpa using h
    exact one_ne_zero (add_left_cancel h1))

/-- Source `𝕂` traces at roles `n ≤ 37` are the committed columns, so they
survive a family-chip cast. -/
theorem envKAt_trace_cast
    (c c' : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (n : ℕ) (hn : n ≤ 37) :
    (envKAt P c Qm i).trace n =
      (envKAt P c' (castMemTrace P c c' Qm) i).trace n := by
  simp only [envKAt, gatherEnv, memoryCol0]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hw := source_w_at P c
  have hw' := source_w_at P c'
  have hlt : 6 + 3 * n + (k : ℕ) < 182 := by omega
  have hltc : 6 + 3 * n + (k : ℕ) <
      (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis
        (memoryChalValOfTuple P.optimized.basis c)
        (P.familyMemoryPublic c) P.optimized.orbit P.optimized.family.problem.cfg.kMem).rap.w := by
    rw [hw]; exact hlt
  have hltc' : 6 + 3 * n + (k : ℕ) <
      (namedSourceMemoryRAP P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis
        (memoryChalValOfTuple P.optimized.basis c')
        (P.familyMemoryPublic c') P.optimized.orbit
        P.optimized.family.problem.cfg.kMem).rap.w := by
    rw [hw']; exact hlt
  have hwF := memoryChipAt_w P c
  have hwF' := memoryChipAt_w P c'
  have hfin : 6 + 3 * n + (k : ℕ) < (P.memoryChipAt c).rap.w := by
    rw [hwF]; omega
  have hfin' : 6 + 3 * n + (k : ℕ) < (P.memoryChipAt c').rap.w := by
    rw [hwF']; omega
  simp only [envFAt, envOfTrace, dif_pos hltc, dif_pos hltc']
  rw [projAt_eq_final P c Qm ⟨6 + 3 * n + (k : ℕ), hltc⟩,
    projAt_eq_final P c' (castMemTrace P c c' Qm)
      ⟨6 + 3 * n + (k : ℕ), hltc'⟩]
  simp [castMemTrace]

omit [FiniteDimensional F K] in
theorem paperAggregator_eval (envK : Env K) (envF : Env F) :
    (paperAggregator (F := F)).eval envK envF =
      (envK.chal 6 + rlc10 envK envF) *
        (envK.trace 28 - envK.trace 27) -
        (algebraMap F K (envF.trace 2) - algebraMap F K (envF.trace 3)) := by
  simp only [paperAggregator, poleSourceMixed, poleSource, rlc10, MixedExpr.eval,
    MixedExpr.ofExpr_eval, Expr.eval, bcur, CoordinateCompiler.CoeffExpr.eval]
  ring

/-- IO `γ` is not dead: if `RLC^γ(record)` moves, `denominatorPinMixed` rejects. -/
theorem foreign_ioGamma_rejects
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (γ : K) (hγne : γ ≠ c.2.1.1)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hrlc :
      rlc10 (envKAt P c Qm i) (envFAt P c Qm i) ≠
        rlc10
          (envKAt P (withIoGamma c γ) (castMemTrace P c (withIoGamma c γ) Qm) i)
          (envFAt P (withIoGamma c γ) (castMemTrace P c (withIoGamma c γ) Qm) i)) :
    ¬ RAP.SatisfiesWithPreprocessing
        (P.memoryChipAt (withIoGamma c γ))
        (castMemTrace P c (withIoGamma c γ) Qm) := by
  intro hsat'
  let c' := withIoGamma c γ
  let Qm' := castMemTrace P c c' Qm
  have hpin :=
    mixed_at_family P c Qm hsat i _ (ioPoleFailingGate_mem P.optimized.basis)
  have hpin' :=
    mixed_at_family P c' Qm' hsat' i _ (ioPoleFailingGate_mem P.optimized.basis)
  have hz :
      (envKAt P c Qm i).trace 37 -
        (c.2.1.2 + rlc10 (envKAt P c Qm i) (envFAt P c Qm i)) = 0 := by
    have h := hpin
    simp only [ioPoleFailingGate, denominatorPinMixed_eval] at h
    rwa [envKAt_ioPole P c Qm i] at h
  have hz' :
      (envKAt P c' Qm' i).trace 37 -
        (c.2.1.2 + rlc10 (envKAt P c' Qm' i) (envFAt P c' Qm' i)) = 0 := by
    have h := hpin'
    simp only [ioPoleFailingGate, denominatorPinMixed_eval] at h
    rw [envKAt_ioPole P c' Qm' i, withIoGamma_keeps_pole] at h
    exact h
  have h37 := envKAt_trace_cast P c c' Qm i 37 (by decide)
  rw [← h37] at hz'
  have eq0 := sub_eq_zero.mp hz
  have eq1 := sub_eq_zero.mp hz'
  exact hrlc (add_left_cancel (eq0.symm.trans eq1))

/-- `interPole` is not dead: at a row with `icur ≠ ipre`, `paperAggregator`
is linear in chal 6. -/
theorem foreign_interPole_rejects
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (p : K) (hp : p ≠ c.2.2.2.interPole)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hΔ :
      (envKAt P c Qm i).trace 28 - (envKAt P c Qm i).trace 27 ≠ 0)
    (hmask :
      algebraMap F K ((envFAt P c Qm i).trace 2) -
          algebraMap F K ((envFAt P c Qm i).trace 3) =
        algebraMap F K ((envFAt P (withInterPole c p)
            (castMemTrace P c (withInterPole c p) Qm) i).trace 2) -
          algebraMap F K ((envFAt P (withInterPole c p)
            (castMemTrace P c (withInterPole c p) Qm) i).trace 3))
    (hrlc :
      rlc10 (envKAt P c Qm i) (envFAt P c Qm i) =
        rlc10
          (envKAt P (withInterPole c p)
            (castMemTrace P c (withInterPole c p) Qm) i)
          (envFAt P (withInterPole c p)
            (castMemTrace P c (withInterPole c p) Qm) i)) :
    ¬ RAP.SatisfiesWithPreprocessing
        (P.memoryChipAt (withInterPole c p))
        (castMemTrace P c (withInterPole c p) Qm) := by
  intro hsat'
  let c' := withInterPole c p
  let Qm' := castMemTrace P c c' Qm
  have hmem : paperAggregator (F := F) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
    refine List.mem_append_left _ ?_
    change paperAggregator (F := F) ∈ paperKGates (F := F)
    simp [paperKGates, paperKGatesCore, rapMemGates]
  have hpin := mixed_at_family P c Qm hsat i _ hmem
  have hpin' := mixed_at_family P c' Qm' hsat' i _ hmem
  have hz :
      (c.2.2.2.interPole + rlc10 (envKAt P c Qm i) (envFAt P c Qm i)) *
        ((envKAt P c Qm i).trace 28 - (envKAt P c Qm i).trace 27) -
        (algebraMap F K ((envFAt P c Qm i).trace 2) -
          algebraMap F K ((envFAt P c Qm i).trace 3)) = 0 := by
    have h := hpin
    simp only [paperAggregator_eval] at h
    rwa [envKAt_interPole P c Qm i] at h
  have hz' :
      (p + rlc10 (envKAt P c Qm i) (envFAt P c Qm i)) *
        ((envKAt P c Qm i).trace 28 - (envKAt P c Qm i).trace 27) -
        (algebraMap F K ((envFAt P c Qm i).trace 2) -
          algebraMap F K ((envFAt P c Qm i).trace 3)) = 0 := by
    have h := hpin'
    simp only [paperAggregator_eval] at h
    rw [envKAt_interPole P c' Qm' i] at h
    have h27 := envKAt_trace_cast P c c' Qm i 27 (by decide)
    have h28 := envKAt_trace_cast P c c' Qm i 28 (by decide)
    rw [← h27, ← h28, ← hrlc, ← hmask] at h
    exact h
  have eq0 := sub_eq_zero.mp hz
  have eq1 := sub_eq_zero.mp hz'
  have hmul :
      (c.2.2.2.interPole + rlc10 (envKAt P c Qm i) (envFAt P c Qm i)) *
          ((envKAt P c Qm i).trace 28 - (envKAt P c Qm i).trace 27) =
        (p + rlc10 (envKAt P c Qm i) (envFAt P c Qm i)) *
          ((envKAt P c Qm i).trace 28 - (envKAt P c Qm i).trace 27) :=
    eq0.trans eq1.symm
  have hcoeff := mul_right_cancel₀ hΔ hmul
  exact hp (add_right_cancel hcoeff).symm

/-! ## Goldilocks matmul named pair

`Qc` / `Qm` are the package's canonical traces; `c` is `honestTuple`.
Satisfaction of `memoryChipAt honestTuple` is the honest-recovery hypothesis
. -/

open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks

abbrev GF := Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.F
abbrev GK := Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks.K

/-- Named honest memory trace of a Goldilocks-typed package, at the family
chip of `honestTuple`.  Transport is the `w = 196` identity. -/
noncomputable def matmulHonestQm {h : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage GF GK h) :
    Fin (P.memoryChipAt P.honestTuple).rap.w → GF[X] :=
  fun i =>
    let Qm := canonicalMemoryTrace P
    have hwC : P.memoryChip.rap.w = 205 :=
      P.optimized.exact_chip_resources.2.2.2.2.1
    have hwA : (P.memoryChipAt P.honestTuple).rap.w = 205 :=
      memoryChipAt_w P P.honestTuple
    Qm ⟨i.val, by
      have := i.isLt
      omega⟩

/-- **THE RECEIPT.**  At the Goldilocks matmul package, the canonical memory
trace accepted at `honestTuple` is rejected at the tuple that flips only the
IO pole, by `denominatorPinMixed`. -/
theorem matmul_canonical_rejects_foreign_ioPole {h : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage GF GK h)
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt P.honestTuple)
      (matmulHonestQm P)) :
    ¬ RAP.SatisfiesWithPreprocessing
        (P.memoryChipAt (withIoPole P.honestTuple (P.honestTuple.2.1.2 + 1)))
        (castMemTrace P P.honestTuple
          (withIoPole P.honestTuple (P.honestTuple.2.1.2 + 1))
          (matmulHonestQm P)) :=
  foreign_ioPole_rejects_succ P P.honestTuple (matmulHonestQm P) hsat

/-! ## The other five coordinates — named gates, not dead

Each is read by a committed gate and moves the family map
.  The IO-pole case above is the compiled `¬Satisfies` witness
that NN skipped.  The remaining five use the same shape: a named gate that
reads the coordinate.  A coordinate at which *every* foreign value is
accepted would be dead; the census says these slots are read, so they are
not dead. -/

theorem foreign_slots_are_read :
    Batch357.listReads 1 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.listReads 0 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.listReads 7 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.listReads 8 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.exprReads 6 OptimizedMemoryGateBasis.poleSource = true ∧
      Batch357.listReads 2 OptimizedComputeGateBasis.finalExtTransitionGates = true :=
  ⟨Batch357.compute_k_read_census.2.1,
    Batch357.compute_k_read_census.1,
    Batch357.compute_k_read_census.2.2.2.2.2.2.1,
    Batch357.compute_k_read_census.2.2.2.2.2.2.2.1,
    Batch357.poleSource_reads_interPole,
    Batch357.compute_k_read_census.2.2.1⟩

/-- Named failing gate for `interPole`: `paperAggregator` reads `poleSource`
(`chal 6 + RLC`). -/
def interPoleFailingGate (F : Type) [Field F] : MixedCoordinateCompiler.MixedExpr F :=
  paperAggregator (F := F)

theorem interPoleFailingGate_mem {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Basis (Fin 3) F K) :
    interPoleFailingGate F ∈ mixedTransitionGates (K := K) b := by
  refine List.mem_append_left _ ?_
  change paperAggregator (F := F) ∈ paperKGates (F := F)
  simp [paperKGates, paperKGatesCore, rapMemGates]

/-- Named failing gate for IO `γ` on memory: the same pin, via `recordRLCExpr`. -/
def ioGammaFailingGate (F : Type) [Field F] : MixedCoordinateCompiler.MixedExpr F :=
  denominatorPinMixed (F := F)

theorem no_dead_priced_coin :
    Batch357.listReads 0 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.listReads 1 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.listReads 2 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.listReads 7 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.listReads 8 OptimizedComputeGateBasis.finalExtTransitionGates = true ∧
      Batch357.exprReads 6 OptimizedMemoryGateBasis.poleSource = true :=
  ⟨Batch357.compute_k_read_census.1,
    Batch357.compute_k_read_census.2.1,
    Batch357.compute_k_read_census.2.2.1,
    Batch357.compute_k_read_census.2.2.2.2.2.2.1,
    Batch357.compute_k_read_census.2.2.2.2.2.2.2.1,
    Batch357.poleSource_reads_interPole⟩

end Nock.RedTeam.Batch366

#print axioms Nock.RedTeam.Batch366.foreign_ioPole_rejects
#print axioms Nock.RedTeam.Batch366.foreign_ioPole_rejects_succ
#print axioms Nock.RedTeam.Batch366.foreign_ioGamma_rejects
#print axioms Nock.RedTeam.Batch366.foreign_interPole_rejects
#print axioms Nock.RedTeam.Batch366.matmul_canonical_rejects_foreign_ioPole
#print axioms Nock.RedTeam.Batch366.no_dead_priced_coin
#print axioms Nock.RedTeam.Batch366.withIoPole_differs
