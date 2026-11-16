/-
  Nock/NockVMROM/Thm54/P8Core/FamilyMemoryRows.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.FamilyMemoryRows`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/FamilyMemoryRows.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.HostilePoleAlignment
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.FamilyMemoryRows

open scoped Polynomial
open Polynomial
open Nock
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.HostilePoleAlignment
open Nock.NockVMROM.Thm54.MemoryFactorizationScope
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open ComputeTable
open Module
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

def honestQm
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) :
    Fin P.memoryChip.rap.w → F[X] :=
  fun j => Qm (Fin.cast (memoryChipAt_width P c).symm j)

def projAt
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) :
    Fin 182 → F[X] :=
  fun j =>
    have hw : (P.memoryChipAt c).rap.w = 205 :=
      (finalMemoryRAP_fingerprint
        P.optimized.family.problem.cfg.memRows_pos
        P.optimized.memoryNodes P.optimized.basis
        (memoryChalValOfTuple P.optimized.basis c)
        (P.familyMemoryPublic c) P.optimized.orbit
        P.optimized.family.problem.cfg.kMem).1
    Qm ⟨j.val, by omega⟩

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

theorem projAt_eq_memorySourceTrace
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X]) :
    projAt P c Qm = P.memorySourceTrace (honestQm P c Qm) := by
  ext j
  simp only [projAt, honestQm, OptimizedFullStrictNockVMROMPackage.memorySourceTrace,
    RAPPadding.projectTrace, RAPPadding.columnInclusion]
  rfl

theorem envF_eq_base
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    envOfTrace (projAt P c Qm) P.optimized.orbit.ω (P.optimized.memoryNodes i)
      (memoryChalValOfTuple P.optimized.basis c) (P.familyMemoryPublic c) =
      memoryBaseEnvAt P c (honestQm P c Qm) i := by
  simp only [memoryBaseEnvAt, projAt_eq_memorySourceTrace]

theorem row_parts_at
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (∀ g ∈ baseTransitionGates P.optimized.basis,
      g.eval (memoryBaseEnvAt P c (honestQm P c Qm) i) = 0) ∧
    (∀ g ∈ equalityChecks P.optimized.basis,
      g.eval (memoryBaseEnvAt P c (honestQm P c Qm) i) = 0) ∧
    (∀ g ∈ (memorySourceTemplate P.optimized.basis).extTransition ++
        (memorySourceTemplate P.optimized.basis).extDeg1 ++
        (memorySourceTemplate P.optimized.basis).extDeg3,
      g.eval (memorySourceEnvAt P c (honestQm P c Qm) i) = 0) ∧
    (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
      g.eval (memorySourceEnvAt P c (honestQm P c Qm) i)
        (memoryBaseEnvAt P c (honestQm P c Qm) i) = 0) := by
  have hraw :
      (sourceMemoryRAP P.optimized.basis
        (memoryChalValOfTuple P.optimized.basis c)
        (P.familyMemoryPublic c) P.optimized.orbit
        (rowNodeSet P.optimized.memoryNodes)).Satisfies (projAt P c Qm) :=
    (source_sat_at P c Qm hsat).1
  rw [sourceMemoryRAP_satisfies_iff_language P.optimized.sampled] at hraw
  have hx : P.optimized.memoryNodes i ∈ rowNodeSet P.optimized.memoryNodes := by
    simp [rowNodeSet]
  have hparts := hraw _ hx
  have hF := envF_eq_base P c Qm i
  rw [hF] at hparts
  -- `memorySourceEnvAt` unfolds to the same gather as the language statement.
  dsimp only [memorySourceEnvAt] at hparts ⊢
  rw [memorySourceTemplate_col0] at hparts ⊢
  exact hparts

theorem mixed_at_family
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    ∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
      g.eval (memorySourceEnvAt P c (honestQm P c Qm) i)
        (memoryBaseEnvAt P c (honestQm P c Qm) i) = 0 :=
  (row_parts_at P c Qm hsat i).2.2.2

theorem base_at_family
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    ∀ g ∈ baseTransitionGates P.optimized.basis,
      g.eval (memoryBaseEnvAt P c (honestQm P c Qm) i) = 0 :=
  (row_parts_at P c Qm hsat i).1

def MemStateTagChar (K : Type) [Field K] : Prop :=
  ∀ n : ℕ, n ≤ 4 → (n : K) = 1 → n = 1

theorem baseOneHot_at_family
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hchar : MemStateTagChar F) :
    ∃ st, MemoryPaperFactorization.BaseOneHot
      (memoryBaseEnvAt P c (honestQm P c Qm) i) st := by
  have hbase := base_at_family P c Qm hsat i
  have hpaper : ∀ g ∈ MemoryPaperFactorization.paperBaseGates (F := F),
      g.eval (memoryBaseEnvAt P c (honestQm P c Qm) i) = 0 := by
    intro g hg
    have hmem : g ∈ baseTransitionGates P.optimized.basis := by
      simp only [baseTransitionGates]
      refine List.mem_append.mpr (Or.inl ?_)
      simpa [MemoryPaperFactorization.paperBaseGates_eq_committed] using hg
    exact hbase g hmem
  exact MemoryPaperFactorization.baseOneHot_of_paperBaseGates _ hchar hpaper

theorem memoryStateOf_eq_of_baseOneHot (envF : Env F) (st : MState)
    (hone : MemoryPaperFactorization.BaseOneHot envF st) :
    memoryStateOf envF = st := by
  cases st <;> simp [memoryStateOf, mopCol] <;>
    (have h0 := hone .decompose; have h1 := hone .halt
     have h2 := hone .read_root; have h3 := hone .verify_child
     simp [mopCol] at h0 h1 h2 h3; simp [h0, h1, h2, h3])

/-- Gate-basis `selScale` at a base one-hot. -/
theorem selScale_eval
    (envK : Env K) (envF : Env F) (st : MState)
    (hone : MemoryPaperFactorization.BaseOneHot envF st)
    (f : MState → Expr) :
    (selScale (F := F) f).eval envK envF = (f st).eval envK := by
  have h0 := hone .decompose
  have h1 := hone .halt
  have h2 := hone .read_root
  have h3 := hone .verify_child
  simp only [mopCol] at h0 h1 h2 h3
  cases st <;>
    simp [selScale, MixedExpr.eval, MixedExpr.ofExpr_eval, bcur, CoeffExpr.eval, h0, h1, h2, h3]

theorem paperClassGate_mem_mixed
    (b : Basis (Fin 3) F K) (q : ℕ) (hq : q ∈ paperClassIndices) :
    paperClassGate (K := K) (F := F) q ∈ mixedTransitionGates (F := F) (K := K) b := by
  change paperClassGate (K := K) (F := F) q ∈ paperKGates (K := K) (F := F) ++ [haltAtomMixed]
  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))))
  rw [mem_paperKGatesCore_iff]
  simp only [paperClassIndices, List.mem_append, List.mem_singleton] at hq
  rcases hq with ((hq | rfl) | hq) | hq
  · exact Or.inl ⟨q, hq, rfl⟩
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hq, rfl⟩)))))

theorem paper_qty_vanishes
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (st : MState)
    (hone : MemoryPaperFactorization.BaseOneHot
      (memoryBaseEnvAt P c (honestQm P c Qm) i) st)
    (q : ℕ) (hq : q ∈ paperClassIndices) :
    ((memQuantity (K := K) st q).subst memorySubst).eval
      (memorySourceEnvAt P c (honestQm P c Qm) i) = 0 := by
  have hg := mixed_at_family P c Qm hsat i _
    (paperClassGate_mem_mixed (K := K) P.optimized.basis q hq)
  simpa [paperClassGate, selScale_eval _ _ st hone] using hg

theorem paper_cons_vanishes
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (st : MState)
    (hone : MemoryPaperFactorization.BaseOneHot
      (memoryBaseEnvAt P c (honestQm P c Qm) i) st) :
    ((MemoryPaperFactorization.consDyckQuantity (K := K) st).subst memorySubst).eval
      (memorySourceEnvAt P c (honestQm P c Qm) i) = 0 := by
  have hmem : MemoryPaperFactorization.paperConsDyck (F := F) (K := K) ∈
      mixedTransitionGates (F := F) (K := K) P.optimized.basis := by
    refine List.mem_append_left _ ?_
    change MemoryPaperFactorization.paperConsDyck (F := F) (K := K) ∈
      paperKGates (K := K) (F := F)
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
    exact (mem_paperKGatesCore_iff _).2 (Or.inr (Or.inl rfl))
  have hg := mixed_at_family P c Qm hsat i _ hmem
  simpa [MemoryPaperFactorization.paperConsDyck,
    MemoryPaperFactorization.selScale_eval (F := F) (K := K)
      (memorySourceEnvAt P c (honestQm P c Qm) i)
      (memoryBaseEnvAt P c (honestQm P c Qm) i) st hone] using hg

/-- `eqBlk` at `read_root` from paper quantities. -/
theorem eqBlk_read_root_of_paper
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hone : MemoryPaperFactorization.BaseOneHot
      (memoryBaseEnvAt P c (honestQm P c Qm) i) .read_root)
    (hst : (decodeMemPub P (honestQm P c Qm) c i).st = .read_root) :
    eqBlk (lblMAt P (honestQm P c Qm) c i).2.1
      (decodeMemPub P (honestQm P c Qm) c i) := by
  set Qmh := honestQm P c Qm
  set envK := memorySourceEnvAt P c Qmh i
  set pub := decodeMemPub P Qmh c i
  have hsz : envK.trace 0 = envK.trace 5 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 0 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, mPt, mLc, fpCol, tc, extVar, sub_eq_zero] at h
    exact h
  have hdy : envK.trace 1 = envK.trace 6 := by
    have h := paper_cons_vanishes P c Qm hsat i .read_root hone
    rw [MemoryPaperFactorization.consDyckQuantity] at h
    simp [MemoryFactorizationScope.memQuantity,
      paddedBlock, blockReadRoot, Expr.subst,
      memorySubst, Expr.eval, mPt, mLc, fpCol, tc, extVar, sub_eq_zero] at h
    exact h
  have hlf : envK.trace 2 = envK.trace 7 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 2 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, mPt, mLc, fpCol, tc, extVar, sub_eq_zero] at h
    exact h
  have hind : envK.trace 3 = envK.trace 8 -
      (Expr.subst memorySubst (lamScaleE (K := K))).eval envK * envK.trace 25 * envK.trace 26 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 3 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, tc, extVar, sub_eq_zero] at h
    exact h
  have hcnt : envK.trace 4 = envK.trace 9 -
      envK.trace 25 * (Expr.subst memorySubst recC').eval envK * envK.trace 26 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 4 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, tc, extVar, sub_eq_zero] at h
    exact h
  have hroot0 : envK.trace 19 = envK.trace 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 15 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, mMem, mPt, fpCol, tc, extVar, sub_eq_zero] at h
    exact h
  have hroot1 : envK.trace 20 = envK.trace 1 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 16 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, mMem, mPt, fpCol, tc, extVar, sub_eq_zero] at h
    exact h
  have hroot2 : envK.trace 21 = envK.trace 2 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 17 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, mMem, mPt, fpCol, tc, extVar, sub_eq_zero] at h
    exact h
  have hrc0 : envK.trace 10 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 10 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, mRc, fpCol, tc, extVar] at h
    exact h
  have hrc1 : envK.trace 11 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 11 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, mRc, fpCol, tc, extVar] at h
    exact h
  have hrc2 : envK.trace 12 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 12 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, mRc, fpCol, tc, extVar] at h
    exact h
  have hrcI : envK.trace 13 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 13 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h
    exact h
  have hrcC : envK.trace 14 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .read_root hone 14 (by decide)
    simp [memQuantity, paddedBlock, blockReadRoot, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h
    exact h
  have hlcSt : pub.lcSt = .read_root := by
    simp only [pub, decodeMemPub]
    have hstF : memoryStateOf (memoryBaseEnvAt P c Qmh i) = .read_root :=
      memoryStateOf_eq_of_baseOneHot _ _ hone
    simp [hstF]
  simp only [eqBlk, hst]
  refine ⟨?noun, hlcSt, ?ind, ?cnt, ?root, ?rc⟩
  · refine ComputeTable.FP.ext ?_ ?_ ?_
    · change pub.pt.noun.size = pub.lc.noun.size
      simpa [pub, decodeMemPub, memoryPtNoun] using hsz
    · change pub.pt.noun.dyck = pub.lc.noun.dyck
      simpa [pub, decodeMemPub, memoryPtNoun] using hdy
    · change pub.pt.noun.leaf = pub.lc.noun.leaf
      simpa [pub, decodeMemPub, memoryPtNoun] using hlf
  · change pub.pt.indicator =
        pub.lc.indicator - pub.lambda ^ MemoryTable.pwScaleExp K * pub.mem.axis * pub.mem.ts
    have hchip := lamScaleE_eval_memorySubst (K := K) envK
    simp [pub, decodeMemPub, Pub.lambda]
    rw [hchip] at hind
    exact hind
  · change pub.pt.counts = pub.lc.counts - pub.mem.axis * pub.cprime * pub.mem.ts
    have hchip := recC'_eval_memorySubst (K := K) envK
    simp [pub, decodeMemPub, Pub.cprime]
    rw [hchip] at hcnt
    exact hcnt
  · refine ComputeTable.FP.ext ?_ ?_ ?_
    · change pub.mem.root.size = pub.pt.noun.size
      simpa [pub, decodeMemPub, memoryMemRoot, memoryPtNoun] using hroot0
    · change pub.mem.root.dyck = pub.pt.noun.dyck
      simpa [pub, decodeMemPub, memoryMemRoot, memoryPtNoun] using hroot1
    · change pub.mem.root.leaf = pub.pt.noun.leaf
      simpa [pub, decodeMemPub, memoryMemRoot, memoryPtNoun] using hroot2
  · change pub.rc = Cell.zero
    refine (Cell.zero_iff _).2 ⟨?_, ?_, ?_⟩
    · refine ComputeTable.FP.ext ?_ ?_ ?_
      · simpa [pub, decodeMemPub, Cell.zero] using hrc0
      · simpa [pub, decodeMemPub, Cell.zero] using hrc1
      · simpa [pub, decodeMemPub, Cell.zero] using hrc2
    · simpa [pub, decodeMemPub, Cell.zero] using hrcI
    · simpa [pub, decodeMemPub, Cell.zero] using hrcC

/-- `eqBlk` at `verify_child` from paper quantities. -/
theorem eqBlk_verify_child_of_paper
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hone : MemoryPaperFactorization.BaseOneHot
      (memoryBaseEnvAt P c (honestQm P c Qm) i) .verify_child)
    (hst : (decodeMemPub P (honestQm P c Qm) c i).st = .verify_child) :
    eqBlk (lblMAt P (honestQm P c Qm) c i).2.1
      (decodeMemPub P (honestQm P c Qm) c i) := by
  set Qmh := honestQm P c Qm
  set envK := memorySourceEnvAt P c Qmh i
  set pub := decodeMemPub P Qmh c i
  have hsz : envK.trace 0 = envK.trace 5 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 0 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, mPt, mLc, fpCol, tc, extVar, sub_eq_zero] at h; exact h
  have hdy : envK.trace 1 = envK.trace 6 := by
    have h := paper_cons_vanishes P c Qm hsat i .verify_child hone
    rw [MemoryPaperFactorization.consDyckQuantity] at h
    simp [MemoryFactorizationScope.memQuantity,
      paddedBlock, blockVerifyChild, Expr.subst,
      memorySubst, Expr.eval, mPt, mLc, fpCol, tc, extVar, sub_eq_zero] at h; exact h
  have hlf : envK.trace 2 = envK.trace 7 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 2 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, mPt, mLc, fpCol, tc, extVar, sub_eq_zero] at h; exact h
  have hind : envK.trace 3 = envK.trace 8 +
      (Expr.subst memorySubst (lamScaleE (K := K))).eval envK * envK.trace 26 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 3 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, tc, extVar, sub_eq_zero] at h; exact h
  have hcnt : envK.trace 4 = envK.trace 9 +
      (Expr.subst memorySubst (lamScaleE (K := K))).eval envK * envK.trace 26 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 4 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, tc, extVar, sub_eq_zero] at h; exact h
  have hch0 : envK.trace 22 = envK.trace 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 18 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, mMem, mPt, fpCol, tc, extVar, sub_eq_zero] at h; exact h
  have hch1 : envK.trace 23 = envK.trace 1 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 19 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, mMem, mPt, fpCol, tc, extVar, sub_eq_zero] at h; exact h
  have hch2 : envK.trace 24 = envK.trace 2 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 20 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, mMem, mPt, fpCol, tc, extVar, sub_eq_zero] at h; exact h
  have hrc0 : envK.trace 10 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 10 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, mRc, fpCol, tc, extVar] at h; exact h
  have hrc1 : envK.trace 11 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 11 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, mRc, fpCol, tc, extVar] at h; exact h
  have hrc2 : envK.trace 12 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 12 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, mRc, fpCol, tc, extVar] at h; exact h
  have hrcI : envK.trace 13 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 13 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  have hrcC : envK.trace 14 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .verify_child hone 14 (by decide)
    simp [memQuantity, paddedBlock, blockVerifyChild, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  have hlcSt : pub.lcSt = .verify_child := by
    simp only [pub, decodeMemPub]
    have hstF : memoryStateOf (memoryBaseEnvAt P c Qmh i) = .verify_child :=
      memoryStateOf_eq_of_baseOneHot _ _ hone
    simp [hstF]
  simp only [eqBlk, hst]
  refine ⟨?noun, hlcSt, ?ind, ?cnt, ?child, ?rc⟩
  · refine ComputeTable.FP.ext ?_ ?_ ?_
    · simpa [pub, decodeMemPub, memoryPtNoun] using hsz
    · simpa [pub, decodeMemPub, memoryPtNoun] using hdy
    · simpa [pub, decodeMemPub, memoryPtNoun] using hlf
  · have hchip := lamScaleE_eval_memorySubst (K := K) envK
    simp [pub, decodeMemPub, Pub.lambda]
    rw [hchip] at hind
    exact hind
  · have hchip := lamScaleE_eval_memorySubst (K := K) envK
    simp [pub, decodeMemPub, Pub.lambda]
    rw [hchip] at hcnt
    exact hcnt
  · refine ComputeTable.FP.ext ?_ ?_ ?_
    · simpa [pub, decodeMemPub, memoryMemChild, memoryPtNoun] using hch0
    · simpa [pub, decodeMemPub, memoryMemChild, memoryPtNoun] using hch1
    · simpa [pub, decodeMemPub, memoryMemChild, memoryPtNoun] using hch2
  · refine (Cell.zero_iff _).2 ⟨?_, ?_, ?_⟩
    · refine ComputeTable.FP.ext ?_ ?_ ?_
      · simpa [pub, decodeMemPub, Cell.zero] using hrc0
      · simpa [pub, decodeMemPub, Cell.zero] using hrc1
      · simpa [pub, decodeMemPub, Cell.zero] using hrc2
    · simpa [pub, decodeMemPub, Cell.zero] using hrcI
    · simpa [pub, decodeMemPub, Cell.zero] using hrcC

/-- `eqBlk` at `halt` from paper quantities. -/
theorem eqBlk_halt_of_paper
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hone : MemoryPaperFactorization.BaseOneHot
      (memoryBaseEnvAt P c (honestQm P c Qm) i) .halt)
    (hst : (decodeMemPub P (honestQm P c Qm) c i).st = .halt) :
    eqBlk (lblMAt P (honestQm P c Qm) c i).2.1
      (decodeMemPub P (honestQm P c Qm) c i) := by
  set Qmh := honestQm P c Qm
  set envK := memorySourceEnvAt P c Qmh i
  set pub := decodeMemPub P Qmh c i
  have hz0 := memorySourceEnvAt_chal0 P c Qmh i
  have hsz : envK.trace 0 = envK.chal 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 0 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mPt, fpCol, tc, chl, extVar, sub_eq_zero] at h
    exact h
  have hdy : envK.trace 1 = 0 := by
    have h := paper_cons_vanishes P c Qm hsat i .halt hone
    rw [MemoryPaperFactorization.consDyckQuantity] at h
    simp [MemoryFactorizationScope.memQuantity,
      paddedBlock, blockHalt, Expr.subst,
      memorySubst, Expr.eval, mPt, fpCol, tc, extVar] at h
    exact h
  have hind : envK.trace 3 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 3 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  have hcnt : envK.trace 4 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 4 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  have hlc0 : envK.trace 5 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 5 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mLc, fpCol, tc, extVar] at h; exact h
  have hlc1 : envK.trace 6 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 6 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mLc, fpCol, tc, extVar] at h; exact h
  have hlc2 : envK.trace 7 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 7 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mLc, fpCol, tc, extVar] at h; exact h
  have hlcI : envK.trace 8 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 8 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  have hlcC : envK.trace 9 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 9 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  have hrc0 : envK.trace 10 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 10 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mRc, fpCol, tc, extVar] at h; exact h
  have hrc1 : envK.trace 11 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 11 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mRc, fpCol, tc, extVar] at h; exact h
  have hrc2 : envK.trace 12 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 12 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mRc, fpCol, tc, extVar] at h; exact h
  have hrcI : envK.trace 13 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 13 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  have hrcC : envK.trace 14 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 14 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  have hr0 : envK.trace 19 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 15 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hr1 : envK.trace 20 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 16 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hr2 : envK.trace 21 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 17 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hc0 : envK.trace 22 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 18 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hc1 : envK.trace 23 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 19 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hc2 : envK.trace 24 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 20 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hax : envK.trace 25 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 21 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  have hts : envK.trace 26 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .halt hone 22 (by decide)
    simp [memQuantity, paddedBlock, blockHalt, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  simp only [eqBlk, hst]
  refine ⟨?sz, ?dy, ?ind, ?cnt, ?lc, ?rc, ?mem⟩
  · change pub.pt.noun.size = nprSeed c.1
    have h := hsz.trans hz0
    simpa [pub, decodeMemPub, memoryPtNoun, envK] using h
  · change pub.pt.noun.dyck = 0
    simpa [pub, decodeMemPub, memoryPtNoun, envK] using hdy
  · change pub.pt.indicator = 0
    simpa [pub, decodeMemPub, envK] using hind
  · change pub.pt.counts = 0
    simpa [pub, decodeMemPub, envK] using hcnt
  · refine (Cell.zero_iff _).2 ⟨?_, ?_, ?_⟩
    · refine FP.ext ?_ ?_ ?_
      · simpa [pub, decodeMemPub, Cell.zero, envK] using hlc0
      · simpa [pub, decodeMemPub, Cell.zero, envK] using hlc1
      · simpa [pub, decodeMemPub, Cell.zero, envK] using hlc2
    · simpa [pub, decodeMemPub, Cell.zero, envK] using hlcI
    · simpa [pub, decodeMemPub, Cell.zero, envK] using hlcC
  · refine (Cell.zero_iff _).2 ⟨?_, ?_, ?_⟩
    · refine FP.ext ?_ ?_ ?_
      · simpa [pub, decodeMemPub, Cell.zero, envK] using hrc0
      · simpa [pub, decodeMemPub, Cell.zero, envK] using hrc1
      · simpa [pub, decodeMemPub, Cell.zero, envK] using hrc2
    · simpa [pub, decodeMemPub, Cell.zero, envK] using hrcI
    · simpa [pub, decodeMemPub, Cell.zero, envK] using hrcC
  · refine MemRec.ext ?_ ?_ ?_ ?_
    · refine FP.ext ?_ ?_ ?_
      · change pub.mem.root.size = 0
        simpa [pub, decodeMemPub, memoryMemRoot, envK] using hr0
      · change pub.mem.root.dyck = 0
        simpa [pub, decodeMemPub, memoryMemRoot, envK] using hr1
      · change pub.mem.root.leaf = 0
        simpa [pub, decodeMemPub, memoryMemRoot, envK] using hr2
    · refine FP.ext ?_ ?_ ?_
      · change pub.mem.child.size = 0
        simpa [pub, decodeMemPub, memoryMemChild, envK] using hc0
      · change pub.mem.child.dyck = 0
        simpa [pub, decodeMemPub, memoryMemChild, envK] using hc1
      · change pub.mem.child.leaf = 0
        simpa [pub, decodeMemPub, memoryMemChild, envK] using hc2
    · change pub.mem.axis = 0
      simpa [pub, decodeMemPub, envK] using hax
    · change pub.mem.ts = 0
      simpa [pub, decodeMemPub, envK] using hts

/-- `eqBlk` at `decompose` from paper quantities.
Dyck uses the inverse-free paper form (`mconsDyckNoInv`) then divides by `z ≠ 0`. -/
theorem eqBlk_decompose_of_paper
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hone : MemoryPaperFactorization.BaseOneHot
      (memoryBaseEnvAt P c (honestQm P c Qm) i) .decompose)
    (hst : (decodeMemPub P (honestQm P c Qm) c i).st = .decompose)
    (hz : nprSeed c.1 ≠ 0) :
    eqBlk (lblMAt P (honestQm P c Qm) c i).2.1
      (decodeMemPub P (honestQm P c Qm) c i) := by
  set Qmh := honestQm P c Qm
  set envK := memorySourceEnvAt P c Qmh i
  set pub := decodeMemPub P Qmh c i
  set z : K := nprSeed c.1
  have hz0 : envK.chal 0 = z := memorySourceEnvAt_chal0 P c Qmh i
  have hsz : envK.trace 0 = envK.trace 5 * envK.trace 10 := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 0 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, mPt, mLc, mRc, mconsExpr, fpCol, tc, extVar, sub_eq_zero] at h
    exact h
  have hdy_scaled :
      envK.chal 0 * envK.trace 1 =
        envK.chal 0 ^ 2 * envK.trace 6 + envK.trace 5 * envK.trace 5 +
          envK.chal 0 * envK.trace 5 * envK.trace 5 * envK.trace 11 := by
    have h := paper_cons_vanishes P c Qm hsat i .decompose hone
    simp [MemoryPaperFactorization.consDyckQuantity, Expr.subst, memorySubst, Expr.eval, mPt, mLc, mRc,
      fpCol, tc, chl, extVar, MemoryFactorizationScope.mconsDyckNoInv,
      sub_eq_zero] at h
    convert h using 1 <;> try ring
  have hdy : envK.trace 1 =
      z * envK.trace 6 + envK.trace 5 * envK.trace 5 * z⁻¹ +
        envK.trace 5 * envK.trace 5 * envK.trace 11 := by
    have h := hdy_scaled
    rw [hz0] at h
    have h' : envK.trace 1 = z⁻¹ * (z * envK.trace 1) := by field_simp [hz]
    rw [h', h]
    field_simp [hz]
    try ring
  have hlf : envK.trace 2 =
      envK.trace 7 + envK.trace 5 * envK.trace 12 := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 2 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, mPt, mLc, mRc, mconsExpr, fpCol, tc, extVar, sub_eq_zero] at h
    exact h
  have hind : envK.trace 3 =
      (Expr.subst memorySubst lamE).eval envK * (envK.trace 8 + envK.trace 13) := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 3 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, tc, extVar, sub_eq_zero] at h; exact h
  have hcnt : envK.trace 4 =
      envK.trace 9 + envK.trace 14 +
        ((Expr.subst memorySubst lamE).eval envK - 1) * (envK.trace 8 + envK.trace 13) +
          envK.trace 13 := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 4 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, tc, extVar, sub_eq_zero] at h
    convert h using 1 <;> try ring
  have hr0 : envK.trace 19 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 15 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hr1 : envK.trace 20 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 16 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hr2 : envK.trace 21 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 17 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hc0 : envK.trace 22 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 18 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hc1 : envK.trace 23 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 19 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hc2 : envK.trace 24 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 20 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, mMem, fpCol, tc, extVar] at h; exact h
  have hax : envK.trace 25 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 21 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  have hts : envK.trace 26 = 0 := by
    have h := paper_qty_vanishes P c Qm hsat i .decompose hone 22 (by decide)
    simp [memQuantity, paddedBlock, blockDecompose, Expr.subst, memorySubst,
      Expr.eval, tc, extVar] at h; exact h
  simp only [eqBlk, hst]
  refine ⟨?noun, ?ind, ?cnt, ?mem⟩
  · refine FP.ext ?_ ?_ ?_
    · change pub.pt.noun.size = pub.lc.noun.size * pub.rc.noun.size
      simpa [pub, decodeMemPub, memoryPtNoun, envK] using hsz
    · change pub.pt.noun.dyck =
        (FP.cons (lblMAt P Qmh c i).2.1.z pub.lc.noun pub.rc.noun).dyck
      simp only [pub, decodeMemPub, memoryPtNoun, FP.cons, lblMAt, envK]
      -- goal: envK.trace 1 = z * … with z = nprSeed
      simpa [z] using hdy
    · change pub.pt.noun.leaf =
        pub.lc.noun.leaf + pub.lc.noun.size * pub.rc.noun.leaf
      simpa [pub, decodeMemPub, memoryPtNoun, envK] using hlf
  · change pub.pt.indicator = pub.lambda * (pub.lc.indicator + pub.rc.indicator)
    have hchip := lamE_eval_memorySubst (K := K) envK
    simp [pub, decodeMemPub, Pub.lambda, envK]
    rw [hchip] at hind
    exact hind
  · change pub.pt.counts = pub.lc.counts + pub.rc.counts
        + (pub.lambda - 1) * (pub.lc.indicator + pub.rc.indicator) + pub.rc.indicator
    have hchip := lamE_eval_memorySubst (K := K) envK
    simp [pub, decodeMemPub, Pub.lambda, envK]
    rw [hchip] at hcnt
    exact hcnt
  · refine MemRec.ext ?_ ?_ ?_ ?_
    · refine FP.ext ?_ ?_ ?_
      · change pub.mem.root.size = 0
        simpa [pub, decodeMemPub, memoryMemRoot, envK] using hr0
      · change pub.mem.root.dyck = 0
        simpa [pub, decodeMemPub, memoryMemRoot, envK] using hr1
      · change pub.mem.root.leaf = 0
        simpa [pub, decodeMemPub, memoryMemRoot, envK] using hr2
    · refine FP.ext ?_ ?_ ?_
      · change pub.mem.child.size = 0
        simpa [pub, decodeMemPub, memoryMemChild, envK] using hc0
      · change pub.mem.child.dyck = 0
        simpa [pub, decodeMemPub, memoryMemChild, envK] using hc1
      · change pub.mem.child.leaf = 0
        simpa [pub, decodeMemPub, memoryMemChild, envK] using hc2
    · change pub.mem.axis = 0
      simpa [pub, decodeMemPub, envK] using hax
    · change pub.mem.ts = 0
      simpa [pub, decodeMemPub, envK] using hts

/-- `eqBlk` from paper quantities at any one-hot family row. -/
theorem eqBlk_of_paper_classes
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (st : MState)
    (hone : MemoryPaperFactorization.BaseOneHot
      (memoryBaseEnvAt P c (honestQm P c Qm) i) st)
    (hst : (decodeMemPub P (honestQm P c Qm) c i).st = st)
    (hz : nprSeed c.1 ≠ 0) :
    eqBlk (lblMAt P (honestQm P c Qm) c i).2.1
      (decodeMemPub P (honestQm P c Qm) c i) := by
  cases st with
  | read_root =>
      exact eqBlk_read_root_of_paper P c Qm hsat i hone hst
  | verify_child =>
      exact eqBlk_verify_child_of_paper P c Qm hsat i hone hst
  | decompose =>
      exact eqBlk_decompose_of_paper P c Qm hsat i hone hst hz
  | halt =>
      exact eqBlk_halt_of_paper P c Qm hsat i hone hst

/-- A6: decoded `λ` is the sampled tuple coin at memory slot 8 / `lamE`. -/
theorem decode_lambda_eq_sampled
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (decodeMemPub P Qm c i).lambda = c.2.2.2.lambda ∧
      (decodeMemPub P Qm c i).lambda = (memorySourceEnvAt P c Qm i).chal 8 ∧
      (Expr.subst memorySubst lamE).eval (memorySourceEnvAt P c Qm i) =
        (decodeMemPub P Qm c i).lambda := by
  have h8 := memorySourceEnvAt_chal8 P c Qm i
  refine ⟨?_, ?_, ?_⟩
  · rw [decodeMemPub_lambda, h8]
  · exact decodeMemPub_lambda P Qm c i
  · rw [lamE_eval_memorySubst, decodeMemPub_lambda]

end

end Nock.NockVMROM.Thm54.FamilyMemoryRows
