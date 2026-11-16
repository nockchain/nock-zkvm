/-
  Nock/RedTeam/Batch340Thm54MemoryTripleGates.lean

  **Measure the deployed memory chip's triple gates.**

  Paper re-read at source: `Lem:NPR_decomp` the paper, `Thm:Noun_Validation` `:1268`,
  `CheckValidNoun` `:1244`, `lem:ion_univariate_sec` `:1188`, `Def:NMR_poly` `:1303`,
  `tab:v_mem` `:2142-2166`, `Algorithm:Memspec` `:2056-2080`.

  The committed chip is `paperBaseGates` / `paperKGates`
  (`OptimizedMemoryGateBasis.memorySourceTemplate`, `Batch278.live_chip_commits_paper_gates`).
  Quantity order (`MemoryFactorizationScope` §3):

  ```
  0 pt.size   1 pt.dyck   2 pt.leaf
  15–17 mem.root.{size,dyck,leaf}
  18–20 mem.child.{size,dyck,leaf}
  ```

  Verdict (bodies, not docstrings):

  * (a) halt leaf triple — `tab:v_mem` `:2142` col halt is `(z, 0, ⊥)`.
    `q=0` pins `pt.size = z`, `paperConsDyck` pins `pt.dyck = 0`, `q=2` is
    `.Const 0` (the paper's `⊥`).  Atom *typing* is constrained; the atom *value*
    is free by the paper.  A leaf with `dt ≠ z` (size) or `dyck ≠ 0` is rejected.
  * (b) decompose composite — `q=0,2` plus `paperConsDyck` are
    `Lem:NPR_decomp` `:1218` (`mconsExpr` / `mconsDyckNoInv`).  Constrained.
  * (c) served record — `read_root` `q=15..17` is `mem.root = pt.noun`
    (`:2164`); `verify_child` `q=18..20` is `mem.child = pt.noun` (`:2166`).
    Constrained.  The other record half is paper `⊥` at each state.

  Instrument: `paperClassGate` / `paperConsDyck` membership in `paperKGates`
  (`mem_paperKGatesCore_iff`) and `MixedExpr.eval` at a base one-hot.
-/
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.MemoryPaperFactorization
import Nock.NockVMROM.Thm54.MemoryFactorizationScope

namespace Nock.RedTeam.Batch340

open Nock
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.MemoryFactorizationScope
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler.MixedExpr (ofExpr)
open Nock.MemoryTable (MState)

set_option maxHeartbeats 800000

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## §0  The deployed chip commits these gates -/

theorem live_chip_commits (b : Module.Basis (Fin 3) F K)
    [FiniteDimensional F K] :
    (memorySourceTemplate b).baseTransition =
      paperBaseGates (F := F) ++ [readRootVerGate b] ∧
      (memorySourceTemplate b).mixedTransition =
        paperKGates (K := K) (F := F) ++ [haltAtomMixed] :=
  ⟨rfl, rfl⟩

theorem classGate_mem (q : ℕ) (hq : q ∈ tabVMemClassIndices) :
    paperClassGate (K := K) (F := F) q ∈ paperKGates (K := K) (F := F) := by
  refine List.mem_append.mpr (.inl (List.mem_append.mpr (.inl ?_)))
  exact (mem_paperKGatesCore_iff _).2 (.inl ⟨q, hq, rfl⟩)

theorem consDyck_mem : paperConsDyck (K := K) (F := F) ∈ paperKGates (K := K) (F := F) := by
  refine List.mem_append.mpr (.inl (List.mem_append.mpr (.inl ?_)))
  exact (mem_paperKGatesCore_iff _).2 (.inr (.inl rfl))

theorem classGate0_mem : paperClassGate (K := K) (F := F) 0 ∈ paperKGates (K := K) :=
  classGate_mem 0 (by decide)

theorem classGate2_mem : paperClassGate (K := K) (F := F) 2 ∈ paperKGates (K := K) :=
  classGate_mem 2 (by decide)

theorem classGate15_mem : paperClassGate (K := K) (F := F) 15 ∈ paperKGates (K := K) :=
  classGate_mem 15 (by decide)

theorem classGate16_mem : paperClassGate (K := K) (F := F) 16 ∈ paperKGates (K := K) :=
  classGate_mem 16 (by decide)

theorem classGate17_mem : paperClassGate (K := K) (F := F) 17 ∈ paperKGates (K := K) :=
  classGate_mem 17 (by decide)

theorem classGate18_mem : paperClassGate (K := K) (F := F) 18 ∈ paperKGates (K := K) :=
  classGate_mem 18 (by decide)

theorem classGate19_mem : paperClassGate (K := K) (F := F) 19 ∈ paperKGates (K := K) :=
  classGate_mem 19 (by decide)

theorem classGate20_mem : paperClassGate (K := K) (F := F) 20 ∈ paperKGates (K := K) :=
  classGate_mem 20 (by decide)

/-! ## §1  One-hot evaluation of a class gate -/

theorem classGate_eval_halt (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 1)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 0) (q : ℕ) :
    (paperClassGate (K := K) (F := F) q).eval envK envF
      = ((memQuantity (K := K) .halt q).subst memorySubst).eval envK := by
  simp [paperClassGate, selScale, MixedExpr.eval, MixedExpr.ofExpr_eval,
    bcur, CoeffExpr.eval, h0, h1, h2, h3]

theorem classGate_eval_decompose (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 1) (h1 : envF.trace 1 = 0)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 0) (q : ℕ) :
    (paperClassGate (K := K) (F := F) q).eval envK envF
      = ((memQuantity (K := K) .decompose q).subst memorySubst).eval envK := by
  simp [paperClassGate, selScale, MixedExpr.eval, MixedExpr.ofExpr_eval,
    bcur, CoeffExpr.eval, h0, h1, h2, h3]

theorem classGate_eval_readRoot (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 0)
    (h2 : envF.trace 2 = 1) (h3 : envF.trace 3 = 0) (q : ℕ) :
    (paperClassGate (K := K) (F := F) q).eval envK envF
      = ((memQuantity (K := K) .read_root q).subst memorySubst).eval envK := by
  simp [paperClassGate, selScale, MixedExpr.eval, MixedExpr.ofExpr_eval,
    bcur, CoeffExpr.eval, h0, h1, h2, h3]

theorem classGate_eval_verifyChild (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 0)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 1) (q : ℕ) :
    (paperClassGate (K := K) (F := F) q).eval envK envF
      = ((memQuantity (K := K) .verify_child q).subst memorySubst).eval envK := by
  simp [paperClassGate, selScale, MixedExpr.eval, MixedExpr.ofExpr_eval,
    bcur, CoeffExpr.eval, h0, h1, h2, h3]

theorem consDyck_eval_halt (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 1)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 0) :
    (paperConsDyck (K := K) (F := F)).eval envK envF
      = ((memQuantity (K := K) .halt 1).subst memorySubst).eval envK := by
  simp [paperConsDyck, consDyckQuantity, selScale, MixedExpr.eval,
    MixedExpr.ofExpr_eval, bcur, CoeffExpr.eval, h0, h1, h2, h3]

theorem consDyck_eval_decompose (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 1) (h1 : envF.trace 1 = 0)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 0) :
    (paperConsDyck (K := K) (F := F)).eval envK envF
      = ((consDyckQuantity (K := K) .decompose).subst memorySubst).eval envK := by
  simp [paperConsDyck, selScale, MixedExpr.eval, MixedExpr.ofExpr_eval,
    bcur, CoeffExpr.eval, h0, h1, h2, h3]

/-! ## §2  Role readers after `memorySubst` (`table col i ↦ role i−4` for `4 ≤ i < 35`) -/

theorem subst_pt_size (envK : Env K) :
    ((mPt.size).subst memorySubst).eval envK = envK.trace 0 := by
  simp [mPt, fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]

theorem subst_pt_dyck (envK : Env K) :
    ((mPt.dyck).subst memorySubst).eval envK = envK.trace 1 := by
  simp [mPt, fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]

theorem subst_pt_leaf (envK : Env K) :
    ((mPt.leaf).subst memorySubst).eval envK = envK.trace 2 := by
  simp [mPt, fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]

theorem subst_z (envK : Env K) :
    ((chl 0).subst memorySubst).eval envK = envK.chal 0 := by
  simp [chl, Expr.subst, memorySubst, Expr.eval]

theorem subst_lc_size (envK : Env K) :
    ((mLc.size).subst memorySubst).eval envK = envK.trace 5 := by
  simp [mLc, fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]

theorem subst_rc_size (envK : Env K) :
    ((mRc.size).subst memorySubst).eval envK = envK.trace 10 := by
  simp [mRc, fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]

theorem subst_memRoot_size (envK : Env K) :
    ((mMem.root.size).subst memorySubst).eval envK = envK.trace 19 := by
  simp [mMem, mrCol, fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]

theorem subst_memRoot_dyck (envK : Env K) :
    ((mMem.root.dyck).subst memorySubst).eval envK = envK.trace 20 := by
  simp [mMem, mrCol, fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]

theorem subst_memRoot_leaf (envK : Env K) :
    ((mMem.root.leaf).subst memorySubst).eval envK = envK.trace 21 := by
  simp [mMem, mrCol, fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]

theorem subst_memChild_size (envK : Env K) :
    ((mMem.child.size).subst memorySubst).eval envK = envK.trace 22 := by
  simp [mMem, mrCol, fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]

theorem subst_memChild_dyck (envK : Env K) :
    ((mMem.child.dyck).subst memorySubst).eval envK = envK.trace 23 := by
  simp [mMem, mrCol, fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]

theorem subst_memChild_leaf (envK : Env K) :
    ((mMem.child.leaf).subst memorySubst).eval envK = envK.trace 24 := by
  simp [mMem, mrCol, fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]


theorem halt_size_gate (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 1)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 0) :
    (paperClassGate (K := K) (F := F) 0).eval envK envF = envK.trace 0 - envK.chal 0 := by
  rw [classGate_eval_halt envK envF h0 h1 h2 h3 0]
  simp [memQuantity, paddedBlock, blockHalt, mPt, fpCol, tc, chl,
    Expr.subst, memorySubst, extVar, Expr.eval]

theorem halt_size_eq_of_accept (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 1)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 0)
    (hacc : ∀ g ∈ paperKGates (K := K) (F := F), g.eval envK envF = 0) :
    envK.trace 0 = envK.chal 0 := by
  have := hacc _ classGate0_mem
  rw [halt_size_gate envK envF h0 h1 h2 h3] at this
  exact sub_eq_zero.mp this

theorem halt_dyck_gate (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 1)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 0) :
    (paperConsDyck (K := K) (F := F)).eval envK envF = envK.trace 1 := by
  rw [consDyck_eval_halt envK envF h0 h1 h2 h3]
  simp [memQuantity, paddedBlock, blockHalt, mPt, fpCol, tc, Expr.subst,
    memorySubst, extVar, Expr.eval]

theorem halt_dyck_eq_zero_of_accept (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 1)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 0)
    (hacc : ∀ g ∈ paperKGates (K := K) (F := F), g.eval envK envF = 0) :
    envK.trace 1 = 0 := by
  have := hacc _ consDyck_mem
  rw [halt_dyck_gate envK envF h0 h1 h2 h3] at this
  exact this

/-- Paper `⊥`: the halt leaf-value class is the zero expression. -/
theorem halt_leaf_quantity_vacuous : memQuantity (K := K) .halt 2 = (Expr.Const 0) := rfl

theorem halt_leaf_gate_zero (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 1)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 0) :
    (paperClassGate (K := K) (F := F) 2).eval envK envF = 0 := by
  rw [classGate_eval_halt envK envF h0 h1 h2 h3 2]
  simp [memQuantity, paddedBlock, blockHalt, Expr.subst, Expr.eval]

/-! ## §4  (b) decompose composite — size half -/

theorem decompose_size_gate (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 1) (h1 : envF.trace 1 = 0)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 0) :
    (paperClassGate (K := K) (F := F) 0).eval envK envF
      = envK.trace 0 - envK.trace 5 * envK.trace 10 := by
  rw [classGate_eval_decompose envK envF h0 h1 h2 h3 0]
  simp [memQuantity, paddedBlock, blockDecompose, mconsExpr, mPt, mLc, mRc,
    fpCol, tc, Expr.subst, memorySubst, extVar, Expr.eval]

theorem decompose_size_eq_of_accept (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 1) (h1 : envF.trace 1 = 0)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 0)
    (hacc : ∀ g ∈ paperKGates (K := K) (F := F), g.eval envK envF = 0) :
    envK.trace 0 = envK.trace 5 * envK.trace 10 := by
  have := hacc _ classGate0_mem
  rw [decompose_size_gate envK envF h0 h1 h2 h3] at this
  exact sub_eq_zero.mp this

/-! ## §5  (c) served record -/

theorem readRoot_memRoot_size_gate (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 0)
    (h2 : envF.trace 2 = 1) (h3 : envF.trace 3 = 0) :
    (paperClassGate (K := K) (F := F) 15).eval envK envF
      = envK.trace 19 - envK.trace 0 := by
  rw [classGate_eval_readRoot envK envF h0 h1 h2 h3 15]
  simp [memQuantity, paddedBlock, blockReadRoot, mMem, mPt, mrCol, fpCol, tc,
    Expr.subst, memorySubst, extVar, Expr.eval]

theorem readRoot_memRoot_size_eq_of_accept (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 0)
    (h2 : envF.trace 2 = 1) (h3 : envF.trace 3 = 0)
    (hacc : ∀ g ∈ paperKGates (K := K) (F := F), g.eval envK envF = 0) :
    envK.trace 19 = envK.trace 0 := by
  have := hacc _ classGate15_mem
  rw [readRoot_memRoot_size_gate envK envF h0 h1 h2 h3] at this
  exact sub_eq_zero.mp this

theorem verifyChild_memChild_size_gate (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 0)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 1) :
    (paperClassGate (K := K) (F := F) 18).eval envK envF
      = envK.trace 22 - envK.trace 0 := by
  rw [classGate_eval_verifyChild envK envF h0 h1 h2 h3 18]
  simp [memQuantity, paddedBlock, blockVerifyChild, mMem, mPt, mrCol, fpCol, tc,
    Expr.subst, memorySubst, extVar, Expr.eval]

theorem verifyChild_memChild_size_eq_of_accept (envK : Env K) (envF : Env F)
    (h0 : envF.trace 0 = 0) (h1 : envF.trace 1 = 0)
    (h2 : envF.trace 2 = 0) (h3 : envF.trace 3 = 1)
    (hacc : ∀ g ∈ paperKGates (K := K) (F := F), g.eval envK envF = 0) :
    envK.trace 22 = envK.trace 0 := by
  have := hacc _ classGate18_mem
  rw [verifyChild_memChild_size_gate envK envF h0 h1 h2 h3] at this
  exact sub_eq_zero.mp this

/-! ## §6  Negative controls over `ℚ` (no `GaloisField`, no `decide` at a cubic) -/

def haltOneHot : Env ℚ where
  trace := fun i => if i = 1 then 1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

theorem haltOneHot_sel :
    haltOneHot.trace 0 = 0 ∧ haltOneHot.trace 1 = 1 ∧
      haltOneHot.trace 2 = 0 ∧ haltOneHot.trace 3 = 0 := by
  simp [haltOneHot]

def envK_pt (size dyck leaf z : ℚ) : Env ℚ where
  trace := fun i =>
    if i = 0 then size else if i = 1 then dyck else if i = 2 then leaf else 0
  traceNext := fun _ => 0
  chal := fun i => if i = 0 then z else 0
  pub := fun _ => 0

/-- Negative control (a): a halt row with `dt ≠ z` (`pt.size = 2`, `z = 1`) is
rejected by `paperClassGate 0`. -/
theorem halt_bad_size_rejected :
    (paperClassGate (K := ℚ) (F := ℚ) 0).eval (envK_pt 2 0 0 1) haltOneHot ≠ 0 := by
  have ⟨h0, h1, h2, h3⟩ := haltOneHot_sel
  rw [halt_size_gate (F := ℚ) (envK_pt 2 0 0 1) haltOneHot h0 h1 h2 h3]
  simp [envK_pt]; norm_num

/-- Negative control (a): a halt row with `dyck ≠ 0` is rejected by `paperConsDyck`. -/
theorem halt_bad_dyck_rejected :
    (paperConsDyck (K := ℚ) (F := ℚ)).eval (envK_pt 1 1 0 1) haltOneHot ≠ 0 := by
  have ⟨h0, h1, h2, h3⟩ := haltOneHot_sel
  rw [halt_dyck_gate (F := ℚ) (envK_pt 1 1 0 1) haltOneHot h0 h1 h2 h3]
  simp [envK_pt]

/-- Paper `⊥`: any halt leaf value still zeroes the leaf-value class. -/
theorem halt_any_leaf_accepted_by_leaf_gate (v : ℚ) :
    (paperClassGate (K := ℚ) (F := ℚ) 2).eval (envK_pt 1 0 v 1) haltOneHot = 0 := by
  have ⟨h0, h1, h2, h3⟩ := haltOneHot_sel
  exact halt_leaf_gate_zero (F := ℚ) (envK_pt 1 0 v 1) haltOneHot h0 h1 h2 h3

def decomposeOneHot : Env ℚ where
  trace := fun i => if i = 0 then 1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

def envK_decomp (ptS lcS rcS : ℚ) : Env ℚ where
  trace := fun i =>
    if i = 0 then ptS else if i = 5 then lcS else if i = 10 then rcS else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

/-- Negative control (b): a decompose row with `pt.size ≠ lc.size · rc.size` is
rejected by `paperClassGate 0`. -/
theorem decompose_bad_composite_rejected :
    (paperClassGate (K := ℚ) (F := ℚ) 0).eval (envK_decomp 2 1 1) decomposeOneHot ≠ 0 := by
  have h0 : decomposeOneHot.trace 0 = 1 := by simp [decomposeOneHot]
  have h1 : decomposeOneHot.trace 1 = 0 := by simp [decomposeOneHot]
  have h2 : decomposeOneHot.trace 2 = 0 := by simp [decomposeOneHot]
  have h3 : decomposeOneHot.trace 3 = 0 := by simp [decomposeOneHot]
  rw [decompose_size_gate (F := ℚ) (envK_decomp 2 1 1) decomposeOneHot h0 h1 h2 h3]
  simp [envK_decomp]; norm_num

def readRootOneHot : Env ℚ where
  trace := fun i => if i = 2 then 1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

def envK_read (ptS rootS : ℚ) : Env ℚ where
  trace := fun i => if i = 0 then ptS else if i = 19 then rootS else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

/-- Negative control (c): a `read_root` row with `mem.root.size ≠ pt.size` is
rejected by `paperClassGate 15`. -/
theorem readRoot_bad_record_rejected :
    (paperClassGate (K := ℚ) (F := ℚ) 15).eval (envK_read 1 2) readRootOneHot ≠ 0 := by
  have h0 : readRootOneHot.trace 0 = 0 := by simp [readRootOneHot]
  have h1 : readRootOneHot.trace 1 = 0 := by simp [readRootOneHot]
  have h2 : readRootOneHot.trace 2 = 1 := by simp [readRootOneHot]
  have h3 : readRootOneHot.trace 3 = 0 := by simp [readRootOneHot]
  rw [readRoot_memRoot_size_gate (F := ℚ) (envK_read 1 2) readRootOneHot h0 h1 h2 h3]
  simp [envK_read]; norm_num

def verifyChildOneHot : Env ℚ where
  trace := fun i => if i = 3 then 1 else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

def envK_verify (ptS childS : ℚ) : Env ℚ where
  trace := fun i => if i = 0 then ptS else if i = 22 then childS else 0
  traceNext := fun _ => 0
  chal := fun _ => 0
  pub := fun _ => 0

/-- Negative control (c): a `verify_child` row with `mem.child.size ≠ pt.size` is
rejected by `paperClassGate 18`. -/
theorem verifyChild_bad_record_rejected :
    (paperClassGate (K := ℚ) (F := ℚ) 18).eval (envK_verify 1 2) verifyChildOneHot ≠ 0 := by
  have h0 : verifyChildOneHot.trace 0 = 0 := by simp [verifyChildOneHot]
  have h1 : verifyChildOneHot.trace 1 = 0 := by simp [verifyChildOneHot]
  have h2 : verifyChildOneHot.trace 2 = 0 := by simp [verifyChildOneHot]
  have h3 : verifyChildOneHot.trace 3 = 1 := by simp [verifyChildOneHot]
  rw [verifyChild_memChild_size_gate (F := ℚ) (envK_verify 1 2) verifyChildOneHot
    h0 h1 h2 h3]
  simp [envK_verify]; norm_num

end

#print axioms Nock.RedTeam.Batch340.halt_bad_size_rejected
#print axioms Nock.RedTeam.Batch340.halt_bad_dyck_rejected
#print axioms Nock.RedTeam.Batch340.decompose_bad_composite_rejected
#print axioms Nock.RedTeam.Batch340.readRoot_bad_record_rejected
#print axioms Nock.RedTeam.Batch340.verifyChild_bad_record_rejected
#print axioms Nock.RedTeam.Batch340.halt_size_eq_of_accept
#print axioms Nock.RedTeam.Batch340.halt_dyck_eq_zero_of_accept
#print axioms Nock.RedTeam.Batch340.decompose_size_eq_of_accept

end Nock.RedTeam.Batch340
