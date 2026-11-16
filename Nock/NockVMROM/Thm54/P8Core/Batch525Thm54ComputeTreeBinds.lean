/-
  Nock/NockVMROM/Thm54/P8Core/Batch525Thm54ComputeTreeBinds.lean

  The
  remaining declarations stay in `Nock/RedTeam/Batch525Thm54ComputeTreeBinds.lean`, which imports this module. This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`. -/
import Nock.NockVMROM.Thm54.SemanticStrategy
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch525

open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.GlobalCarryRecognizer
variable {K : Type} [Field K] [DecidableEq K]

theorem bindFP_cons {z : K} (hz : z ≠ 0) (x y : Noun) (fx fy : FP K)
    (hx : bindFP z x fx) (hy : bindFP z y fy) :
    bindFP z (Noun.cell x y) (FP.cons z fx fy) := by
  rw [bindFP, enc_cons hz, ← hx, ← hy]

theorem bindFP_inc_atom {z : K} (k : ℕ) :
    bindFP z (Noun.atom (k + 1)) (FP.inc z (FP.atomFP z (k : K))) := by
  rw [bindFP, enc_atom]
  apply FP.ext
  · simp [FP.inc, FP.atomFP]
  · simp [FP.inc, FP.atomFP]
  · simp [FP.inc, FP.atomFP, Nat.cast_succ]

/-- Autocons skeleton (`genComputeSkeleton` cons branch). -/
def skelCons (subj fh ft eL eR : Noun) : ComputeRowSkeleton where
  state := .cons
  subject := subj
  formula := .cell fh ft
  evaluation := .cell eL eR
  decomposition := fun slot h =>
    match slot with
    | .f_h => fh
    | .f_t => ft
    | .f_th | .f_tt | .f_tth | .f_ttt => False.elim (by
        simp [decActive, hasTailDecomposition] at h)
  subformula := fun i _hi slot =>
    if i.val = 0 then
      match slot with
      | .subject => subj | .formula => fh | .result => eL
    else
      match slot with
      | .subject => subj | .formula => ft | .result => eR
  memoryRecord := fun i hi =>
    if i.val = 0 then ⟨.cell fh ft, ft, 3⟩
    else ⟨.atom 0, .atom 0, 0⟩

/-- OP1 skeleton (`genComputeSkeleton` OP1). -/
def skelOp1 (subj tail : Noun) : ComputeRowSkeleton where
  state := .s1
  subject := subj
  formula := .cell (.atom 1) tail
  evaluation := tail
  decomposition := fun slot h =>
    match slot with
    | .f_h => .atom 1
    | .f_t => tail
    | .f_th | .f_tt | .f_tth | .f_ttt => False.elim (by
        simp [decActive, hasTailDecomposition] at h)
  subformula := fun i hi _ => False.elim (by
    simp [fanoutComp] at hi)
  memoryRecord := fun i hi =>
    if i.val = 0 then ⟨.cell (.atom 1) tail, tail, 3⟩
    else ⟨.atom 0, .atom 0, 0⟩

/-- OP4 skeleton (`genComputeSkeleton` OP4). -/
def skelOp4 (subj tail callResult result : Noun) : ComputeRowSkeleton where
  state := .s4
  subject := subj
  formula := .cell (.atom 4) tail
  evaluation := result
  decomposition := fun slot h =>
    match slot with
    | .f_h => .atom 4
    | .f_t => tail
    | .f_th | .f_tt | .f_tth | .f_ttt => False.elim (by
        simp [decActive, hasTailDecomposition] at h)
  subformula := fun i _hi slot =>
    match slot with
    | .subject => subj | .formula => tail | .result => callResult
  memoryRecord := fun i hi =>
    if i.val = 0 then ⟨.cell (.atom 4) tail, tail, 3⟩
    else ⟨.atom 0, .atom 0, 0⟩

/-- OP3 skeleton (`genComputeSkeleton` OP3). -/
def skelOp3 (subj tail callResult : Noun) : ComputeRowSkeleton where
  state := .s3
  subject := subj
  formula := .cell (.atom 3) tail
  evaluation := Noun.wut callResult
  decomposition := fun slot h =>
    match slot with
    | .f_h => .atom 3
    | .f_t => tail
    | .f_th | .f_tt | .f_tth | .f_ttt => False.elim (by
        simp [decActive, hasTailDecomposition] at h)
  subformula := fun i _hi slot =>
    match slot with
    | .subject => subj | .formula => tail | .result => callResult
  memoryRecord := fun i hi =>
    if i.val = 0 then ⟨.cell (.atom 3) tail, tail, 3⟩
    else ⟨.atom 0, .atom 0, 0⟩

/-- OP0 skeleton (`genComputeSkeleton` OP0). -/
def skelOp0 (subj tail result : Noun) (ax : ℕ) : ComputeRowSkeleton where
  state := .s0
  subject := subj
  formula := .cell (.atom 0) tail
  evaluation := result
  decomposition := fun slot h =>
    match slot with
    | .f_h => .atom 0
    | .f_t => tail
    | .f_th | .f_tt | .f_tth | .f_ttt => False.elim (by
        simp [decActive, hasTailDecomposition] at h)
  subformula := fun i hi _ => False.elim (by
    simp [fanoutComp] at hi)
  memoryRecord := fun i hi =>
    match i.val with
    | 0 => ⟨.cell (.atom 0) tail, tail, 3⟩
    | 1 => ⟨subj, result, ax⟩
    | _ => ⟨.atom 0, .atom 0, 0⟩

/-- `BindComputeRow` on autocons when `Vcomp` and the five `bindFP`s hold. -/
theorem bindComputeRow_cons {z : K} (hz : z ≠ 0)
    (subj fh ft eL eR : Noun)
    (row : State × DTcomp K)
    (hstate : row.1 = .cons)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .cons)
    (hs : bindFP z subj row.2.2.1.s)
    (hfh : bindFP z fh row.2.2.2.f_h)
    (hft : bindFP z ft row.2.2.2.f_t)
    (heL : bindFP z eL row.2.2.1.sf1_e)
    (heR : bindFP z eR row.2.2.1.sf2_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindComputeRow z (skelCons subj fh ft eL eR) row := by
  obtain ⟨hf, hmr1, _, hmem, heval⟩ := hV
  simp only [evalV, hpubSt] at heval
  simp only [memBlk, hpubSt] at hmem
  have hfBind : bindFP z (.cell fh ft) row.2.2.1.f := by
    rw [hf, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz fh ft _ _ hfh hft
  have heBind : bindFP z (.cell eL eR) row.2.2.1.e := by
    have he := heval.2.2.2.2.1
    rw [he, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz eL eR _ _ heL heR
  refine ⟨hstate, hzRow, hpubSt, hs, hfBind, heBind, ?_, ?_, ?_⟩
  · intro slot
    match slot with
    | .f_h =>
        simp [skelCons, decActive, decFP]; exact hfh
    | .f_t =>
        simp [skelCons, decActive, decFP]; exact hft
    | .f_th | .f_tt | .f_tth | .f_ttt =>
        simp [skelCons, decActive, hasTailDecomposition]
  · intro i
    fin_cases i
    · simp [skelCons, fanoutComp]
      intro slot
      have hs1 := heval.1
      have hf1 := heval.2.1
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [hs1]; exact hs
      · rw [hf1]; exact hfh
      · exact heL
    · simp [skelCons, fanoutComp]
      intro slot
      have hs2 := heval.2.2.1
      have hf2 := heval.2.2.2.1
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [hs2]; exact hs
      · rw [hf2]; exact hft
      · exact heR
    · simp [skelCons, fanoutComp]
      obtain ⟨h1, h2, h3⟩ := heval.2.2.2.2.2
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
  · intro i
    fin_cases i
    · have hrec : (0 : ℕ) < Nock.Framework.recordCount .cons := by
        simp [Nock.Framework.recordCount]
      simp only [skelCons, hrec, ↓reduceDIte, computeMemRec]
      have hmr := hmr1
      refine ⟨?_, ?_, ?_⟩
      · rw [hmr]; exact hfBind
      · -- mr1.child = f_t
        change bindFP z ft row.2.2.1.mr1.child
        rw [hmr]; exact hft
      · -- axis = 3
        change row.2.2.1.mr1.axis = (3 : K)
        rw [hmr]
    · have hrec : ¬ (1 : ℕ) < Nock.Framework.recordCount .cons := by
        simp [Nock.Framework.recordCount]
      simp only [skelCons, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.1
    · have hrec : ¬ (2 : ℕ) < Nock.Framework.recordCount .cons := by
        simp [Nock.Framework.recordCount]
      simp only [skelCons, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.2.1

/-- `BindComputeRow` on OP1: evaluation is the formula tail. -/
theorem bindComputeRow_op1 {z : K} (hz : z ≠ 0)
    (subj tail : Noun)
    (row : State × DTcomp K)
    (hstate : row.1 = .s1)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s1)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 1) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindComputeRow z (skelOp1 subj tail) row := by
  obtain ⟨hf, hmr1, _, hmem, heval⟩ := hV
  simp only [evalV, hpubSt] at heval
  simp only [memBlk, hpubSt] at hmem
  have hfBind : bindFP z (.cell (.atom 1) tail) row.2.2.1.f := by
    rw [hf, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz (.atom 1) tail _ _ hh ht
  have heBind : bindFP z tail row.2.2.1.e := by
    rw [heval.1]; exact ht
  refine ⟨hstate, hzRow, hpubSt, hs, hfBind, heBind, ?_, ?_, ?_⟩
  · intro slot
    match slot with
    | .f_h => simp [skelOp1, decActive, decFP]; exact hh
    | .f_t => simp [skelOp1, decActive, decFP]; exact ht
    | .f_th | .f_tt | .f_tth | .f_ttt =>
        simp [skelOp1, decActive, hasTailDecomposition]
  · intro i
    have hfo : ¬ (i : ℕ) < fanoutComp .s1 := by simp [fanoutComp]
    simp only [skelOp1, hfo, ↓reduceDIte]
    have hsf := heval.2.1
    fin_cases i <;> simp [computeSubformulaFPs, sfTriple, sfz1, sfz2, sfz3] at hsf ⊢
    · exact ⟨hsf.1, hsf.2.1, hsf.2.2⟩
    · exact ⟨heval.2.2.1.1, heval.2.2.1.2.1, heval.2.2.1.2.2⟩
    · exact ⟨heval.2.2.2.1, heval.2.2.2.2.1, heval.2.2.2.2.2⟩
  · intro i
    fin_cases i
    · have hrec : (0 : ℕ) < Nock.Framework.recordCount .s1 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp1, hrec, ↓reduceDIte, computeMemRec]
      refine ⟨?_, ?_, ?_⟩
      · rw [hmr1]; exact hfBind
      · change bindFP z tail row.2.2.1.mr1.child
        rw [hmr1]; exact ht
      · change row.2.2.1.mr1.axis = (3 : K)
        rw [hmr1]
    · have hrec : ¬ (1 : ℕ) < Nock.Framework.recordCount .s1 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp1, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.1
    · have hrec : ¬ (2 : ℕ) < Nock.Framework.recordCount .s1 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp1, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.2.1

/-- `BindComputeRow` on OP3: evaluation is `wut` of the call. -/
theorem bindComputeRow_op3 {z : K} (hz : z ≠ 0)
    (subj tail callResult : Noun)
    (row : State × DTcomp K)
    (hstate : row.1 = .s3)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s3)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 3) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hcall : bindFP z callResult row.2.2.1.sf1_e)
    (hwin : OpcodeSemantics.SizeWindow z callResult)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindComputeRow z (skelOp3 subj tail callResult) row := by
  obtain ⟨hf, hmr1, _, hmem, heval⟩ := hV
  simp only [evalV, hpubSt] at heval
  simp only [memBlk, hpubSt] at hmem
  have hfBind : bindFP z (.cell (.atom 3) tail) row.2.2.1.f := by
    rw [hf, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz (.atom 3) tail _ _ hh ht
  have heBind : bindFP z (Noun.wut callResult) row.2.2.1.e := by
    have hshape := heval.2.2.2.2
    have hzEq : row.2.1.z = z := hzRow
    have hleaf : row.2.2.1.e.leaf = FP.qm z row.2.2.1.sf1_e := by
      simpa [hzEq] using hshape.2.2
    have henc : GlobalCarryRecognizer.enc z (Noun.wut callResult) =
        FP.atomFP z (FP.qm z (GlobalCarryRecognizer.enc z callResult)) :=
      OpcodeSemantics.enc_wut_eq hwin
    rw [bindFP, henc, ← hcall]
    apply ComputeTable.FP.ext
    · simpa [FP.atomFP, hzEq] using hshape.1
    · simpa [FP.atomFP] using hshape.2.1
    · simpa [FP.atomFP, hleaf]
  refine ⟨hstate, hzRow, hpubSt, hs, hfBind, heBind, ?_, ?_, ?_⟩
  · intro slot
    match slot with
    | .f_h => simp [skelOp3, decActive, decFP]; exact hh
    | .f_t => simp [skelOp3, decActive, decFP]; exact ht
    | .f_th | .f_tt | .f_tth | .f_ttt =>
        simp [skelOp3, decActive, hasTailDecomposition]
  · intro i
    have hfo : (i : ℕ) < fanoutComp .s3 → True := fun _ => trivial
    fin_cases i
    · have hactive : (0 : ℕ) < fanoutComp .s3 := by simp [fanoutComp]
      simp only [skelOp3, hactive, ↓reduceDIte]
      intro slot
      have hs1 := heval.1
      have hf1 := heval.2.1
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [hs1]; exact hs
      · rw [hf1]; exact ht
      · exact hcall
    · have hpad : ¬ (1 : ℕ) < fanoutComp .s3 := by simp [fanoutComp]
      simp only [skelOp3, hpad, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := heval.2.2.1
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
    · have hpad : ¬ (2 : ℕ) < fanoutComp .s3 := by simp [fanoutComp]
      simp only [skelOp3, hpad, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := heval.2.2.2.1
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
  · intro i
    fin_cases i
    · have hrec : (0 : ℕ) < Nock.Framework.recordCount .s3 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp3, hrec, ↓reduceDIte, computeMemRec]
      refine ⟨?_, ?_, ?_⟩
      · rw [hmr1]; exact hfBind
      · change bindFP z tail row.2.2.1.mr1.child
        rw [hmr1]; exact ht
      · change row.2.2.1.mr1.axis = (3 : K)
        rw [hmr1]
    · have hrec : ¬ (1 : ℕ) < Nock.Framework.recordCount .s3 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp3, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.1
    · have hrec : ¬ (2 : ℕ) < Nock.Framework.recordCount .s3 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp3, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.2.1

/-- `BindComputeRow` on OP4: evaluation is the increment. -/
theorem bindComputeRow_op4 {z : K} (hz : z ≠ 0)
    (subj tail : Noun) (k : ℕ)
    (row : State × DTcomp K)
    (hstate : row.1 = .s4)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s4)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 4) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hcall : bindFP z (.atom k) row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindComputeRow z (skelOp4 subj tail (.atom k) (.atom (k + 1))) row := by
  obtain ⟨hf, hmr1, _, hmem, heval⟩ := hV
  simp only [evalV, hpubSt] at heval
  simp only [memBlk, hpubSt] at hmem
  have hfBind : bindFP z (.cell (.atom 4) tail) row.2.2.1.f := by
    rw [hf, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz (.atom 4) tail _ _ hh ht
  have heBind : bindFP z (.atom (k + 1)) row.2.2.1.e := by
    have hinc := heval.2.2.2.2.2.2
    rw [bindFP, hinc, show row.2.1.z = z from hzRow]
    have hfp : row.2.2.1.sf1_e = FP.atomFP z (k : K) := by
      rw [hcall, GlobalCarryRecognizer.enc_atom]
    rw [hfp]
    exact bindFP_inc_atom (z := z) k
  refine ⟨hstate, hzRow, hpubSt, hs, hfBind, heBind, ?_, ?_, ?_⟩
  · intro slot
    match slot with
    | .f_h => simp [skelOp4, decActive, decFP]; exact hh
    | .f_t => simp [skelOp4, decActive, decFP]; exact ht
    | .f_th | .f_tt | .f_tth | .f_ttt =>
        simp [skelOp4, decActive, hasTailDecomposition]
  · intro i
    fin_cases i
    · have hactive : (0 : ℕ) < fanoutComp .s4 := by simp [fanoutComp]
      simp only [skelOp4, hactive, ↓reduceDIte]
      intro slot
      have hs1 := heval.1
      have hf1 := heval.2.1
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [hs1]; exact hs
      · rw [hf1]; exact ht
      · exact hcall
    · have hpad : ¬ (1 : ℕ) < fanoutComp .s4 := by simp [fanoutComp]
      simp only [skelOp4, hpad, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := heval.2.2.2.2.1
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
    · have hpad : ¬ (2 : ℕ) < fanoutComp .s4 := by simp [fanoutComp]
      simp only [skelOp4, hpad, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := heval.2.2.2.2.2.1
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
  · intro i
    fin_cases i
    · have hrec : (0 : ℕ) < Nock.Framework.recordCount .s4 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp4, hrec, ↓reduceDIte, computeMemRec]
      refine ⟨?_, ?_, ?_⟩
      · rw [hmr1]; exact hfBind
      · change bindFP z tail row.2.2.1.mr1.child
        rw [hmr1]; exact ht
      · change row.2.2.1.mr1.axis = (3 : K)
        rw [hmr1]
    · have hrec : ¬ (1 : ℕ) < Nock.Framework.recordCount .s4 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp4, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.1
    · have hrec : ¬ (2 : ℕ) < Nock.Framework.recordCount .s4 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp4, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.2.1

/-- `BindComputeRow` on OP0: slot result from the served record. -/
theorem bindComputeRow_op0 {z : K} (hz : z ≠ 0)
    (subj tail result : Noun) (ax : ℕ)
    (row : State × DTcomp K)
    (hstate : row.1 = .s0)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s0)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 0) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (he : bindFP z result row.2.2.1.e)
    (hax : (ax : K) = row.2.2.2.f_t.leaf)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindComputeRow z (skelOp0 subj tail result ax) row := by
  obtain ⟨hf, hmr1, _, hmem, heval⟩ := hV
  simp only [evalV, hpubSt] at heval
  simp only [memBlk, hpubSt] at hmem
  have hfBind : bindFP z (.cell (.atom 0) tail) row.2.2.1.f := by
    rw [hf, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz (.atom 0) tail _ _ hh ht
  refine ⟨hstate, hzRow, hpubSt, hs, hfBind, he, ?_, ?_, ?_⟩
  · intro slot
    match slot with
    | .f_h => simp [skelOp0, decActive, decFP]; exact hh
    | .f_t => simp [skelOp0, decActive, decFP]; exact ht
    | .f_th | .f_tt | .f_tth | .f_ttt =>
        simp [skelOp0, decActive, hasTailDecomposition]
  · intro i
    have hfo : ¬ (i : ℕ) < fanoutComp .s0 := by simp [fanoutComp]
    simp only [skelOp0, hfo, ↓reduceDIte]
    fin_cases i
    · obtain ⟨h1, h2, h3⟩ := heval.1
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
    · obtain ⟨h1, h2, h3⟩ := heval.2.1
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
    · obtain ⟨h1, h2, h3⟩ := heval.2.2
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
  · intro i
    fin_cases i
    · have hrec : (0 : ℕ) < Nock.Framework.recordCount .s0 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp0, hrec, ↓reduceDIte, computeMemRec]
      refine ⟨?_, ?_, ?_⟩
      · rw [hmr1]; exact hfBind
      · change bindFP z tail row.2.2.1.mr1.child
        rw [hmr1]; exact ht
      · change row.2.2.1.mr1.axis = (3 : K)
        rw [hmr1]
    · have hrec : (1 : ℕ) < Nock.Framework.recordCount .s0 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp0, hrec, ↓reduceDIte, computeMemRec]
      have hmr2 := hmem.1
      refine ⟨?_, ?_, ?_⟩
      · change bindFP z subj row.2.2.1.mr2.root
        rw [hmr2]; exact hs
      · change bindFP z result row.2.2.1.mr2.child
        rw [hmr2]; exact he
      · change row.2.2.1.mr2.axis = (ax : K)
        rw [hmr2, hax]
    · have hrec : ¬ (2 : ℕ) < Nock.Framework.recordCount .s0 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp0, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.2.1

/-- OP2 skeleton (`genComputeSkeleton` OP2).  Child 2 subject/formula
    are sibling results. -/
def skelOp2 (subj fth ftt e1 e2 eApp : Noun) : ComputeRowSkeleton where
  state := .s2
  subject := subj
  formula := .cell (.atom 2) (.cell fth ftt)
  evaluation := eApp
  decomposition := fun slot h =>
    match slot with
    | .f_h => .atom 2
    | .f_t => .cell fth ftt
    | .f_th => fth
    | .f_tt => ftt
    | .f_tth | .f_ttt => False.elim (by
        simp [decActive] at h)
  subformula := fun i _hi slot =>
    match i.val with
    | 0 => match slot with
      | .subject => subj | .formula => fth | .result => e1
    | 1 => match slot with
      | .subject => subj | .formula => ftt | .result => e2
    | _ => match slot with
      | .subject => e1 | .formula => e2 | .result => eApp
  memoryRecord := fun i hi =>
    match i.val with
    | 0 => ⟨.cell (.atom 2) (.cell fth ftt), .cell fth ftt, 3⟩
    | 1 => ⟨.cell fth ftt, fth, 2⟩
    | _ => ⟨.atom 0, .atom 0, 0⟩

/-- OP5 skeleton (`genComputeSkeleton` OP5). -/
def skelOp5 (subj fth ftt eL eR : Noun) : ComputeRowSkeleton where
  state := .s5
  subject := subj
  formula := .cell (.atom 5) (.cell fth ftt)
  evaluation := Noun.tis eL eR
  decomposition := fun slot h =>
    match slot with
    | .f_h => .atom 5
    | .f_t => .cell fth ftt
    | .f_th => fth
    | .f_tt => ftt
    | .f_tth | .f_ttt => False.elim (by
        simp [decActive] at h)
  subformula := fun i _hi slot =>
    if i.val = 0 then
      match slot with
      | .subject => subj | .formula => fth | .result => eL
    else
      match slot with
      | .subject => subj | .formula => ftt | .result => eR
  memoryRecord := fun i hi =>
    match i.val with
    | 0 => ⟨.cell (.atom 5) (.cell fth ftt), .cell fth ftt, 3⟩
    | 1 => ⟨.cell fth ftt, fth, 2⟩
    | _ => ⟨.atom 0, .atom 0, 0⟩

/-- OP6 skeleton (`genComputeSkeleton` OP6).  `b` is the condition bit. -/
def skelOp6 (subj fth ftth fttt : Noun) (b : ℕ) (eTaken : Noun) :
    ComputeRowSkeleton where
  state := .s6
  subject := subj
  formula := .cell (.atom 6) (.cell fth (.cell ftth fttt))
  evaluation := eTaken
  decomposition := fun slot _ =>
    match slot with
    | .f_h => .atom 6
    | .f_t => .cell fth (.cell ftth fttt)
    | .f_th => fth
    | .f_tt => .cell ftth fttt
    | .f_tth => ftth
    | .f_ttt => fttt
  subformula := fun i _hi slot =>
    if i.val = 0 then
      match slot with
      | .subject => subj
      | .formula => if b = 0 then ftth else fttt
      | .result => eTaken
    else
      match slot with
      | .subject => subj | .formula => fth | .result => .atom b
  memoryRecord := fun i hi =>
    match i.val with
    | 0 => ⟨.cell (.atom 6) (.cell fth (.cell ftth fttt)),
        .cell fth (.cell ftth fttt), 3⟩
    | 1 => ⟨.cell fth (.cell ftth fttt), fth, 2⟩
    | _ => ⟨.cell ftth fttt, ftth, 2⟩

/-- OP7 skeleton (`genComputeSkeleton` OP7).  AIR: sf1 = consumer. -/
def skelOp7 (subj fth ftt eHelp eCons : Noun) : ComputeRowSkeleton where
  state := .s7
  subject := subj
  formula := .cell (.atom 7) (.cell fth ftt)
  evaluation := eCons
  decomposition := fun slot h =>
    match slot with
    | .f_h => .atom 7
    | .f_t => .cell fth ftt
    | .f_th => fth
    | .f_tt => ftt
    | .f_tth | .f_ttt => False.elim (by
        simp [decActive] at h)
  subformula := fun i _hi slot =>
    if i.val = 0 then
      match slot with
      | .subject => eHelp | .formula => ftt | .result => eCons
    else
      match slot with
      | .subject => subj | .formula => fth | .result => eHelp
  memoryRecord := fun i hi =>
    match i.val with
    | 0 => ⟨.cell (.atom 7) (.cell fth ftt), .cell fth ftt, 3⟩
    | 1 => ⟨.cell fth ftt, fth, 2⟩
    | _ => ⟨.atom 0, .atom 0, 0⟩

/-- OP8 skeleton (`genComputeSkeleton` OP8).  Consumer subject is
    `cons(helper.e, parent.s)`. -/
def skelOp8 (subj fth ftt eHelp eCons : Noun) : ComputeRowSkeleton where
  state := .s8
  subject := subj
  formula := .cell (.atom 8) (.cell fth ftt)
  evaluation := eCons
  decomposition := fun slot h =>
    match slot with
    | .f_h => .atom 8
    | .f_t => .cell fth ftt
    | .f_th => fth
    | .f_tt => ftt
    | .f_tth | .f_ttt => False.elim (by
        simp [decActive] at h)
  subformula := fun i _hi slot =>
    if i.val = 0 then
      match slot with
      | .subject => .cell eHelp subj | .formula => ftt | .result => eCons
    else
      match slot with
      | .subject => subj | .formula => fth | .result => eHelp
  memoryRecord := fun i hi =>
    match i.val with
    | 0 => ⟨.cell (.atom 8) (.cell fth ftt), .cell fth ftt, 3⟩
    | 1 => ⟨.cell fth ftt, fth, 2⟩
    | _ => ⟨.atom 0, .atom 0, 0⟩

/-- OP9 skeleton (`genComputeSkeleton` OP9).  `coreF` is `f_tt`
    (AIR sf1); `arm` is the served `mr3.child` / `sf2_f`. -/
def skelOp9 (subj coreF arm eCore eInv : Noun) (ax : ℕ) : ComputeRowSkeleton where
  state := .s9
  subject := subj
  formula := .cell (.atom 9) (.cell (.atom ax) coreF)
  evaluation := eInv
  decomposition := fun slot h =>
    match slot with
    | .f_h => .atom 9
    | .f_t => .cell (.atom ax) coreF
    | .f_th => .atom ax
    | .f_tt => coreF
    | .f_tth | .f_ttt => False.elim (by
        simp [decActive] at h)
  subformula := fun i _hi slot =>
    if i.val = 0 then
      match slot with
      | .subject => subj | .formula => coreF | .result => eCore
    else
      match slot with
      | .subject => eCore | .formula => arm | .result => eInv
  memoryRecord := fun i hi =>
    match i.val with
    | 0 => ⟨.cell (.atom 9) (.cell (.atom ax) coreF), .cell (.atom ax) coreF, 3⟩
    | 1 => ⟨.cell (.atom ax) coreF, .atom ax, 2⟩
    | _ => ⟨eCore, arm, ax⟩

/-- `BindComputeRow` on OP2. -/
theorem bindComputeRow_op2 {z : K} (hz : z ≠ 0)
    (subj fth ftt e1 e2 eApp : Noun)
    (row : State × DTcomp K)
    (hstate : row.1 = .s2)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s2)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 2) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (he1 : bindFP z e1 row.2.2.1.sf1_e)
    (he2 : bindFP z e2 row.2.2.1.sf2_e)
    (heApp : bindFP z eApp row.2.2.1.sf3_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindComputeRow z (skelOp2 subj fth ftt e1 e2 eApp) row := by
  obtain ⟨hf, hmr1, _, hmem, heval⟩ := hV
  simp only [evalV, hpubSt] at heval
  simp only [memBlk, hpubSt] at hmem
  have hftBind : bindFP z (.cell fth ftt) row.2.2.2.f_t := by
    have hcons := hmem.2.1
    rw [← hcons, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz fth ftt _ _ hth htt
  have hfBind : bindFP z (.cell (.atom 2) (.cell fth ftt)) row.2.2.1.f := by
    rw [hf, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz (.atom 2) (.cell fth ftt) _ _ hh hftBind
  have heBind : bindFP z eApp row.2.2.1.e := by
    rw [heval.2.2.2.2.2.2]; exact heApp
  refine ⟨hstate, hzRow, hpubSt, hs, hfBind, heBind, ?_, ?_, ?_⟩
  · intro slot
    match slot with
    | .f_h => simp [skelOp2, decActive, decFP]; exact hh
    | .f_t => simp [skelOp2, decActive, decFP]; exact hftBind
    | .f_th => simp [skelOp2, decActive, decFP] <;> first | exact hth | (intro; exact hth)
    | .f_tt => simp [skelOp2, decActive, decFP] <;> first | exact htt | (intro; exact htt)
    | .f_tth | .f_ttt => simp [skelOp2, decActive]
  · intro i
    fin_cases i
    · have hactive : (0 : ℕ) < fanoutComp .s2 := by simp [fanoutComp]
      simp only [skelOp2, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.1]; exact hs
      · rw [heval.2.1]; exact hth
      · exact he1
    · have hactive : (1 : ℕ) < fanoutComp .s2 := by simp [fanoutComp]
      simp only [skelOp2, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.2.2.1]; exact hs
      · rw [heval.2.2.2.1]; exact htt
      · exact he2
    · have hactive : (2 : ℕ) < fanoutComp .s2 := by simp [fanoutComp]
      simp only [skelOp2, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.2.2.2.2.1]; exact he1
      · rw [heval.2.2.2.2.2.1]; exact he2
      · exact heApp
  · intro i
    fin_cases i
    · have hrec : (0 : ℕ) < Nock.Framework.recordCount .s2 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp2, hrec, ↓reduceDIte, computeMemRec]
      refine ⟨?_, ?_, ?_⟩
      · rw [hmr1]; exact hfBind
      · change bindFP z (.cell fth ftt) row.2.2.1.mr1.child
        rw [hmr1]; exact hftBind
      · change row.2.2.1.mr1.axis = (3 : K)
        rw [hmr1]
    · have hrec : (1 : ℕ) < Nock.Framework.recordCount .s2 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp2, hrec, ↓reduceDIte, computeMemRec]
      have hmr2 := hmem.1
      refine ⟨?_, ?_, ?_⟩
      · change bindFP z (.cell fth ftt) row.2.2.1.mr2.root
        rw [hmr2]; exact hftBind
      · change bindFP z fth row.2.2.1.mr2.child
        rw [hmr2]; exact hth
      · change row.2.2.1.mr2.axis = (2 : K)
        rw [hmr2]
    · have hrec : ¬ (2 : ℕ) < Nock.Framework.recordCount .s2 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp2, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.2.2.1

/-- `BindComputeRow` on OP5.  `PairFaithful` is the
    P8 collision side-condition, not a `V_comp` gap. -/
theorem bindComputeRow_op5 {z : K} (hz : z ≠ 0) {q : ℕ}
    (subj fth ftt eL eR : Noun)
    (row : State × DTcomp K)
    (hstate : row.1 = .s5)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s5)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 5) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (heL : bindFP z eL row.2.2.1.sf1_e)
    (heR : bindFP z eR row.2.2.1.sf2_e)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hfaith : OpcodeSemantics.PairFaithful z q eL eR)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindComputeRow z (skelOp5 subj fth ftt eL eR) row := by
  obtain ⟨hf, hmr1, _, hmem, heval⟩ := hV
  simp only [evalV, hpubSt] at heval
  simp only [memBlk, hpubSt] at hmem
  have hftBind : bindFP z (.cell fth ftt) row.2.2.2.f_t := by
    have hcons := hmem.2.1
    rw [← hcons, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz fth ftt _ _ hth htt
  have hfBind : bindFP z (.cell (.atom 5) (.cell fth ftt)) row.2.2.1.f := by
    rw [hf, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz (.atom 5) (.cell fth ftt) _ _ hh hftBind
  have heBind : bindFP z (Noun.tis eL eR) row.2.2.1.e := by
    have henc : GlobalCarryRecognizer.enc z (Noun.tis eL eR) =
        FP.atomFP z (FP.eqOp (GlobalCarryRecognizer.enc z eL)
          (GlobalCarryRecognizer.enc z eR)) :=
      OpcodeSemantics.enc_tis_eq hcast hfaith
    rw [bindFP, henc, ← heL, ← heR]
    apply ComputeTable.FP.ext
    · simpa [FP.atomFP, show row.2.1.z = z from hzRow] using heval.2.2.2.2.2.1
    · simpa [FP.atomFP] using heval.2.2.2.2.2.2.1
    · simpa [FP.atomFP] using heval.2.2.2.2.2.2.2
  refine ⟨hstate, hzRow, hpubSt, hs, hfBind, heBind, ?_, ?_, ?_⟩
  · intro slot
    match slot with
    | .f_h => simp [skelOp5, decActive, decFP]; exact hh
    | .f_t => simp [skelOp5, decActive, decFP]; exact hftBind
    | .f_th => simp [skelOp5, decActive, decFP]; intro; exact hth
    | .f_tt => simp [skelOp5, decActive, decFP]; intro; exact htt
    | .f_tth | .f_ttt => simp [skelOp5, decActive]
  · intro i
    fin_cases i
    · have hactive : (0 : ℕ) < fanoutComp .s5 := by simp [fanoutComp]
      simp only [skelOp5, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.1]; exact hs
      · rw [heval.2.1]; exact hth
      · exact heL
    · have hactive : (1 : ℕ) < fanoutComp .s5 := by simp [fanoutComp]
      simp only [skelOp5, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.2.2.1]; exact hs
      · rw [heval.2.2.2.1]; exact htt
      · exact heR
    · have hpad : ¬ (2 : ℕ) < fanoutComp .s5 := by simp [fanoutComp]
      simp only [skelOp5, hpad, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := heval.2.2.2.2.1
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
  · intro i
    fin_cases i
    · have hrec : (0 : ℕ) < Nock.Framework.recordCount .s5 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp5, hrec, ↓reduceDIte, computeMemRec]
      refine ⟨?_, ?_, ?_⟩
      · rw [hmr1]; exact hfBind
      · change bindFP z (.cell fth ftt) row.2.2.1.mr1.child
        rw [hmr1]; exact hftBind
      · change row.2.2.1.mr1.axis = (3 : K)
        rw [hmr1]
    · have hrec : (1 : ℕ) < Nock.Framework.recordCount .s5 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp5, hrec, ↓reduceDIte, computeMemRec]
      have hmr2 := hmem.1
      refine ⟨?_, ?_, ?_⟩
      · change bindFP z (.cell fth ftt) row.2.2.1.mr2.root
        rw [hmr2]; exact hftBind
      · change bindFP z fth row.2.2.1.mr2.child
        rw [hmr2]; exact hth
      · change row.2.2.1.mr2.axis = (2 : K)
        rw [hmr2]
    · have hrec : ¬ (2 : ℕ) < Nock.Framework.recordCount .s5 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp5, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.2.2.1

/-- `BindComputeRow` on OP6. -/
theorem bindComputeRow_op6 {z : K} (hz : z ≠ 0)
    (subj fth ftth fttt : Noun) (b : ℕ) (eTaken : Noun)
    (row : State × DTcomp K)
    (hstate : row.1 = .s6)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s6)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 6) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htth : bindFP z ftth row.2.2.2.f_tth)
    (httt : bindFP z fttt row.2.2.2.f_ttt)
    (hb : b = 0 ∨ b = 1)
    (hcond : bindFP z (.atom b) row.2.2.1.sf2_e)
    (heTaken : bindFP z eTaken row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindComputeRow z (skelOp6 subj fth ftth fttt b eTaken) row := by
  obtain ⟨hf, hmr1, _, hmem, heval⟩ := hV
  simp only [evalV, hpubSt] at heval
  simp only [memBlk, hpubSt] at hmem
  have httBind : bindFP z (.cell ftth fttt) row.2.2.2.f_tt := by
    have hcons := hmem.2.2.2.1
    rw [← hcons, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz ftth fttt _ _ htth httt
  have hftBind : bindFP z (.cell fth (.cell ftth fttt)) row.2.2.2.f_t := by
    have hcons := hmem.2.1
    rw [← hcons, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz fth (.cell ftth fttt) _ _ hth httBind
  have hfBind :
      bindFP z (.cell (.atom 6) (.cell fth (.cell ftth fttt))) row.2.2.1.f := by
    rw [hf, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz (.atom 6) _ _ _ hh hftBind
  have heBind : bindFP z eTaken row.2.2.1.e := by
    rw [heval.2.2.1]; exact heTaken
  have htakenF : bindFP z (if b = 0 then ftth else fttt) row.2.2.1.sf1_f := by
    have hsel := heval.2.1
    have hleaf : row.2.2.1.sf2_e.leaf = (b : K) := by
      rw [hcond, GlobalCarryRecognizer.enc_atom]; rfl
    cases hb with
    | inl hb0 =>
        simp [hb0] at hsel ⊢
        rw [hleaf, hb0, Nat.cast_zero, if_pos rfl] at hsel
        rw [hsel]; exact htth
    | inr hb1 =>
        have hbne : b ≠ 0 := by omega
        simp [hbne] at hsel ⊢
        have hleaf1 : row.2.2.1.sf2_e.leaf ≠ 0 := by
          rw [hleaf, hb1, Nat.cast_one]
          exact one_ne_zero (α := K)
        rw [if_neg hleaf1] at hsel
        rw [hsel]; exact httt
  refine ⟨hstate, hzRow, hpubSt, hs, hfBind, heBind, ?_, ?_, ?_⟩
  · intro slot
    match slot with
    | .f_h => simp [skelOp6, decActive, decFP]; exact hh
    | .f_t => simp [skelOp6, decActive, decFP]; exact hftBind
    | .f_th => simp [skelOp6, decActive, decFP]; intro; exact hth
    | .f_tt => simp [skelOp6, decActive, decFP]; intro; exact httBind
    | .f_tth => simp [skelOp6, decActive, decFP]; exact htth
    | .f_ttt => simp [skelOp6, decActive, decFP]; exact httt
  · intro i
    fin_cases i
    · have hactive : (0 : ℕ) < fanoutComp .s6 := by simp [fanoutComp]
      simp only [skelOp6, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.1]; exact hs
      · exact htakenF
      · exact heTaken
    · have hactive : (1 : ℕ) < fanoutComp .s6 := by simp [fanoutComp]
      simp only [skelOp6, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.2.2.2.1]; exact hs
      · rw [heval.2.2.2.2.1]; exact hth
      · exact hcond
    · have hpad : ¬ (2 : ℕ) < fanoutComp .s6 := by simp [fanoutComp]
      simp only [skelOp6, hpad, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := heval.2.2.2.2.2.2.2.2
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
  · intro i
    fin_cases i
    · have hrec : (0 : ℕ) < Nock.Framework.recordCount .s6 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp6, hrec, ↓reduceDIte, computeMemRec]
      refine ⟨?_, ?_, ?_⟩
      · rw [hmr1]; exact hfBind
      · change bindFP z (.cell fth (.cell ftth fttt)) row.2.2.1.mr1.child
        rw [hmr1]; exact hftBind
      · change row.2.2.1.mr1.axis = (3 : K)
        rw [hmr1]
    · have hrec : (1 : ℕ) < Nock.Framework.recordCount .s6 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp6, hrec, ↓reduceDIte, computeMemRec]
      have hmr2 := hmem.1
      refine ⟨?_, ?_, ?_⟩
      · change bindFP z (.cell fth (.cell ftth fttt)) row.2.2.1.mr2.root
        rw [hmr2]; exact hftBind
      · change bindFP z fth row.2.2.1.mr2.child
        rw [hmr2]; exact hth
      · change row.2.2.1.mr2.axis = (2 : K)
        rw [hmr2]
    · have hrec : (2 : ℕ) < Nock.Framework.recordCount .s6 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp6, hrec, ↓reduceDIte, computeMemRec]
      have hmr3 := hmem.2.2.1
      refine ⟨?_, ?_, ?_⟩
      · change bindFP z (.cell ftth fttt) row.2.2.1.mr3.root
        rw [hmr3]; exact httBind
      · change bindFP z ftth row.2.2.1.mr3.child
        rw [hmr3]; exact htth
      · change row.2.2.1.mr3.axis = (2 : K)
        rw [hmr3]

/-- `BindComputeRow` on OP7. -/
theorem bindComputeRow_op7 {z : K} (hz : z ≠ 0)
    (subj fth ftt eHelp eCons : Noun)
    (row : State × DTcomp K)
    (hstate : row.1 = .s7)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s7)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 7) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (heHelp : bindFP z eHelp row.2.2.1.sf2_e)
    (heCons : bindFP z eCons row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindComputeRow z (skelOp7 subj fth ftt eHelp eCons) row := by
  obtain ⟨hf, hmr1, _, hmem, heval⟩ := hV
  simp only [evalV, hpubSt] at heval
  simp only [memBlk, hpubSt] at hmem
  have hftBind : bindFP z (.cell fth ftt) row.2.2.2.f_t := by
    have hcons := hmem.2.1
    rw [← hcons, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz fth ftt _ _ hth htt
  have hfBind : bindFP z (.cell (.atom 7) (.cell fth ftt)) row.2.2.1.f := by
    rw [hf, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz (.atom 7) (.cell fth ftt) _ _ hh hftBind
  have heBind : bindFP z eCons row.2.2.1.e := by
    rw [heval.2.2.1]; exact heCons
  refine ⟨hstate, hzRow, hpubSt, hs, hfBind, heBind, ?_, ?_, ?_⟩
  · intro slot
    match slot with
    | .f_h => simp [skelOp7, decActive, decFP]; exact hh
    | .f_t => simp [skelOp7, decActive, decFP]; exact hftBind
    | .f_th => simp [skelOp7, decActive, decFP]; intro; exact hth
    | .f_tt => simp [skelOp7, decActive, decFP]; intro; exact htt
    | .f_tth | .f_ttt => simp [skelOp7, decActive]
  · intro i
    fin_cases i
    · have hactive : (0 : ℕ) < fanoutComp .s7 := by simp [fanoutComp]
      simp only [skelOp7, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.1]; exact heHelp
      · rw [heval.2.1]; exact htt
      · exact heCons
    · have hactive : (1 : ℕ) < fanoutComp .s7 := by simp [fanoutComp]
      simp only [skelOp7, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.2.2.2.1]; exact hs
      · rw [heval.2.2.2.2.1]; exact hth
      · exact heHelp
    · have hpad : ¬ (2 : ℕ) < fanoutComp .s7 := by simp [fanoutComp]
      simp only [skelOp7, hpad, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := heval.2.2.2.2.2
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
  · intro i
    fin_cases i
    · have hrec : (0 : ℕ) < Nock.Framework.recordCount .s7 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp7, hrec, ↓reduceDIte, computeMemRec]
      refine ⟨?_, ?_, ?_⟩
      · rw [hmr1]; exact hfBind
      · change bindFP z (.cell fth ftt) row.2.2.1.mr1.child
        rw [hmr1]; exact hftBind
      · change row.2.2.1.mr1.axis = (3 : K)
        rw [hmr1]
    · have hrec : (1 : ℕ) < Nock.Framework.recordCount .s7 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp7, hrec, ↓reduceDIte, computeMemRec]
      have hmr2 := hmem.1
      refine ⟨?_, ?_, ?_⟩
      · change bindFP z (.cell fth ftt) row.2.2.1.mr2.root
        rw [hmr2]; exact hftBind
      · change bindFP z fth row.2.2.1.mr2.child
        rw [hmr2]; exact hth
      · change row.2.2.1.mr2.axis = (2 : K)
        rw [hmr2]
    · have hrec : ¬ (2 : ℕ) < Nock.Framework.recordCount .s7 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp7, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.2.2.1

/-- `BindComputeRow` on OP8. -/
theorem bindComputeRow_op8 {z : K} (hz : z ≠ 0)
    (subj fth ftt eHelp eCons : Noun)
    (row : State × DTcomp K)
    (hstate : row.1 = .s8)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s8)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 8) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (heHelp : bindFP z eHelp row.2.2.1.sf2_e)
    (heCons : bindFP z eCons row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindComputeRow z (skelOp8 subj fth ftt eHelp eCons) row := by
  obtain ⟨hf, hmr1, _, hmem, heval⟩ := hV
  simp only [evalV, hpubSt] at heval
  simp only [memBlk, hpubSt] at hmem
  have hftBind : bindFP z (.cell fth ftt) row.2.2.2.f_t := by
    have hcons := hmem.2.1
    rw [← hcons, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz fth ftt _ _ hth htt
  have hfBind : bindFP z (.cell (.atom 8) (.cell fth ftt)) row.2.2.1.f := by
    rw [hf, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz (.atom 8) (.cell fth ftt) _ _ hh hftBind
  have heBind : bindFP z eCons row.2.2.1.e := by
    rw [heval.2.2.1]; exact heCons
  have hpushed : bindFP z (.cell eHelp subj) row.2.2.1.sf1_s := by
    rw [heval.1, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz eHelp subj _ _ heHelp hs
  refine ⟨hstate, hzRow, hpubSt, hs, hfBind, heBind, ?_, ?_, ?_⟩
  · intro slot
    match slot with
    | .f_h => simp [skelOp8, decActive, decFP]; exact hh
    | .f_t => simp [skelOp8, decActive, decFP]; exact hftBind
    | .f_th => simp [skelOp8, decActive, decFP]; intro; exact hth
    | .f_tt => simp [skelOp8, decActive, decFP]; intro; exact htt
    | .f_tth | .f_ttt => simp [skelOp8, decActive]
  · intro i
    fin_cases i
    · have hactive : (0 : ℕ) < fanoutComp .s8 := by simp [fanoutComp]
      simp only [skelOp8, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · exact hpushed
      · rw [heval.2.1]; exact htt
      · exact heCons
    · have hactive : (1 : ℕ) < fanoutComp .s8 := by simp [fanoutComp]
      simp only [skelOp8, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.2.2.2.1]; exact hs
      · rw [heval.2.2.2.2.1]; exact hth
      · exact heHelp
    · have hpad : ¬ (2 : ℕ) < fanoutComp .s8 := by simp [fanoutComp]
      simp only [skelOp8, hpad, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := heval.2.2.2.2.2
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
  · intro i
    fin_cases i
    · have hrec : (0 : ℕ) < Nock.Framework.recordCount .s8 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp8, hrec, ↓reduceDIte, computeMemRec]
      refine ⟨?_, ?_, ?_⟩
      · rw [hmr1]; exact hfBind
      · change bindFP z (.cell fth ftt) row.2.2.1.mr1.child
        rw [hmr1]; exact hftBind
      · change row.2.2.1.mr1.axis = (3 : K)
        rw [hmr1]
    · have hrec : (1 : ℕ) < Nock.Framework.recordCount .s8 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp8, hrec, ↓reduceDIte, computeMemRec]
      have hmr2 := hmem.1
      refine ⟨?_, ?_, ?_⟩
      · change bindFP z (.cell fth ftt) row.2.2.1.mr2.root
        rw [hmr2]; exact hftBind
      · change bindFP z fth row.2.2.1.mr2.child
        rw [hmr2]; exact hth
      · change row.2.2.1.mr2.axis = (2 : K)
        rw [hmr2]
    · have hrec : ¬ (2 : ℕ) < Nock.Framework.recordCount .s8 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp8, hrec, ↓reduceDIte, computeMemRec]
      exact hmem.2.2.1

/-- `BindComputeRow` on OP9.  `coreF` binds
    `f_tt`; `arm` binds `sf2_f` (`mr3.child`, `:1879`). -/
theorem bindComputeRow_op9 {z : K} (hz : z ≠ 0)
    (subj coreF arm eCore eInv : Noun) (ax : ℕ)
    (row : State × DTcomp K)
    (hstate : row.1 = .s9)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s9)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 9) row.2.2.2.f_h)
    (hax : bindFP z (.atom ax) row.2.2.2.f_th)
    (hcoreF : bindFP z coreF row.2.2.2.f_tt)
    (harm : bindFP z arm row.2.2.1.sf2_f)
    (heCore : bindFP z eCore row.2.2.1.sf1_e)
    (heInv : bindFP z eInv row.2.2.1.sf2_e)
    (haxK : (ax : K) = row.2.2.2.f_th.leaf)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    BindComputeRow z (skelOp9 subj coreF arm eCore eInv ax) row := by
  obtain ⟨hf, hmr1, _, hmem, heval⟩ := hV
  simp only [evalV, hpubSt] at heval
  simp only [memBlk, hpubSt] at hmem
  have hftBind : bindFP z (.cell (.atom ax) coreF) row.2.2.2.f_t := by
    have hcons := hmem.2.1
    rw [← hcons, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz (.atom ax) coreF _ _ hax hcoreF
  have hfBind :
      bindFP z (.cell (.atom 9) (.cell (.atom ax) coreF)) row.2.2.1.f := by
    rw [hf, show row.2.1.z = z from hzRow]
    exact bindFP_cons hz (.atom 9) (.cell (.atom ax) coreF) _ _ hh hftBind
  have heBind : bindFP z eInv row.2.2.1.e := by
    rw [heval.2.2.2.1]; exact heInv
  refine ⟨hstate, hzRow, hpubSt, hs, hfBind, heBind, ?_, ?_, ?_⟩
  · intro slot
    match slot with
    | .f_h => simp [skelOp9, decActive, decFP]; exact hh
    | .f_t => simp [skelOp9, decActive, decFP]; exact hftBind
    | .f_th => simp [skelOp9, decActive, decFP]; intro; exact hax
    | .f_tt => simp [skelOp9, decActive, decFP]; intro; exact hcoreF
    | .f_tth | .f_ttt => simp [skelOp9, decActive]
  · intro i
    fin_cases i
    · have hactive : (0 : ℕ) < fanoutComp .s9 := by simp [fanoutComp]
      simp only [skelOp9, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.1]; exact hs
      · rw [heval.2.1]; exact hcoreF
      · exact heCore
    · have hactive : (1 : ℕ) < fanoutComp .s9 := by simp [fanoutComp]
      simp only [skelOp9, hactive, ↓reduceDIte]
      intro slot
      cases slot <;> simp [tripleFP, computeSubformulaFPs, sfTriple]
      · rw [heval.2.2.1]; exact heCore
      · exact harm
      · exact heInv
    · have hpad : ¬ (2 : ℕ) < fanoutComp .s9 := by simp [fanoutComp]
      simp only [skelOp9, hpad, ↓reduceDIte]
      obtain ⟨h1, h2, h3⟩ := heval.2.2.2.2.1
      simp [computeSubformulaFPs, sfTriple, h1, h2, h3]
  · intro i
    fin_cases i
    · have hrec : (0 : ℕ) < Nock.Framework.recordCount .s9 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp9, hrec, ↓reduceDIte, computeMemRec]
      refine ⟨?_, ?_, ?_⟩
      · rw [hmr1]; exact hfBind
      · change bindFP z (.cell (.atom ax) coreF) row.2.2.1.mr1.child
        rw [hmr1]; exact hftBind
      · change row.2.2.1.mr1.axis = (3 : K)
        rw [hmr1]
    · have hrec : (1 : ℕ) < Nock.Framework.recordCount .s9 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp9, hrec, ↓reduceDIte, computeMemRec]
      have hmr2 := hmem.1
      refine ⟨?_, ?_, ?_⟩
      · change bindFP z (.cell (.atom ax) coreF) row.2.2.1.mr2.root
        rw [hmr2]; exact hftBind
      · change bindFP z (.atom ax) row.2.2.1.mr2.child
        rw [hmr2]; exact hax
      · change row.2.2.1.mr2.axis = (2 : K)
        rw [hmr2]
    · have hrec : (2 : ℕ) < Nock.Framework.recordCount .s9 := by
        simp [Nock.Framework.recordCount]
      simp only [skelOp9, hrec, ↓reduceDIte, computeMemRec]
      have hmr3 := hmem.2.2.1
      refine ⟨?_, ?_, ?_⟩
      · change bindFP z eCore row.2.2.1.mr3.root
        rw [hmr3]; exact heCore
      · change bindFP z arm row.2.2.1.mr3.child
        rw [hmr3]; exact harm
      · change row.2.2.1.mr3.axis = (ax : K)
        rw [hmr3, haxK]

/-- Tree induction step: a cons node binds when both children bind. -/
theorem computeTreeBinds_cons {z : K} (hz : z ≠ 0)
    (subj fh ft eL eR : Noun)
    (row : State × DTcomp K)
    (left right : NTree (State × DTcomp K))
    (skelL skelR : NTree ComputeRowSkeleton)
    (hstate : row.1 = .cons)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .cons)
    (hs : bindFP z subj row.2.2.1.s)
    (hfh : bindFP z fh row.2.2.2.f_h)
    (hft : bindFP z ft row.2.2.2.f_t)
    (heL : bindFP z eL row.2.2.1.sf1_e)
    (heR : bindFP z eR row.2.2.1.sf2_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hL : ComputeTreeBinds z skelL left)
    (hR : ComputeTreeBinds z skelR right) :
    ComputeTreeBinds z
      (.node (skelCons subj fh ft eL eR) [skelL, skelR])
      (.node row [left, right]) :=
  ComputeTreeBinds.node (by simp [skelCons, fanoutComp, hstate])
    (bindComputeRow_cons hz subj fh ft eL eR row hstate hzRow hpubSt
      hs hfh hft heL heR hV)
    (.cons hL (.cons hR .nil))

theorem computeTreeBinds_op1 {z : K} (hz : z ≠ 0)
    (subj tail : Noun)
    (row : State × DTcomp K)
    (hstate : row.1 = .s1)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s1)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 1) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    ComputeTreeBinds z (.node (skelOp1 subj tail) []) (.node row []) :=
  ComputeTreeBinds.node (by simp [skelOp1, fanoutComp])
    (bindComputeRow_op1 hz subj tail row hstate hzRow hpubSt hs hh ht hV)
    .nil

theorem computeTreeBinds_op0 {z : K} (hz : z ≠ 0)
    (subj tail result : Noun) (ax : ℕ)
    (row : State × DTcomp K)
    (hstate : row.1 = .s0)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s0)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 0) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (he : bindFP z result row.2.2.1.e)
    (hax : (ax : K) = row.2.2.2.f_t.leaf)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    ComputeTreeBinds z (.node (skelOp0 subj tail result ax) []) (.node row []) :=
  ComputeTreeBinds.node (by simp [skelOp0, fanoutComp])
    (bindComputeRow_op0 hz subj tail result ax row hstate hzRow hpubSt
      hs hh ht he hax hV)
    .nil

theorem computeTreeBinds_op3 {z : K} (hz : z ≠ 0)
    (subj tail callResult : Noun)
    (row : State × DTcomp K)
    (child : NTree (State × DTcomp K))
    (skelC : NTree ComputeRowSkeleton)
    (hstate : row.1 = .s3)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s3)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 3) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hcall : bindFP z callResult row.2.2.1.sf1_e)
    (hwin : OpcodeSemantics.SizeWindow z callResult)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hC : ComputeTreeBinds z skelC child) :
    ComputeTreeBinds z
      (.node (skelOp3 subj tail callResult) [skelC])
      (.node row [child]) :=
  ComputeTreeBinds.node (by simp [skelOp3, fanoutComp])
    (bindComputeRow_op3 hz subj tail callResult row hstate hzRow hpubSt
      hs hh ht hcall hwin hV)
    (.cons hC .nil)

theorem computeTreeBinds_op4 {z : K} (hz : z ≠ 0)
    (subj tail : Noun) (k : ℕ)
    (row : State × DTcomp K)
    (child : NTree (State × DTcomp K))
    (skelC : NTree ComputeRowSkeleton)
    (hstate : row.1 = .s4)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s4)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 4) row.2.2.2.f_h)
    (ht : bindFP z tail row.2.2.2.f_t)
    (hcall : bindFP z (.atom k) row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hC : ComputeTreeBinds z skelC child) :
    ComputeTreeBinds z
      (.node (skelOp4 subj tail (.atom k) (.atom (k + 1))) [skelC])
      (.node row [child]) :=
  ComputeTreeBinds.node (by simp [skelOp4, fanoutComp])
    (bindComputeRow_op4 hz subj tail k row hstate hzRow hpubSt
      hs hh ht hcall hV)
    (.cons hC .nil)

theorem computeTreeBinds_op2 {z : K} (hz : z ≠ 0)
    (subj fth ftt e1 e2 eApp : Noun)
    (row : State × DTcomp K)
    (c1 c2 c3 : NTree (State × DTcomp K))
    (s1 s2 s3 : NTree ComputeRowSkeleton)
    (hstate : row.1 = .s2)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s2)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 2) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (he1 : bindFP z e1 row.2.2.1.sf1_e)
    (he2 : bindFP z e2 row.2.2.1.sf2_e)
    (heApp : bindFP z eApp row.2.2.1.sf3_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (h1 : ComputeTreeBinds z s1 c1)
    (h2 : ComputeTreeBinds z s2 c2)
    (h3 : ComputeTreeBinds z s3 c3) :
    ComputeTreeBinds z
      (.node (skelOp2 subj fth ftt e1 e2 eApp) [s1, s2, s3])
      (.node row [c1, c2, c3]) :=
  ComputeTreeBinds.node (by simp [skelOp2, fanoutComp])
    (bindComputeRow_op2 hz subj fth ftt e1 e2 eApp row hstate hzRow hpubSt
      hs hh hth htt he1 he2 heApp hV)
    (.cons h1 (.cons h2 (.cons h3 .nil)))

theorem computeTreeBinds_op5 {z : K} (hz : z ≠ 0) {q : ℕ}
    (subj fth ftt eL eR : Noun)
    (row : State × DTcomp K)
    (cL cR : NTree (State × DTcomp K))
    (sL sR : NTree ComputeRowSkeleton)
    (hstate : row.1 = .s5)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s5)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 5) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (heL : bindFP z eL row.2.2.1.sf1_e)
    (heR : bindFP z eR row.2.2.1.sf2_e)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hfaith : OpcodeSemantics.PairFaithful z q eL eR)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hL : ComputeTreeBinds z sL cL)
    (hR : ComputeTreeBinds z sR cR) :
    ComputeTreeBinds z
      (.node (skelOp5 subj fth ftt eL eR) [sL, sR])
      (.node row [cL, cR]) :=
  ComputeTreeBinds.node (by simp [skelOp5, fanoutComp])
    (bindComputeRow_op5 hz subj fth ftt eL eR row hstate hzRow hpubSt
      hs hh hth htt heL heR hcast hfaith hV)
    (.cons hL (.cons hR .nil))

theorem computeTreeBinds_op6 {z : K} (hz : z ≠ 0)
    (subj fth ftth fttt : Noun) (b : ℕ) (eTaken : Noun)
    (row : State × DTcomp K)
    (cTaken cCond : NTree (State × DTcomp K))
    (sTaken sCond : NTree ComputeRowSkeleton)
    (hstate : row.1 = .s6)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s6)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 6) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htth : bindFP z ftth row.2.2.2.f_tth)
    (httt : bindFP z fttt row.2.2.2.f_ttt)
    (hb : b = 0 ∨ b = 1)
    (hcond : bindFP z (.atom b) row.2.2.1.sf2_e)
    (heTaken : bindFP z eTaken row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hT : ComputeTreeBinds z sTaken cTaken)
    (hC : ComputeTreeBinds z sCond cCond) :
    ComputeTreeBinds z
      (.node (skelOp6 subj fth ftth fttt b eTaken) [sTaken, sCond])
      (.node row [cTaken, cCond]) :=
  ComputeTreeBinds.node (by simp [skelOp6, fanoutComp])
    (bindComputeRow_op6 hz subj fth ftth fttt b eTaken row hstate hzRow hpubSt
      hs hh hth htth httt hb hcond heTaken hV)
    (.cons hT (.cons hC .nil))

theorem computeTreeBinds_op7 {z : K} (hz : z ≠ 0)
    (subj fth ftt eHelp eCons : Noun)
    (row : State × DTcomp K)
    (cCons cHelp : NTree (State × DTcomp K))
    (sCons sHelp : NTree ComputeRowSkeleton)
    (hstate : row.1 = .s7)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s7)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 7) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (heHelp : bindFP z eHelp row.2.2.1.sf2_e)
    (heCons : bindFP z eCons row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hCons : ComputeTreeBinds z sCons cCons)
    (hHelp : ComputeTreeBinds z sHelp cHelp) :
    ComputeTreeBinds z
      (.node (skelOp7 subj fth ftt eHelp eCons) [sCons, sHelp])
      (.node row [cCons, cHelp]) :=
  ComputeTreeBinds.node (by simp [skelOp7, fanoutComp])
    (bindComputeRow_op7 hz subj fth ftt eHelp eCons row hstate hzRow hpubSt
      hs hh hth htt heHelp heCons hV)
    (.cons hCons (.cons hHelp .nil))

theorem computeTreeBinds_op8 {z : K} (hz : z ≠ 0)
    (subj fth ftt eHelp eCons : Noun)
    (row : State × DTcomp K)
    (cCons cHelp : NTree (State × DTcomp K))
    (sCons sHelp : NTree ComputeRowSkeleton)
    (hstate : row.1 = .s8)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s8)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 8) row.2.2.2.f_h)
    (hth : bindFP z fth row.2.2.2.f_th)
    (htt : bindFP z ftt row.2.2.2.f_tt)
    (heHelp : bindFP z eHelp row.2.2.1.sf2_e)
    (heCons : bindFP z eCons row.2.2.1.sf1_e)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hCons : ComputeTreeBinds z sCons cCons)
    (hHelp : ComputeTreeBinds z sHelp cHelp) :
    ComputeTreeBinds z
      (.node (skelOp8 subj fth ftt eHelp eCons) [sCons, sHelp])
      (.node row [cCons, cHelp]) :=
  ComputeTreeBinds.node (by simp [skelOp8, fanoutComp])
    (bindComputeRow_op8 hz subj fth ftt eHelp eCons row hstate hzRow hpubSt
      hs hh hth htt heHelp heCons hV)
    (.cons hCons (.cons hHelp .nil))

theorem computeTreeBinds_op9 {z : K} (hz : z ≠ 0)
    (subj coreF arm eCore eInv : Noun) (ax : ℕ)
    (row : State × DTcomp K)
    (cCore cInv : NTree (State × DTcomp K))
    (sCore sInv : NTree ComputeRowSkeleton)
    (hstate : row.1 = .s9)
    (hzRow : row.2.1.z = z)
    (hpubSt : row.2.2.1.state = .s9)
    (hs : bindFP z subj row.2.2.1.s)
    (hh : bindFP z (.atom 9) row.2.2.2.f_h)
    (hax : bindFP z (.atom ax) row.2.2.2.f_th)
    (hcoreF : bindFP z coreF row.2.2.2.f_tt)
    (harm : bindFP z arm row.2.2.1.sf2_f)
    (heCore : bindFP z eCore row.2.2.1.sf1_e)
    (heInv : bindFP z eInv row.2.2.1.sf2_e)
    (haxK : (ax : K) = row.2.2.2.f_th.leaf)
    (hV : Vcomp row.2.1 row.2.2.1 row.2.2.2)
    (hCore : ComputeTreeBinds z sCore cCore)
    (hInv : ComputeTreeBinds z sInv cInv) :
    ComputeTreeBinds z
      (.node (skelOp9 subj coreF arm eCore eInv ax) [sCore, sInv])
      (.node row [cCore, cInv]) :=
  ComputeTreeBinds.node (by simp [skelOp9, fanoutComp])
    (bindComputeRow_op9 hz subj coreF arm eCore eInv ax row hstate hzRow hpubSt
      hs hh hax hcoreF harm heCore heInv haxK hV)
    (.cons hCore (.cons hInv .nil))

end Nock.RedTeam.Batch525
