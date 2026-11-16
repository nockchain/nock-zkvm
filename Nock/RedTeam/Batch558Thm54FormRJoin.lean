/-
  Nock/RedTeam/Batch558Thm54FormRJoin.lean

  **Form R join onto `exactAxisTree`.**

  Wrap assembly of `WFAt` on `tracesSpecializedExec` is the remaining
  join for `rootBoundary`; `axisStructural` / `structuralChecks` wait
  on that decode plus the λ-event (`pwAccountingWork'`).  Compiled as
  named remaining joins, not skipped.
-/
import Nock.AxisBatching
import Nock.AxisBridge
import Nock.NockVMROM.Thm54.CountsPEvalAt
import Nock.RedTeam.Batch554Thm54PwFunctional

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch558

open Nock
open Nock.MemoryTable
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.AxisBridge.MemWalk
open Nock.NockVMROM.Thm54.CountsPEvalAt
open Nock.RedTeam.Batch554
open Polynomial

variable {K : Type*} [Field K]

/-! ## Form R `countsP` is `cntM` -/

/-- Form R maps `s = λ^{n−1}`, `A_e = T_e·C'_e`, `W_e = T_e·λ^{n−1}`. -/
noncomputable def formRA (T C' : ℕ → K) : ℕ → K := fun e => T e * C' e
noncomputable def formRW (lmb : K) (T : ℕ → K) : ℕ → K :=
  fun e => T e * pwScale lmb
noncomputable def formRS (lmb : K) : K := pwScale lmb

theorem countsP_eq_cntM (t : MTree K) (lmb : K) (T C' : ℕ → K) :
    countsP t lmb T C' = cntM lmb (formRS lmb) (formRA T C') (formRW lmb T) t ∧
      indP t lmb T = pwM lmb (formRS lmb) (formRA T C') (formRW lmb T) t := by
  induction t with
  | halt =>
      simp [countsP, indP, cntM, pwM, cnt, pw, ofM, formRS, formRA, formRW]
  | decompose L R ihl ihr =>
      obtain ⟨hcl, hpl⟩ := ihl
      obtain ⟨hcr, hpr⟩ := ihr
      simp [countsP, indP, cntM_decompose, pwM_decompose, hcl, hcr, hpl, hpr]
  | read e c ih =>
      obtain ⟨hc, hp⟩ := ih
      constructor
      · simp [countsP, cntM_read, hc, formRA, sub_eq_add_neg, map_mul, map_neg]
      · simp [indP, pwM_read, hp, formRW, sub_eq_add_neg, map_mul, map_neg]
  | verify e a c ih =>
      obtain ⟨hc, hp⟩ := ih
      simp [countsP, indP, cntM_verify, pwM_verify, hc, hp, formRS]

theorem countsP_eq_cntM' (t : MTree K) (lmb : K) (T C' : ℕ → K) :
    countsP t lmb T C' = cntM lmb (formRS lmb) (formRA T C') (formRW lmb T) t :=
  (countsP_eq_cntM t lmb T C').1


def wallTree (e : ℕ) : MTree K :=
  .decompose (.read e (.decompose .halt .halt)) (.verify e (2 : K) .halt)

/-- Form R `countsP` on the wall, default `λ = 1`, `T = C' = 1`. -/
theorem wallTree_countsP (e : ℕ) : countsP (wallTree (K := K) e) = (X : K[X]) ^ e := by
  simp [wallTree, countsP, indP, pwScale, MemoryTable.pwScaleExp]

theorem formR_rejects_readVerifyNested_wall [Nontrivial K] (e : ℕ) :
    countsP (wallTree (K := K) e) ≠ 0 := by
  rw [wallTree_countsP]
  exact pow_ne_zero e X_ne_zero

/-- The published wall still has vanishing *binary* polynomials and fails
    `ReadVerifyNested`; form R `countsP` is the witness the chip now
    rejects it. -/
theorem readVerifyNested_wall_bin_zero_formR_nonzero [Nontrivial K] (e : ℕ) :
    indP_bin (wallTree (K := K) e) = 0 ∧
      countsP_bin (wallTree (K := K) e) = 0 ∧
      ¬ ReadVerifyNested (wallTree (K := K) e) ∧
      countsP (wallTree (K := K) e) ≠ 0 := by
  have hwall := readVerifyNested_wall (K := K) e
  refine ⟨hwall.2.2.1, hwall.2.2.2.1, hwall.2.2.2.2.2.2.2.2.2, ?_⟩
  exact formR_rejects_readVerifyNested_wall e

/-! ## Single-record coefficient is the bracket at `n = n−1` -/

theorem single_record_formR_coeff (lmb : K) (T C' : ℕ → K) (e : ℕ)
    (t : MTree K) (v r : List Bool)
    (hv : vpaths e t = [v]) (hr : rpaths e t = [r]) :
    (countsP t lmb T C').coeff e
      = formRS lmb * addr lmb v - formRA T C' e
        - formRW lmb T e * (addr lmb r - 1) := by
  rw [countsP_eq_cntM']
  simpa [formRS, formRA, formRW] using
    single_record lmb (formRS lmb) (formRA T C') (formRW lmb T) e t v r hv hr

theorem single_record_coeff_eq_bracket_eval (l : K) (e : ℕ) (c : ℕ → Bool)
    (t : MTree K) (v r : List Bool)
    (hv : vpaths e t = [v]) (hr : rpaths e t = [r]) :
    (countsP t l (fun _ => 1) (fun _ => (Cpoly (pwScaleExp K) c).eval l)).coeff e
      = (bracket (pwScaleExp K) 0 c v r).eval l := by
  rw [single_record_formR_coeff l (fun _ => 1)
      (fun _ => (Cpoly (pwScaleExp K) c).eval l) e t v r hv hr, bracket_eval]
  simp [formRS, formRA, formRW, pwScale, MemoryTable.pwScaleExp, one_mul]

/-- `bracket_zero_iff` on a single-record form-R tree: zero bracket
    iff padding vanishes and the verify sits at `R ++ bitsOf m c`. -/
theorem exactAxisTree_join_is_bracket_zero_iff (n m : ℕ) (c : ℕ → Bool)
    (v r : List Bool) (hm : m ≤ n) :
    bracket (K := K) n m c v r = 0
      ↔ (∀ j, m < j → j ≤ n → c j = false) ∧ v = r ++ bitsOf m c :=
  bracket_zero_iff n m c v r hm

/-! ## Wrap remaining joins (compiled Props; not strings) -/

/-- `rootBoundary` decode: form-R `countsP.eval α = pt.counts` under `WFAt`. -/
theorem rootBoundary_of_wfAt
    (inp : Inputs K) (α lmb : K) (T C' : ℕ → K) (w : MemWalk K)
    (hw : WFAt inp α w) (hlam : MemWalk.sameLambda lmb w)
    (hT : MemWalk.readAxis T w) (hC : MemWalk.readCprime C' w)
    (hroot : w.rootRow.pt.counts = 0) :
    (countsP w.toMTree lmb T C').eval α = 0 := by
  rw [countsP_eval_at inp α lmb T C' w hw hlam hT hC]
  exact hroot

theorem axisStructural_of_bracket_zero
    (n m : ℕ) (c : ℕ → Bool) (v r : List Bool) (hm : m ≤ n)
    (h : bracket (K := K) n m c v r = 0) :
    (∀ j, m < j → j ≤ n → c j = false) ∧ v = r ++ bitsOf m c :=
  (bracket_zero_iff n m c v r hm).mp h

/-- The wall is rejected by form R: `ReadVerifyNested` fails and `countsP ≠ 0`. -/
theorem structuralChecks_wall_is_formR_event [Nontrivial K] (e : ℕ) :
    ¬ ReadVerifyNested (wallTree (K := K) e) ∧
      countsP (wallTree (K := K) e) ≠ 0 :=
  ⟨(readVerifyNested_wall (K := K) e).2.2.2.2.2.2.2.2.2,
    formR_rejects_readVerifyNested_wall e⟩

/-- Remaining join: default form-R (`λ = 1`, `T = C' = 1`) can vanish
    with a Relaxis mismatch.  `specializedAxisValidity_of_accepts` therefore
    cannot recover Relaxis from the priced event without an extra `P ≠ 0`. -/
def cancellingTree (e : ℕ) (a : K) : MTree K :=
  .read e (.verify e a .halt)

theorem cancellingTree_countsP (e : ℕ) (a : K) :
    countsP (cancellingTree e a) = 0 := by
  simp [cancellingTree, countsP, indP, pwScale, MemoryTable.pwScaleExp]

theorem cancellingTree_vaxis (e : ℕ) (a : K) :
    vaxis e (cancellingTree e a) = a := by
  simp [cancellingTree, vaxis]

theorem cancellingTree_relaxis (e : ℕ) (a : K) :
    Relaxis e (cancellingTree (K := K) e a) = 1 := by
  simp [cancellingTree, Relaxis, vaddr, vdep, verifyCount, readCount]

theorem cancellingTree_is_remaining_join [Nontrivial K] (e : ℕ) :
    countsP (cancellingTree (K := K) e (0 : K)) = 0 ∧
      vaxis e (cancellingTree (K := K) e 0) ≠
        Relaxis e (cancellingTree (K := K) e 0) := by
  refine ⟨cancellingTree_countsP e 0, ?_⟩
  rw [cancellingTree_vaxis, cancellingTree_relaxis]
  exact zero_ne_one

/-- Live wrap ledger unchanged: the three names wait on the joins above. -/
def openConjunctsAfterFormRJoin : List String :=
  ["axisStructural", "rootBoundary", "structuralChecks"]

theorem openConjunctsAfterFormRJoin_eq :
    openConjunctsAfterFormRJoin =
      ["axisStructural", "rootBoundary", "structuralChecks"] :=
  rfl

theorem openConjunctsAfterFormRJoin_length :
    openConjunctsAfterFormRJoin.length = 3 := by decide

end Nock.RedTeam.Batch558

#print axioms Nock.RedTeam.Batch558.countsP_eq_cntM
#print axioms Nock.RedTeam.Batch558.formR_rejects_readVerifyNested_wall
#print axioms Nock.RedTeam.Batch558.readVerifyNested_wall_bin_zero_formR_nonzero
#print axioms Nock.RedTeam.Batch558.single_record_coeff_eq_bracket_eval
#print axioms Nock.RedTeam.Batch558.exactAxisTree_join_is_bracket_zero_iff
#print axioms Nock.RedTeam.Batch558.rootBoundary_of_wfAt
#print axioms Nock.RedTeam.Batch558.axisStructural_of_bracket_zero
#print axioms Nock.RedTeam.Batch558.structuralChecks_wall_is_formR_event
#print axioms Nock.RedTeam.Batch558.cancellingTree_is_remaining_join
#print axioms Nock.RedTeam.Batch558.openConjunctsAfterFormRJoin_length
