/-
  Nock/RedTeam/Batch554Thm54PwFunctional.lean

  * **A. The functional on `WT`** (a tree whose wrappers inject arbitrary `(δc, δw)` at
    arbitrary positions).  `decompose`: `counts_P = counts_L + counts_R + (λ−1)(pw_L + pw_R) +
    pw_R`, `pw_P = λ(pw_L + pw_R)`; wrapper: `+ δc·X^e`, `+ δw·X^e`.  `functional`: every
    wrapper at top-down path `p` contributes `δc + (P_p − 1)·δw` to `counts` and `λ^{|p|}·δw` to
    `pw` at the top, `P_p = addr λ p` the paper's `2·axis + bit` address at base `λ`.
  * **B. The `MTree` instance with a general verify weight `s`** (`ofM`): verify `(s, s)`, read
    wrapper `(−A_e, −W_e)`; the `X^e`-coefficient at the top is
    `s·Σ_{verifies of e} P_V − Σ_{reads of e} (A_e + W_e(P_R − 1))` (`coeff_cntM`) — for ANY
    number of reads/verifies of `e`, so "two records with the same timestamp" is a case, not an
    exclusion.  `honest_single_record`: exact for every `λ`, every placement, every `s`.
  * **C. The (i'') certificate, polynomial form.**  `bracket_zero_iff`: zero as a polynomial **iff** every padding bit `c_{j>m}` is
    `0` and `V = R ++ [c_1, …, c_m]` — one theorem, both directions, the Laurent step and the
    ancestry step together.  Corollaries: verify above its read, read and verify on the same
    node (forces `a = 1`), a read whose subtree holds no verify, `a = 0`, cross-root (both
    roots' polynomials nonzero for every certificate).
  * **D. Concrete traces**, by this file's own computation: honest `/[5 S]` exact, `/[6 S]` served
    for `5` gives `(λ−1)·ts`; D-λ's `t1`, `t2`, `tfull` give `λ(λ−1)·ts`, `λ²(λ−1)·ts`,
    `λ(λ−1)·ts₂`; the same-timestamp cancellation `X^{e₁} − X^{e₂}` (two wrong records, accepted
    exactly on `α^{e₁} = α^{e₂}`, with `pw ≡ 0` — the bivariate event, not `pw`, prices it).
-/
import Nock.AxisBatching
import Nock.Reference
import Nock.RedTeam.Batch546Thm54LambdaModel
import Nock.NockVMROM.Thm54.FormRCore.PwFunctional

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch554

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Polynomial

variable {K : Type*} [Field K]

/-! ## A–C. -/

/-! ## D. -/

/-- `/[5 S]`: read at the root, verify at `[left, right]`; certificate `a = 5`: `T = λ²`,
`a_λ = λ² + 1`.  Exact for every `λ`. -/
theorem honest_five_exact (l : K) (e : ℕ) :
    cntM l 1 (fun _ => l ^ 2 + 1) (fun _ => l ^ 2)
      (.read e (place [false, true] (.verify e 0 .halt))) = 0 := by
  have h := (honest_single_record l 1 e 0 [] [false, true]).1
  have ha : addr l [false, true] = l ^ 2 + 1 := by simp [addr, addrFrom, bit]; ring
  simpa [honestTree, place, ha] using h

/-- The same record served at `/[6 S]` (verify at `[right, left]`): `(λ − 1)·ts`, rejected for
every `λ ≠ 1`. -/
theorem forged_six_for_five (l : K) (e : ℕ) :
    cntM l 1 (fun _ => l ^ 2 + 1) (fun _ => l ^ 2)
      (.read e (place [true, false] (.verify e 0 .halt))) = C (l - 1) * X ^ e := by
  have hv : vpaths e (.read e (place [true, false] (.verify e 0 .halt)) : MTree K)
      = [[true, false]] := by simp [vpaths, vpaths_place]
  have hr : rpaths e (.read e (place [true, false] (.verify e 0 .halt)) : MTree K) = [[]] := by
    simp [rpaths, rpaths_place]
  ext e'
  rw [coeff_C_mul, coeff_X_pow]
  by_cases h : e' = e
  · subst h
    rw [single_record _ _ _ _ _ _ _ _ hv hr, if_pos rfl]
    simp [addr, addrFrom, bit]; ring
  · rw [(coeff_cntM _ _ _ _ _ _).2, if_neg h]
    simp [vpaths, rpaths, vpaths_place, rpaths_place, Ne.symm h, sumAddr]

/-- D-λ's `t1` (`a = 1`): `λ(λ − 1)·ts`. -/
theorem t1_rejected (l : K) (e : ℕ) :
    cntM l 1 (fun _ => 1) (fun _ => 1) (Batch546.t1 e 0) = C (l * (l - 1)) * X ^ e := by
  simp only [Batch546.t1, cntM, ofM, cnt, pw, C_mul, C_sub, C_1, C_neg]; ring

/-- D-λ's `t2` (`a = 2`, `T = λ`, `a_λ = λ`): `λ²(λ − 1)·ts`. -/
theorem t2_rejected (l : K) (e : ℕ) :
    cntM l 1 (fun _ => l) (fun _ => l) (Batch546.t2 e 0) = C (l ^ 2 * (l - 1)) * X ^ e := by
  simp only [Batch546.t2, cntM, ofM, cnt, pw, C_mul, C_sub, C_1, C_neg, C_pow]; ring

/-- D-λ's `tfull` (honest `a = 3` at the root, forged `a = 1` at the tail): `λ(λ − 1)·ts₂`. -/
theorem tfull_rejected (l : K) (e₁ e₂ : ℕ) (hne : e₁ ≠ e₂) :
    cntM l 1 (fun e => if e = e₁ then l + 1 else 1) (fun e => if e = e₁ then l else 1)
      (Batch546.tfull e₁ e₂ 0 0) = C (l * (l - 1)) * X ^ e₂ := by
  simp only [Batch546.tfull, cntM, ofM, cnt, pw, if_true, if_neg (Ne.symm hne), C_mul, C_sub,
    C_add, C_1, C_neg]
  ring

/-- **Two records with DISTINCT exponents `e₁ ≠ e₂`, both wrong** (record `e₁` certifies `a = 2`
but its verify sits at `/[3]`; record `e₂` certifies `a = 3` but sits at `/[2]`): the top
`counts` is `X^{e₁} − X^{e₂}` — a NONZERO polynomial that vanishes exactly on the timestamp
collision `α^{e₁} = α^{e₂}` — while `pw ≡ 0`.  Distinct EXPONENTS are what the bivariate event
prices; `pw = 0` sees nothing here. -/
def sameTsTree (e₁ e₂ : ℕ) : MTree K :=
  .read e₁ (.read e₂ (.decompose (.verify e₂ 0 .halt) (.verify e₁ 0 .halt)))

theorem same_ts_cancellation (l : K) (e₁ e₂ : ℕ) (hne : e₂ ≠ e₁) :
    cntM l 1 (fun e => if e = e₁ then l else l + 1) (fun _ => l) (sameTsTree e₁ e₂)
        = X ^ e₁ - X ^ e₂
    ∧ pwM l 1 (fun e => if e = e₁ then l else l + 1) (fun _ => l) (sameTsTree e₁ e₂) = 0 := by
  constructor
  · simp only [sameTsTree, cntM, ofM, cnt, pw, if_true, if_neg hne, C_neg, C_add, C_1, C_sub]
    ring
  · simp only [sameTsTree, pwM, ofM, pw, C_neg, C_1]; ring

theorem same_ts_cancellation_nonzero (e₁ e₂ : ℕ) (hne : e₁ ≠ e₂) :
    (X ^ e₁ - X ^ e₂ : K[X]) ≠ 0 := by
  intro h
  have hc := congrArg (fun q : K[X] => q.coeff e₁) h
  simp [coeff_X_pow, hne] at hc

/-- `/[5 S] ≠ /[6 S]` on `S = [[u v] [x y]]`, `v ≠ x`: the accepted forgery is a false claim. -/
theorem slot_five_ne_six (u v x y : ℕ) (h : v ≠ x) :
    Noun.slot 5 (.cell (.cell (.atom u) (.atom v)) (.cell (.atom x) (.atom y)))
      ≠ Noun.slot 6 (.cell (.cell (.atom u) (.atom v)) (.cell (.atom x) (.atom y))) := by
  simp [Noun.slot]; exact h

end Nock.RedTeam.Batch554

#print axioms Nock.RedTeam.Batch554.functional
#print axioms Nock.RedTeam.Batch554.coeff_cntM
#print axioms Nock.RedTeam.Batch554.honest_single_record
#print axioms Nock.RedTeam.Batch554.addrP_injective
#print axioms Nock.RedTeam.Batch554.bracket_zero_iff
#print axioms Nock.RedTeam.Batch554.verify_above_read_rejected
#print axioms Nock.RedTeam.Batch554.same_node_forces_axis_one
#print axioms Nock.RedTeam.Batch554.cross_root_both_nonzero
#print axioms Nock.RedTeam.Batch554.forged_six_for_five
#print axioms Nock.RedTeam.Batch554.tfull_rejected
#print axioms Nock.RedTeam.Batch554.same_ts_cancellation
