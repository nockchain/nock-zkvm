/-
  Nock/RedTeam/Batch576Thm54FormRNegatives.lean

  **Form R negative controls on `MTree`.**

  `S = cons(R, w)`, read at `R`, verify at sibling `w`.
      `formRCounts ≠ 0`; the `X^e` coefficient is the cross-root bracket.
      The OO wall (`u = w`) is the same `MTree` shape.
  N2. The seeing term is the root-level `+ pw_R` (`formRPw` of the right child).
  N3. Alias/padding: `c_e j = true` for some `j > m_e` is rejected by S2's padding.
  N4. The same N1/N2 trees have base-2 `countsP_bin = 0` (imported receipts).
-/
import Nock.AxisBatching
import Nock.AxisBridge
import Nock.RedTeam.Batch534Thm54CrossingVmem
import Nock.RedTeam.Batch546Thm54LambdaModel
import Nock.RedTeam.Batch554Thm54PwFunctional
import Nock.RedTeam.Batch575Thm54FormRMtree

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch576

open Nock
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.RedTeam.Batch554
  (vpaths rpaths addrP addrPFrom addrP_nil bitsOf Cpoly bracket bracket_zero_iff
    bracket_zero_prefix bit)
open Nock.RedTeam.Batch575
open Nock.RedTeam.Batch546
open Polynomial

variable {K : Type*} [Field K]


/-- Crossing shape of `Batch534.crossing_shape_is_the_wall` / `readVerifyNested_wall`:
read on the left child, verify on the right sibling. -/
def crossingTree (e : ℕ) (a : K) : MTree K :=
  .decompose (.read e (.decompose .halt .halt)) (.verify e a .halt)

theorem crossing_paths (e : ℕ) (a : K) :
    vpaths e (crossingTree e a) = [[true]]
    ∧ rpaths e (crossingTree e a) = [[false]] := by
  simp [crossingTree, vpaths, rpaths]

theorem crossing_unique (e : ℕ) (a : K) : UniqueExponents (crossingTree e a) := by
  intro e'
  constructor <;> simp [crossingTree, readCount, verifyCount] <;> split_ifs <;> simp

/-- **N1.** Form R rejects the crossing for every certificate: `r = [false]` is not a
prefix of `v = [true]`, so the bracket is nonzero (`Batch554.bracket_zero_prefix`). -/
theorem n1_crossing_rejected (n e : ℕ) (a : K) (mm : ℕ) (c : ℕ → Bool)
    (hm : mm ≤ n - 1) :
    (formRCounts n (fun _ => mm) (fun _ => c) (crossingTree e a)).coeff e ≠ 0 := by
  obtain ⟨hv, hr⟩ := crossing_paths e a
  rw [paired_bracket n (fun _ => mm) (fun _ => c) e (crossingTree e a) [true] [false] hv hr]
  intro hz
  have hpre := bracket_zero_prefix (n - 1) mm c [true] [false] hm hz
  have : ([false] : List Bool) <+: [true] := hpre
  simp [List.IsPrefix] at this

/-- OO wall (`u = w`): same `MTree` as N1. Form R still rejects. -/
theorem n1_oo_wall (n e : ℕ) (mm : ℕ) (c : ℕ → Bool) (hm : mm ≤ n - 1) :
    (formRCounts n (fun _ => mm) (fun _ => c) (crossingTree e (2 : K))).coeff e ≠ 0 :=
  n1_crossing_rejected n e (2 : K) mm c hm


/-- **N2.** `t1` with the axis-1 certificate (`m = 0`, padding `0`).
The named seeing term is the root-level `+ pw_R`: `formRPw` of the right-child
read equals `- Y^{n−1} · X^e`. -/
theorem n2_pw_R (n e : ℕ) (a : K) :
    formRPw n axis1 (MTree.read e (.halt : MTree K))
      = -C (scale n) * (X : (Polynomial K)[X]) ^ e := by
  simp only [formRPw, axis1, Tpoly, scale, Y, pow_zero, mul_one]
  ring

theorem n2_t1_rejected (n e : ℕ) :
    (formRCounts n axis1 axis1bits (t1 e (1 : K))).coeff e ≠ 0 := by
  have hv : vpaths e (t1 (K := K) e 1) = [[false, true]] := by
    simp [t1, vpaths]
  have hr : rpaths e (t1 (K := K) e 1) = [[true]] := by
    simp [t1, rpaths]
  rw [paired_bracket n axis1 axis1bits e (t1 e 1) [false, true] [true] hv hr]
  intro hz
  have hpre := bracket_zero_prefix (n - 1) 0 (axis1bits e) [false, true] [true]
    (Nat.zero_le _) hz
  -- `[true]` is not a prefix of `[false, true]`
  simp [List.IsPrefix] at hpre

/-! ## N3 — padding bit above `m` -/

def padBit (_j : ℕ) : Bool := true

/-- **N3.** Same-node tree (the S2-failing shape) with a padding bit `c_1 = true`
and `m = 0`, `n ≥ 2`: S2's padding conjunct fails and the bracket is nonzero. -/
theorem n3_padding_rejected (n e : ℕ) (a : K) (hn : 2 ≤ n) :
    (formRCounts n (fun _ => 0) (fun _ => padBit) (s2FailTree e a)).coeff e ≠ 0 := by
  obtain ⟨hv, hr⟩ := s2Fail_paths e a
  rw [paired_bracket n (fun _ => 0) (fun _ => padBit) e (s2FailTree e a) [] [] hv hr]
  intro hz
  have ⟨hpad, _⟩ := (bracket_zero_iff (n - 1) 0 padBit [] [] (Nat.zero_le _)).mp hz
  have := hpad 1 (by omega) (by omega)
  simp [padBit] at this

/-! ## N4 — base-2 `countsP_bin` accepts the same trees -/

/-- **N4 / N1.** -/
theorem n4_crossing_countsP (e : ℕ) :
    countsP_bin (crossingTree (K := ℚ) e 2) = 0 :=
  (Batch534.crossing_shape_is_the_wall e).2.1

/-- **N4 / N2.** Base-2 `countsP_bin` vanishes on `t1` at committed axis `1`. -/
theorem n4_t1_countsP (e : ℕ) :
    countsP_bin (t1 (K := ℚ) e 1) = 0 := by
  simp only [t1, countsP_bin, indP_bin, C_1]
  ring


end Nock.RedTeam.Batch576

#print axioms Nock.RedTeam.Batch576.n1_crossing_rejected
#print axioms Nock.RedTeam.Batch576.n2_t1_rejected
#print axioms Nock.RedTeam.Batch576.n3_padding_rejected
#print axioms Nock.RedTeam.Batch576.n4_crossing_countsP
