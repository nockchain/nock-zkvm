/-
  Nock/RedTeam/Batch910Thm54HWAxisDichotomy.lean

  * `hW_axis_zero_or_fixed` — `hW` forces, on EVERY decoded row (not only active ones), the
    `axis` slot to be `0` (inactive rows: `specializeA` writes `MemRec.zero`) or a fixed point of
    `formRT λ ∘ nockAxisOf` (active rows, `Batch844.hW_forces_axis_fixed`).
  * `not_hW_of_row` — so one decoded row with a nonzero, non-fixed `axis` slot refutes `hW`.
  * `three_four_witness` — at EVERY field with `25 ≤ ringChar K` (so `p = 31`, `p = 769`,
    Goldilocks; every prime `nockCompiles_zmod` admits), the honest encode of axis `4` at
    `λ = 3` is `T = 9 ≠ 0`, and `formRT 3 (nockAxisOf 9) = 3³ = 27 ≠ 9`.  Instances at `ZMod 31`
    and `ZMod 769` are spelled out.

  No gate is read here: the failure is a property of the decode / re-encode pair at the value an
  honest row stores.  Part 2 puts it on the package's own canonical memory trace,
  accepted by the deployed family memory chip.
-/
import Nock.RedTeam.Batch844Thm54HpowHW
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch910

open scoped Polynomial
open Polynomial
open Nock
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

noncomputable section

/-! ## A. The row-level content of `hW` -/

section HW

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

/-- On an inactive row, wrap-then-specialize writes the zero record: its `axis` is `0`. -/
theorem specialize_wrap_axis_inactive (α lmb : K) (row : MState × DTmem K)
    (hact : memoryMemRecKind row.1 ≠ .active) :
    ((wrapMemoryLabel α row).specialize α lmb).2.2.mem.axis = 0 := by
  simp [MemoryRowTemplate.specialize, MemoryRowTemplate.encodeRow,
    MemoryRowTemplate.specializeA, wrapMemoryLabel, specializeMemRec, hact, MemRec.zero]

/-- **What `hW` says about one row.**  Every decoded row's `axis` slot (memory role 25) is `0` or
a fixed point of `formRT λ ∘ nockAxisOf`. -/
theorem hW_axis_zero_or_fixed (hW : Batch509.WrapMemoryIdentity P c Qm₀) (i : ℕ) :
    (lblM P Qm₀ c i).2.2.mem.axis = 0 ∨
      (lblM P Qm₀ c i).2.2.mem.axis =
        formRT c.2.2.2.lambda (nockAxisOf (lblM P Qm₀ c i).2.2.mem.axis) := by
  by_cases hact : memoryMemRecKind (lblM P Qm₀ c i).1 = .active
  · exact Or.inr (Batch844.hW_forces_axis_fixed P c Qm₀ hW i hact)
  · left
    have h := congrArg (fun r : MState × DTmem K => r.2.2.mem.axis) (hW i)
    rw [specialize_wrap_axis_inactive _ _ _ hact] at h
    exact h.symm

/-- **One bad row refutes `hW`.** -/
theorem not_hW_of_row (i : ℕ)
    (h0 : (lblM P Qm₀ c i).2.2.mem.axis ≠ 0)
    (hfix : (lblM P Qm₀ c i).2.2.mem.axis ≠
      formRT c.2.2.2.lambda (nockAxisOf (lblM P Qm₀ c i).2.2.mem.axis)) :
    ¬ Batch509.WrapMemoryIdentity P c Qm₀ := fun hW =>
  (hW_axis_zero_or_fixed P c Qm₀ hW i).elim h0 hfix

end HW

/-! ## B. The witness value, at every admissible prime -/

theorem formRCertShift_four : formRCertShift 4 = 2 := by decide
theorem formRCertShift_five : formRCertShift 5 = 2 := by decide
theorem formRCertShift_six : formRCertShift 6 = 2 := by decide
theorem formRCertShift_seven : formRCertShift 7 = 2 := by decide
theorem formRCertShift_nine : formRCertShift 9 = 3 := by decide

section Witness

variable {K : Type} [Field K]

theorem natCast_ne_zero_of_lt {n : ℕ} (hn : 0 < n) (hlt : n < ringChar K) : (n : K) ≠ 0 := by
  intro h
  have hdvd : ringChar K ∣ n := (CharP.cast_eq_zero_iff K (ringChar K) n).mp h
  exact absurd (Nat.le_of_dvd hn hdvd) (by omega)

/-- Every axis with shift `2` (`a ∈ {4, 5, 6, 7}`) encodes at `λ = 3` to `T = 9`. -/
theorem formRT_three_of_shift_two {a : ℕ} (ha : formRCertShift a = 2) :
    formRT (3 : K) a = ((9 : ℕ) : K) := by
  rw [formRT, ha]; push_cast; norm_num

/-- **The witness.**  At every field with `25 ≤ ringChar K`, an honest row storing the Form R
encode of an axis with shift `2` at `λ = 3` has `T = 9 ≠ 0`, and the decode / re-encode pair
sends it to `27 ≠ 9`. -/
theorem three_shift_two_witness (hp : 25 ≤ ringChar K) {a : ℕ} (ha : formRCertShift a = 2) :
    formRT (3 : K) a ≠ 0 ∧
      formRT (3 : K) a ≠ formRT (3 : K) (nockAxisOf (formRT (3 : K) a)) := by
  rw [formRT_three_of_shift_two ha]
  refine ⟨natCast_ne_zero_of_lt (by norm_num) (by omega), ?_⟩
  rw [nockAxisOf_natCast (by omega), formRT, formRCertShift_nine]
  intro h
  have h18 : ((18 : ℕ) : K) = 0 := by
    have : ((27 : ℕ) : K) - ((9 : ℕ) : K) = ((18 : ℕ) : K) := by push_cast; ring
    rw [← this]
    have h' : ((9 : ℕ) : K) = (3 : K) ^ 3 := h
    rw [h']; push_cast; ring
  exact natCast_ne_zero_of_lt (K := K) (by norm_num) (by omega) h18

theorem three_four_witness (hp : 25 ≤ ringChar K) :
    formRT (3 : K) 4 ≠ 0 ∧
      formRT (3 : K) 4 ≠ formRT (3 : K) (nockAxisOf (formRT (3 : K) 4)) :=
  three_shift_two_witness hp formRCertShift_four

end Witness

instance fact_prime_31 : Fact (Nat.Prime 31) := ⟨by norm_num⟩
instance fact_prime_769 : Fact (Nat.Prime 769) := ⟨by norm_num⟩

theorem three_four_witness_31 :
    formRT (3 : ZMod 31) 4 ≠ 0 ∧
      formRT (3 : ZMod 31) 4 ≠ formRT (3 : ZMod 31) (nockAxisOf (formRT (3 : ZMod 31) 4)) :=
  three_four_witness (by rw [ZMod.ringChar_zmod_n]; norm_num)

theorem three_four_witness_769 :
    formRT (3 : ZMod 769) 4 ≠ 0 ∧
      formRT (3 : ZMod 769) 4 ≠ formRT (3 : ZMod 769) (nockAxisOf (formRT (3 : ZMod 769) 4)) :=
  three_four_witness (by rw [ZMod.ringChar_zmod_n]; norm_num)

end

end Nock.RedTeam.Batch910

#print axioms Nock.RedTeam.Batch910.hW_axis_zero_or_fixed
#print axioms Nock.RedTeam.Batch910.not_hW_of_row
#print axioms Nock.RedTeam.Batch910.three_shift_two_witness
#print axioms Nock.RedTeam.Batch910.three_four_witness_31
#print axioms Nock.RedTeam.Batch910.three_four_witness_769
