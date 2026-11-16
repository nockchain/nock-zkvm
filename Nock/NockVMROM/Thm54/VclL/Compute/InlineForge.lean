import Nock.NockVMROM.Thm54.VclL.Compute.AxGate

/-!
VCL-L decomposes record `0` (`[op tail] @ 3`) inline:
the row's gates give `f = FP.cons z f_h f_t` with `f_h = atomFP z op` for the row's own opcode `op`
(the SV head gates) — i.e. `f = cons(atomFP z op, f_t)`, and `f_t` is then UNIQUE
(`Consumers.cons_right_unique`).  L-C's `inline_records` asks for more: every bounded noun `rt` with
`enc z rt = f` has a child at axis `3` whose fingerprint is `f_t`.

* `inline_sound_of_head`: that holds when `rt`'s head IS the atom `op`.
* `wrong_opcode_inline_forge`: it fails otherwise, at EVERY seed `z ≠ 0`, for EVERY choice of
  `inlinePairs` (the failure is a polynomial identity in `z`, not a collision): for
  `rt = [k t]` with `k ≠ op` (a row labelled with opcode `op` whose formula's head is `k`), the
  forged tail `f_t := (S_t, D_t, L_t + (k − op)·z⁻¹)` satisfies `cons(atomFP z op, f_t) = enc z rt`,
  and no child of `rt` at axis `3` has fingerprint `f_t` (the only one is `t`, and
  `enc z t ≠ f_t`).
  Its fingerprint, window and bound premises hold; the only other premise is the instance's pair
  separation, and `t` is the unique axis-3 child, so no pair list rescues it at any `z` where the
  pairs separate.

So `inlinePairCount` can be neither `0` nor `1` with the inline gate alone: the inline record is not
sound as gated.

Paper: `:1846-1852` (the always-operative record `mr1 = ⟨f, f_t, 3⟩`), `:1728-1742` (`V_comp`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute

open Nock
open Nock.ComputeTable (FP)

noncomputable section

section forge
variable {K : Type*} [Field K]

/-- The inline step is sound when the root noun's head is the row's opcode atom. -/
theorem inline_sound_of_head {z : K} (hz : z ≠ 0) (op : ℕ) (t : Noun) (ft : FP K)
    (h : GlobalCarryRecognizer.enc z (.cell (.atom op) t) = FP.cons z (FP.atomFP z (op : K)) ft) :
    Noun.slot 3 (.cell (.atom op) t) = some t ∧ GlobalCarryRecognizer.enc z t = ft := by
  refine ⟨by simp [Noun.slot], ?_⟩
  rw [GlobalCarryRecognizer.enc_cons hz, GlobalCarryRecognizer.enc_atom] at h
  exact cons_right_unique z hz h

/-- The forged tail fingerprint of a row labelled `op` whose formula is `[k t]`. -/
def forgedTail (z : K) (k op : ℕ) (t : Noun) : FP K :=
  ⟨(GlobalCarryRecognizer.enc z t).size, (GlobalCarryRecognizer.enc z t).dyck,
    (GlobalCarryRecognizer.enc z t).leaf + ((k : K) - (op : K)) * z⁻¹⟩

theorem wrong_opcode_inline_forge {z : K} (hz : z ≠ 0) (k op : ℕ) (hk : (k : K) ≠ (op : K))
    (t : Noun) :
    FP.cons z (FP.atomFP z (op : K)) (forgedTail z k op t) =
        GlobalCarryRecognizer.enc z (.cell (.atom k) t) ∧
      ¬ ∃ ch : Noun, Noun.slot 3 (.cell (.atom k) t) = some ch ∧
        GlobalCarryRecognizer.enc z ch = forgedTail z k op t := by
  constructor
  · rw [GlobalCarryRecognizer.enc_cons hz, GlobalCarryRecognizer.enc_atom]
    simp only [FP.cons, FP.atomFP, forgedTail]
    refine FP.ext rfl rfl ?_
    field_simp
    ring
  · rintro ⟨ch, hs, he⟩
    have hch : ch = t := by simp [Noun.slot] at hs; exact hs.symm
    subst hch
    have hl := congrArg FP.leaf he
    simp only [forgedTail] at hl
    have : ((k : K) - (op : K)) * z⁻¹ = 0 := by linear_combination -hl
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hk (sub_eq_zero.1 h1)
    · exact inv_ne_zero hz h1

/-- The concrete instance: a row labelled `s1` (opcode `1`) whose formula is `[2 [0 1] [0 1]]`. -/
theorem wrong_opcode_forge_s1 {z : K} (hz : z ≠ 0) (hchar : ((2 : ℕ) : K) ≠ ((1 : ℕ) : K)) :
    let t : Noun := .cell (.cell (.atom 0) (.atom 1)) (.cell (.atom 0) (.atom 1))
    FP.cons z (FP.atomFP z ((1 : ℕ) : K)) (forgedTail z 2 1 t) =
        GlobalCarryRecognizer.enc z (.cell (.atom 2) t) ∧
      ¬ ∃ ch : Noun, Noun.slot 3 (.cell (.atom 2) t) = some ch ∧
        GlobalCarryRecognizer.enc z ch = forgedTail z 2 1 t :=
  wrong_opcode_inline_forge hz 2 1 hchar _

end forge

end

end VclL.Compute
end Nock.NockVMROM.Thm54
