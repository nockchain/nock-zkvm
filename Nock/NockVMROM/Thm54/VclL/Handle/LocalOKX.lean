/-
  Nock/NockVMROM/Thm54/VclL/Handle/LocalOKX.lean

  **Card C-2 : step 3, the chip-level `LocalOK` cases, from
  `computeChipVCLHX`'s base gates (`BaseHoldsX`) to `LocalVSX.RowSemX` — first case: op 4 FAST.**
  New module, additive.

  A row's handle `h` decodes to `(val k, val v)` over `ZMod p` (`hdV`).  `op4_fast_sem`: on an
  OP4 row with `fast = 1`, the base gates alone (no record) give `D sf1 = atom n`,
  `D e = atom (n + 1)` for ANY `D` with `DenOKX` — the gate `v2 · inv4 = 1` excludes the wrap
  `p − 1 ↦ 0`, so the field increment is the ℕ increment.  The slow case, op 5, op 10 and op 11 need
  the served-record hypotheses (A-2 `inc_chain_sound_of_served`, AW `walkRecA`, J-3b
  `jetChip_holds`) and are not covered here.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
import Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX

open Nock Nock.Reified
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH (Hd)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX)

variable {p : ℕ} [Fact p.Prime]

/-- The decoded handle of a row: `(val k, val v)`. -/
def hdV (env : Env (ZMod p)) (h : Hd) : HX := ((env.trace h.k).val, (env.trace h.v).val)

/-- A kind with `kc = kb = 0` is the wire kind `0`. -/
theorem kind_zero {env : Env (ZMod p)} {h : Hd} (hc : kcV env h = 0) (hb : kbV env h = 0) :
    env.trace h.k = 0 := by
  simp only [kcV, kbV] at hc hb
  rw [hb, mul_zero, sub_zero] at hc
  exact hc

/-- **op 4, fast (C-2 step 3)**: the base gates give the exact ℕ increment on small atoms. -/
theorem op4_fast_sem {env : Env (ZMod p)} (hB : BaseHoldsX env) (h4 : tr env 4 = 1)
    (hf : tr env fastX = 1) {D : HX → Option Noun} (hD : DenOKX p D) :
    ∃ n : ℕ, D (hdV env xSf1) = some (.atom n) ∧ D (hdV env xE) = some (.atom (n + 1)) := by
  obtain ⟨hc1, hce, hb1, hbe, hv, hne⟩ := op4_fast_row hB h4 hf
  have k1 := kind_zero hc1 hb1
  have ke := kind_zero hce hbe
  refine ⟨(env.trace xSf1.v).val, ?_, ?_⟩
  · simp only [hdV, k1, ZMod.val_zero]; exact hD.atom _
  · simp only [hdV, ke, ZMod.val_zero]
    rw [show (tr env xE.v) = env.trace xE.v from rfl] at hv
    rw [hv]
    have hlt : (env.trace xSf1.v).val + 1 < p := by
      have h1 := ZMod.val_lt (env.trace xSf1.v)
      rcases Nat.lt_or_ge ((env.trace xSf1.v).val + 1) p with h | h
      · exact h
      · exfalso
        have heq : (env.trace xSf1.v).val + 1 = p := by omega
        apply hne
        have : ((env.trace xSf1.v).val + 1 : ZMod p) = 0 := by
          rw [show ((env.trace xSf1.v).val + 1 : ZMod p) = (((env.trace xSf1.v).val + 1 : ℕ) : ZMod p)
            by push_cast; ring, heq, ZMod.natCast_self]
        simpa [ZMod.natCast_zmod_val] using this
    have : (env.trace xSf1.v + 1).val = (env.trace xSf1.v).val + 1 := by
      rw [ZMod.val_add_of_lt (by rwa [ZMod.val_one_eq_one_mod, Nat.one_mod_eq_one.mpr
        (Fact.out : p.Prime).one_lt.ne'])]
      rw [ZMod.val_one_eq_one_mod, Nat.one_mod_eq_one.mpr (Fact.out : p.Prime).one_lt.ne']
    rw [this]; exact hD.atom _

end Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX
