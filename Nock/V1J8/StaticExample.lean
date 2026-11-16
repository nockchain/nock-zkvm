/-
  Nock/V1J8/StaticExample.lean

  **The static check at the J-8 example `*[[0 0] [0 1]] = [0 0]`.**

  * `staticJ8_example` / `checkStaticJ8_example`: the inhabitant's public data `PbJ hdvd Rt`, claim `c0`, claim
    message `mC0 (H0 p)`, rows `rJ0`, budget `0` satisfy `StaticJ8`, so `checkStaticJ8 … = true` (kernel, through
    `checkStaticJ8_iff`; no `decide`), at every `p` with `B ≤ p`, `3 · 2 ∣ p − 1`, and at Goldilocks.
-/
import Nock.V1J8.Static
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J8.StaticExample

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (RowsJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Static
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemDom
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemMain
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Atom
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main
open Nock.V1J8

section Ex
variable {p : ℕ} [Fact p.Prime] [Fact (ringChar (ZMod p)).Prime]

/-- **`StaticJ8` at the J-8 example** (the inhabitant's public data). -/
theorem staticJ8_example (hB : Nock.Atoms.B ≤ p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    StaticJ8 (PbJ hdvd Rt) c0 (InhabJ8Comp.mC0 (H0 p)) rJ0 0 := by
  have hBp : 2 ^ 32 ≤ p := hB
  have hp2 : 2 ≤ p := le_trans (by norm_num) hBp
  have hr : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  exact
  { hinjX := fun a c _ => Fin.ext (by
      have h1 : (a : ℕ) < 1 := a.isLt
      have h2 : (c : ℕ) < 1 := c.isLt
      omega)
    hadjX := fun i hi => absurd (show (i : ℕ) + 1 < 1 from hi) (by omega)
    hinjC := memC_inj (PbBase hdvd Rt) hdvd
    hadjC := memC_adj (PbBase hdvd Rt) hdvd
    hnpC := lt_of_lt_of_eq (memC_np (PbBase hdvd Rt) hdvd) hr
    hinjW := memW_inj (PbBase hdvd Rt) hdvd
    hadjW := memW_adj (PbBase hdvd Rt) hdvd
    hkW := memW_k (PbBase hdvd Rt) hdvd
    hknW := memW_kn (PbBase hdvd Rt) hdvd
    hkpW := lt_of_lt_of_eq (memW_kp (PbBase hdvd Rt) hdvd) hr
    hinjA := hinjA_A0 (PbJ hdvd Rt) rfl
    hadjA := hadjA_A0 (PbJ hdvd Rt) rfl
    hnpA := hnpA_A0 (PbJ hdvd Rt) rfl
    hlay := hlay0 (PbJ hdvd Rt) rfl rfl rfl
    hsmall := hsmall0 (PbJ hdvd Rt) rfl rfl
    huniq := huniq0 (PbJ hdvd Rt) rfl rfl
    haxT := regs_vacuous (PbJ hdvd Rt) rfl
    hnd := hnd0 (PbJ hdvd Rt) rfl
    hidx := regs_vacuous (PbJ hdvd Rt) rfl
    hrk := regs_vacuous (PbJ hdvd Rt) rfl
    hlt := regs_vacuous (PbJ hdvd Rt) rfl
    hclA := hclA0 p
    hclI := fun k _ => by
      show (H0 p (claimNoun c0 k)).2 < p
      rw [claimNoun_c0]
      split_ifs
      · rw [H0_f0]; omega
      · rw [H0_s0]; omega
    hclR := hclR0 p (by omega)
    hcen := hcen0 (PbJ hdvd Rt) rfl hp2
    hlenC := by show 3 + 0 + 2 * 2 < p; omega
    hlenA := by show 1 + 1 < p; omega
    hcellF := hcellF0
    hnA62 := by show 1 ≤ 2 ^ 62; norm_num
    hbud := hbud0 (PbJ hdvd Rt) rJ0 _ rfl rfl (by simp [PbJ, PbBase, withMem, rJ0])
      (by simp [PbJ, PbBase, withMem, rJ0]) (by simp [PbJ, PbBase, withMem, rJ0])
      (by simp [PbJ, PbBase, withMem, rJ0]) (by simp [PbJ, PbBase, withMem, rJ0])
      (by simp [PbJ, PbBase, withMem, rJ0])
    hbudV := ⟨le_refl _, by simp [PbJ, PbBase, withMem, rJ0], by simp [PbJ, PbBase, withMem, rJ0],
      by simp [PbJ, PbBase, withMem, rJ0]⟩ }

/-- **The static check passes at the J-8 example** (kernel, through `checkStaticJ8_iff`). -/
theorem checkStaticJ8_example (hB : Nock.Atoms.B ≤ p) (hdvd : 3 * 2 ^ 1 ∣ p - 1) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    checkStaticJ8 (PbJ hdvd Rt) c0 (InhabJ8Comp.mC0 (H0 p)) rJ0 0 = true :=
  (checkStaticJ8_iff _ _ _ _ _).mpr (staticJ8_example hB hdvd Rt)

/-- **At Goldilocks.** -/
theorem checkStaticJ8_example_goldilocks (hpG : p = Nock.Atoms.p) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    ∃ hdvd : 3 * 2 ^ 1 ∣ p - 1, checkStaticJ8 (PbJ hdvd Rt) c0 (InhabJ8Comp.mC0 (H0 p)) rJ0 0 = true := by
  have hB : Nock.Atoms.B ≤ p := by
    rw [hpG, show Nock.Atoms.B = 2 ^ 32 from rfl, show Nock.Atoms.p = Nock.Field.p from rfl, Nock.Field.p_eq]
    norm_num
  have hdvd : 3 * 2 ^ 1 ∣ p - 1 := by
    rw [hpG, show Nock.Atoms.p = Nock.Field.p from rfl, Nock.Field.p_eq, Nat.dvd_iff_mod_eq_zero]
    norm_num
  exact ⟨hdvd, checkStaticJ8_example hB hdvd Rt⟩

end Ex

end Nock.V1J8.StaticExample
