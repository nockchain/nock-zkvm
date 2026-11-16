/-
`acceptsJ9AL_congr_reg0`, the template / index / rank functions of the public parameters are read by
`AcceptsJ9AL` only at the registered ids `Pb.regs` (and through `layoutJ8 Pb.Rt Pb.regs Pb.ids`).  At a jet-free instance (`regs = ids = []`) the three functions
`Rt`, `idx`, `rk` can be replaced by arbitrary ones.  This is needed because nock's generator `genJ9ALXJ` records the real `idxOf` / `rkC` of the (unused) template
`Rt id`, whereas the datum `DX9L` carries `idx = fun _ => 0`, `rk = fun _ => (0,0)`, `Rt = fun _ => tplDummy`.  Not zero-knowledge.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.J9AL.AccCongJ9AL

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (pinRecsJ8 censusG)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.ChipJ8 (layoutJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (censusGJ9)
open Module Polynomial

section Cong
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

theorem acceptsJ9AL_congr_reg0 {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : SVFrame.Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g : ℕ}
    (Rt' : ℕ → Nock.Jet.Autogen.Tpl) (idx' : ℕ → ℕ) (rk' : ℕ → ℕ × ℕ) (idxP' : ℕ → ℕ) (rkP' : ℕ → ℕ × ℕ)
    (hregs : Pb.regs = []) (hids : Pb.ids = [])
    (hiP : ∀ q ∈ Pb.prims, idxP' q.1 = Pb.idxP q.1) (hrP : ∀ q ∈ Pb.prims, rkP' q.1 = Pb.rkP q.1)
    (h : AcceptsJ9AL.AcceptsJ9AL δ b Pb Rg c χ M tr r g) :
    AcceptsJ9AL.AcceptsJ9AL δ b { Pb with Rt := Rt', idx := idx', rk := rk', idxP := idxP', rkP := rkP' } Rg c χ M tr r g := by
  generalize hP' : ({ Pb with Rt := Rt', idx := idx', rk := rk', idxP := idxP', rkP := rkP' } : PubJ9AL p) = Pb'
  have hr : Pb'.regs = [] := by rw [← hP']; exact hregs
  have e1 : AcceptsJ9AL.pinRgP (K := K) Pb' = AcceptsJ9AL.pinRgP (K := K) Pb := by
    rw [← hP']
    unfold AcceptsJ9AL.pinRgP
    exact List.map_congr_left (fun q hq => by simp only [hiP q hq])
  have e2 : AcceptsJ9AL.pinOpP (K := K) Pb' = AcceptsJ9AL.pinOpP (K := K) Pb := by rw [← hP']; rfl
  have e3 : pinRecsJ8 δ Pb'.toPubJ8 χ = [] := by rw [← hP']; simp [pinRecsJ8, hregs]
  have e4 : pinRecsJ8 δ Pb.toPubJ8 χ = [] := by simp [pinRecsJ8, hregs]
  have e5 : censusGJ9 Pb'.toPubJ8 c = censusGJ9 Pb.toPubJ8 c := by rw [← hP']; simp [censusGJ9, censusG, hregs]
  have e6 : AcceptsJ9AL.censusP Pb' = AcceptsJ9AL.censusP Pb := by rw [← hP']; rfl
  have e7 : AcceptsJ9AL.pinRecsP δ Pb' χ = AcceptsJ9AL.pinRecsP δ Pb χ := by
    rw [← hP']
    unfold AcceptsJ9AL.pinRecsP
    exact List.map_congr_left (fun q hq => by simp only [hiP q hq, hrP q hq])
  have hip : ∀ q ∈ Pb'.prims, Pb'.idxP q.1 = Pb.idxP q.1 := by rw [← hP']; exact hiP
  have hrp : ∀ q ∈ Pb'.prims, Pb'.rkP q.1 = Pb.rkP q.1 := by rw [← hP']; exact hrP
  have hpr : Pb'.prims = Pb.prims := by rw [← hP']
  subst hP'
  refine { h with hbud := ⟨h.hbud.x1, h.hbud.x2, h.hbud.p1, h.hbud.p2, h.hbud.s1, h.hbud.s2⟩, hGS := ?_, hlay := ?_, hsmall := ?_, huniq := ?_, hTpl := ?_, hidx := ?_, hrk := ?_, hlt := ?_, hsumC' := ?_, hcen' := ?_, hlenL := ?_, hrkP := ?_, hltP := ?_ }
  · have h1 := h.hGS
    rw [hregs] at h1
    show _ = _
    rw [e1, e2, hr]
    simpa [pinCons] using h1
  · have h1 := h.hlay
    show List.ofFn Pb.lay = layoutJ8 Rt' Pb.regs Pb.ids
    rw [hregs, hids] at h1 ⊢
    exact h1
  · have h1 := h.hsmall
    show ∀ q ∈ layoutJ8 Rt' Pb.regs Pb.ids, _
    rw [hregs, hids] at h1 ⊢
    exact h1
  · have h1 := h.huniq
    show ((layoutJ8 Rt' Pb.regs Pb.ids).filterMap _).Nodup
    rw [hregs, hids] at h1 ⊢
    exact h1
  · intro i hi; exact absurd hi (by simp [hregs])
  · intro i hi; exact absurd hi (by simp [hregs])
  · intro i hi; exact absurd hi (by simp [hregs])
  · intro i hi; exact absurd hi (by simp [hregs])
  · have h1 := h.hsumC'
    rw [e4] at h1
    show _ = _
    rw [e3, e7]
    exact h1
  · have h1 := h.hcen'
    rw [e5, e6]
    exact h1
  · obtain ⟨a, b', c'⟩ := h.hlenL
    refine ⟨a, b', fun q hq => ?_⟩
    have := c' q hq
    show q.1 < p ∧ idxP' q.1 < p
    rw [hiP q hq]; exact this
  · intro q hq
    have := h.hrkP q hq
    show rkP' q.1 ≠ (0, 0)
    rw [hrP q hq]; exact this
  · intro q hq
    have := h.hltP q hq
    show (rkP' q.1).1 < ringChar (ZMod p) ∧ (rkP' q.1).2 < ringChar (ZMod p) ∧ idxP' q.1 < ringChar (ZMod p)
    rw [hrP q hq, hiP q hq]; exact this

end Cong

end NockvmE2E.J9AL.AccCongJ9AL

#print axioms NockvmE2E.J9AL.AccCongJ9AL.acceptsJ9AL_congr_reg0
