/-
NockvmE2E/Z38/AccCongJ9ALJ.lean: the template-jet twin of `acceptsJ9AL_congr_reg0` (J9AL/AccCongJ9AL.lean).
`AcceptsJ9AL` reads the template / index / rank functions of the public parameters only at the registered ids `Pb.regs` (and `Rt` also at the call ids `Pb.ids`, through `layoutJ8`).
So `Rt`, `idx`, `rk` may be replaced by functions that agree with them on `regs` (`Rt`: on `regs ++ ids`).  This is needed because nock's generator records the real `idxOf` / `rkC` / `rtP`
of the run, whereas the datum `DX9LJ` carries `catJ.toCR.Rt`, `idxOfPub`, `rkOfPub`.  Not zero-knowledge.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Z38.AccCongJ9ALJ

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (pinRecsJ8 censusG)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.ChipJ8 (layoutJ8 blocks)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (censusGJ9)
open Module Polynomial

/-- `blocks` reads the template function only at the call ids -/
theorem blocks_congr (R R' : ℕ → Nock.Jet.Autogen.Tpl) :
    ∀ (ids : List ℕ) (c0 : ℕ), (∀ i ∈ ids, R' i = R i) → blocks R' c0 ids = blocks R c0 ids
  | [], _, _ => rfl
  | j :: is, c0, h => by
    have hj := h j (List.mem_cons_self)
    have hb : Nock.Jet.ChipJ8.blockPre R' c0 j = Nock.Jet.ChipJ8.blockPre R c0 j := by
      simp only [Nock.Jet.ChipJ8.blockPre, Nock.Jet.ChipJ8.callPre, hj]
    simp only [blocks]
    rw [hb, blocks_congr R R' is (c0 + 1) (fun i hi => h i (List.mem_cons_of_mem _ hi))]

theorem layoutJ8_congr (R R' : ℕ → Nock.Jet.Autogen.Tpl) (regs ids : List ℕ) (h : ∀ i ∈ ids, R' i = R i) :
    layoutJ8 R' regs ids = layoutJ8 R regs ids := by
  unfold layoutJ8
  rw [blocks_congr R R' ids 0 h]

section Cong
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

theorem acceptsJ9AL_congr_regs {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : SVFrame.Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g : ℕ}
    (Rt' : ℕ → Nock.Jet.Autogen.Tpl) (idx' : ℕ → ℕ) (rk' : ℕ → ℕ × ℕ) (idxP' : ℕ → ℕ) (rkP' : ℕ → ℕ × ℕ)
    (hRtR : ∀ i ∈ Pb.regs, Rt' i = Pb.Rt i) (hRtI : ∀ i ∈ Pb.ids, Rt' i = Pb.Rt i)
    (hix : ∀ i ∈ Pb.regs, idx' i = Pb.idx i) (hrk : ∀ i ∈ Pb.regs, rk' i = Pb.rk i)
    (hiP : ∀ q ∈ Pb.prims, idxP' q.1 = Pb.idxP q.1) (hrP : ∀ q ∈ Pb.prims, rkP' q.1 = Pb.rkP q.1)
    (h : AcceptsJ9AL.AcceptsJ9AL δ b Pb Rg c χ M tr r g) :
    AcceptsJ9AL.AcceptsJ9AL δ b { Pb with Rt := Rt', idx := idx', rk := rk', idxP := idxP', rkP := rkP' } Rg c χ M tr r g := by
  generalize hP' : ({ Pb with Rt := Rt', idx := idx', rk := rk', idxP := idxP', rkP := rkP' } : PubJ9AL p) = Pb'
  have hreg : Pb'.regs = Pb.regs := by rw [← hP']
  have hids : Pb'.ids = Pb.ids := by rw [← hP']
  have e0 : pinCons (p := p) (K := K) Pb'.regs Pb'.idx = pinCons (p := p) (K := K) Pb.regs Pb.idx := by
    rw [← hP']
    unfold pinCons
    exact List.map_congr_left (fun id hid => by simp only [hix id hid])
  have e1 : AcceptsJ9AL.pinRgP (K := K) Pb' = AcceptsJ9AL.pinRgP (K := K) Pb := by
    rw [← hP']
    unfold AcceptsJ9AL.pinRgP
    exact List.map_congr_left (fun q hq => by simp only [hiP q hq])
  have e2 : AcceptsJ9AL.pinOpP (K := K) Pb' = AcceptsJ9AL.pinOpP (K := K) Pb := by rw [← hP']; rfl
  have e3 : pinRecsJ8 δ Pb'.toPubJ8 χ = pinRecsJ8 δ Pb.toPubJ8 χ := by
    rw [← hP']
    unfold pinRecsJ8
    exact List.map_congr_left (fun id hid => by simp only [hRtR id hid, hix id hid, hrk id hid])
  have e5 : censusGJ9 Pb'.toPubJ8 c = censusGJ9 Pb.toPubJ8 c := by
    rw [← hP']
    unfold censusGJ9 censusG
    congr 2
    exact List.map_congr_left (fun id hid => by simp only [hRtR id hid])
  have e6 : AcceptsJ9AL.censusP Pb' = AcceptsJ9AL.censusP Pb := by rw [← hP']; rfl
  have e7 : AcceptsJ9AL.pinRecsP δ Pb' χ = AcceptsJ9AL.pinRecsP δ Pb χ := by
    rw [← hP']
    unfold AcceptsJ9AL.pinRecsP
    exact List.map_congr_left (fun q hq => by simp only [hiP q hq, hrP q hq])
  have hlayJ : layoutJ8 Pb'.Rt Pb'.regs Pb'.ids = layoutJ8 Pb.Rt Pb.regs Pb.ids := by
    rw [hreg, hids]
    have : Pb'.Rt = Rt' := by rw [← hP']
    rw [this]
    exact layoutJ8_congr Pb.Rt Rt' _ _ hRtI
  have hip : ∀ q ∈ Pb'.prims, Pb'.idxP q.1 = Pb.idxP q.1 := by rw [← hP']; exact hiP
  have hrp : ∀ q ∈ Pb'.prims, Pb'.rkP q.1 = Pb.rkP q.1 := by rw [← hP']; exact hrP
  have hpr : Pb'.prims = Pb.prims := by rw [← hP']
  have hRt' : Pb'.Rt = Rt' := by rw [← hP']
  have hidx' : Pb'.idx = idx' := by rw [← hP']
  have hrk' : Pb'.rk = rk' := by rw [← hP']
  subst hP'
  refine { h with hbud := ⟨h.hbud.x1, h.hbud.x2, h.hbud.p1, h.hbud.p2, h.hbud.s1, h.hbud.s2⟩, hGS := ?_, hlay := ?_, hsmall := ?_, huniq := ?_, hTpl := ?_, hidx := ?_, hrk := ?_, hlt := ?_, hsumC' := ?_, hcen' := ?_, hlenL := ?_, hrkP := ?_, hltP := ?_ }
  · have h1 := h.hGS
    show _ = _
    rw [e0, e1, e2]
    exact h1
  · have h1 := h.hlay
    show List.ofFn Pb.lay = layoutJ8 Rt' Pb.regs Pb.ids
    rw [← hRt', hlayJ]
    exact h1
  · have h1 := h.hsmall
    show ∀ q ∈ layoutJ8 Rt' Pb.regs Pb.ids, _
    rw [← hRt', hlayJ]
    exact h1
  · have h1 := h.huniq
    show ((layoutJ8 Rt' Pb.regs Pb.ids).filterMap _).Nodup
    rw [← hRt', hlayJ]
    exact h1
  · intro i hi
    have h1 := h.hTpl i hi
    show Rg i = some ⟨(Rt' i).toTemplate p, Nock.Jet.Autogen.compile p (Rt' i)⟩ ∧ Nock.Jet.ChipJ8.axPosB (Rt' i) = true ∧ (Rt' i).WellTyped p
    rw [hRtR i hi]
    exact h1
  · intro i hi
    have h1 := h.hidx i hi
    show idx' i < p
    rw [hix i hi]; exact h1
  · intro i hi
    have h1 := h.hrk i hi
    show rk' i ≠ (0, 0)
    rw [hrk i hi]; exact h1
  · intro i hi
    have h1 := h.hlt i hi
    show (rk' i).1 < ringChar (ZMod p) ∧ (rk' i).2 < ringChar (ZMod p) ∧ idx' i < ringChar (ZMod p)
    rw [hrk i hi, hix i hi]; exact h1
  · have h1 := h.hsumC'
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

end NockvmE2E.Z38.AccCongJ9ALJ

#print axioms NockvmE2E.Z38.AccCongJ9ALJ.acceptsJ9AL_congr_regs
