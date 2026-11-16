/-
`DatumOK` is inhabited in-tree, at nock's jetted witness
(`Nock.RedTeam.Batch4775.nvJet_in_regime`; every numeric binder of `DatumOK` comes from it). The only new facts are the union domain
`H = {ω^i : i < 192}` with `ω` = the cell chip's generator (order `3·2^6`): every chip's generator has order `3·2^h`, `h ≤ 6`, so it lies in
the (unique) subgroup of order 192.
-/
import NockvmE2E.J8.InstJ8
import Nock.RedTeam.Batch4775Thm54NVJetRegime

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.J8.InstJ8D

open NockvmE2E.J8.InstJ8
open Nock.RedTeam.Batch4771 Nock.RedTeam.Batch4774 Nock.RedTeam.Batch4775 Nock.V1J8.Check
open Nock.NockVMROM.Thm54.VclL.Handle Nock.Framework

/-- the powers `ω^i`, `i < 192`, of an element of exact order 192 are all the 192-th roots of unity -/
theorem pow_surj_192 (ω x : ZMod P) (hω : orderOf ω = 192) (hx : x ^ 192 = 1) :
    x ∈ (Finset.range 192).image (fun i => ω ^ i) := by
  have hprim : IsPrimitiveRoot ω 192 := (IsPrimitiveRoot.iff_orderOf).mpr hω
  obtain ⟨i, hi, rfl⟩ := hprim.eq_pow_of_pow_eq_one hx
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem pow192_of_ord {q : ChipIn} (ho : OrbOK q) (hh : q.h ≤ 6) : q.ω.toZ ^ 192 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ho.ord]
  exact (mul_dvd_mul_left 3 (pow_dvd_pow 2 hh)).trans (by norm_num)

/-- the generator of the union domain of the witness: the cell chip's -/
theorem rowNodeSet_sub {q : ChipIn} (ho : OrbOK q) (hh : q.h ≤ 6) (ω : ZMod P) (hω : orderOf ω = 192) :
    rowNodeSet (nodesOf q) ⊆ (Finset.range 192).image (fun i => ω ^ i) := by
  intro x hx
  unfold rowNodeSet at hx
  obtain ⟨i, -, rfl⟩ := (@Finset.mem_image _ _ (fun a b => Classical.propDecidable (a = b)) (nodesOf q) Finset.univ x).mp hx
  apply pow_surj_192 ω _ hω
  rw [nodesOf_eq, ← pow_mul, mul_comm, pow_mul, pow192_of_ord ho hh, one_pow]

/-- **`DatumOK` is inhabited**, at nock's jetted witness (`nvJet_in_regime`), with the union domain `{ω_C^i : i < 192}`. -/
theorem datumOK_witness : ∃ d : Datum, DatumOK d := by
  obtain ⟨hv, hA, hJ, hHold, hF, hcK, hpG, hr, hqM, hk, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM, hreg⟩ := nvJet_in_regime
  have hωC : orderOf (mkPb Ijet hv).orbitC.ω = 192 := by
    show orderOf Ijet.C.ω.toZ = 192
    rw [hv.oC.ord]; rfl
  refine ⟨⟨mkPb Ijet hv, RgJ, Ijet.c, EncInjJ8.cornerC, Ijet.g, 192, (mkPb Ijet hv).orbitC.ω⟩, ?_⟩
  refine ⟨hF, hcK, hr, hqM, hk, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM, hreg, ?_, by norm_num⟩
  intro t
  fin_cases t
  · exact rowNodeSet_sub hv.oX (by decide) _ hωC
  · exact rowNodeSet_sub hv.oC (by decide) _ hωC
  · exact rowNodeSet_sub hv.oW (by decide) _ hωC
  · exact rowNodeSet_sub hv.oJ (by decide) _ hωC
  · exact rowNodeSet_sub hv.oA (by decide) _ hωC
  · exact rowNodeSet_sub hv.oV (by decide) _ hωC

end NockvmE2E.J8.InstJ8D

#print axioms NockvmE2E.J8.InstJ8D.datumOK_witness
