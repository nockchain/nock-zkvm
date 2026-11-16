/-
  **Row-budget monotonicity of `AcceptsJ8V`, and the witnesses restated at the census corner.**
  `r` and `g` enter `AcceptsJ8V` ONLY through `hbud : BudJ8 Pb r (g + r.N)` and
  `hbudV : Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW` (every field an upper bound), so a larger
  budget keeps it: `acceptsJ8V_mono_rows`.  The jetted witness is thereby restated at
  `r' = EncInjJ8.cornerC`, where `hr : RowsLe r' cornerC` and `hk : 2 * fuelChip ≤ r'.leaves` of `probJ8V_final` hold.
-/
import Nock.RedTeam.Batch4774Thm54NVJetFinal
import Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8
import Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch4775

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe corner31)
open Nock.Atoms (lenL)
open Nock.RedTeam.Batch4771 Nock.RedTeam.Batch4774 Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.TraceGenExe

section Mono
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`AcceptsJ8V` is monotone in the row budget and `g`.** -/
theorem acceptsJ8V_mono_rows {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r r' : RowsJ8} {g g' : ℕ}
    (h : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hN : r.N ≤ r'.N) (hD : r.D ≤ r'.D) (hW : r.W ≤ r'.W) (hJ : r.J ≤ r'.J) (hcalls : r.calls ≤ r'.calls)
    (hheads : r.heads ≤ r'.heads) (hblocks : r.blocks ≤ r'.blocks) (hrd : r.rd ≤ r'.rd) (hmb : r.mb ≤ r'.mb)
    (hA : r.A ≤ r'.A) (hAW : r.AW ≤ r'.AW) (hg : g ≤ g') :
    AcceptsJ8V δ b Pb Rg c χ M tr r' g' := by
  have hb := h.hbud
  have hv := h.hbudV
  exact { h with
    hbud := ⟨by have := hb.x1; omega, by have := hb.x2; omega, by have := hb.p1; omega, by have := hb.p2; omega,
      by have := hb.s1; omega, by have := hb.s2; omega⟩
    hbudV := ⟨by have := hv.1; omega, by have := hv.2.1; omega, by have := hv.2.2.1; omega,
      by have := hv.2.2.2; omega⟩ }

end Mono

/-- **The jetted witness inside `probJ8V_final`'s regime.**  At `r := EncInjJ8.cornerC`, `g := Ijet.g` (concrete
Goldilocks instance `deltaF`/`powerBasis3` of the generic `K,δ,b`): `AcceptsJ8V` holds with the J chip present, the claim
true and the registry faithful, and every numeric binder of `probJ8V_final` holds: `card K = cK`, `p = Atoms.p`,
`RowsLe r cornerC`, `hqM`, `hk`, `hmax`, `hg`, `hLC hLM hLW hLA hLV`, `hnM`, `hreg`.
NOT discharged (not one-coin facts): `hQ : StJ8 Q` (the coin-to-trace map `Q`), the `[CharP K p] [CharP 𝕂′ p]`
instances at this field, and the probabilistic conclusion itself. -/
theorem nvJet_in_regime : ∃ hv : ValidJ8 Ijet,
    Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V.AcceptsJ8V deltaF powerBasis3 (mkPb Ijet hv) RgJ Ijet.c
      (toχ Ijet.χ) Ijet.M.toMsg (mkTr Ijet) EncInjJ8.cornerC Ijet.g ∧
    0 < (mkPb Ijet hv).nJ ∧ Nock.Jet.HoldsN Ijet.c ∧ RgJ.Faithful ∧
    Fintype.card KC = Nock.NockVMROM.Thm54.VclL.Events.cK ∧ Nock.Field.p = Nock.Atoms.p ∧
    RowsLe EncInjJ8.cornerC EncInjJ8.cornerC ∧
    (∀ x < ringChar (ZMod Nock.Field.p), lenL x ≤ EncInjJ8.cornerC.maxlen) ∧
    2 * fuelChip ≤ EncInjJ8.cornerC.leaves ∧
    (mkPb Ijet hv).nA + 2 ≤ EncInjJ8.cornerC.maxlen ∧ Ijet.g ≤ 2 ^ 31 ∧
    (mkPb Ijet hv).n ≤ EncInjJ8.cornerC.N ∧ (mkPb Ijet hv).nC ≤ EncInjJ8.cornerC.D ∧
    (mkPb Ijet hv).nW ≤ EncInjJ8.cornerC.W ∧ (mkPb Ijet hv).nA ≤ EncInjJ8.cornerC.A ∧
    (mkPb Ijet hv).nV ≤ EncInjJ8.cornerC.AW ∧ (mkPb Ijet hv).nC ≤ 2 ^ 31 ∧
    (censusG (mkPb Ijet hv) Ijet.c).length ≤ 2 ^ 31 := by
  obtain ⟨hv, hA, hJ, -, hH, hF⟩ := nvJet_goldilocks
  have hrc : ringChar (ZMod Nock.Field.p) = Nock.Field.p := ZMod.ringChar_zmod_n _
  have hpG : Nock.Field.p = Nock.Atoms.p := rfl
  have hbig : ∀ n : ℕ, n ≤ 2 ^ 31 → n ≤ EncInjJ8.cornerC.N := fun n h => h
  refine ⟨hv, ?_, hJ, hH, hF, by rw [Nock.TraceGenExe.KC_card, Nock.NockVMROM.Thm54.VclL.Events.cK_eq], hpG, ?_, ?_,
    le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine acceptsJ8V_mono_rows deltaF powerBasis3 hA ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (first | decide +kernel | (unfold EncInjJ8.cornerC corner31; decide +kernel))
  · simp [RowsLe]
  · intro x hx
    rw [hrc] at hx
    unfold lenL
    rw [if_pos hx]
    show 1 ≤ 2 ^ 31
    norm_num
  all_goals ((try simp only [mkPb, censusG]); first | decide +kernel | (unfold EncInjJ8.cornerC corner31; decide +kernel))


section Inhab
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Static
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8MemMain Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **The no-jet inhabitant inside `probJ8V_final`'s regime** (generic `K,δ,b`; `hpG : p = Atoms.p`, `card K = cK`):
`InhabJ8Main.inhabitant_goldilocks` restated at `r := EncInjJ8.cornerC` (by `acceptsJ8V_mono_rows`; the original sits at
`rJ0`, `Λ = 10`, outside `RowsLe r cornerC`), with the numeric binders of `probJ8V_final` for its public data `PbJ`.
NOT discharged (not one-coin facts): `hQ : StJ8 Q`, the `[CharP K p] [CharP 𝕂′ p]` instances, the probabilistic conclusion. -/
theorem inhabitant_in_regime (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = Nock.NockVMROM.Thm54.VclL.Events.cK)
    (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    ∃ (hdvd : 3 * 2 ^ 1 ∣ p - 1) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (g : ℕ),
      AcceptsJ8V δ b (PbJ hdvd Rt) R0 c0 χ M tr EncInjJ8.cornerC g ∧ (PbJ hdvd Rt).krootsV = 0 ∧
      (PbJ hdvd Rt).nJ = 0 ∧ Nock.Jet.HoldsN c0 ∧
      Fintype.card K = Nock.NockVMROM.Thm54.VclL.Events.cK ∧
      RowsLe EncInjJ8.cornerC EncInjJ8.cornerC ∧
      (∀ x < ringChar (ZMod p), lenL x ≤ EncInjJ8.cornerC.maxlen) ∧
      2 * fuelChip ≤ EncInjJ8.cornerC.leaves ∧ (PbJ hdvd Rt).nA + 2 ≤ EncInjJ8.cornerC.maxlen ∧ g ≤ 2 ^ 31 ∧
      (PbJ hdvd Rt).n ≤ EncInjJ8.cornerC.N ∧ (PbJ hdvd Rt).nC ≤ EncInjJ8.cornerC.D ∧
      (PbJ hdvd Rt).nW ≤ EncInjJ8.cornerC.W ∧ (PbJ hdvd Rt).nA ≤ EncInjJ8.cornerC.A ∧
      (PbJ hdvd Rt).nV ≤ EncInjJ8.cornerC.AW ∧ (PbJ hdvd Rt).nC ≤ 2 ^ 31 ∧
      (censusG (PbJ hdvd Rt) c0).length ≤ 2 ^ 31 := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  haveI : Fact (ringChar (ZMod p)).Prime := ⟨by rw [hrc]; exact Fact.out⟩
  haveI : Algebra (ZMod (ringChar (ZMod p))) K :=
    @Eq.rec ℕ p (fun q _ => Algebra (ZMod q) K) ‹Algebra (ZMod p) K› _ hrc.symm
  have hB : Nock.Atoms.B ≤ p := by
    rw [hpG, show Nock.Atoms.B = 2 ^ 32 from rfl, show Nock.Atoms.p = Nock.Field.p from rfl, Nock.Field.p_eq]
    norm_num
  have hdvd : 3 * 2 ^ 1 ∣ p - 1 := by
    rw [hpG, show Nock.Atoms.p = Nock.Field.p from rfl, Nock.Field.p_eq, Nat.dvd_iff_mod_eq_zero]
    norm_num
  refine ⟨hdvd, χ0, MJ0 δ b χ0, trJ0 δ b hdvd Rt χ0, 0, ?_, rfl, rfl, ⟨1, evalN0⟩, hcK, ?_, ?_, le_refl _, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine acceptsJ8V_mono_rows δ b (inhabitant δ b hB hdvd Rt) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (first | decide +kernel | (unfold EncInjJ8.cornerC corner31 rJ0; decide +kernel))
  · simp [RowsLe]
  · intro x hx
    rw [hrc] at hx
    unfold lenL
    rw [hpG] at hx
    rw [if_pos hx]
    show 1 ≤ 2 ^ 31
    norm_num
  all_goals first
    | (norm_num [PbJ, PbBase, withMem, EncInjJ8.cornerC, corner31]; done)
    | (simp only [censusG, PbJ, PbBase, withMem, List.map_nil, List.nil_append, List.length_map]
       first | (decide +kernel) | (simp [Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P.claimCells]; done))

end Inhab

end Nock.RedTeam.Batch4775

#print axioms Nock.RedTeam.Batch4775.acceptsJ8V_mono_rows
#print axioms Nock.RedTeam.Batch4775.nvJet_in_regime
#print axioms Nock.RedTeam.Batch4775.inhabitant_in_regime
