/-
  Non-vacuity of `AcceptsJ9V` at Goldilocks, for a claim with a big atom.
  The demo claim
  `c9 := *[[(p+5) 0] [0 2]] = p+5` (`p` Goldilocks) has the big result `p + 5 ≥ p` (`claimBigs p c9 = [2]`, the
  kind-2 handle `(2, 0)` at atom-table row 0) — a claim `AcceptsJ8V` rejects (`hclA`).
  * `nv9_goldilocks` via **`checkJ9_iff`**: `AcceptsJ9V deltaF powerBasis3 (mkPb I9 hv) Rg0 c9 …` with `HoldsN c9`
    (kernel `evalN`), the empty registry `Rg0` (faithful);
  * `acceptsJ9V_mono_rows` (`r`, `g` enter only through `hbud` / `hbudV`), and the restatement at
    `r' = EncInjJ8.cornerC`: `nv9_in_regime` with the numeric binders of `LinkJ9G.probJ9B_final_clean`;
  * **`probJ9B_nonvacuous_demo`** (the headline, existential form) and `nv9_hyps_final_clean` (the witness conjoined
    with `probJ9B_final_clean`'s conclusion at it).
  Taken as hypotheses, not proved here (they are not one-coin facts; arguments of `nv9_hyps_final_clean`): `hQ : StJ8 Q` (the coin-to-trace
  map), the instances `[CharP KC p] [CharP 𝕂′ p]`; and the probabilistic conclusion is a statement about all coins, not
  about this witness.
-/
import Nock.RedTeam.Batch4811Thm54J9bNVParts
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch4812

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8' censusG)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 (RowsLe corner31)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V (AcceptsJ9V)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (claimBigs)
open Nock.Atoms (lenL)
open Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J9 Nock.V1J9.Exe9 Nock.V1J9.Check9
open Nock.RedTeam.Batch4810 Nock.RedTeam.Batch4811

/-! ## 1. `checkJ9 I9 = true` and the witness at Goldilocks -/

theorem i9_check : checkJ9 I9 = true := by
  unfold checkJ9
  rw [dif_pos i9_valid]
  simp only [Bool.and_eq_true]
  refine ⟨⟨i9_static, i9_pub⟩, ?_⟩
  unfold chipsB9
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨i9_X, i9_C⟩, i9_W⟩, i9_J⟩, i9_A⟩, i9_AW⟩, i9_AL⟩

/-- The empty registry (the demo calls no jet). -/
abbrev Rg0 : Nock.Jet.Registry := fun _ => none

/-- The input `I9` satisfies the registry condition `RegOK` for the empty registry `Rg0` (the input calls no jet). -/
theorem i9_regOK : RegOK I9 Rg0 := by
  intro i hi
  exact absurd hi (by simp [I9])

/-- The empty registry `Rg0` is faithful (it registers no jet). -/
theorem rg0_faithful : Rg0.Faithful := by
  intro n j h
  cases h

/-- **The claim is true**: `*[[(p+5) 0] [0 2]] = p+5` (kernel `evalN`). -/
theorem c9_holdsN : Nock.Jet.HoldsN c9 := ⟨1000, by decide +kernel⟩

/-- **The J-9 demo witness at Goldilocks**: the honest input is valid and accepted by `AcceptsJ9V` (verifier data,
coins, message, traces, rows and budget all built from the input), the claim is true, and its result is a big atom. -/
theorem nv9_goldilocks : ∃ hv : ValidJ8 I9,
    AcceptsJ9V deltaF powerBasis3 (mkPb I9 hv) Rg0 c9 (toχ I9.χ) I9.M.toMsg (mkTr I9) I9.r I9.g ∧
      Nock.Jet.HoldsN c9 ∧ claimBigs Nock.Field.p c9 = [2] ∧ Rg0.Faithful := by
  haveI : Fact (ringChar (ZMod Nock.Field.p)).Prime := ⟨by rw [ZMod.ringChar_zmod_n]; exact Fact.out⟩
  haveI hcp : CharP KC (ringChar (ZMod Nock.Field.p)) := by
    rw [ZMod.ringChar_zmod_n]; exact charP_of_injective_algebraMap (algebraMap (ZMod Nock.Field.p) KC).injective _
  letI : Algebra (ZMod (ringChar (ZMod Nock.Field.p))) KC := ZMod.algebra KC _
  obtain ⟨hv, h⟩ := (checkJ9_iff I9 Rg0 i9_regOK).mp i9_check
  exact ⟨hv, h, c9_holdsN, c9_bigs, rg0_faithful⟩

/-! ## 2. Row-budget monotonicity and the census corner -/

section Mono
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **`AcceptsJ9V` is monotone in the row budget and `g`** (they enter only through `hbud` and `hbudV`). -/
theorem acceptsJ9V_mono_rows {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r r' : RowsJ8} {g g' : ℕ}
    (h : AcceptsJ9V δ b Pb Rg c χ M tr r g)
    (hN : r.N ≤ r'.N) (hD : r.D ≤ r'.D) (hW : r.W ≤ r'.W) (hJ : r.J ≤ r'.J) (hcalls : r.calls ≤ r'.calls)
    (hheads : r.heads ≤ r'.heads) (hblocks : r.blocks ≤ r'.blocks) (hrd : r.rd ≤ r'.rd) (hmb : r.mb ≤ r'.mb)
    (hA : r.A ≤ r'.A) (hAW : r.AW ≤ r'.AW) (hg : g ≤ g') :
    AcceptsJ9V δ b Pb Rg c χ M tr r' g' := by
  have hb := h.hbud
  have hv := h.hbudV
  exact { h with
    hbud := ⟨by have := hb.x1; omega, by have := hb.x2; omega, by have := hb.p1; omega, by have := hb.p2; omega,
      by have := hb.s1; omega, by have := hb.s2; omega⟩
    hbudV := ⟨by have := hv.1; omega, by have := hv.2.1; omega, by have := hv.2.2.1; omega,
      by have := hv.2.2.2; omega⟩ }

end Mono

/-- **The J-9 demo witness inside `probJ9B_final_clean`'s regime.**  At `r := EncInjJ8.cornerC`, `g := I9.g`
(concrete Goldilocks instance `deltaF` / `powerBasis3` of the generic `K, δ, b`): `AcceptsJ9V` holds at the big-atom
claim `c9`, the claim is true, the registry faithful, and every numeric binder of `probJ9B_final_clean` holds:
`hpG`, `hcK`, `hr`, `hqM`, `hk`, `hmax`, `hg`, `hLC hLM hLW hLA hLV`, `hnM`, `hreg9`.
Not proved here: `hQ : StJ8 Q`, the `[CharP K p] [CharP 𝕂′ p]` instances, the probabilistic conclusion itself. -/
theorem nv9_in_regime : ∃ hv : ValidJ8 I9,
    AcceptsJ9V deltaF powerBasis3 (mkPb I9 hv) Rg0 c9 (toχ I9.χ) I9.M.toMsg (mkTr I9) EncInjJ8.cornerC I9.g ∧
    Nock.Jet.HoldsN c9 ∧ claimBigs Nock.Field.p c9 = [2] ∧ Rg0.Faithful ∧
    Nock.Field.p = Nock.Atoms.p ∧ Fintype.card KC = Nock.NockVMROM.Thm54.VclL.Events.cK ∧
    RowsLe EncInjJ8.cornerC EncInjJ8.cornerC ∧
    (∀ x < ringChar (ZMod Nock.Field.p), lenL x ≤ EncInjJ8.cornerC.maxlen) ∧
    2 * fuelChip ≤ EncInjJ8.cornerC.leaves ∧
    (mkPb I9 hv).nA + 2 ≤ EncInjJ8.cornerC.maxlen ∧ I9.g ≤ 2 ^ 31 ∧
    (mkPb I9 hv).n ≤ EncInjJ8.cornerC.N ∧ (mkPb I9 hv).nC ≤ EncInjJ8.cornerC.D ∧
    (mkPb I9 hv).nW ≤ EncInjJ8.cornerC.W ∧ (mkPb I9 hv).nA ≤ EncInjJ8.cornerC.A ∧
    (mkPb I9 hv).nV ≤ EncInjJ8.cornerC.AW ∧ (mkPb I9 hv).nC ≤ 2 ^ 31 ∧
    (censusG (mkPb I9 hv) c9).length + 6 ≤ 2 ^ 31 := by
  haveI : Fact (ringChar (ZMod Nock.Field.p)).Prime := ⟨by rw [ZMod.ringChar_zmod_n]; exact Fact.out⟩
  haveI hcp : CharP KC (ringChar (ZMod Nock.Field.p)) := by
    rw [ZMod.ringChar_zmod_n]; exact charP_of_injective_algebraMap (algebraMap (ZMod Nock.Field.p) KC).injective _
  letI : Algebra (ZMod (ringChar (ZMod Nock.Field.p))) KC := ZMod.algebra KC _
  obtain ⟨hv, hA, hH, hB, hF⟩ := nv9_goldilocks
  have hrc : ringChar (ZMod Nock.Field.p) = Nock.Field.p := ZMod.ringChar_zmod_n _
  refine ⟨hv, ?_, hH, hB, hF, rfl, by rw [Nock.TraceGenExe.KC_card, Nock.NockVMROM.Thm54.VclL.Events.cK_eq], ?_, ?_,
    le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine acceptsJ9V_mono_rows deltaF powerBasis3 hA ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (first | decide +kernel | (unfold EncInjJ8.cornerC corner31; decide +kernel))
  · simp [RowsLe]
  · intro x hx
    rw [hrc] at hx
    unfold lenL
    rw [if_pos hx]
    show 1 ≤ 2 ^ 31
    norm_num
  all_goals ((try simp only [mkPb, censusG]); first | decide +kernel | (unfold EncInjJ8.cornerC corner31; decide +kernel))

/-! ## 3. The headline, in `probJ9B_final_clean`'s context -/

/-- **`probJ9B_nonvacuous_demo`: `AcceptsJ9V` is satisfiable at a claim with a big atom.**  At Goldilocks
(`K = KC`, `δ = deltaF`, `b = powerBasis3`), for the claim `c9 = *[[(p+5) 0] [0 2]] = p+5`, there are public data
`Pb`, coins `χ`, a message `M`, traces `tr` and `g` with `AcceptsJ9V … Pb Rg0 c9 χ M tr cornerC g`; the claim is true;
its big positions are `[2]` (the result); and the numeric binders of `probJ9B_final_clean` hold at `Pb`, `cornerC`,
`g` (`hmax hg hLC hLM hLW hLA hLV hnM hreg9`; `hpG hcK hr hqM hk` are `Pb`-free and in `nv9_in_regime`). -/
theorem probJ9B_nonvacuous_demo : ∃ (Pb : PubJ8 Nock.Field.p) (χ : Coins frameJ8 KC) (M : MsgJ8' Nock.Field.p KC deltaF)
    (tr : TrJ8 (ZMod Nock.Field.p)) (g : ℕ),
    AcceptsJ9V deltaF powerBasis3 Pb Rg0 c9 χ M tr EncInjJ8.cornerC g ∧ Nock.Jet.HoldsN c9 ∧
      claimBigs Nock.Field.p c9 = [2] ∧
      Pb.nA + 2 ≤ EncInjJ8.cornerC.maxlen ∧ g ≤ 2 ^ 31 ∧ Pb.n ≤ EncInjJ8.cornerC.N ∧ Pb.nC ≤ EncInjJ8.cornerC.D ∧
      Pb.nW ≤ EncInjJ8.cornerC.W ∧ Pb.nA ≤ EncInjJ8.cornerC.A ∧ Pb.nV ≤ EncInjJ8.cornerC.AW ∧ Pb.nC ≤ 2 ^ 31 ∧
      (censusG Pb c9).length + 6 ≤ 2 ^ 31 := by
  obtain ⟨hv, hA, hH, hB, -, -, -, -, -, -, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM, hreg⟩ := nv9_in_regime
  exact ⟨mkPb I9 hv, toχ I9.χ, I9.M.toMsg, mkTr I9, I9.g, hA, hH, hB, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM, hreg⟩

open Classical in
/-- **`nv9_hyps_final_clean`**: the witness conjoined with the conclusion of `probJ9B_final_clean` at `K := KC`,
`δ := deltaF`, `b := powerBasis3`, `Pb := mkPb I9 hv`, `Rg := Rg0`, `c := c9`, `r := cornerC`, `g := I9.g`: every
numeric hypothesis is proved here.  Taken as arguments: `hQ : StJ8 Q`, and the instances
`[CharP KC p] [CharP 𝕂′ p]`. -/
theorem nv9_hyps_final_clean [CharP KC Nock.Field.p]
    [CharP (Quad (algebraMap (ZMod Nock.Field.p) KC deltaF)) Nock.Field.p]
    (Q : Coins frameJ8 KC → TrJ8 (ZMod Nock.Field.p)) (hQ : StJ8 Q) :
    ∃ hv : ValidJ8 I9,
      AcceptsJ9V deltaF powerBasis3 (mkPb I9 hv) Rg0 c9 (toχ I9.χ) I9.M.toMsg (mkTr I9) EncInjJ8.cornerC I9.g ∧
      ((Finset.univ.filter fun χ : Coins frameJ8 KC =>
        (∃ M : MsgJ8' Nock.Field.p KC deltaF, AcceptsJ9V deltaF powerBasis3
          (mkPb I9 hv) Rg0 c9 χ M (Q χ) EncInjJ8.cornerC I9.g) ∧ ¬ Nock.Jet.HoldsN c9).card : ℚ) /
        Fintype.card (Coins frameJ8 KC) < 1 / (2 : ℚ) ^ 155 := by
  obtain ⟨hv, hA, hH, hB, hF, hpG, hcK, hr, hqM, hk, hmax, hg, hLC, hLM, hLW, hLA, hLV, hnM, hreg⟩ := nv9_in_regime
  exact ⟨hv, hA, Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G.probJ9B_final_clean deltaF powerBasis3 (mkPb I9 hv) hF
    c9 Q hQ hpG hcK hr hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg⟩

end Nock.RedTeam.Batch4812

#print axioms Nock.RedTeam.Batch4812.i9_check
#print axioms Nock.RedTeam.Batch4812.nv9_goldilocks
#print axioms Nock.RedTeam.Batch4812.acceptsJ9V_mono_rows
#print axioms Nock.RedTeam.Batch4812.nv9_in_regime
#print axioms Nock.RedTeam.Batch4812.probJ9B_nonvacuous_demo
#print axioms Nock.RedTeam.Batch4812.nv9_hyps_final_clean
#print axioms Nock.V1J9.Check9.checkJ9_iff
