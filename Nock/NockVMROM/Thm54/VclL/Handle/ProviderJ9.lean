/-
  Nock/NockVMROM/Thm54/VclL/Handle/ProviderJ9.lean

  J-9 B is a swapped CLAIM COMPONENT, not an appended provider: `claimJ9` replaces `claimJ8`
  (`pubVJ9` for the compute publics, `claimRecsJ9` for the validity term, the J-9 checks `hclI` widened and `hcen'` in
  place of `hclA`/`hcen`), with the SAME `J8providers` and `budgetJ8`.

  * `claimJ9`;
  * `acceptsGeneric_j9_iff`: `AcceptsGeneric (J8providers) claimJ9 budgetJ8 ↔ AcceptsJ9V` at the same binders;
  * `probGeneric_j9_final`: `probJ9B_final_clean` through the iff (same figure `< 2^-155`);
  * `acceptsGeneric_j9_of_accepts`: the `.2` direction, the transport for any non-vacuity witness
.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G
import Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8Iff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ9

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8

noncomputable section

section Inst
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The J-9 B claim component**: `pubVJ9` for the compute publics; `service` as in J-8; `validity` over
`claimRecsJ9`; the checks: the registry statics, `hclI` widened to big-atom positions, `hclR`, `hcen'` (census with
the claim's big atoms, limb length `≤ nA + 2`), `hcellF` (`hclA` is dropped). -/
def claimJ9 : ClaimSpec (K := K) δ where
  pubs := fun c M χ => pubVJ9 δ b c M.m M.ρ M.ρS χ
  verifierTerm := fun β c Pb M χ => match β with
    | .service => ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum
    | .validity => ((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb χ).map fun r => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum
    | _ => 0
  checks := fun Rg c Pb M =>
    staticsJ8 Pb Rg ∧
    (∀ k : Fin 3, (isCellN (claimNoun c k) = true ∨ isBigN p (claimNoun c k) = true) → (M.m k).1 < p) ∧
    (∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p) ∧
    (∀ x ∈ censusGJ9 Pb c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ Pb.nA + 2) ∧
    isCellN c.formula = true

variable {δ b}

/-- **THE J-9 B IFF.**  `AcceptsGeneric` at the J-8 providers and the J-9 B claim is `AcceptsJ9V`, same binders. -/
theorem acceptsGeneric_j9_iff (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ) :
    AcceptsGeneric δ (J8providers δ b) (claimJ9 δ b) budgetJ8 Pb Rg c χ M tr r g ↔
      AcceptsJ9V.AcceptsJ9V δ b Pb Rg c χ M tr r g := by
  constructor
  · intro h
    have hP := h.hprov
    have hX := hP (provX δ b) (by simp [J8providers])
    have hC := hP (provC δ b) (by simp [J8providers])
    have hW := hP (provW δ b) (by simp [J8providers])
    have hJ := hP (provJ δ b) (by simp [J8providers])
    have hA := hP (provA δ b) (by simp [J8providers])
    have hV := hP (provV δ b) (by simp [J8providers])
    have hX' : (provX δ b).chipOK (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb M tr χ := hX.resolve_right id
    have hC' := hC.resolve_right id
    have hW' := hW.resolve_right id
    have hA' := hA.resolve_right id
    obtain ⟨hsatX, hinjX, hadjX⟩ := hX'
    obtain ⟨hsatC, hbindC, hinjC, hadjC, hnpC⟩ := hC'
    obtain ⟨hsatW, hbindW, hinjW, hadjW, hkW, hknW, hkpW⟩ := hW'
    obtain ⟨hsatA, hbindA, hinjA, hadjA, hnpA, hsatL, hbindL⟩ := hA'
    obtain ⟨hstat, hclI, hclR, hcen, hcellF⟩ := h.hclaim
    obtain ⟨hlay, hsmall, huniq, hTpl, hnd, hidx, hrk, hlt⟩ := hstat
    obtain ⟨hnA62, hbud, hbudV⟩ := h.hbud
    have hs1 := h.hsize .rows
    have hs2 := h.hsize .atoms
    simp only [J8providers, provX, provC, provW, provJ, provA, provV, budgetJ8, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at hs1 hs2
    have e1 := h.hbal .export
    have e2 := h.hbal .path
    have e3 := h.hbal .service
    have e4 := h.hbal .validity
    have e5 := h.hbal .atomHandle
    have e6 := h.hbal .atomValidity
    have e7 := h.hbal .fxC
    have e8 := h.hbal .fxA
    simp only [J8providers, provX, provC, provW, provJ, provA, provV, claimJ9, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at e1 e2 e3 e4 e5 e6 e7 e8
    refine
      { hsatX := hsatX, hinjX := hinjX, hadjX := hadjX
        hsatC := hsatC, hbindC := hbindC, hinjC := hinjC, hadjC := hadjC, hnpC := hnpC
        hsatW := hsatW, hbindW := hbindW, hinjW := hinjW, hadjW := hadjW, hkW := hkW, hknW := hknW, hkpW := hkpW
        hJk := hJ
        hsatA := hsatA, hbindA := hbindA, hinjA := hinjA, hadjA := hadjA, hnpA := hnpA
        hVk := hV
        hGx := by linear_combination e1
        hGp := by linear_combination e2
        hGS := by linear_combination e3
        hlay := hlay, hsmall := hsmall, huniq := huniq, hTpl := hTpl, hnd := hnd, hidx := hidx, hrk := hrk
        hlt := hlt
        hsumC' := by linear_combination e4
        hbalA' := by linear_combination e5
        hvalA0 := ?_
        hfxC := ?_
        hfxA := ?_
        hclI := hclI, hclR := hclR, hcen' := hcen
        hlenC := by omega
        hlenA := by omega
        hcellF := hcellF, hnA62 := hnA62, hbud := hbud, hbudV := hbudV
        hsatL := hsatL, hbindL := hbindL }
    · have := (Quad.mk_eq_zero_iff (algebraMap (ZMod p) K δ) _ _).1 (by simpa using e6)
      exact this
    · have h' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 2) (M.pubsC 3) =
          Quad.mk (algebraMap (ZMod p) K δ) (M.pubsW 0) (M.pubsW 1) := by linear_combination e7
      have := Quad.mk_injective (algebraMap (ZMod p) K δ) (a₁ := (M.pubsC 2, M.pubsC 3))
        (a₂ := (M.pubsW 0, M.pubsW 1)) h'
      simpa only [Prod.mk.injEq] using this
    · have h' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA 2) (M.pubsA 3) =
          Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV 0) (M.pubsV 1) := by linear_combination e8
      have := Quad.mk_injective (algebraMap (ZMod p) K δ) (a₁ := (M.pubsA 2, M.pubsA 3))
        (a₂ := (M.pubsV 0, M.pubsV 1)) h'
      simpa only [Prod.mk.injEq] using this
  · intro h
    refine
      { hprov := ?_, hbal := ?_, hclaim := ?_, hsize := ?_, hbud := ?_ }
    · intro P hP
      simp only [J8providers, List.mem_cons, List.mem_nil_iff, or_false] at hP
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨h.hsatX, h.hinjX, h.hadjX⟩
      · exact Or.inl ⟨h.hsatC, h.hbindC, h.hinjC, h.hadjC, h.hnpC⟩
      · exact Or.inl ⟨h.hsatW, h.hbindW, h.hinjW, h.hadjW, h.hkW, h.hknW, h.hkpW⟩
      · exact h.hJk
      · exact Or.inl ⟨h.hsatA, h.hbindA, h.hinjA, h.hadjA, h.hnpA, h.hsatL, h.hbindL⟩
      · exact h.hVk
    · intro β
      cases β <;>
        simp only [J8providers, provX, provC, provW, provJ, provA, provV, claimJ9, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
      · linear_combination h.hGx
      · linear_combination h.hGp
      · linear_combination h.hGS
      · linear_combination h.hsumC'
      · linear_combination h.hbalA'
      · obtain ⟨h0, h1⟩ := h.hvalA0
        have hz := (Quad.mk_eq_zero_iff (algebraMap (ZMod p) K δ) (M.pubsA 0) (M.pubsA 1)).2 ⟨h0, h1⟩
        linear_combination hz
      · obtain ⟨h0, h1⟩ := h.hfxC
        rw [h0, h1]; ring
      · obtain ⟨h0, h1⟩ := h.hfxA
        rw [h0, h1]; ring
    · exact ⟨⟨h.hlay, h.hsmall, h.huniq, h.hTpl, h.hnd, h.hidx, h.hrk, h.hlt⟩, h.hclI, h.hclR, h.hcen',
        h.hcellF⟩
    · intro s
      cases s <;>
        simp only [J8providers, provX, provC, provW, provJ, provA, provV, budgetJ8, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
      · have := h.hlenC; omega
      · have := h.hlenA; omega
    · exact ⟨h.hnA62, h.hbud, h.hbudV⟩

/-- The `.2` direction: any `AcceptsJ9V` witness (e.g. `probJ9B_nonvacuous_demo`'s) is an `AcceptsGeneric` witness. -/
theorem acceptsGeneric_j9_of_accepts (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim)
    (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ)
    (h : AcceptsJ9V.AcceptsJ9V δ b Pb Rg c χ M tr r g) :
    AcceptsGeneric δ (J8providers δ b) (claimJ9 δ b) budgetJ8 Pb Rg c χ M tr r g :=
  (acceptsGeneric_j9_iff Pb Rg c χ M tr r g).2 h

variable [DecidableEq K] {r : RowsJ8} {g : ℕ}

open Classical in
/-- **The J-9 B bound at `AcceptsGeneric J8providers claimJ9`**: `probJ9B_final_clean` through the iff.
Same binders, same figure `< 2^-155`. -/
theorem probGeneric_j9_final [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ8 p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r EncInjJ8.cornerC) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg9 : (censusG Pb c).length + 6 ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsGeneric δ (J8providers δ b) (claimJ9 δ b) budgetJ8 Pb Rg c χ M (Q χ) r g) ∧
          ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  have h := LinkJ9G.probJ9B_final_clean δ b Pb hRg c Q hQ hpG hcK hr hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg9
  have hset : (Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsGeneric δ (J8providers δ b) (claimJ9 δ b) budgetJ8 Pb Rg c χ M (Q χ) r g) ∧
          ¬ Nock.Jet.HoldsN c) =
      (Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ9V.AcceptsJ9V δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c) := by
    refine Finset.filter_congr fun χ _ => ?_
    rw [exists_congr fun M => acceptsGeneric_j9_iff Pb Rg c χ M (Q χ) r g]
  rw [hset]
  exact h

end Inst

end

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ9
#print axioms acceptsGeneric_j9_iff
#print axioms acceptsGeneric_j9_of_accepts
#print axioms probGeneric_j9_final
end Axioms

end Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ9
