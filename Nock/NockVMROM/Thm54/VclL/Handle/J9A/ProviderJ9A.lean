/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ProviderJ9A.lean

`acceptsGeneric_j9a_iff`: `AcceptsGenericG providersJ9A claimJ9A budJ9A` is `AcceptsJ9A` at the same binders.

  **Field grouping (every one of the 52 fields of `AcceptsJ9A` exactly once; count at the end).**
  * `hprov` (one entry per provider; a conjunct bundle in the provider's `chipOK`, its ABSENT case in `absentOK`):
    - compute (`provXA`, `computeChipVCLHX9`, `qX9` at the claim's compute publics `pubVJ9`): `hsatX hinjX hadjX` (3);
    - cell (`J-8 provC` read at `toPubJ8 / toJ8`): `hsatC hbindC hinjC hadjC hnpC` (5);
    - walk (`provW`): `hsatW hbindW hinjW hadjW hkW hknW hkpW` (7);
    - J (`provJ`): `hJk` (1; its present / absent disjuncts are `chipOK` / `absentOK`);
    - atom (`provA`): `hsatA hbindA hinjA hadjA hnpA hsatL hbindL` (7);
    - atom walk (`provV`): `hVk` (1; present / absent);
    - axis (`provAX`): `hAXk` (1; `AXChipOK`'s present disjunct is `chipOK`, its absent disjunct `absentOK`);
    - split (`provSP`): `hSPk` (1; `SPChipOK`, same).
  * `hbal` (the eight balance classes of `ProviderJ8.Bal`): `hGx hGp hGS hsumC' hbalA' hvalA0 hfxC hfxA` (8); the axis
    chip contributes `+pubAXp` to `path` and `+pubAXs` to `service`, the split chip `-pubSPs` to `service`; the
    verifier terms (pin consumes, claim and pin records) are in `claimJ9A`.
  * `hclaim` (`claimJ9A.checks` = the J-9 B claim checks at `toPubJ8 / toMsgJ8'`): `hlay hsmall huniq hTpl hnd hidx hrk
    hlt hclI hclR hcen' hcellF` (12).
  * `hsize` (the two size classes): `hlenC hlenA` (2); the axis and split providers have size `0`.
  * `hbud` (`budJ9A.ok`): `hnAS hbud hbudV hlenX` (4; `hlenX` has no balance or size home: it is two independent
    inequalities, so it rides with the budget, as `hnA62` does at J-8).
  Count: hprov 3 + 5 + 7 + 1 + 7 + 1 + 1 + 1 = 26, hbal 8, hclaim 12, hsize 2, hbud 4: 26 + 8 + 12 + 2 + 4 = 52 =
  the 52 fields of `AcceptsJ9A` (hsatL/hbindL are in the atom provider's 7).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ9
import Nock.NockVMROM.Thm54.VclL.Handle.ProviderG

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ9A

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AXChipOK SPChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8 (Bal SizeClass provC provW provJ provA provV staticsJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProviderG

noncomputable section

section Inst
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- A J-8 provider read through `toPubJ8 / toMsgJ8' / toJ8`. -/
def liftJ9A (P : ProviderJ8.Provider (K := K) δ) :
    ProviderG (K := K) δ (PubJ9A p) (MsgJ9A' p K δ) (TrJ9A (ZMod p)) (Coins frameJ8 K) where
  chipOK := fun pv Pb M tr χ => P.chipOK pv Pb.toPubJ8 M.toMsgJ8' tr.toJ8 χ
  absentOK := fun Pb M => P.absentOK Pb.toPubJ8 M.toMsgJ8'
  term := fun β Pb M => P.term β Pb.toPubJ8 M.toMsgJ8'
  size := fun s Pb => P.size s Pb.toPubJ8

/-- The compute provider (mandatory), swapped to the twin RAP `computeChipVCLHX9` at the claim's `pubVJ9`. -/
def provXA : ProviderG (K := K) δ (PubJ9A p) (MsgJ9A' p K δ) (TrJ9A (ZMod p)) (Coins frameJ8 K) where
  chipOK := fun pv Pb M tr χ =>
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ (chalVJ8 b χ) pv Pb.orbit)
        (qX9 δ b Pb tr (chalVJ8 b χ) pv) ∧
      Function.Injective Pb.nodes ∧
      ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  absentOK := fun _ _ => False
  term := fun β _ M => match β with
    | .export => M.ρ 3
    | .path => M.ρ 4
    | .service => M.ρS
    | _ => 0
  size := fun _ _ => 0

/-- The axis chip (optional): PRESENT = the left disjunct of `AXChipOK`, ABSENT = its right disjunct. -/
def provAX : ProviderG (K := K) δ (PubJ9A p) (MsgJ9A' p K δ) (TrJ9A (ZMod p)) (Coins frameJ8 K) where
  chipOK := fun _ Pb M tr χ =>
    Pb.axOn = true ∧
      (AxisChipJ9.axisChipJ9 δ b Pb.hnX Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX).rap.Satisfies
        (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX) ∧
      (AxisChipJ9.axisChipJ9 δ b Pb.hnX Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX).BindsPreprocessing
        (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX) ∧
      Function.Injective Pb.nodesX ∧
      (∀ (i : Fin Pb.nX) (hi : (i : ℕ) + 1 < Pb.nX), Pb.nodesX ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesX i * Pb.orbitX.ω) ∧
      Pb.nX < p
  absentOK := fun Pb M =>
    Pb.axOn = false ∧ M.pubsX AxisChipJ9.pubAXs = 0 ∧ M.pubsX (AxisChipJ9.pubAXs + 1) = 0 ∧
      M.pubsX AxisChipJ9.pubAXp = 0 ∧ M.pubsX (AxisChipJ9.pubAXp + 1) = 0
  term := fun β _ M => match β with
    | .path => Quad.mk _ (M.pubsX AxisChipJ9.pubAXp) (M.pubsX (AxisChipJ9.pubAXp + 1))
    | .service => Quad.mk _ (M.pubsX AxisChipJ9.pubAXs) (M.pubsX (AxisChipJ9.pubAXs + 1))
    | _ => 0
  size := fun _ _ => 0

/-- The split chip (optional): PRESENT = the left disjunct of `SPChipOK`, ABSENT = its right disjunct. -/
def provSP : ProviderG (K := K) δ (PubJ9A p) (MsgJ9A' p K δ) (TrJ9A (ZMod p)) (Coins frameJ8 K) where
  chipOK := fun _ Pb M tr χ =>
    Pb.spOn = true ∧
      (SplitChipJ9.splitChipJ9 δ Pb.nA b Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS).rap.Satisfies
        (qSP δ b Pb tr (chalsMJ8 δ χ) M.pubsS) ∧
      (SplitChipJ9.splitChipJ9 δ Pb.nA b Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS).BindsPreprocessing
        (qSP δ b Pb tr (chalsMJ8 δ χ) M.pubsS) ∧
      Function.Injective Pb.nodesS ∧
      (∀ (i : Fin Pb.nS) (hi : (i : ℕ) + 1 < Pb.nS), Pb.nodesS ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesS i * Pb.orbitS.ω) ∧
      Pb.nS < p
  absentOK := fun Pb M =>
    Pb.spOn = false ∧ M.pubsS SplitChipJ9.pubSPs = 0 ∧ M.pubsS (SplitChipJ9.pubSPs + 1) = 0
  term := fun β _ M => match β with
    | .service => -Quad.mk _ (M.pubsS SplitChipJ9.pubSPs) (M.pubsS (SplitChipJ9.pubSPs + 1))
    | _ => 0
  size := fun _ _ => 0

/-- **The J-9 A provider list**: compute (twin RAP), cell, walk, J, atom, atom walk (J-8 providers read through the
projections), axis, split. -/
def providersJ9A : List (ProviderG (K := K) δ (PubJ9A p) (MsgJ9A' p K δ) (TrJ9A (ZMod p)) (Coins frameJ8 K)) :=
  [provXA δ b, liftJ9A δ (provC δ b), liftJ9A δ (provW δ b), liftJ9A δ (provJ δ b), liftJ9A δ (provA δ b),
    liftJ9A δ (provV δ b), provAX δ b, provSP δ b]

/-- **The J-9 A claim component**: `pubVJ9` for the compute publics, the J-9 B verifier terms and checks at the
projections. -/
def claimJ9A : ClaimSpecG (K := K) δ (PubJ9A p) (MsgJ9A' p K δ) (Coins frameJ8 K) where
  pubs := fun c M χ => pubVJ9 δ b c M.m M.ρ M.ρS χ
  verifierTerm := fun β c Pb M χ => (ProviderJ9.claimJ9 δ b).verifierTerm β c Pb.toPubJ8 M.toMsgJ8' χ
  checks := fun Rg c Pb M => (ProviderJ9.claimJ9 δ b).checks Rg c Pb.toPubJ8 M.toMsgJ8'

/-- **The J-9 A budget component**: `hnAS`, `BudJ9A`, `hbudV` (with the axis and split row parameters) and `hlenX`. -/
def budJ9A : BudgetG (PubJ9A p) RowsJ9A where
  offset := fun s _ => match s with
    | .rows => 3
    | .atoms => 0
  cap := fun _ => p
  ok := fun Pb r g => Pb.nA + Pb.nS < 2 ^ 57 ∧ BudJ9A Pb r (g + r.N) ∧
    (Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW ∧ Pb.nX ≤ r.AX ∧ Pb.nS ≤ r.SP) ∧
    (Pb.nX + Pb.n < p ∧ 2 * Pb.nS < p)

variable {δ b}

/-- **THE J-9 A IFF.**  `AcceptsGenericG` at the J-9 A providers, claim and budget is `AcceptsJ9A`, same binders. -/
theorem acceptsGeneric_j9a_iff (Pb : PubJ9A p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) (r : RowsJ9A) (g : ℕ) :
    AcceptsGenericG δ (providersJ9A δ b) (claimJ9A δ b) budJ9A Pb Rg c χ M tr r g ↔
      AcceptsJ9A.AcceptsJ9A δ b Pb Rg c χ M tr r g := by
  constructor
  · intro h
    have hP := h.hprov
    have hX := hP (provXA δ b) (by simp [providersJ9A])
    have hC := hP (liftJ9A δ (provC δ b)) (by simp [providersJ9A])
    have hW := hP (liftJ9A δ (provW δ b)) (by simp [providersJ9A])
    have hJ := hP (liftJ9A δ (provJ δ b)) (by simp [providersJ9A])
    have hA := hP (liftJ9A δ (provA δ b)) (by simp [providersJ9A])
    have hV := hP (liftJ9A δ (provV δ b)) (by simp [providersJ9A])
    have hAX := hP (provAX δ b) (by simp [providersJ9A])
    have hSP := hP (provSP δ b) (by simp [providersJ9A])
    have hX' : (provXA δ b).chipOK (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb M tr χ := hX.resolve_right id
    have hC' : (provC δ b).chipOK (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.toPubJ8 M.toMsgJ8' tr.toJ8 χ :=
      hC.resolve_right id
    have hW' : (provW δ b).chipOK (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.toPubJ8 M.toMsgJ8' tr.toJ8 χ :=
      hW.resolve_right id
    have hA' : (provA δ b).chipOK (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.toPubJ8 M.toMsgJ8' tr.toJ8 χ :=
      hA.resolve_right id
    obtain ⟨hsatX, hinjX, hadjX⟩ := hX'
    obtain ⟨hsatC, hbindC, hinjC, hadjC, hnpC⟩ := hC'
    obtain ⟨hsatW, hbindW, hinjW, hadjW, hkW, hknW, hkpW⟩ := hW'
    obtain ⟨hsatA, hbindA, hinjA, hadjA, hnpA, hsatL, hbindL⟩ := hA'
    obtain ⟨hstat, hclI, hclR, hcen, hcellF⟩ := h.hclaim
    obtain ⟨hlay, hsmall, huniq, hTpl, hnd, hidx, hrk, hlt⟩ := hstat
    obtain ⟨hnAS, hbud, hbudV, hlenX⟩ := h.hbud
    have hs1 := h.hsize .rows
    have hs2 := h.hsize .atoms
    simp only [providersJ9A, liftJ9A, provXA, provAX, provSP, ProviderJ8.provC, ProviderJ8.provW, ProviderJ8.provJ,
      ProviderJ8.provA, ProviderJ8.provV, budJ9A, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hs1 hs2
    have e1 := h.hbal .export
    have e2 := h.hbal .path
    have e3 := h.hbal .service
    have e4 := h.hbal .validity
    have e5 := h.hbal .atomHandle
    have e6 := h.hbal .atomValidity
    have e7 := h.hbal .fxC
    have e8 := h.hbal .fxA
    simp only [providersJ9A, liftJ9A, provXA, provAX, provSP, ProviderJ8.provC, ProviderJ8.provW, ProviderJ8.provJ,
      ProviderJ8.provA, ProviderJ8.provV, claimJ9A, ProviderJ9.claimJ9, List.map_cons, List.map_nil,
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
        hcellF := hcellF, hnAS := hnAS, hbud := hbud, hbudV := hbudV
        hsatL := hsatL, hbindL := hbindL
        hAXk := hAX
        hSPk := hSP
        hlenX := hlenX }
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
      simp only [providersJ9A, List.mem_cons, List.mem_nil_iff, or_false] at hP
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨h.hsatX, h.hinjX, h.hadjX⟩
      · exact Or.inl ⟨h.hsatC, h.hbindC, h.hinjC, h.hadjC, h.hnpC⟩
      · exact Or.inl ⟨h.hsatW, h.hbindW, h.hinjW, h.hadjW, h.hkW, h.hknW, h.hkpW⟩
      · exact h.hJk
      · exact Or.inl ⟨h.hsatA, h.hbindA, h.hinjA, h.hadjA, h.hnpA, h.hsatL, h.hbindL⟩
      · exact h.hVk
      · exact h.hAXk
      · exact h.hSPk
    · intro β
      cases β <;>
        simp only [providersJ9A, liftJ9A, provXA, provAX, provSP, ProviderJ8.provC, ProviderJ8.provW,
          ProviderJ8.provJ, ProviderJ8.provA, ProviderJ8.provV, claimJ9A, ProviderJ9.claimJ9, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil]
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
        simp only [providersJ9A, liftJ9A, provXA, provAX, provSP, ProviderJ8.provC, ProviderJ8.provW,
          ProviderJ8.provJ, ProviderJ8.provA, ProviderJ8.provV, budJ9A, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
      · have := h.hlenC; omega
      · have := h.hlenA; omega
    · exact ⟨h.hnAS, h.hbud, h.hbudV, h.hlenX⟩

end Inst

end

end Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ9A
#print axioms acceptsGeneric_j9a_iff
end Axioms
