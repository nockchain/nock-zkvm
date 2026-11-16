/-
  Nock/NockVMROM/Thm54/VclL/Handle/BundleJ8.lean

  **The bundled lemma — outside the J-8 list, every exclusion
  ingredient of `hsound` at once; and the figure at the census corner with the registry pin.**

  * §1 `chalsMJ8_z`: the memory vector's leaves `2, 3` are `χ₂, χ₃` (the structure coin `z`).
  * **`outJ8_of_outside`**: outside `allJ8C (withLiftC R L)` ⇒ `OutJ8`.
  * §3 **`figJ8C_155_census`**: with the pin (`g ≤ 2^31`) at the census corner (`leaves ≤ 2·fuelChip`,
    `P ≤ 2^66`), `boundJ8Pin < 2^-155` (`decide +kernel`); `epsJ8C_lt_155_census`, `probJ8C_lt_155_census`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C
import Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8 Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 Nock.NockVMROM.Thm54.VclL.Handle.WalkKJ8
open Nock.NockVMROM.Thm54.VclL.Events
open Nock.ComputeTable (FP)
open Nock.Atoms (lenL)

noncomputable section

section Bundle
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8 chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (RowVSX)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX (foOf)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX (cwEvent tileSet)

/-- The memory vector's leaves `2, 3` are the structure coin `z = (χ₂, χ₃)`. -/
theorem chalsMJ8_z (χ : Coins frameJ8 K) : chalsMJ8 δ χ 2 = χ c2 ∧ chalsMJ8 δ χ 3 = χ c3 := by
  rw [chalsMJ8_lo δ χ 2 (by norm_num), chalsMJ8_lo δ χ 3 (by norm_num)]
  constructor
  · simp [FrameVS.chalsVS, Chips.ChipRAP.chalsVCL, CellH.hGam, CellH.hRho, FrameVS.toVCL, toVS, toVSQ, c2]
  · simp [FrameVS.chalsVS, Chips.ChipRAP.chalsVCL, CellH.hGam, CellH.hRho, FrameVS.toVCL, toVS, toVSQ, c3]

/-- **The exclusion ingredients of `hsound` at `(tr, χ)`**, one field per class. -/
structure OutJ8 (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (b : Module.Basis (Fin 3) (ZMod p) K)
    (tr : Tr) (χ : Coins frameJ8 K) : Prop where
  /-- #8: the atom table's `hz`. -/
  atom_hz : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8 δ χ 2) (chalsAJ8 δ χ 3) ≠ 0
  /-- #1 (zero seed): `z ≠ 0`, the cell table's `hz`. -/
  z_ne : Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) ≠ 0
  valid : (R.D.valReqs tr χ).length ≤ 3 + 2 * r.D + g → (R.D.valProvs tr χ).length ≤ r.D + r.mb →
    (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ)
  /-- #1: the compute walk event. -/
  hw : ∀ {α γ : K}, limbVal b (chalVJ8 b χ) ChipH.chalAlphaW = α → limbVal b (chalVJ8 b χ) ChipH.chalGammaW = γ →
    (α, γ) ∉ cwEvent (K := K) (L.cRows tr) (L.cH tr)
  /-- #1: the compute tiling. -/
  hα : ∀ {α : K}, limbVal b (chalVJ8 b χ) ChipH.chalAlphaW = α → α ∉ tileSet (K := K) (foOf (L.cRows tr)) (L.cH tr)
  /-- #5: `hout.x`. -/
  hout_x : (R.D.cxReqs tr χ).length ≤ 3 * r.N + r.W + r.rd → (R.D.cxProvs tr χ).length ≤ r.D →
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.cxReqs tr χ) (R.D.cxProvs tr χ)
  hout_s : (R.D.svReqs tr χ).length ≤ r.N + 2 * r.J + g → (R.D.svProvs tr χ).length ≤ r.calls + r.heads + r.blocks + r.J →
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.svReqs tr χ) (R.D.svProvs tr χ)
  /-- #1: `hout.p`. -/
  hout_p : (L.pReqs tr (toVSQ χ)).length ≤ 2 * r.N → (L.pProvs tr (toVSQ χ)).length ≤ 2 * r.W →
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (L.pReqs tr (toVSQ χ)) (L.pProvs tr (toVSQ χ))
  /-- #9 (ruled): the atom walk's `houtV`. -/
  houtV : (chalsVJ8 δ χ 0, chalsVJ8 δ χ 1) ∉ WalkVCL.walkEvent (algebraMap (ZMod p) K δ) (R.wdC tr χ)
  biv : ∀ pr ∈ R.D.prs tr, pr.1.length = pr.2.length → pr.1 ≠ pr.2 → pr.1.length ≤ r.leaves →
    (∀ a ∈ pr.1, lenL a ≤ r.maxlen) → (∀ a ∈ pr.2, lenL a ≤ r.maxlen) →
    Nock.Atoms.leafSum (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
        (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) pr.1 ≠
      Nock.Atoms.leafSum (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
        (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) pr.2
  encInj : ∀ {t : List (CellRow Nock.Atoms.p 𝕂′)} {vp : List (VKey 𝕂′)}
    {ext : ℕ → Option Noun},
    TableAccepts2 (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) t vp →
    AtomLeaves (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3))
      (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))) vp ext →
    (∀ j m, ext j = some m → ∃ v, m = .atom v ∧ lenL v ≤ r.maxlen) →
    (∀ x < Nock.Atoms.p, lenL x ≤ r.maxlen) → 2 * fuelChip ≤ r.leaves →
    (∀ pr ∈ censusPairs (censusList2 (t.map (·.b0)) ext), pr ∈ R.D.prs tr) →
    EncInj2 (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3))
      (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))) t ext

theorem outJ8_of_outside (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (b : Module.Basis (Fin 3) (ZMod p) K)
    {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ) :
    OutJ8 (withLiftC R L) L b tr χ := by
  have hz : Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) ≠ 0 := by
    have := hz_of_outside40C R L h (chalsMJ8 δ χ) rfl rfl
    rwa [(chalsMJ8_z χ).1, (chalsMJ8_z χ).2] at this
  have h10 := outside_sumJ8_D (withLiftC R L) h .bivariateCensus (by decide) (by decide) (by decide)
  refine ⟨atom_hz_of_outsideC _ h, hz, fun h1 h2 => valid_out_of_outsideC _ h h1 h2,
    fun hα hγ => hw_of_outside40C R L b h rfl rfl hα hγ, fun hα => hα_of_outside40C R L b h rfl rfl hα,
    fun h1 h2 => hout_x_of_outsideC _ b h _ _ rfl rfl h1 h2,
    fun h1 h2 => hout_s_of_outsideC _ b h _ _ rfl rfl h1 h2,
    fun h1 h2 => hout_p_of_outside40C R L b h _ _ rfl rfl h1 h2,
    houtV_of_outsideC _ h,
    fun _pr hpr hlen hne hk hM1 hM2 => biv_out_of_outsideC _ h hpr hlen hne hk hM1 hM2, ?_⟩
  intro t vp ext htab hvp hext hqM hk hprs
  have hq : 2 ^ 63 < Nock.Atoms.p := by norm_num [Nock.Atoms.p, Nock.Field.p]
  exact encInj2_of_outside (withLiftC R L).D h10 hq hz
    (inlineAtoms_encZY rfl _ _) htab hvp hext hqM hk hprs

end Bundle

/-! ## 3. The figure at the census corner with the pin -/

theorem numJ8Pin_census (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numJ8Pin c cornerC (2 ^ 66) (2 ^ 31) * 2 ^ 155 < c ^ 4 := by
  subst hc; unfold numJ8Pin numHQ cornerC corner31 fuelChip pairCount ioFailureUnionBound; decide +kernel

/-- **`< 2^-155` with the pin at the census corner**: rows `≤ 2^31`, `leaves ≤ 2·fuelChip`, `P ≤ 2^66`,
`g ≤ 2^31` registered ids. -/
theorem figJ8C_155_census (r : RowsJ8) (P g : ℕ) (h : RowsLe r cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31) :
    boundJ8Pin cK (cK ^ 2) r P g < 1 / (2 : ℚ) ^ 155 :=
  boundJ8Pin_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numJ8Pin_corner h hP hg)) (numJ8Pin_census cK cK_eq))

section Fig
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {δ : K} [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

theorem epsJ8C_lt_155_census (R : DataJ8C (q := q) δ Tr St r P g) (hcK : Fintype.card K = cK)
    (h : RowsLe r cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31) : epsilonOf (allJ8C R) < 1 / (2 : ℚ) ^ 155 := by
  rw [epsilon_allJ8C, quad_card, hcK]
  exact figJ8C_155_census r P g h hP hg

open Classical in
theorem probJ8C_lt_155_census (R : DataJ8C (q := q) δ Tr St r P g) (Q : Coins frameJ8 K → Tr) (hQ : St Q)
    (Acc : Coins frameJ8 K → Prop) (Holds : Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ allJ8C R, ¬ s.mem (Q χ) χ) → Holds)
    (hcK : Fintype.card K = cK) (h : RowsLe r cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => Acc χ ∧ ¬ Holds).card : ℚ) /
        Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  lt_of_le_of_lt (prob_le_of_outside _ Q hQ Acc Holds hsound) (epsJ8C_lt_155_census R hcK h hP hg)

end Fig

end

end Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8
