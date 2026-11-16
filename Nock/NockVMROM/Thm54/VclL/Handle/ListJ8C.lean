/-
  Nock/NockVMROM/Thm54/VclL/Handle/ListJ8C.lean

  * §1 **`DataJ8C`**: a `DataJ8` `D` (every readout but #9; its `wdA` group is NOT used) plus the atom walk's data
    `wdC` read on the round-0 coins (`coinsBelow frameJ8 1`, `y` included), the number of registered ids `g`
    (a type parameter, as `P`).
  * `epsilon_sumJ8C` (each `ε` is `weightJ8Pin`), **`epsilon_allJ8C`**
    (`= boundJ8Pin`), **`epsJ8C_lt_155`**, **`probJ8C_le`**, **`probJ8C_lt_155`**.
  * §4 `withLiftC R L` (#1 at the J-8 readouts, `Lift40J8.withLift` on `R.D`), `outside40C`, and the `FinalJ8`
    shapes `hw_of_outside40C`, `hα_of_outside40C`, `hout_p_of_outside40C`, `hz_of_outside40C`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8
import Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8 Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8
open Nock.NockVMROM.Thm54.VclL.Events

noncomputable section

/-! ## 1–2. The data and the list -/

section Data
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  (δ : K) [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]

local notation "𝕂′" => Quad δ

/-- `g` is the number of registered ids. -/
structure DataJ8C (Tr : Type) (St : (Coins frameJ8 K → Tr) → Prop) (r : RowsJ8) (P g : ℕ) where
  D : DataJ8 (q := q) δ Tr St r P
  /-- #9 the atom walk's data (labels at `y`, committed in round 1, read on round-0 coins). -/
  wdC : Tr → Coins frameJ8 K → WalkVCL.WalkData q 𝕂′
  wdC_le : ∀ tr χ, (wdC tr χ).h ≤ r.AW
  wdC_reads : ∀ Q, St Q → ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ => wdC (Q χ) χ

variable {δ} {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

local notation "qmk" => Chips.quadMk_inj δ

def sumJ8C (R : DataJ8C (q := q) δ Tr St r P g) : SummandM → List (BadSummand frameJ8 K Tr St)
  | .fortieth => sumJ8 R.D .fortieth
  | .cellValidity2 => [ioSummandJ8 (specV (Quad.mk δ) qmk) _ (specV_disj _ _) St R.D.valReqs R.D.valProvs
      (3 + 2 * r.D + g) (r.D + r.mb) R.D.val_reads]
  | .atomValidity => sumJ8 R.D .atomValidity
  | .atomExport => sumJ8 R.D .atomExport
  | .cellExport3 => sumJ8 R.D .cellExport3
  | .service => [ioSummandJ8 (specH (Quad.mk δ) qmk) _ (specH_disj _ _) St R.D.svReqs R.D.svProvs
      (r.N + 2 * r.J + g) (r.calls + r.heads + r.blocks + r.J) R.D.sv_reads]
  | .atomCensus => sumJ8 R.D .atomCensus
  | .atomWalk => [atomWalkJ8C δ St R.wdC r.AW R.wdC_le R.wdC_reads]
  | .bivariateCensus => sumJ8 R.D .bivariateCensus

/-- The six unchanged classes are `sumJ8 R.D`'s. -/
theorem sumJ8C_eq (R : DataJ8C (q := q) δ Tr St r P g) (s : SummandM) (h2 : s ≠ .cellValidity2)
    (h6 : s ≠ .service) (h9 : s ≠ .atomWalk) : sumJ8C R s = sumJ8 R.D s := by
  cases s <;> first | exact absurd rfl h2 | exact absurd rfl h6 | exact absurd rfl h9 | rfl

theorem epsilon_sumJ8C (R : DataJ8C (q := q) δ Tr St r P g) (s : SummandM) :
    epsilonOf (sumJ8C R s) = weightJ8Pin (Fintype.card K) (Fintype.card (Quad δ)) r P g s := by
  cases s
  · exact epsilon_sumJ8 R.D .fortieth
  · exact eps_validity_pin δ _ _ r P g _
  · exact epsilon_sumJ8 R.D .atomValidity
  · exact epsilon_sumJ8 R.D .atomExport
  · exact epsilon_sumJ8 R.D .cellExport3
  · exact eps_service_pin δ _ _ r P g _
  · exact epsilon_sumJ8 R.D .atomCensus
  · rw [sumJ8C, epsilon_atomWalkJ8C]; rfl
  · exact epsilon_sumJ8 R.D .bivariateCensus

def allJ8C (R : DataJ8C (q := q) δ Tr St r P g) : List (BadSummand frameJ8 K Tr St) := orderJ8.flatMap (sumJ8C R)

/-- **`ε` of the list is `boundJ8Pin`.** -/
theorem epsilon_allJ8C (R : DataJ8C (q := q) δ Tr St r P g) :
    epsilonOf (allJ8C R) = boundJ8Pin (Fintype.card K) (Fintype.card (Quad δ)) r P g := by
  rw [allJ8C, epsilonOf_flatMap, boundJ8Pin, sum_univ_SummandM]
  congr 1
  exact List.map_congr_left fun s _ => epsilon_sumJ8C R s

/-- **The figure**: at Goldilocks (`|𝕂| = p³`), rows `≤ 2^31`, `≤ 2^31` census pairs and registered ids,
`ε < 2^-155`. -/
theorem epsJ8C_lt_155 (R : DataJ8C (q := q) δ Tr St r P g) (hcK : Fintype.card K = cK) (h : RowsLe r corner31)
    (hP : P ≤ 2 ^ 31) (hg : g ≤ 2 ^ 31) : epsilonOf (allJ8C R) < 1 / (2 : ℚ) ^ 155 := by
  rw [epsilon_allJ8C, quad_card, hcK]
  exact figJ8Pin_155 r P g h hP hg

open Classical in
theorem probJ8C_le (R : DataJ8C (q := q) δ Tr St r P g) (Q : Coins frameJ8 K → Tr) (hQ : St Q)
    (Acc : Coins frameJ8 K → Prop) (Holds : Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ allJ8C R, ¬ s.mem (Q χ) χ) → Holds) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => Acc χ ∧ ¬ Holds).card : ℚ) /
        Fintype.card (Coins frameJ8 K) ≤ boundJ8Pin (Fintype.card K) (Fintype.card (Quad δ)) r P g :=
  (prob_le_of_outside _ Q hQ Acc Holds hsound).trans (epsilon_allJ8C R).le

open Classical in
theorem probJ8C_lt_155 (R : DataJ8C (q := q) δ Tr St r P g) (Q : Coins frameJ8 K → Tr) (hQ : St Q)
    (Acc : Coins frameJ8 K → Prop) (Holds : Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ allJ8C R, ¬ s.mem (Q χ) χ) → Holds)
    (hcK : Fintype.card K = cK) (h : RowsLe r corner31) (hP : P ≤ 2 ^ 31) (hg : g ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => Acc χ ∧ ¬ Holds).card : ℚ) /
        Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  lt_of_le_of_lt (prob_le_of_outside _ Q hQ Acc Holds hsound) (epsJ8C_lt_155 R hcK h hP hg)

/-- Outside the list is outside every summand of every class. -/
theorem outside_sumJ8C (R : DataJ8C (q := q) δ Tr St r P g) {tr : Tr} {χ : Coins frameJ8 K}
    (h : ∀ s ∈ allJ8C R, ¬ s.mem tr χ) (k : SummandM) : ∀ s ∈ sumJ8C R k, ¬ s.mem tr χ := by
  intro s hs
  refine h s (List.mem_flatMap.mpr ⟨k, ?_, hs⟩)
  cases k <;> simp [orderJ8]

/-- Outside the list, outside every unchanged class of `R.D`. -/
theorem outside_sumJ8_D (R : DataJ8C (q := q) δ Tr St r P g) {tr : Tr} {χ : Coins frameJ8 K}
    (h : ∀ s ∈ allJ8C R, ¬ s.mem tr χ) (k : SummandM) (h2 : k ≠ .cellValidity2) (h6 : k ≠ .service)
    (h9 : k ≠ .atomWalk) : ∀ s ∈ sumJ8 R.D k, ¬ s.mem tr χ := by
  rw [← sumJ8C_eq R k h2 h6 h9]
  exact outside_sumJ8C R h k

end Data

/-! ## 3. The discharges outside `allJ8C` -/

section Discharge
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8 chalsMJ8 coinsCV_J8)

/-- #8: the atom table's `hz`. -/
theorem atom_hz_of_outsideC (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C R, ¬ s.mem tr χ) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8 δ χ 2) (chalsAJ8 δ χ 3) ≠ 0 :=
  atom_hz_of_outside R.D (outside_sumJ8_D R h .atomCensus (by decide) (by decide) (by decide))

theorem valid_out_of_outsideC (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C R, ¬ s.mem tr χ)
    (h1 : (R.D.valReqs tr χ).length ≤ 3 + 2 * r.D + g) (h2 : (R.D.valProvs tr χ).length ≤ r.D + r.mb) :
    (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := by
  have hs := outside_sumJ8C R h .cellValidity2
  simp only [sumJ8C, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at hs
  exact pair_notMem_of_io _ _ _ St _ _ _ _ _ hs h1 h2

/-- #5: `FinalJ8`'s `hout.x`. -/
theorem hout_x_of_outsideC (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g)
    (b : Module.Basis (Fin 3) (ZMod p) K) {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C R, ¬ s.mem tr χ)
    (reqs : List (Fin 5 → 𝕂′)) (provs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hr : R.D.cxReqs tr χ = reqs) (hp : R.D.cxProvs tr χ = provs)
    (h1 : reqs.length ≤ 3 * r.N + r.W + r.rd) (h2 : provs.length ≤ r.D) :
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW reqs provs :=
  hout_x_of_outside R.D b (outside_sumJ8_D R h .cellExport3 (by decide) (by decide) (by decide)) reqs provs hr hp
    h1 h2

theorem hout_s_of_outsideC (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g)
    (b : Module.Basis (Fin 3) (ZMod p) K) {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C R, ¬ s.mem tr χ)
    (rs : List (Fin 8 → 𝕂′)) (ps : List ((Fin 8 → 𝕂′) × 𝕂′))
    (hr : R.D.svReqs tr χ = rs) (hp : R.D.svProvs tr χ = ps)
    (h1 : rs.length ≤ r.N + 2 * r.J + g) (h2 : ps.length ≤ r.calls + r.heads + r.blocks + r.J) :
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW rs ps := by
  have hs := outside_sumJ8C R h .service
  simp only [sumJ8C, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at hs
  subst hr hp
  exact hout_of_specH b _ _ _ _ _ hs h1 h2

theorem biv_out_of_outsideC (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C R, ¬ s.mem tr χ) {pr : List ℕ × List ℕ} (hpr : pr ∈ R.D.prs tr)
    (hlen : pr.1.length = pr.2.length) (hne : pr.1 ≠ pr.2) (hk : pr.1.length ≤ r.leaves)
    (hM1 : ∀ a ∈ pr.1, Nock.Atoms.lenL a ≤ r.maxlen) (hM2 : ∀ a ∈ pr.2, Nock.Atoms.lenL a ≤ r.maxlen) :
    Nock.Atoms.leafSum (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
        (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) pr.1 ≠
      Nock.Atoms.leafSum (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
        (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) pr.2 :=
  biv_out_of_outside R.D (outside_sumJ8_D R h .bivariateCensus (by decide) (by decide) (by decide)) hpr hlen hne
    hk hM1 hM2

/-- **#9 (ruled): `CorJ8A`'s `houtV`**: the atom walk's coins `(chalsVJ8 0, chalsVJ8 1)` are outside `walkEvent`
of its data. -/
theorem houtV_of_outsideC (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C R, ¬ s.mem tr χ) :
    (chalsVJ8 δ χ 0, chalsVJ8 δ χ 1) ∉ WalkVCL.walkEvent (algebraMap (ZMod p) K δ) (R.wdC tr χ) := by
  have hs := outside_sumJ8C R h .atomWalk
  simp only [sumJ8C, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at hs
  exact houtV_of_outside St R.wdC r.AW R.wdC_le R.wdC_reads hs

end Discharge

/-! ## 4. #1 at the J-8 readouts -/

section Lift
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {δ : K} [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

/-- **`withLiftC R L`**: `R` with #1 at the J-8 readouts (`Lift40J8.withLift` on `R.D`). -/
def withLiftC (R : DataJ8C (q := q) δ Tr St r P g) (L : Data40J8 (q := q) δ Tr St r) :
    DataJ8C (q := q) δ Tr St r P g :=
  { R with D := withLift R.D L }

theorem outside40C (R : DataJ8C (q := q) δ Tr St r P g) (L : Data40J8 (q := q) δ Tr St r) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ) :
    ∀ s ∈ sum40 L, ¬ s.mem tr (toVSQ χ) := by
  intro s hs hm
  have h1 := outside_sumJ8C (withLiftC R L) h .fortieth
  refine h1 (liftJ8 s id (hπ40_id St)) (List.mem_map.mpr ⟨s, hs, rfl⟩) ?_
  rw [mem_liftJ8]
  exact hm

end Lift

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8 chalsMJ8 coinsCV_J8)
open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (RowVSX)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX (foOf)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX (cwEvent tileSet)

/-- **`FinalJ8`'s `hw`** outside `allJ8C`. -/
theorem hw_of_outside40C (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (b : Module.Basis (Fin 3) (ZMod p) K)
    {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    {rows : ℕ → RowVSX} {n : ℕ} (hr : L.cRows tr = rows) (hn : L.cH tr = n) {α γ : K}
    (hα : limbVal b (chalVJ8 b χ) ChipH.chalAlphaW = α) (hγ : limbVal b (chalVJ8 b χ) ChipH.chalGammaW = γ) :
    (α, γ) ∉ cwEvent (K := K) rows n := by
  rw [← hα, ← hγ, limb_alphaW_J8, limb_gammaW_J8, ← hr, ← hn]
  exact cw_out L (outside40C R L h)

/-- **`FinalJ8`'s `hα`** outside `allJ8C`. -/
theorem hα_of_outside40C (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (b : Module.Basis (Fin 3) (ZMod p) K)
    {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    {rows : ℕ → RowVSX} {n : ℕ} (hr : L.cRows tr = rows) (hn : L.cH tr = n) {α : K}
    (hα : limbVal b (chalVJ8 b χ) ChipH.chalAlphaW = α) :
    α ∉ tileSet (K := K) (foOf rows) n := by
  rw [← hα, limb_alphaW_J8, ← hr, ← hn]
  exact tile_out L (outside40C R L h)

/-- **`FinalJ8`'s `hout.p`** outside `allJ8C`. -/
theorem hout_p_of_outside40C (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r) (b : Module.Basis (Fin 3) (ZMod p) K)
    {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    (reqs : List (Fin 5 → 𝕂′)) (provs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hr : L.pReqs tr (toVSQ χ) = reqs) (hp : L.pProvs tr (toVSQ χ) = provs)
    (h1 : reqs.length ≤ 2 * r.N) (h2 : provs.length ≤ 2 * r.W) :
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW reqs provs := by
  rw [coinsCV_J8 δ b χ]
  subst hr hp
  exact hp_out L (outside40C R L h) h1 h2

/-- **The cell table's `hz`** outside `allJ8C`. -/
theorem hz_of_outside40C (R : DataJ8C (q := q) (algebraMap (ZMod p) K δ) Tr St r P g)
    (L : Data40J8 (q := q) (algebraMap (ZMod p) K δ) Tr St r)
    {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    (chals : ℕ → K) (h2 : chals 2 = chalsMJ8 δ χ 2) (h3 : chals 3 = chalsMJ8 δ χ 3) :
    Quad.mk (algebraMap (ZMod p) K δ) (chals 2) (chals 3) ≠ 0 := by
  rw [h2, h3, chalsMJ8_lo δ χ 2 (by norm_num), chalsMJ8_lo δ χ 3 (by norm_num)]
  have hz := zero_out L (outside40C R L h)
  have e2 : FrameVS.chalsVS δ (toVS (toVSQ χ)) 2 = toVSQ χ v2 := by
    simp [FrameVS.chalsVS, Chips.ChipRAP.chalsVCL, CellH.hGam, CellH.hRho, FrameVS.toVCL, toVS, v2]
  have e3 : FrameVS.chalsVS δ (toVS (toVSQ χ)) 3 = toVSQ χ v3 := by
    simp [FrameVS.chalsVS, Chips.ChipRAP.chalsVCL, CellH.hGam, CellH.hRho, FrameVS.toVCL, toVS, v3]
  rw [e2, e3]
  exact hz

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C
