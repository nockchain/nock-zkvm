/-
  Nock/NockVMROM/Thm54/VclL/Handle/AtomFpxJ8.lean

The 40th's #1.5 (`WalkChainSumVS.fpExportIOVS`, `Lift40J8.fpxL`) prices the cell walk's export lookup: the walk's
  consumed keys `walkXInternal` (arity 11) against the cell table's export records `cellXRecords` (two per row), at
  the validity coins `γ′ = mk χ₄ χ₆`, `ρ′ = mk χ₅ χ₇`, reading round `0`. The J-8 atom walk (`walkChipHQK`, the
  restriction `restrictWalkK` to `walkChip`) consumes the atom table's export records (the restriction
  `restrictAtomCell` to `cellChip`) through the SAME lookup, at the atom vector `chalsAJ8`, which carries the same
  validity coins (`ProbJ8.chalsAJ8_ok`: `ChalsOK … (mk χ₄ χ₆) (mk χ₅ χ₇) 11`).

  * §1 **`DataJ8X`**: a `DataJ8C` plus the two lists `vxReqs` / `vxProvs` read on `coinsBelow frameJ8 1`;
    **`atomFpxJ8`** = `ioSummandJ8 specV` (coins `{4, 6, 5, 7}`), budgets `(AW, 2A)`;
    **`eps_atomFpxJ8`**: `ε = ioFUB 11 AW (2A) |𝕂′| / |𝕂|⁴` (the weight).
  * §2 **`allJ8X X = allJ8C X.C ++ [atomFpxJ8 X]`**, `epsilon_allJ8X` (`= boundJ8X`), `numJ8X`, `boundJ8X_eq`,
    `numJ8X_corner`, **`figJ8X_155_census`** (`< 2^-155` at `cornerC`, `P ≤ 2^66`, `g ≤ 2^31`) and
    **`figJ8X_not_156`** (tight); `epsJ8X_lt_155_census`, `probJ8X_lt_155_census`.
  * §3 outside `allJ8X`: `outsideC_of_outsideX` (outside `allJ8C X.C`, so every existing discharge applies) and
    **`afx_out_of_outsideX`** (the validity pair is outside `IOFailureEventW vxReqs vxProvs`, within the budgets).
  * §4 **the real readout** on `TrJ8`: `vxReqsJ8` (the atom walk's `walkXInternal` on `restrictQ 21 25 tr.V`, coins
    and publics `0`) and `vxProvsJ8` (the atom table's `cXRec` on `restrictQ 129 205 tr.A`, lifted);
    **`vxJ8_reads`** (along `StJ8`, round-`≤ 1` columns only: `coinsBelow frameJ8 1`), the lengths `n_V`,
    `≤ 2 n_A`; `withFpxV`: a `DataJ8X` from a `DataJ8C` and the real readout.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8
import Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8

open Nock Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8 Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (cornerC)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (numJ8Pin_census)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8 crA crW shV shV_round staged_eq below_of_mem)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (walkXInternal cXRec wXInt_congr cXRec_congr walkXInternal_length
  cXRec_length)
open Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP

noncomputable section

/-! ## 1. -/

section Data
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  (δ : K) [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]

local notation "𝕂′" => Quad δ


structure DataJ8X (Tr : Type) (St : (Coins frameJ8 K → Tr) → Prop) (r : RowsJ8) (P g : ℕ) where
  C : DataJ8C (q := q) δ Tr St r P g
  vxReqs : Tr → Coins frameJ8 K → List (Fin 11 → 𝕂′)
  vxProvs : Tr → Coins frameJ8 K → List ((Fin 11 → 𝕂′) × 𝕂′)
  vx_reads : ∀ Q, St Q → ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ => (vxReqs (Q χ) χ, vxProvs (Q χ) χ)

variable {δ} {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

local notation "qmk" => Chips.quadMk_inj δ


def atomFpxJ8 (X : DataJ8X (q := q) δ Tr St r P g) : BadSummand frameJ8 K Tr St :=
  ioSummandJ8 (specV (Quad.mk δ) qmk) (coinsBelow frameJ8 1) (specV_disj _ _) St X.vxReqs X.vxProvs r.AW (2 * r.A)
    X.vx_reads


theorem atomFpxJ8_coins (X : DataJ8X (q := q) δ Tr St r P g) :
    ((atomFpxJ8 X).coins.image Fin.val) = {4, 6, 5, 7} :=
  specV_class (Quad.mk δ) qmk


theorem atomFpxJ8_dep (X : DataJ8X (q := q) δ Tr St r P g) : (atomFpxJ8 X).dep = coinsBelow frameJ8 1 := rfl


theorem atomFpxJ8_weight (X : DataJ8X (q := q) δ Tr St r P g) :
    (atomFpxJ8 X).weight = ioFailureUnionBound 11 r.AW (2 * r.A) (Fintype.card 𝕂′) := rfl

theorem eps_atomFpxJ8 (X : DataJ8X (q := q) δ Tr St r P g) :
    epsilonOf [atomFpxJ8 X] =
      (ioFailureUnionBound 11 r.AW (2 * r.A) (Fintype.card 𝕂′) : ℚ) / (Fintype.card K : ℚ) ^ 4 := by
  erw [atomFpxJ8, ioSummandJ8, eps_specSummand, specV_dep_card]

/-! ## 2. The list and the figure -/


def allJ8X (X : DataJ8X (q := q) δ Tr St r P g) : List (BadSummand frameJ8 K Tr St) :=
  allJ8C X.C ++ [atomFpxJ8 X]

end Data


def boundJ8X (c c' : ℕ) (r : RowsJ8) (P g : ℕ) : ℚ :=
  boundJ8Pin c c' r P g + (ioFailureUnionBound 11 r.AW (2 * r.A) c' : ℚ) / c ^ 4

section Eps
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {δ : K} [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

/-- **`ε` of the list is `boundJ8X`.** -/
theorem epsilon_allJ8X (X : DataJ8X (q := q) δ Tr St r P g) :
    epsilonOf (allJ8X X) = boundJ8X (Fintype.card K) (Fintype.card (Quad δ)) r P g := by
  rw [allJ8X, WeightsJ8.epsilonOf_append, epsilon_allJ8C, eps_atomFpxJ8, boundJ8X]

end Eps

/-- The numerator over `|𝕂|⁴` at `|𝕂′| = |𝕂|²`. -/
def numJ8X (c : ℕ) (r : RowsJ8) (P g : ℕ) : ℕ :=
  numJ8Pin c r P g + ioFailureUnionBound 11 r.AW (2 * r.A) (c ^ 2)

theorem boundJ8X_eq (c : ℕ) (r : RowsJ8) (P g : ℕ) (hc : 0 < c) :
    boundJ8X c (c ^ 2) r P g = (numJ8X c r P g : ℚ) / (c : ℚ) ^ 4 := by
  rw [boundJ8X, boundJ8Pin_eq c r P g hc, numJ8X]
  push_cast
  ring

theorem numJ8X_corner {c : ℕ} {r r₀ : RowsJ8} {P P₀ g g₀ : ℕ} (h : RowsLe r r₀) (hP : P ≤ P₀)
    (hg : g ≤ g₀) : numJ8X c r P g ≤ numJ8X c r₀ P₀ g₀ := by
  have e := numJ8Pin_corner (c := c) h hP hg
  obtain ⟨hN, hD, hW, hΛ, hA, hAW, hJ, hmb, hinc, hcalls, hheads, hblocks, hrd, hlv, hml⟩ := h
  have i := ioFUB_mono 11 (c ^ 2) (a := r.AW) (a' := r₀.AW) (b := 2 * r.A) (b' := 2 * r₀.A) hAW (by omega)
  unfold numJ8X
  omega

theorem boundJ8X_lt_of_num {r : RowsJ8} {P g b : ℕ} (h : numJ8X cK r P g * 2 ^ b < cK ^ 4) :
    boundJ8X cK (cK ^ 2) r P g < 1 / (2 : ℚ) ^ b := by
  rw [boundJ8X_eq _ _ _ _ cK_pos]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 4 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ hc (by positivity), one_mul]
  exact_mod_cast h

theorem not_boundJ8X_le_of_num {r : RowsJ8} {P g b : ℕ} (h : cK ^ 4 < numJ8X cK r P g * 2 ^ b) :
    ¬ boundJ8X cK (cK ^ 2) r P g ≤ 1 / (2 : ℚ) ^ b := by
  rw [boundJ8X_eq _ _ _ _ cK_pos, not_le]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 4 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ (by positivity) hc, one_mul]
  exact_mod_cast h

theorem numJ8X_census (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numJ8X c cornerC (2 ^ 66) (2 ^ 31) * 2 ^ 155 < c ^ 4 := by
  subst hc; unfold numJ8X numJ8Pin numHQ cornerC corner31 fuelChip pairCount ioFailureUnionBound; decide +kernel

theorem numJ8X_census_not (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < numJ8X c cornerC (2 ^ 66) (2 ^ 31) * 2 ^ 156 := by
  subst hc; unfold numJ8X numJ8Pin numHQ cornerC corner31 fuelChip pairCount ioFailureUnionBound; decide +kernel


theorem figJ8X_155_census (r : RowsJ8) (P g : ℕ) (h : RowsLe r cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31) :
    boundJ8X cK (cK ^ 2) r P g < 1 / (2 : ℚ) ^ 155 :=
  boundJ8X_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numJ8X_corner h hP hg)) (numJ8X_census cK cK_eq))

/-- **Tight**: at the corner, not `≤ 2^-156`. -/
theorem figJ8X_not_156 : ¬ boundJ8X cK (cK ^ 2) cornerC (2 ^ 66) (2 ^ 31) ≤ 1 / (2 : ℚ) ^ 156 :=
  not_boundJ8X_le_of_num (numJ8X_census_not cK cK_eq)

section Fig
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {δ : K} [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

theorem epsJ8X_lt_155_census (X : DataJ8X (q := q) δ Tr St r P g) (hcK : Fintype.card K = cK)
    (h : RowsLe r cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31) : epsilonOf (allJ8X X) < 1 / (2 : ℚ) ^ 155 := by
  rw [epsilon_allJ8X, quad_card, hcK]
  exact figJ8X_155_census r P g h hP hg

open Classical in

theorem probJ8X_lt_155_census (X : DataJ8X (q := q) δ Tr St r P g) (Q : Coins frameJ8 K → Tr) (hQ : St Q)
    (Acc : Coins frameJ8 K → Prop) (Holds : Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ allJ8X X, ¬ s.mem (Q χ) χ) → Holds)
    (hcK : Fintype.card K = cK) (h : RowsLe r cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => Acc χ ∧ ¬ Holds).card : ℚ) /
        Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  lt_of_le_of_lt (prob_le_of_outside _ Q hQ Acc Holds hsound) (epsJ8X_lt_155_census X hcK h hP hg)

/-! ## 3. Outside `allJ8X` -/

/-- Outside `allJ8X X`, outside `allJ8C X.C`: every existing discharge applies. -/
theorem outsideC_of_outsideX (X : DataJ8X (q := q) δ Tr St r P g) {tr : Tr} {χ : Coins frameJ8 K}
    (h : ∀ s ∈ allJ8X X, ¬ s.mem tr χ) : ∀ s ∈ allJ8C X.C, ¬ s.mem tr χ :=
  fun s hs => h s (List.mem_append_left _ hs)


theorem afx_out_of_outsideX (X : DataJ8X (q := q) δ Tr St r P g) {tr : Tr} {χ : Coins frameJ8 K}
    (h : ∀ s ∈ allJ8X X, ¬ s.mem tr χ) (h1 : (X.vxReqs tr χ).length ≤ r.AW)
    (h2 : (X.vxProvs tr χ).length ≤ 2 * r.A) :
    (Quad.mk δ (χ c4) (χ c6), Quad.mk δ (χ c5) (χ c7)) ∉ IOFailureEventW (X.vxReqs tr χ) (X.vxProvs tr χ) :=
  pair_notMem_of_io _ _ _ St _ _ _ _ _ (h (atomFpxJ8 X) (List.mem_append_right _ (List.mem_singleton_self _))) h1 h2

end Fig

/-! ## 4. The real readout on `TrJ8` -/

theorem shA : ∀ j < 225, shiftCol 129 205 j < 349 := by
  intro j hj; unfold shiftCol; split_ifs <;> omega

theorem shA_round (j : ℕ) (hj : j < 183) : crA ⟨shiftCol 129 205 j, shA j (by omega)⟩ ≤ 1 := by
  simp only [crA, shiftCol]; split_ifs <;> omega

section Real
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  (δF : F) [Fact (¬ IsSquare (algebraMap F K δF))] (b : Basis (Fin 3) F K)

local notation "𝕂′" => Quad (algebraMap F K δF)


def vxReqsJ8 (kroots : ℕ) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (tr : TrJ8 F) : List (Fin 11 → 𝕂′) :=
  walkXInternal δF kroots b hn nodes orbit (fun _ => 0) (fun _ => 0) (restrictQ 21 25 shV tr.V)


def vxProvsJ8 {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (tr : TrJ8 F) :
    List ((Fin 11 → 𝕂′) × 𝕂′) :=
  liftWts (cXRec δF b nodes orbit (fun _ => (0 : K)) (fun _ => 0) (restrictQ 129 205 shA tr.A))

theorem vxReqsJ8_length (kroots : ℕ) {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h)
    (tr : TrJ8 F) : (vxReqsJ8 δF b kroots hn nodes orbit tr).length = n :=
  walkXInternal_length δF kroots b hn nodes orbit _ _ _

theorem vxProvsJ8_length {h n : ℕ} (nodes : Fin n → F) (orbit : StrictOrbitDomain F 3 h) (tr : TrJ8 F) :
    (vxProvsJ8 δF b nodes orbit tr).length ≤ 2 * n := by
  rw [vxProvsJ8, liftWts_length]
  exact cXRec_length δF b nodes orbit _ _ _


theorem vxJ8_reads (kroots : ℕ) {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → F)
    (orbitV : StrictOrbitDomain F 3 hV) {hA nA : ℕ} (nodesA : Fin nA → F) (orbitA : StrictOrbitDomain F 3 hA)
    (Q : Coins frameJ8 K → TrJ8 F) (hQ : StJ8 Q) :
    ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ =>
      (vxReqsJ8 δF b kroots hnV nodesV orbitV (Q χ), vxProvsJ8 δF b nodesA orbitA (Q χ)) := by
  intro χ χ' hχ
  refine Prod.ext ?_ ?_
  · refine wXInt_congr δF kroots b hnV nodesV orbitV _ _ _ _ _ _ (by norm_num) (by norm_num) fun j hj => ?_
    exact staged_eq hQ.2.2.2.2.2 (below_of_mem hχ) _ (shV_round j hj)
  · show liftWts _ = liftWts _
    congr 1
    refine cXRec_congr δF b nodesA orbitA _ _ _ _ _ _ (by norm_num) (by norm_num) fun j hj => ?_
    exact staged_eq hQ.2.2.2.2.1 (below_of_mem hχ) _ (shA_round j hj)

variable [Fintype K] [DecidableEq K] [Fact (ringChar F).Prime] [Algebra (ZMod (ringChar F)) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap F K δF))] {r : RowsJ8} {P g : ℕ}


def withFpxV (R : DataJ8C (q := ringChar F) (algebraMap F K δF) (TrJ8 F) StJ8 r P g) (kroots : ℕ) {hV nV : ℕ}
    (hnV : 0 < nV) (nodesV : Fin nV → F) (orbitV : StrictOrbitDomain F 3 hV) {hA nA : ℕ} (nodesA : Fin nA → F)
    (orbitA : StrictOrbitDomain F 3 hA) :
    DataJ8X (q := ringChar F) (algebraMap F K δF) (TrJ8 F) StJ8 r P g where
  C := R
  vxReqs tr _ := vxReqsJ8 δF b kroots hnV nodesV orbitV tr
  vxProvs tr _ := vxProvsJ8 δF b nodesA orbitA tr
  vx_reads Q hQ := vxJ8_reads δF b kroots hnV nodesV orbitV nodesA orbitA Q hQ


theorem withFpxV_budgets (R : DataJ8C (q := ringChar F) (algebraMap F K δF) (TrJ8 F) StJ8 r P g) (kroots : ℕ)
    {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → F) (orbitV : StrictOrbitDomain F 3 hV) {hA nA : ℕ}
    (nodesA : Fin nA → F) (orbitA : StrictOrbitDomain F 3 hA) (hbV : nV ≤ r.AW) (hbA : nA ≤ r.A)
    (tr : TrJ8 F) (χ : Coins frameJ8 K) :
    ((withFpxV δF b R kroots hnV nodesV orbitV nodesA orbitA).vxReqs tr χ).length ≤ r.AW ∧
      ((withFpxV δF b R kroots hnV nodesV orbitV nodesA orbitA).vxProvs tr χ).length ≤ 2 * r.A :=
  ⟨(vxReqsJ8_length δF b kroots hnV nodesV orbitV tr).le.trans hbV,
    (vxProvsJ8_length δF b nodesA orbitA tr).trans (by omega)⟩

end Real

end

end Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
