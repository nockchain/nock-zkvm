/-
  Nock/NockVMROM/Thm54/VclL/Handle/ProbJ8.lean

  * §2 at the J-8 list: `probJ8_le` (`≤ boundJ8P`, by `epsilon_allJ8`) and **`probJ8_lt_155`** (`< 2^-155` at
    Goldilocks, every row count `≤ 2^31`, by `epsJ8_lt_155`).
  * §3 `outside_sumJ8`: outside `allJ8 R` is outside every summand of every class.
  * §5 the memory challenge vectors at `frameJ8`: `chalsOK_J8` (the cell / walk vector `chalsMJ8` carries the
    validity coins `γ′ρ′`, `ChalsOK … 11`); the atom table's vector **`chalsAJ8`** (`y` at leaves `2, 3`,
    otherwise `chalsMJ8`): `chalsAJ8_agree` (FinalJ8's `hchA`), `chalsAJ8_y`, `chalsAJ8_ok`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
import Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
import Nock.NockVMROM.Thm54.VclL.Handle.ClaimVS
import Nock.NockVMROM.Thm54.P8Core.SVFrame.FibreBound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (ChalsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalVJ8 chalsMJ8 coinsCV_J8)

noncomputable section

/-! ## 1. The probability statement for any summand list -/

section Prob
variable {Φ : CoinFrame} {K : Type} [Field K] [Fintype K] [DecidableEq K] {Tr : Type}
  {St : (Coins Φ K → Tr) → Prop}

open Classical in
/-- **`Pr[accept ∧ ¬ target] ≤ epsilonOf L`** along any staged strategy, whenever acceptance outside every
summand of `L` proves the target. -/
theorem prob_le_of_outside (L : List (BadSummand Φ K Tr St)) (Q : Coins Φ K → Tr) (hQ : St Q)
    (Acc : Coins Φ K → Prop) (Holds : Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ L, ¬ s.mem (Q χ) χ) → Holds) :
    ((Finset.univ.filter fun χ : Coins Φ K => Acc χ ∧ ¬ Holds).card : ℚ) / Fintype.card (Coins Φ K) ≤
      epsilonOf L := by
  have hpos : (0 : ℚ) ≤ Fintype.card (Coins Φ K) := by positivity
  refine le_trans (div_le_div_of_nonneg_right ?_ hpos) (union_prob_le L Q hQ)
  refine Nat.cast_le.mpr (Finset.card_le_card fun χ hχ => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
  simp only [unionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hno
  push Not at hno
  exact hχ.2 (hsound χ hχ.1 hno)

end Prob

/-! ## 2–3. At the J-8 list -/

section J8
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {δ : K} [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P : ℕ}

open Classical in
/-- **The J-8 probability statement**: `Pr[accept ∧ ¬ target] ≤ boundJ8P` (`= epsilonOf (allJ8 R)`). -/
theorem probJ8_le (R : DataJ8 (q := q) δ Tr St r P) (Q : Coins frameJ8 K → Tr) (hQ : St Q)
    (Acc : Coins frameJ8 K → Prop) (Holds : Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ allJ8 R, ¬ s.mem (Q χ) χ) → Holds) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => Acc χ ∧ ¬ Holds).card : ℚ) /
        Fintype.card (Coins frameJ8 K) ≤ boundJ8P (Fintype.card K) (Fintype.card (Quad δ)) r P :=
  (prob_le_of_outside _ Q hQ Acc Holds hsound).trans (epsilon_allJ8 R).le

open Classical in
/-- **The J-8 figure**: at Goldilocks (`|𝕂| = p³`), every row count `≤ 2^31`, `≤ 2^31` census pairs,
`Pr[accept ∧ ¬ target] < 2^-155`. -/
theorem probJ8_lt_155 (R : DataJ8 (q := q) δ Tr St r P) (Q : Coins frameJ8 K → Tr) (hQ : St Q)
    (Acc : Coins frameJ8 K → Prop) (Holds : Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ allJ8 R, ¬ s.mem (Q χ) χ) → Holds)
    (hcK : Fintype.card K = cK) (h : RowsLe r corner31) (hP : P ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => Acc χ ∧ ¬ Holds).card : ℚ) /
        Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  lt_of_le_of_lt (prob_le_of_outside _ Q hQ Acc Holds hsound) (epsJ8_lt_155 R hcK h hP)

/-- Outside the J-8 list is outside every summand of every class. -/
theorem outside_sumJ8 (R : DataJ8 (q := q) δ Tr St r P) {tr : Tr} {χ : Coins frameJ8 K}
    (h : ∀ s ∈ allJ8 R, ¬ s.mem tr χ) (k : SummandM) : ∀ s ∈ sumJ8 R k, ¬ s.mem tr χ := by
  intro s hs
  refine h s (List.mem_flatMap.mpr ⟨k, ?_, hs⟩)
  cases k <;> simp [orderJ8]

end J8

/-! ## 4. The IO bridges -/

section IO
variable {K Kio : Type} [Field K] [Fintype K] [DecidableEq K] [Field Kio] [Fintype Kio] [DecidableEq Kio]

theorem mem_ioSummandJ8 (I : IOCoinSpec frameJ8 K Kio) (dep : Finset (Fin frameJ8.n)) (hdisj : Disjoint I.dep dep)
    {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop) {m : ℕ}
    (reqs : Tr → Coins frameJ8 K → List (Fin m → Kio)) (provs : Tr → Coins frameJ8 K → List ((Fin m → Kio) × Kio))
    (k₁ k₂ : ℕ) (hreads) (tr : Tr) (χ : Coins frameJ8 K) :
    (ioSummandJ8 I dep hdisj St reqs provs k₁ k₂ hreads).mem tr χ ↔ I.pair χ ∈ evIO (reqs tr χ) (provs tr χ) k₁ k₂ :=
  mem_specSummand _ _ _ _ _ _ _ _ tr χ

/-- **Outside an IO summand, within its budgets**, the coin pair is outside `IOFailureEventW` of the lists. -/
theorem pair_notMem_of_io (I : IOCoinSpec frameJ8 K Kio) (dep : Finset (Fin frameJ8.n)) (hdisj : Disjoint I.dep dep)
    {Tr : Type} (St : (Coins frameJ8 K → Tr) → Prop) {m : ℕ}
    (reqs : Tr → Coins frameJ8 K → List (Fin m → Kio)) (provs : Tr → Coins frameJ8 K → List ((Fin m → Kio) × Kio))
    (k₁ k₂ : ℕ) (hreads) {tr : Tr} {χ : Coins frameJ8 K}
    (h : ¬ (ioSummandJ8 I dep hdisj St reqs provs k₁ k₂ hreads).mem tr χ)
    (h1 : (reqs tr χ).length ≤ k₁) (h2 : (provs tr χ).length ≤ k₂) :
    I.pair χ ∉ IOFailureEventW (reqs tr χ) (provs tr χ) := by
  rw [mem_ioSummandJ8, evIO_of_guard h1 h2] at h
  exact h

end IO

/-! ## 5. The memory challenge vectors at `frameJ8` -/

section Vectors
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

theorem chalsMJ8_lo (χ : Coins frameJ8 K) (j : ℕ) (hj : j < 35) :
    chalsMJ8 δ χ j = chalsVS δ (toVS (toVSQ χ)) j := by
  have h1 : j ≠ 35 := by omega
  have h2 : j ≠ 36 := by omega
  simp only [chalsMJ8, chalsVSQ, if_neg h1, if_neg h2]

/-- **The cell / walk vector carries the validity coins**: `ChalsOK` at `γ′ = χ₄ + χ₆√δ`, `ρ′ = χ₅ + χ₇√δ`, `11`
(the shape `provOK_x` / `exportHKW_genuine` take). -/
theorem chalsOK_J8 (χ : Coins frameJ8 K) :
    ChalsOK δ (chalsMJ8 δ χ) (Quad.mk _ (χ c4) (χ c6)) (Quad.mk _ (χ c5) (χ c7)) 11 := by
  have h := ClaimVS.chalsOK_VS (K := K) δ (toVS (toVSQ χ))
  refine ⟨?_, fun i hi => ?_⟩
  · rw [chalsMJ8_lo δ χ 5 (by norm_num), chalsMJ8_lo δ χ 7 (by norm_num)]; exact h.1
  · rw [chalsMJ8_lo δ χ _ (by omega), chalsMJ8_lo δ χ _ (by omega)]; exact h.2 i hi

/-- **The atom table's challenge vector at `frameJ8`**: the limb coin `y = (χ₁₇, χ₁₈)` at leaves `2, 3` (where the
cell table reads `z`), every other leaf `chalsMJ8` (validity coins, handle coins). -/
def chalsAJ8 (χ : Coins frameJ8 K) (j : ℕ) : K :=
  if j = 2 then χ cY1 else if j = 3 then χ cY2 else chalsMJ8 δ χ j

/-- FinalJ8's `hchA`: the atom vector agrees with `chalsMJ8` at the handle leaves. -/
theorem chalsAJ8_agree (χ : Coins frameJ8 K) : ∀ j, 33 ≤ j → j ≤ 36 → chalsAJ8 δ χ j = chalsMJ8 δ χ j := by
  intro j h1 _
  simp only [chalsAJ8, if_neg (show j ≠ 2 by omega), if_neg (show j ≠ 3 by omega)]

/-- The atom table's coin is `y`. -/
theorem chalsAJ8_y (χ : Coins frameJ8 K) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8 δ χ 2) (chalsAJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2) := by
  simp [chalsAJ8]

/-- The atom vector carries the validity coins too. -/
theorem chalsAJ8_ok (χ : Coins frameJ8 K) :
    ChalsOK δ (chalsAJ8 δ χ) (Quad.mk _ (χ c4) (χ c6)) (Quad.mk _ (χ c5) (χ c7)) 11 := by
  have h := chalsOK_J8 δ χ
  have e : ∀ j, 4 ≤ j → chalsAJ8 δ χ j = chalsMJ8 δ χ j := fun j hj => by
    simp only [chalsAJ8, if_neg (show j ≠ 2 by omega), if_neg (show j ≠ 3 by omega)]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [e 5 (by norm_num), e 7 (by norm_num)]; exact h.1
  · rw [e _ (by omega), e _ (by omega)]; exact h.2 i hi

end Vectors

/-! ## 6. The frame-side discharges, per class -/

section Discharge
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The atom table's `hz`** (`atomTable_accepts`, `provOK_*` at the atom vector): outside the zero-`y`
summand of #8, the atom table's coin `y` is nonzero. -/
theorem atom_hz_of_outside (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ sumJ8 R .atomCensus, ¬ s.mem tr χ) :
    Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8 δ χ 2) (chalsAJ8 δ χ 3) ≠ 0 := by
  rw [chalsAJ8_y]
  have hs := h
  simp only [sumJ8, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hs
  have := hs.2.2
  rwa [mem_zeroYJ8] at this

/-- **#2**: outside the class-#2 summand, within the budgets, the validity pair `(γ′, ρ′)` is outside the two-provider cell
validity event of `R`'s lists (the shape of `provOK_x`'s `hout`). -/
theorem valid_out_of_outside (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ sumJ8 R .cellValidity2, ¬ s.mem tr χ)
    (h1 : (R.valReqs tr χ).length ≤ 3 + 2 * r.D) (h2 : (R.valProvs tr χ).length ≤ r.D + r.mb) :
    (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.valReqs tr χ) (R.valProvs tr χ) := by
  have hs := h
  simp only [sumJ8, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at hs
  exact pair_notMem_of_io _ _ _ St _ _ _ _ _ hs h1 h2

/-- **Any handle-class IO summand** (`γH′ρH′`, read set `∅`) **gives FinalJ8's `hout` shape**: outside it, within
its budgets, the compute coins `coinsCV (chalVJ8 b χ)` are outside `IOFailureEventW` of its lists. -/
theorem hout_of_specH (b : Module.Basis (Fin 3) (ZMod p) K) {m : ℕ}
    (reqs : Tr → Coins frameJ8 K → List (Fin m → 𝕂′)) (provs : Tr → Coins frameJ8 K → List ((Fin m → 𝕂′) × 𝕂′))
    (k₁ k₂ : ℕ) (hreads) {tr : Tr} {χ : Coins frameJ8 K}
    (h : ¬ (ioSummandJ8 (specH (Quad.mk (algebraMap (ZMod p) K δ)) (Chips.quadMk_inj _)) ∅
      (specH_disj _ _) St reqs provs k₁ k₂ hreads).mem tr χ)
    (h1 : (reqs tr χ).length ≤ k₁) (h2 : (provs tr χ).length ≤ k₂) :
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqs tr χ) (provs tr χ) := by
  rw [coinsCV_J8 δ b χ]
  exact pair_notMem_of_io _ _ _ St _ _ _ _ _ h h1 h2

/-- **#5, FinalJ8's `hout.x`**: if `R`'s cell-export lists at `(tr, χ)` are the `x` balance's (`reqsJ8 … ext.x`,
`liftP (provs.x)`) and fit the budgets, then outside the class-#5 summand the compute coins are outside its IO event. -/
theorem hout_x_of_outside (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P)
    (b : Module.Basis (Fin 3) (ZMod p) K) {tr : Tr} {χ : Coins frameJ8 K} (h : ∀ s ∈ sumJ8 R .cellExport3, ¬ s.mem tr χ)
    (reqs : List (Fin 5 → 𝕂′)) (provs : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hr : R.cxReqs tr χ = reqs) (hp : R.cxProvs tr χ = provs)
    (h1 : reqs.length ≤ 3 * r.N + r.W + r.rd) (h2 : provs.length ≤ r.D) :
    ((Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).gamma, (Handle.TeleCQ.coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW reqs provs := by
  have hs := h
  simp only [sumJ8, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at hs
  subst hr hp
  exact hout_of_specH b _ _ _ _ _ hs h1 h2

theorem biv_out_of_outside (R : DataJ8 (q := q) (algebraMap (ZMod p) K δ) Tr St r P) {tr : Tr}
    {χ : Coins frameJ8 K} (h : ∀ s ∈ sumJ8 R .bivariateCensus, ¬ s.mem tr χ) {pr : List ℕ × List ℕ} (hpr : pr ∈ R.prs tr)
    (hlen : pr.1.length = pr.2.length) (hne : pr.1 ≠ pr.2) (hk : pr.1.length ≤ r.leaves)
    (hM1 : ∀ a ∈ pr.1, Nock.Atoms.lenL a ≤ r.maxlen) (hM2 : ∀ a ∈ pr.2, Nock.Atoms.lenL a ≤ r.maxlen) :
    Nock.Atoms.leafSum (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
        (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) pr.1 ≠
      Nock.Atoms.leafSum (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
        (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) pr.2 := by
  have hs := h
  simp only [sumJ8, List.mem_cons, List.mem_nil_iff, or_false, forall_eq] at hs
  rw [mem_bivJ8] at hs
  exact leafSum_ne_of_not_mem hs hpr hlen hne hk hM1 hM2

end Discharge

end

end Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8
