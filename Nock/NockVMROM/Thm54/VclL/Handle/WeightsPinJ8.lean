/-
  Nock/NockVMROM/Thm54/VclL/Handle/WeightsPinJ8.lean

The pin adds, per registered id, ONE external consumer to the cell validity balance (summand #2,
  `cellValidity2`: the claim key `(E (compile p (R id)), rk id, idx id)`) and ONE consumer to the J
  tagged balance, whose terminal enters the service balance (summand #6, `service`: the in-chip key
  `(id, 1, idx id, 2)`).  No coin, so no summand changes its coins; only the two consumer budgets grow
  by `g = #regs`:

  * `weightJ8Pin c c' r P g`: `weightJ8P` with `#2`'s consumer budget `3 + 2D → 3 + 2D + g` and the
    merged service summand's (W2: #6 + #7) `N + 2J → N + 2J + g`; the other seven weights unchanged (`weightJ8Pin_other`), `g = 0` is `weightJ8P`
    (`weightJ8Pin_zero`), monotone (`weightJ8P_le_pin`);
  * `eps_validity_pin` / `eps_service_pin`: the two IO summands at the new budgets have exactly the new
    weights (the `ioSummandJ8` constructor is budget-parametric);
  * `boundJ8Pin`, `numJ8Pin`, `boundJ8Pin_eq`, `numJ8Pin_corner`;
  * **figures**: `figJ8Pin_155` (`< 2^-155` at every row count `≤ 2^31` and `g ≤ 2^31`) and
    `figJ8Pin_not_156` (tight at the corner): the J-8 figure is unchanged by the pin.

  The pin's `+g` on the J tagged balance therefore lands on
  `SummandM.service`'s consumer budget; `numJ8Pin` has no separate J term. Same names, same figures. -/
import Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Events

noncomputable section

/-! ## 1. The weights with the pin -/

/-- **The proved weights with the registry pin** (`g` = number of registered ids). -/
def weightJ8Pin (c c' : ℕ) (r : RowsJ8) (P g : ℕ) : SummandM → ℚ
  | .cellValidity2 => (ioFailureUnionBound 5 (3 + 2 * r.D + g) (r.D + r.mb) c' : ℚ) / c ^ 4
  | .service =>
      (ioFailureUnionBound 8 (r.N + 2 * r.J + g) (r.calls + r.heads + r.blocks + r.J) c' : ℚ) / c ^ 4
  | s => weightJ8P c c' r P s

/-- **Delta, validity (#2)**: `+g` external consumers. -/
theorem weightJ8Pin_validity (c c' : ℕ) (r : RowsJ8) (P g : ℕ) :
    weightJ8Pin c c' r P g .cellValidity2 =
      (ioFailureUnionBound 5 (3 + 2 * r.D + g) (r.D + r.mb) c' : ℚ) / c ^ 4 := rfl

/-- **Delta, service (#6, merged with #7)**: `+g` consumers (the J tagged terminal enters the service balance). -/
theorem weightJ8Pin_service (c c' : ℕ) (r : RowsJ8) (P g : ℕ) :
    weightJ8Pin c c' r P g .service =
      (ioFailureUnionBound 8 (r.N + 2 * r.J + g) (r.calls + r.heads + r.blocks + r.J) c' : ℚ) / c ^ 4 := rfl

/-- The other seven weights are unchanged. -/
theorem weightJ8Pin_other (c c' : ℕ) (r : RowsJ8) (P g : ℕ) (s : SummandM)
    (h2 : s ≠ .cellValidity2) (h6 : s ≠ .service) : weightJ8Pin c c' r P g s = weightJ8P c c' r P s := by
  cases s <;> first | exact absurd rfl h2 | exact absurd rfl h6 | rfl

/-- No registered id: the weights of `WeightsJ8`. -/
theorem weightJ8Pin_zero (c c' : ℕ) (r : RowsJ8) (P : ℕ) : weightJ8Pin c c' r P 0 = weightJ8P c c' r P := by
  funext s; cases s <;> rfl

/-- The pin only adds. -/
theorem weightJ8P_le_pin (c c' : ℕ) (r : RowsJ8) (P g : ℕ) (s : SummandM) :
    weightJ8P c c' r P s ≤ weightJ8Pin c c' r P g s := by
  cases s
  case cellValidity2 =>
    show (ioFailureUnionBound 5 (3 + 2 * r.D) (r.D + r.mb) c' : ℚ) / c ^ 4 ≤ _
    exact div_le_div_of_nonneg_right (by exact_mod_cast ioFUB_mono 5 c' (by omega) le_rfl) (by positivity)
  case service =>
    show (ioFailureUnionBound 8 (r.N + 2 * r.J) (r.calls + r.heads + r.blocks + r.J) c' : ℚ) / c ^ 4 ≤ _
    exact div_le_div_of_nonneg_right (by exact_mod_cast ioFUB_mono 8 c' (by omega) le_rfl) (by positivity)
  all_goals exact le_rfl

/-! ## 2. The two IO summands at the new budgets -/

section Eps
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] (δ : K) [Fact (¬ IsSquare δ)]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop}

local notation "qmk" => Chips.quadMk_inj δ

/-- **#2 at the pinned budget** has `ε = weightJ8Pin … .cellValidity2`. -/
theorem eps_validity_pin (reqs : Tr → Coins frameJ8 K → List (Fin 5 → Quad δ))
    (provs : Tr → Coins frameJ8 K → List ((Fin 5 → Quad δ) × Quad δ)) (r : RowsJ8) (P g : ℕ)
    (hreads : ∀ Q, St Q → ReadsOnC frameJ8 (coinsBelow frameJ8 1) fun χ => (reqs (Q χ) χ, provs (Q χ) χ)) :
    epsilonOf [ioSummandJ8 (specV (Quad.mk δ) qmk) _ (specV_disj _ _) St reqs provs
        (3 + 2 * r.D + g) (r.D + r.mb) hreads] =
      weightJ8Pin (Fintype.card K) (Fintype.card (Quad δ)) r P g .cellValidity2 := by
  erw [ioSummandJ8, eps_specSummand, specV_dep_card]; rfl

/-- **#6 (merged service) at the pinned budget** has `ε = weightJ8Pin … .service`. -/
theorem eps_service_pin (reqs : Tr → Coins frameJ8 K → List (Fin 8 → Quad δ))
    (provs : Tr → Coins frameJ8 K → List ((Fin 8 → Quad δ) × Quad δ)) (r : RowsJ8) (P g : ℕ)
    (hreads : ∀ Q, St Q → ReadsOnC frameJ8 ∅ fun χ => (reqs (Q χ) χ, provs (Q χ) χ)) :
    epsilonOf [ioSummandJ8 (specH (Quad.mk δ) qmk) _ (specH_disj _ _) St reqs provs
        (r.N + 2 * r.J + g) (r.calls + r.heads + r.blocks + r.J) hreads] =
      weightJ8Pin (Fintype.card K) (Fintype.card (Quad δ)) r P g .service := by
  erw [ioSummandJ8, eps_specSummand, specH_dep_card]; rfl

end Eps

/-! ## 3. The bound and the figure -/

/-- **`boundJ8Pin`**: the sum of the nine weights with the pin. -/
def boundJ8Pin (c c' : ℕ) (r : RowsJ8) (P g : ℕ) : ℚ := ∑ s : SummandM, weightJ8Pin c c' r P g s

theorem boundJ8Pin_zero (c c' : ℕ) (r : RowsJ8) (P : ℕ) : boundJ8Pin c c' r P 0 = boundJ8P c c' r P := by
  rw [boundJ8Pin, boundJ8P, weightJ8Pin_zero]

/-- The numerator over `|𝕂|⁴` at `|𝕂′| = |𝕂|²`. -/
def numJ8Pin (c : ℕ) (r : RowsJ8) (P g : ℕ) : ℕ :=
  numHQ c r.N r.D r.W r.Λ +
  (ioFailureUnionBound 5 (3 + 2 * r.D + g) (r.D + r.mb) (c ^ 2) +
    ioFailureUnionBound 5 (3 + 2 * r.A) r.A (c ^ 2) +
    ioFailureUnionBound 5 (r.A + r.inc + r.AW) r.A (c ^ 2) +
    ioFailureUnionBound 5 (3 * r.N + r.W + r.rd) r.D (c ^ 2) +
    ioFailureUnionBound 8 (r.N + 2 * r.J + g) (r.calls + r.heads + r.blocks + r.J) (c ^ 2)) +
  c ^ 2 * (r.A * (2 * fuelChip - 1) + pairCount (r.A + 3) * (2 * r.Λ - 1) + 1) +
  c ^ 3 * (15 * r.AW) +
  P * (c ^ 2 * (r.leaves - 1) + c ^ 2 * (r.maxlen - 1))

theorem boundJ8Pin_eq (c : ℕ) (r : RowsJ8) (P g : ℕ) (hc : 0 < c) :
    boundJ8Pin c (c ^ 2) r P g = (numJ8Pin c r P g : ℚ) / (c : ℚ) ^ 4 := by
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [boundJ8Pin, sum_univ_SummandM]
  simp only [orderJ8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, weightJ8Pin, weightJ8P]
  rw [boundVCLHQ''_eq c r.N r.D r.W r.Λ hc]
  unfold numJ8Pin
  push_cast
  field_simp
  ring

theorem numJ8Pin_corner {c : ℕ} {r r₀ : RowsJ8} {P P₀ g g₀ : ℕ} (h : RowsLe r r₀) (hP : P ≤ P₀)
    (hg : g ≤ g₀) : numJ8Pin c r P g ≤ numJ8Pin c r₀ P₀ g₀ := by
  obtain ⟨hN, hD, hW, hΛ, hA, hAW, hJ, hmb, hinc, hcalls, hheads, hblocks, hrd, hlv, hml⟩ := h
  have e0 := numHQ_corner (c := c) r.Λ hN hD hW
  rw [hΛ] at e0
  have i1 := ioFUB_mono 5 (c ^ 2) (a := 3 + 2 * r.D + g) (a' := 3 + 2 * r₀.D + g₀) (b := r.D + r.mb)
    (b' := r₀.D + r₀.mb) (by omega) (by omega)
  have i2 := ioFUB_mono 5 (c ^ 2) (a := 3 + 2 * r.A) (a' := 3 + 2 * r₀.A) (b := r.A) (b' := r₀.A) (by omega) hA
  have i3 := ioFUB_mono 5 (c ^ 2) (a := r.A + r.inc + r.AW) (a' := r₀.A + r₀.inc + r₀.AW) (b := r.A) (b' := r₀.A)
    (by omega) hA
  have i4 := ioFUB_mono 5 (c ^ 2) (a := 3 * r.N + r.W + r.rd) (a' := 3 * r₀.N + r₀.W + r₀.rd) (b := r.D)
    (b' := r₀.D) (by omega) hD
  have i5 := ioFUB_mono 8 (c ^ 2) (a := r.N + 2 * r.J + g) (a' := r₀.N + 2 * r₀.J + g₀)
    (b := r.calls + r.heads + r.blocks + r.J) (b' := r₀.calls + r₀.heads + r₀.blocks + r₀.J) (by omega) (by omega)
  have hp : pairCount (r.A + 3) ≤ pairCount (r₀.A + 3) := pairCount_mono (by omega)
  have hl : r.leaves - 1 ≤ r₀.leaves - 1 := Nat.sub_le_sub_right hlv 1
  have hm : r.maxlen - 1 ≤ r₀.maxlen - 1 := Nat.sub_le_sub_right hml 1
  unfold numJ8Pin
  rw [hΛ]
  gcongr

theorem boundJ8Pin_lt_of_num {r : RowsJ8} {P g b : ℕ} (h : numJ8Pin cK r P g * 2 ^ b < cK ^ 4) :
    boundJ8Pin cK (cK ^ 2) r P g < 1 / (2 : ℚ) ^ b := by
  rw [boundJ8Pin_eq _ _ _ _ cK_pos]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 4 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ hc (by positivity), one_mul]
  exact_mod_cast h

theorem not_boundJ8Pin_le_of_num {r : RowsJ8} {P g b : ℕ} (h : cK ^ 4 < numJ8Pin cK r P g * 2 ^ b) :
    ¬ boundJ8Pin cK (cK ^ 2) r P g ≤ 1 / (2 : ℚ) ^ b := by
  rw [boundJ8Pin_eq _ _ _ _ cK_pos, not_le]
  have hc : (0 : ℚ) < (cK : ℚ) ^ 4 := by have := cK_pos; positivity
  rw [div_lt_div_iff₀ (by positivity) hc, one_mul]
  exact_mod_cast h

theorem numJ8Pin_31 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numJ8Pin c corner31 (2 ^ 31) (2 ^ 31) * 2 ^ 155 < c ^ 4 := by
  subst hc; unfold numJ8Pin numHQ corner31 fuelChip pairCount ioFailureUnionBound; decide +kernel

theorem numJ8Pin_31_not (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < numJ8Pin c corner31 (2 ^ 31) (2 ^ 31) * 2 ^ 156 := by
  subst hc; unfold numJ8Pin numHQ corner31 fuelChip pairCount ioFailureUnionBound; decide +kernel

/-- **The J-8 figure with the pin: `< 2^-155`** at every row count `≤ 2^31` and `≤ 2^31` registered
ids (the corner of `WeightsJ8.figJ8_155`). -/
theorem figJ8Pin_155 (r : RowsJ8) (P g : ℕ) (h : RowsLe r corner31) (hP : P ≤ 2 ^ 31) (hg : g ≤ 2 ^ 31) :
    boundJ8Pin cK (cK ^ 2) r P g < 1 / (2 : ℚ) ^ 155 :=
  boundJ8Pin_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numJ8Pin_corner h hP hg))
    (numJ8Pin_31 cK cK_eq))

/-- **Tight**: at the corner (`g = 2^31`), not `≤ 2^-156`. -/
theorem figJ8Pin_not_156 : ¬ boundJ8Pin cK (cK ^ 2) corner31 (2 ^ 31) (2 ^ 31) ≤ 1 / (2 : ℚ) ^ 156 :=
  not_boundJ8Pin_le_of_num (numJ8Pin_31_not cK cK_eq)

end

end Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8
