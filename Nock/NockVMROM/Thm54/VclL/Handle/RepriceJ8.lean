/-
  Nock/NockVMROM/Thm54/VclL/Handle/RepriceJ8.lean

  The J-8 list `allJ8C R` prices the service summand at consumers `N + 2J + g` and the cell validity #2 at
  `3 + 2D + g`, where `g` is the list's registered-id parameter.  Instantiating the SAME list at
  `g' := g + N` prices #6 at exactly `N + 2J + (g + N) = 2N + 2J + g` (`service_budget_reprice`); #2 is then priced
  at `3 + 2D + g + N`, i.e. over-priced by `N` consumers (sound: a larger budget only enlarges the bad event; the
  figure does not move, below).

  * **`numJ8X_census32`** / **`numJ8X_census32_not`** (kernel `decide`): the numerator at the census corner,
    `P = 2^66`, `g' = 2^32` (`= 2^31` ids `+ N = 2^31`): `< 2^-155`, not `≤ 2^-156`.  **The figure stays 155, tight.**
  * **`figJ8X_155_census32`** (`g' ≤ 2^32`), `figJ8X_not_156_32`, `epsJ8X_lt_155_census32`,
    **`probJ8X_lt_155_census32`**.
  * The budget side: `BudJ8 Pb r (g + r.N)`'s `s1` is `2·n + |regs| + J-consumes ≤ 2N + 2J + g`
    (`budJ8_s1_reprice`), and `hcap_corner32` (`2N + 2J + g < p` at the corner, `g ≤ 2^31`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ8

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.WeightsPinJ8 Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C
open Nock.NockVMROM.Thm54.VclL.Handle.AtomFpxJ8
open Nock.NockVMROM.Thm54.VclL.Handle.EncInjJ8 (cornerC)
open Nock.NockVMROM.Thm54.VclL.Events

noncomputable section

/-- **#6 re-priced**: the service summand of `allJ8C` at `g + N` has consumer budget `2N + 2J + g`. -/
theorem service_budget_reprice (r : RowsJ8) (g : ℕ) : r.N + 2 * r.J + (g + r.N) = 2 * r.N + 2 * r.J + g := by
  omega

/-- #2 at `g + N`: over-priced by `N` consumers. -/
theorem validity_budget_reprice (r : RowsJ8) (g : ℕ) : 3 + 2 * r.D + (g + r.N) = (3 + 2 * r.D + g) + r.N := by
  omega

theorem numJ8X_census32 (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    numJ8X c cornerC (2 ^ 66) (2 ^ 32) * 2 ^ 155 < c ^ 4 := by
  subst hc; unfold numJ8X numJ8Pin numHQ cornerC corner31 fuelChip pairCount ioFailureUnionBound; decide +kernel

theorem numJ8X_census32_not (c : ℕ) (hc : c = 18446744069414584321 ^ 3) :
    c ^ 4 < numJ8X c cornerC (2 ^ 66) (2 ^ 32) * 2 ^ 156 := by
  subst hc; unfold numJ8X numJ8Pin numHQ cornerC corner31 fuelChip pairCount ioFailureUnionBound; decide +kernel

/-- **The J-8 figure with #6 re-priced: `< 2^-155`** at the census corner, `P ≤ 2^66`, `g' ≤ 2^32`
(`g' = g + N`: `≤ 2^31` registered ids plus the `N ≤ 2^31` extra service consumers). -/
theorem figJ8X_155_census32 (r : RowsJ8) (P g : ℕ) (h : RowsLe r cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 32) :
    boundJ8X cK (cK ^ 2) r P g < 1 / (2 : ℚ) ^ 155 :=
  boundJ8X_lt_of_num (lt_of_le_of_lt (Nat.mul_le_mul_right _ (numJ8X_corner h hP hg)) (numJ8X_census32 cK cK_eq))

/-- **Tight**: at the corner with `g' = 2^32`, not `≤ 2^-156`. -/
theorem figJ8X_not_156_32 : ¬ boundJ8X cK (cK ^ 2) cornerC (2 ^ 66) (2 ^ 32) ≤ 1 / (2 : ℚ) ^ 156 :=
  not_boundJ8X_le_of_num (numJ8X_census32_not cK cK_eq)

section Fig
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  {δ : K} [Fact (¬ IsSquare δ)] [Algebra Nock.Atoms.Fp (Quad δ)]
  {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8} {P g : ℕ}

theorem epsJ8X_lt_155_census32 (X : DataJ8X (q := q) δ Tr St r P g) (hcK : Fintype.card K = cK)
    (h : RowsLe r cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 32) : epsilonOf (allJ8X X) < 1 / (2 : ℚ) ^ 155 := by
  rw [epsilon_allJ8X, quad_card, hcK]
  exact figJ8X_155_census32 r P g h hP hg

open Classical in
/-- **The J-8 probability statement, #6 re-priced** (`g' ≤ 2^32`): `Pr[accept ∧ ¬ target] < 2^-155`. -/
theorem probJ8X_lt_155_census32 (X : DataJ8X (q := q) δ Tr St r P g) (Q : Coins frameJ8 K → Tr) (hQ : St Q)
    (Acc : Coins frameJ8 K → Prop) (Holds : Prop)
    (hsound : ∀ χ, Acc χ → (∀ s ∈ allJ8X X, ¬ s.mem (Q χ) χ) → Holds)
    (hcK : Fintype.card K = cK) (h : RowsLe r cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 32) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K => Acc χ ∧ ¬ Holds).card : ℚ) /
        Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  lt_of_le_of_lt (prob_le_of_outside _ Q hQ Acc Holds hsound) (epsJ8X_lt_155_census32 X hcK h hP hg)

end Fig

section Bud
open Nock.Jet.ChipJ8 (ents0T ents1T)
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8 (BudJ8 jCount)
variable {p : ℕ} [Fact p.Prime]

/-- The re-priced budget check `s1`: at `g + N`, it reads `2·n + |regs| + J-consumes ≤ 2N + 2J + g`. -/
theorem budJ8_s1_reprice (Pb : AcceptsJ8.PubJ8 p) (r : RowsJ8) (g : ℕ) :
    (2 * Pb.n + Pb.regs.length + (jCount ents0T Pb.lay + jCount ents1T Pb.lay) ≤ r.N + 2 * r.J + (g + r.N)) ↔
      (2 * Pb.n + Pb.regs.length + (jCount ents0T Pb.lay + jCount ents1T Pb.lay) ≤ 2 * r.N + 2 * r.J + g) := by
  rw [service_budget_reprice]

/-- The caps below `p` at the re-priced parameter `g + N`, census corner, `g ≤ 2^31`, Goldilocks. -/
theorem hcap_corner32 {r : RowsJ8} {g : ℕ} (hr : RowsLe r cornerC) (hg : g ≤ 2 ^ 31) (hpG : p = Nock.Atoms.p) :
    3 * r.N + r.W + r.rd < p ∧ 2 * r.N < p ∧ r.N + 2 * r.J + (g + r.N) < p := by
  obtain ⟨hN, -, hW, -, -, -, hJ, -, -, -, -, -, hrd, -, -⟩ := hr
  simp only [cornerC, corner31] at hN hW hJ hrd
  subst hpG
  simp only [Nock.Atoms.p, Nock.Field.p]
  refine ⟨by omega, by omega, by omega⟩

/-- `g + N ≤ 2^32` at the corner. -/
theorem g32_of_corner {r : RowsJ8} {g : ℕ} (hr : RowsLe r cornerC) (hg : g ≤ 2 ^ 31) : g + r.N ≤ 2 ^ 32 := by
  have hN := hr.1
  simp only [cornerC, corner31] at hN
  omega

end Bud

end

end Nock.NockVMROM.Thm54.VclL.Handle.RepriceJ8
