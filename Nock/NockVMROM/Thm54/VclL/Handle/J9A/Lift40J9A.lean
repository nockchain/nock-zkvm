/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/Lift40J9A.lean

  `Lift40J8.Data40J8.cRows` is typed at the J-8 rows `RowVSX`; the J-9 A compute walk is over
  `RowVSX9` (`cwEvent9`, `foOf9`, `WalkTreeX9`). `DataJ8`'s summand #1 is a generic slot (`l40`, `eps40`), so the twin
  only replaces the two compute-walk summands:
  * `CW9`: the J-9 A compute walk readout (`rows : Tr → ℕ → RowVSX9`, `h ≤ N`, constant along `St40`);
  * `cwalk9`, `ctile9`: `cwEvent9` / `tileSet (foOf9 …)` at the SAME coin sets and weights (`|𝕂|·6N`, `2N + 2`:
    `cwEvent9_card_le`, `fanS9_le`);
  * `sum40A L C`: `Lift40J8.sum40 L` with summands 1–2 replaced; **`epsilon_sum40A`** = `boundVCLHQ''` (the J-8
    proof verbatim); `withLiftA`, `withLiftCA` (twins of `withLift` / `withLiftC`), `outside40CA`, `cw9_out`,
    `tile9_out`, and the eight shared summands' membership `mem_sum40A_of`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.WalkTreeX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.Lift40J9A

open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVSQ Nock.NockVMROM.Thm54.VclL.Handle.EpsFigVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8 Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8
open Nock.NockVMROM.Thm54.VclL.Events
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C sumJ8C outside_sumJ8C)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 (RowVSX9)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeX9 (cwEvent9 cwEvent9_card_le foOf9 foOf9_le)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX (tileSet tileSet_card)

noncomputable section

section Data
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ} [Fact q.Prime] [Algebra (ZMod q) K]
  (δ : K) [Fact (¬ IsSquare δ)]

local notation "𝕂′" => Quad δ

/-- **The J-9 A compute walk readout** (rows `RowVSX9`, count `≤ N`, constant along `St40`). -/
structure CW9 (Tr : Type) (St : (Coins frameJ8 K → Tr) → Prop) (r : RowsJ8) where
  rows : Tr → ℕ → RowVSX9
  h : Tr → ℕ
  h_le : ∀ tr, h tr ≤ r.N
  const : ∀ Q, St40 St Q → ∀ ψ ψ', rows (Q ψ) = rows (Q ψ') ∧ h (Q ψ) = h (Q ψ')

variable {δ} {Tr : Type} {St : (Coins frameJ8 K → Tr) → Prop} {r : RowsJ8}

/-- **#1.1 at J-9 A**: the compute walk `cwEvent9` (`(αW, γW)`, `dep = ∅`, weight `|𝕂|·6N`). -/
def cwalk9 (C : CW9 (K := K) Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  specSummandF spec1314 ∅ spec1314_disj (St40 St) (fun tr _ => cwEvent9 (K := K) (C.rows tr) (C.h tr))
    (Fintype.card K * (6 * r.N)) (fun tr _ => cwEvent9_card_le _ (C.h_le tr))
    (fun Q hQ ψ ψ' _ => by simp only [(C.const Q hQ ψ ψ').1, (C.const Q hQ ψ ψ').2])

/-- **#1.2 at J-9 A**: the `αW`-tiling at `foOf9` (coin `13`, weight `2N + 2`). -/
def ctile9 (C : CW9 (K := K) Tr St r) : BadSummand frameVSQ K Tr (St40 St) :=
  Compute.SummandsQ7.coinSummand v13 ∅ v13_not_mem (fun tr _ => tileSet (K := K) (foOf9 (C.rows tr)) (C.h tr))
    (2 * r.N + 2) (fun tr _ => (tileSet_card _ (foOf9_le _) _).trans (by have := C.h_le tr; omega))
    (fun Q hQ ψ ψ' _ => by simp only [(C.const Q hQ ψ ψ').1, (C.const Q hQ ψ ψ').2])

/-- **The J-9 A list of the 40th's class**: `sum40 L` with the compute walk summands at `C`. -/
def sum40A (L : Data40J8 (q := q) δ Tr St r) (C : CW9 (K := K) Tr St r) :
    List (BadSummand frameVSQ K Tr (St40 St)) :=
  [cwalk9 C, ctile9 C, dyckL L, wchainL L, fpxL L, zeroL L, censusL L, valL L, hxL L, hpL L]

/-- **`ε` of the J-9 A list is `boundVCLHQ''`** (the J-8 proof verbatim). -/
theorem epsilon_sum40A (L : Data40J8 (q := q) δ Tr St r) (C : CW9 (K := K) Tr St r) :
    epsilonOf (sum40A L C) = boundVCLHQ'' (Fintype.card K) (Fintype.card 𝕂′) r.N r.D r.W r.Λ := by
  have hc : (Fintype.card K : ℚ) ≠ 0 := by
    have := Fintype.card_pos (α := K); positivity
  simp only [sum40A, epsilonOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have e1 : (cwalk9 C).coins.card = 2 := rfl
  have e2 : (ctile9 C).coins.card = 1 := Finset.card_singleton _
  have e3 : (dyckL L).coins.card = 2 := Finset.card_pair (by decide)
  have e4 : (wchainL L).coins.card = 2 := rfl
  have e5 : (fpxL L).coins.card = 4 := rfl
  have e6 : (zeroL L).coins.card = 2 := Finset.card_pair (by decide)
  have e7 : (censusL L).coins.card = 2 := Finset.card_pair (by decide)
  have e8 : (valL L).coins.card = 4 := rfl
  have e9 : (hxL L).coins.card = 4 := rfl
  have e10 : (hpL L).coins.card = 4 := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  have w1 : (cwalk9 C).weight = Fintype.card K * (6 * r.N) := rfl
  have w2 : (ctile9 C).weight = 2 * r.N + 2 := rfl
  have w3 : (dyckL L).weight = r.D * (2 * fuelChip - 1) := rfl
  have w4 : (wchainL L).weight = Fintype.card K * (15 * r.W) := rfl
  have w5 : (fpxL L).weight = ioFailureUnionBound 11 r.W (2 * r.D) (Fintype.card 𝕂′) := rfl
  have w6 : (zeroL L).weight = 1 := rfl
  have w7 : (censusL L).weight = pairCount (r.D + 3) * (2 * r.Λ - 1) := rfl
  have w8 : (valL L).weight = ioFailureUnionBound 5 (3 + 2 * r.D) r.D (Fintype.card 𝕂′) := rfl
  have w9 : (hxL L).weight = ioFailureUnionBound 5 (3 * r.N + r.W) r.D (Fintype.card 𝕂′) := rfl
  have w10 : (hpL L).weight = ioFailureUnionBound 5 (2 * r.N) (2 * r.W) (Fintype.card 𝕂′) := rfl
  rw [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10]
  unfold boundVCLHQ''
  push_cast
  field_simp
  ring

variable {P g : ℕ} [Algebra Nock.Atoms.Fp (Quad δ)]

/-- **`withLiftA R L C`**: `R` with summand #1 the J-9 A list of the 40th's class. -/
def withLiftA (R : DataJ8 (q := q) δ Tr St r P) (L : Data40J8 (q := q) δ Tr St r) (C : CW9 (K := K) Tr St r) :
    DataJ8 (q := q) δ Tr St r P :=
  { R with
    Tr40 := Tr
    St40 := St40 St
    l40 := sum40A L C
    π40 := id
    hπ40 := hπ40_id St
    eps40 := epsilon_sum40A L C }

/-- **`withLiftCA`**: the `DataJ8C` twin of `withLiftC`. -/
def withLiftCA (R : DataJ8C (q := q) δ Tr St r P g) (L : Data40J8 (q := q) δ Tr St r) (C : CW9 (K := K) Tr St r) :
    DataJ8C (q := q) δ Tr St r P g :=
  { R with D := withLiftA R.D L C }

/-- Outside the list, outside every summand of the J-9 A 40th's class at `toVSQ χ`. -/
theorem outside40CA (R : DataJ8C (q := q) δ Tr St r P g) (L : Data40J8 (q := q) δ Tr St r)
    (C : CW9 (K := K) Tr St r) {tr : Tr} {χ : Coins frameJ8 K}
    (h : ∀ s ∈ allJ8C (withLiftCA R L C), ¬ s.mem tr χ) :
    ∀ s ∈ sum40A L C, ¬ s.mem tr (toVSQ χ) := by
  intro s hs hm
  have h1 := outside_sumJ8C (withLiftCA R L C) h .fortieth
  refine h1 (liftJ8 s id (hπ40_id St)) (List.mem_map.mpr ⟨s, hs, rfl⟩) ?_
  rw [mem_liftJ8]
  exact hm

theorem cw9_out (L : Data40J8 (q := q) δ Tr St r) (C : CW9 (K := K) Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40A L C, ¬ s.mem tr ψ) : (ψ v13, ψ v14) ∉ cwEvent9 (K := K) (C.rows tr) (C.h tr) := by
  have := h (cwalk9 C) (by simp [sum40A])
  erw [cwalk9, mem_specSummandF] at this; exact this

theorem tile9_out (L : Data40J8 (q := q) δ Tr St r) (C : CW9 (K := K) Tr St r) {tr : Tr} {ψ : Coins frameVSQ K}
    (h : ∀ s ∈ sum40A L C, ¬ s.mem tr ψ) : ψ v13 ∉ tileSet (K := K) (foOf9 (C.rows tr)) (C.h tr) := by
  have := h (ctile9 C) (by simp [sum40A])
  erw [ctile9, Compute.SummandsQ7.coinSummand_mem] at this; exact this

/-- The eight shared summands (#1.3 – #1.10) are in the J-9 A list. -/
theorem mem_sum40A_of (L : Data40J8 (q := q) δ Tr St r) (C : CW9 (K := K) Tr St r)
    {s : BadSummand frameVSQ K Tr (St40 St)} (hs : s ∈ (sum40 L).drop 2) : s ∈ sum40A L C := by
  simp only [sum40, List.drop_succ_cons, List.drop_zero] at hs
  simp only [sum40A, List.mem_cons] at hs ⊢
  exact Or.inr (Or.inr hs)

end Data

end

end Nock.NockVMROM.Thm54.VclL.Handle.Lift40J9A

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J9A
#print axioms epsilon_sum40A
#print axioms withLiftCA
#print axioms outside40CA
#print axioms cw9_out
#print axioms tile9_out
#print axioms mem_sum40A_of
end Axioms
