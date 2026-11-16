/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/CarrySZ.lean

  **Groundwork: the honest carries of the SZ
  identities** (completeness direction of `Nock.Atoms.ArithSZ`'s lifts).  Pure `ℤ`-list math, no chip.

  Every SZ identity of `AluSZChipJ9` has the shape `Σ_k d_k·y^k = (B − y)·Σ_k q_k·y^k` (the Q block contributes
  `(y − B)·H_Q`, `H_Q = Σ q_k y^k`), where `d_k` is a coefficient of the op's integer polynomial, which vanishes at
  `X = B` on an honest call.  This module proves:
  * **`carry_id`**: if `Σ d_k·B^k = 0` (`evB B ds = 0`), the running carries `carr B 0 ds` satisfy the identity
    `evR y ds = (B − y)·evR y (carr B 0 ds)` in EVERY commutative ring at EVERY `y`: the identity holds as a
    polynomial identity, so the SZ summand costs completeness nothing.
  * **`carr_bound`**: the carries lie in `[0, M]` when every coefficient satisfies `−B < d` and `d + M < B·(M+1)`
    (`M = 1` for add/sub, the 1-bit Q block; `M = 2^25 − 1` for mul, the 25-bit Q block).
  * `carr_length`: one carry per coefficient.
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CarrySZ

/-- `Σ_k d_k·B^k` (Horner, low coefficient first). -/
def evB (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | d :: ds => d + B * evB B ds

/-- `Σ_k d_k·y^k` in a commutative ring (Horner, low coefficient first). -/
def evR {R : Type} [CommRing R] (y : R) : List ℤ → R
  | [] => 0
  | d :: ds => (d : R) + y * evR y ds

/-- **The running carries** from an incoming carry `c`: `q_k = (q_{k−1} + d_k) / B`. -/
def carr (B : ℤ) : ℤ → List ℤ → List ℤ
  | _, [] => []
  | c, d :: ds => (c + d) / B :: carr B ((c + d) / B) ds

theorem carr_length (B : ℤ) : ∀ (c : ℤ) (ds : List ℤ), (carr B c ds).length = ds.length
  | _, [] => rfl
  | c, d :: ds => by simp [carr, carr_length B _ ds]

/-- One step: the incoming carry plus the coefficient is divisible by `B`, and the outgoing carry restarts the
invariant. -/
theorem carr_step {B : ℤ} (hB : B ≠ 0) {c d : ℤ} {ds : List ℤ} (h : c + evB B (d :: ds) = 0) :
    c + d = B * ((c + d) / B) ∧ (c + d) / B + evB B ds = 0 := by
  have h' : c + d = B * (-evB B ds) := by simp only [evB] at h; linarith
  have hq : (c + d) / B = -evB B ds := by rw [h']; exact Int.mul_ediv_cancel_left _ hB
  exact ⟨by rw [hq]; exact h', by rw [hq]; ring⟩

/-- **The carry identity** at an incoming carry `c` with `c + Σ d_k B^k = 0`. -/
theorem carry_id_from {B : ℤ} (hB : B ≠ 0) {R : Type} [CommRing R] (y : R) :
    ∀ (ds : List ℤ) (c : ℤ), c + evB B ds = 0 →
      (c : R) + evR y ds = ((B : R) - y) * evR y (carr B c ds)
  | [], c, h => by
    have : c = 0 := by simpa [evB] using h
    simp [evR, carr, this]
  | d :: ds, c, h => by
    obtain ⟨hcd, hrest⟩ := carr_step hB h
    have ih := carry_id_from hB y ds _ hrest
    have hcdR : ((c : ℤ) : R) + (d : R) = (B : R) * (((c + d) / B : ℤ) : R) := by
      have := congrArg (fun z : ℤ => (z : R)) hcd
      push_cast at this
      exact this
    simp only [evR, carr]
    linear_combination hcdR + y * ih

/-- **`carry_id`: the SZ identity holds as a polynomial identity** when the coefficients vanish at `B`. -/
theorem carry_id {B : ℤ} (hB : B ≠ 0) {R : Type} [CommRing R] (y : R) (ds : List ℤ) (h : evB B ds = 0) :
    evR y ds = ((B : R) - y) * evR y (carr B 0 ds) := by
  have := carry_id_from hB y ds 0 (by simpa using h)
  simpa using this

/-- **`carr_bound`: the carries lie in `[0, M]`** when the incoming carry does and every coefficient satisfies
`−B < d`, `d + M < B·(M + 1)`. -/
theorem carr_bound {B M : ℤ} (hB : 0 < B) :
    ∀ (ds : List ℤ) (c : ℤ), c + evB B ds = 0 → 0 ≤ c → c ≤ M →
      (∀ d ∈ ds, -B < d ∧ d + M < B * (M + 1)) → ∀ q ∈ carr B c ds, 0 ≤ q ∧ q ≤ M
  | [], _, _, _, _, _, q, hq => by simp [carr] at hq
  | d :: ds, c, h, h0, hM, hd, q, hq => by
    obtain ⟨hcd, hrest⟩ := carr_step hB.ne' h
    have hdd := hd d (List.mem_cons_self ..)
    have hq0 : 0 ≤ (c + d) / B := by
      by_contra hneg
      replace hneg := not_le.mp hneg
      have : B * ((c + d) / B) ≤ B * (-1) := by
        exact mul_le_mul_of_nonneg_left (by omega) hB.le
      linarith
    have hqM : (c + d) / B ≤ M := by
      by_contra hbig
      replace hbig := not_le.mp hbig
      have : B * (M + 1) ≤ B * ((c + d) / B) := mul_le_mul_of_nonneg_left (by omega) hB.le
      linarith
    simp only [carr, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨hq0, hqM⟩
    · exact carr_bound hB ds _ hrest hq0 hqM (fun d' hd' => hd d' (List.mem_cons_of_mem _ hd')) q hq

/-- The carries from `0`, bounded (`carr_bound` at `c = 0`). -/
theorem carr_bound0 {B M : ℤ} (hB : 0 < B) (hM : 0 ≤ M) (ds : List ℤ) (h : evB B ds = 0)
    (hd : ∀ d ∈ ds, -B < d ∧ d + M < B * (M + 1)) : ∀ q ∈ carr B 0 ds, 0 ≤ q ∧ q ≤ M :=
  carr_bound hB ds 0 (by simpa using h) le_rfl hM hd

/-! ## Coefficient lists of the additive identities -/

/-- `evB` is additive in the coefficient lists (zero-padded `zipWith`). -/
def addL : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addL as bs

def negL (as : List ℤ) : List ℤ := as.map fun a => -a

theorem evB_addL (B : ℤ) : ∀ as bs : List ℤ, evB B (addL as bs) = evB B as + evB B bs
  | [], bs => by simp [addL, evB]
  | a :: as, [] => by simp [addL, evB]
  | a :: as, b :: bs => by simp only [addL, evB, evB_addL B as bs]; ring

theorem evR_addL {R : Type} [CommRing R] (y : R) :
    ∀ as bs : List ℤ, evR y (addL as bs) = evR y as + evR y bs
  | [], bs => by simp [addL, evR]
  | a :: as, [] => by simp [addL, evR]
  | a :: as, b :: bs => by simp only [addL, evR, evR_addL y as bs]; push_cast; ring

theorem evB_negL (B : ℤ) : ∀ as : List ℤ, evB B (negL as) = -evB B as
  | [] => by simp [negL, evB]
  | a :: as => by simp only [negL, List.map_cons, evB] at *; rw [show evB B (as.map fun a => -a) = -evB B as from
      evB_negL B as]; ring

theorem evR_negL {R : Type} [CommRing R] (y : R) : ∀ as : List ℤ, evR y (negL as) = -evR y as
  | [] => by simp [negL, evR]
  | a :: as => by
    simp only [negL, List.map_cons, evR] at *
    rw [show evR y (as.map fun a => -a) = -evR y as from evR_negL y as]; push_cast; ring

/-- Membership in `addL`: an entry is a sum of at most one entry of each side. -/
theorem mem_addL_bound (P : ℤ → Prop) (as bs : List ℤ)
    (h : ∀ x, (x = 0 ∨ x ∈ as) → ∀ z, (z = 0 ∨ z ∈ bs) → P (x + z)) : ∀ d ∈ addL as bs, P d := by
  induction as generalizing bs with
  | nil => intro d hd; simpa using h 0 (Or.inl rfl) d (Or.inr hd)
  | cons a as ih =>
    cases bs with
    | nil => intro d hd; simpa using h d (Or.inr hd) 0 (Or.inl rfl)
    | cons b bs =>
      intro d hd
      simp only [addL, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact h a (Or.inr (List.mem_cons_self ..)) b (Or.inr (List.mem_cons_self ..))
      · exact ih bs (fun x hx z hz => h x (hx.imp_right (List.mem_cons_of_mem _))
          z (hz.imp_right (List.mem_cons_of_mem _))) d hd

end Nock.NockVMROM.Thm54.VclL.Handle.CarrySZ

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.CarrySZ
#print axioms carry_id
#print axioms carr_bound0
#print axioms evB_addL
#print axioms evR_addL
#print axioms mem_addL_bound
end Axioms
