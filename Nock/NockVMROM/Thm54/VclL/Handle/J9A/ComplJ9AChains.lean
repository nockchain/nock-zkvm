/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9AChains.lean

  **J-9 A: the honest axis chains.**  `segN` (the noun after chain row `j`), `chainOf` (the `ChainSpec` of an
  axis read), `chainOf_OK`, the side facts at Goldilocks, and the id map `idOf9`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AAxisRows
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AGen
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AData
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9ABinders

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains

open Nock
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (Bf)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (segX)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (AxCap)
open Nock.J9A.NounAx (top segAx segRd nxtAx segAx_decomp segAx_next segRd_pos nxtAx_lt_pow top_eq_length
  slot_atom_none)

/-- The noun after chain row `j`. -/
def segN (n : ℕ) (X : Noun) : ℕ → Noun
  | 0 => segX n (top n) X
  | j + 1 => segX n (top n - (j + 1)) (segN n X j)

/-- The noun before chain row `k`. -/
def curN (n : ℕ) (X : Noun) : ℕ → Noun
  | 0 => X
  | k + 1 => segN n X k

theorem segN_eq (n : ℕ) (X : Noun) (k : ℕ) : segN n X k = segX n (top n - k) (curN n X k) := by
  cases k <;> simp [segN, curN]

/-- The honest chain of an axis read `n` from `X`. -/
def chainOf {F : Type} [Field F] (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun) :
    ComplJ9AAxisRows.ChainSpec F where
  ls := Nock.Atoms.limbs n
  route0 := route0
  R := R
  hrv := (H X).2
  vv := n
  mu := mu
  g4 := if route0 then (((n / 2 ^ 32 : ℕ) : F) - (Bf - 1))⁻¹ else 0
  houts := fun j => H (segN n X j)

/-! ## limbs -/

theorem digits_getD (b : ℕ) (hb : 1 < b) : ∀ (i n : ℕ), (Nat.digits b n).getD i 0 = n / b ^ i % b := by
  intro i
  induction i with
  | zero =>
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' hb hn]; simp
  | succ i ih =>
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.digits_def' hb hn]
      simp only [List.getD_cons_succ]
      rw [ih, Nat.div_div_eq_div_mul, pow_succ, mul_comm b]

theorem limbs_getD (n i : ℕ) : (Nock.Atoms.limbs n).getD i 0 = n / 2 ^ (32 * i) % 2 ^ 32 := by
  have := digits_getD (2 ^ 32) (by norm_num) i n
  rw [← pow_mul] at this
  simpa [Nock.Atoms.limbs, Nock.Atoms.B] using this

/-! ## the invariant -/

theorem slot_seg (n m : ℕ) (X : Noun) (hn : n ≠ 0) (hm : m ≤ top n) :
    Noun.slot (segAx n m) X = (Noun.slot (segRd n m) X).bind (Noun.slot (nxtAx n m)) := by
  rw [segAx_decomp n m hm, Nock.J9A.NounComp.slot_comp _ _ _ _ (segRd_pos hn m hm) (nxtAx_lt_pow n m)]
  rfl

theorem chain_inv (n : ℕ) (X Y : Noun) (hn : n ≠ 0) (hX : Noun.slot n X = some Y) :
    ∀ k, k ≤ top n → Noun.slot (segAx n (top n - k)) (curN n X k) = some Y := by
  intro k
  induction k with
  | zero => intro _; simpa [curN, Nock.J9A.NounAx.segAx_top] using hX
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := slot_seg n (top n - k) (curN n X k) hn (by omega)
    rw [h1] at h2
    cases hs : Noun.slot (segRd n (top n - k)) (curN n X k) with
    | none => rw [hs] at h2; simp at h2
    | some Z =>
      rw [hs] at h2
      simp only [Option.bind_some] at h2
      have h3 : segN n X k = Z := by rw [segN_eq, segX, hs]; rfl
      have h4 : segAx n (top n - (k + 1)) = nxtAx n (top n - k) := by
        rw [← segAx_next n (top n - k) (by omega) (by omega)]
        congr 1
      show Noun.slot (segAx n (top n - (k + 1))) (segN n X k) = some Y
      rw [h3, h4]; exact h2.symm

theorem segN_cell (n : ℕ) (X Y : Noun) (hn : n ≠ 0) (hX : Noun.slot n X = some Y) (k : ℕ)
    (hk : k + 1 ≤ top n) : ∃ a b, segN n X k = .cell a b := by
  have h := chain_inv n X Y hn hX (k + 1) hk
  have hne : segAx n (top n - (k + 1)) ≠ segAx n (top n) ∨ True := Or.inr trivial
  have h2 : 2 ≤ segAx n (top n - (k + 1)) := by
    have : top n - (k + 1) ≠ top n := by omega
    simp only [segAx, this, ite_false]
    have : 2 ^ 32 ≤ 2 ^ (32 * (top n - (k + 1) + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ 32 ≥ 2 := by norm_num
    omega
  cases hc : segN n X k with
  | cell a b => exact ⟨a, b, rfl⟩
  | atom m =>
    have h' : Noun.slot (segAx n (top n - (k + 1))) (curN n X (k + 1)) = some Y := h
    simp only [curN, hc] at h'
    rw [slot_atom_none m _ h2] at h'
    simp at h'

theorem cell_of_slot (n : ℕ) (X Y : Noun) (hn : 2 ≤ n) (hX : Noun.slot n X = some Y) :
    ∃ a b, X = .cell a b := by
  cases X with
  | cell a b => exact ⟨a, b, rfl⟩
  | atom m => rw [slot_atom_none m n hn] at hX; simp at hX

theorem field_limbs (n : ℕ) (hn : 2 ^ 32 ≤ n) (hp : n < Nock.Atoms.p) :
    n < 2 ^ 64 ∧ n / 2 ^ 32 < 2 ^ 32 ∧ (Nock.Atoms.limbs n).getD 0 0 = n % 2 ^ 32 ∧
      (Nock.Atoms.limbs n).getD 1 0 = n / 2 ^ 32 := by
  have hlt : n < 2 ^ 64 := by
    have : Nock.Atoms.p < 2 ^ 64 := by norm_num [Nock.Atoms.p, Nock.Field.p]
    omega
  have hhi : n / 2 ^ 32 < 2 ^ 32 := by
    apply Nat.div_lt_of_lt_mul
    have : (2 : ℕ) ^ 32 * 2 ^ 32 = 2 ^ 64 := by norm_num
    omega
  refine ⟨hlt, hhi, ?_, ?_⟩
  · simpa using limbs_getD n 0
  · rw [limbs_getD]; simpa using Nat.mod_eq_of_lt hhi

/-! ## chainOf_OK -/

theorem chainOf_OK {F : Type} [Field F] (H : Noun → ℕ × ℕ) (route0 : Bool) (R n mu : ℕ) (X : Noun)
    (hH : ∀ a b, (H (.cell a b)).1 = 1) (hn : 2 ^ 32 ≤ n) (hX : ∃ Y, Noun.slot n X = some Y)
    (hr : route0 = true → n < Nock.Atoms.p) (hch : route0 = true → 2 ^ 32 < ringChar F) :
    (chainOf (F := F) H route0 R n mu X).OK := by
  obtain ⟨Y, hY⟩ := hX
  have hn0 : n ≠ 0 := by have : 0 < 2 ^ 32 := by norm_num
                         omega
  have hlen : (Nock.Atoms.limbs n).length = top n + 1 := top_eq_length n hn0
  have htop : 1 ≤ top n := Nat.log_pos (by norm_num) hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 2 ≤ (Nock.Atoms.limbs n).length
    omega
  · intro hz
    show H (segN n X 0) = (1, (H X).2)
    have hz' : (Nock.Atoms.limbs n).getD ((Nock.Atoms.limbs n).length - 1) 0 = 1 := hz
    rw [hlen, Nat.add_sub_cancel, limbs_getD] at hz'
    have h1 : segRd n (top n) = 1 := by simpa [segRd] using hz'
    have h2 : segN n X 0 = X := by simp [segN, segX, h1, Noun.slot]
    have hc := cell_of_slot n X Y (by omega) hY
    obtain ⟨a, b, rfl⟩ := hc
    rw [h2]
    exact Prod.ext (hH a b) rfl
  · intro k hk
    have hk' : k + 1 ≤ top n := by
      have : k + 1 < (chainOf (F := F) H route0 R n mu X).ls.length := hk
      simp only [chainOf] at this
      omega
    obtain ⟨a, b, hab⟩ := segN_cell n X Y hn0 hY k hk'
    show (H (segN n X k)).1 = 1
    rw [hab]; exact hH a b
  · intro h0
    show (Nock.Atoms.limbs n).length = 2
    have hp := hr h0
    have hlt : n < 2 ^ 64 := by
      have : Nock.Atoms.p < 2 ^ 64 := by norm_num [Nock.Atoms.p, Nock.Field.p]
      omega
    have : top n = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num; omega) (by norm_num; omega)
    omega
  · intro h0
    obtain ⟨hlt, hhi, hg0, hg1⟩ := field_limbs n hn (hr h0)
    show (Nock.Atoms.limbs n).getD 0 0 = 0 ∨ (((Nock.Atoms.limbs n).getD 1 0 : ℕ) - (Bf - 1) : F) *
      (if route0 then (((n / 2 ^ 32 : ℕ) : F) - (Bf - 1))⁻¹ else 0) = 1
    have h0' : route0 = true := h0
    rw [hg0, hg1]
    simp only [h0', ite_true]
    by_cases he : n / 2 ^ 32 = 2 ^ 32 - 1
    · left
      have hp := hr h0
      have := Nat.div_add_mod n (2 ^ 32)
      simp only [Nock.Atoms.p, Nock.Field.p] at hp
      omega
    · right
      apply mul_inv_cancel₀
      intro h
      obtain ⟨d, hd⟩ : ∃ d, n / 2 ^ 32 + d + 1 = 2 ^ 32 := ⟨2 ^ 32 - 1 - n / 2 ^ 32, by omega⟩
      have hcast : ((n / 2 ^ 32 : ℕ) : F) + (d : F) + 1 = (2 : F) ^ 32 := by exact_mod_cast congrArg (Nat.cast : ℕ → F) hd
      have hdz : (d : F) = 0 := by
        unfold Bf at h
        linear_combination hcast - h
      have hdv : ringChar F ∣ d := (ringChar.spec F d).1 hdz
      have hdpos : 0 < d := by omega
      have := Nat.le_of_dvd hdpos hdv
      have := hch h0
      omega
  · intro h0
    obtain ⟨hlt, hhi, hg0, hg1⟩ := field_limbs n hn (hr h0)
    show ((n : ℕ) : F) = (((Nock.Atoms.limbs n).getD 1 0 : ℕ) : F) * Bf + (((Nock.Atoms.limbs n).getD 0 0 : ℕ) : F)
    rw [hg0, hg1]
    have := Nat.div_add_mod n (2 ^ 32)
    unfold Bf
    have h2 : ((n : ℕ) : F) = (((2 ^ 32 * (n / 2 ^ 32) + n % 2 ^ 32 : ℕ)) : F) := by rw [this]
    rw [h2]; push_cast; ring

/-! ## Goldilocks side facts -/

theorem hp32_of_G {p : ℕ} (hpG : p = Nock.Atoms.p) : 2 ^ 32 < p := by
  rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]

theorem hp63_of_G {p : ℕ} (hpG : p = Nock.Atoms.p) : 2 ^ 63 < p := by
  rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]

theorem lt64_of_G {p : ℕ} (hpG : p = Nock.Atoms.p) {n : ℕ} (h : n < p) : n < 2 ^ 64 := by
  have : p < 2 ^ 64 := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  omega

theorem top_lt_62 {n : ℕ} (hcap : AxCap n) (hn : n ≠ 0) : top n < 62 := by
  have h := top_eq_length n hn
  have : (Nock.Atoms.limbs n).length ≤ 62 := hcap
  omega

theorem le_top_lt_63 {n : ℕ} (hcap : AxCap n) (hn : n ≠ 0) {m : ℕ} (hm : m ≤ top n) : m < 63 := by
  have := top_lt_62 hcap hn
  omega

theorem field_split_range {p : ℕ} (hpG : p = Nock.Atoms.p) {v : ℕ} (h : 2 ^ 62 ≤ v ∧ v < p) :
    2 ^ 32 ≤ v ∧ v < 2 ^ 64 := by
  refine ⟨?_, lt64_of_G hpG h.2⟩
  have : (2 : ℕ) ^ 32 ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

/-! ## The id map -/

/-- The id of an axis atom `n`: a big atom's atom-table root (`H`), a field atom `nA + index`. -/
def idOf9 (p nA : ℕ) (H : Noun → ℕ × ℕ) (fx : List ℕ) (n : ℕ) : ℕ :=
  if p ≤ n then (H (.atom n)).2 else nA + fx.idxOf n

theorem idOf9_big {p nA : ℕ} {H : Noun → ℕ × ℕ} {fx : List ℕ} {n : ℕ} (h : p ≤ n) :
    idOf9 p nA H fx n = (H (.atom n)).2 := by
  simp [idOf9, h]

theorem idOf9_field {p nA : ℕ} {H : Noun → ℕ × ℕ} {fx : List ℕ} {n : ℕ} (h : n < p) :
    idOf9 p nA H fx n = nA + fx.idxOf n := by
  simp [idOf9, Nat.not_le.2 h]

theorem idxOf_lt {fx : List ℕ} {n : ℕ} (h : n ∈ fx) : fx.idxOf n < fx.length :=
  List.idxOf_lt_length_iff.2 h

section Axioms
#print axioms segN_eq
#print axioms digits_getD
#print axioms limbs_getD
#print axioms slot_seg
#print axioms chain_inv
#print axioms segN_cell
#print axioms cell_of_slot
#print axioms field_limbs
#print axioms chainOf_OK
#print axioms hp32_of_G
#print axioms hp63_of_G
#print axioms lt64_of_G
#print axioms top_lt_62
#print axioms le_top_lt_63
#print axioms field_split_range
#print axioms idOf9_big
#print axioms idOf9_field
#print axioms idxOf_lt
end Axioms

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains
