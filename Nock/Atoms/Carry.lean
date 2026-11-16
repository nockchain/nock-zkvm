/-
  Nock/Atoms/Carry.lean

  **The local-carry lemma for op 4 (`+1`) on big atoms.**

  * `Carry cin l l′` — the per-position relation, as an inductive over the limb lists (little
    endian; `nil0` = the chain ends with no carry, `nil1` = overflow appends the top limb `1`).
  * `carry_val` — **`val l′ = val l + cin`**; so `Carry 1 l l′ → val l′ = val l + 1` (`inc_val`).
  * `carry_zero_eq` — **tail sharing**: with `c_in = 0` and limbs `< B`, `l′ = l`; `Carry.stop` —
    the chain stops (`c_out = 0`) with the old tail reused verbatim.
  * `carry_canonical` — **canonical form is preserved**.
  * `carry_cout` / `carry_det` — **uniqueness**: each carry is determined (`c_out = (l + c_in)/B`)
    and so is the result list.
  * `carry_exists` / `inc_eq_limbs` — completeness: a canonical `l` has its `+1` chain, and it is
    `limbs (val l + 1)`.
  * `inc_big` — big stays big; `crossing` — the boundary `p − 1 ↦ p`, `[0, B−1] ↦ [1, B−1]`.
-/
import Nock.Atoms.Limbs

set_option autoImplicit false

namespace Nock.Atoms

/-- **The local carry relation.**  `Carry cin l l′`: adding the carry `cin ∈ {0,1}` into the limb
list `l` gives `l′`, position by position: `l′ᵢ + B·c_outᵢ = lᵢ + c_inᵢ`, `l′ᵢ < B`, carries
boolean, `c_inᵢ₊₁ = c_outᵢ`; past the top limb a carry `1` appends the limb `1`. -/
inductive Carry : ℕ → List ℕ → List ℕ → Prop
  | nil0 : Carry 0 [] []
  | nil1 : Carry 1 [] [1]
  | cons {cin cout a a' : ℕ} {l l' : List ℕ} :
      cin ≤ 1 → cout ≤ 1 → a' < B → a' + B * cout = a + cin → Carry cout l l' →
        Carry cin (a :: l) (a' :: l')

/-- **Value**: `val l′ = val l + cin`. -/
theorem carry_val {cin : ℕ} {l l' : List ℕ} (h : Carry cin l l') : val l' = val l + cin := by
  induction h with
  | nil0 => simp
  | nil1 => simp
  | cons _ _ _ he _ ih => simp only [val_cons, ih]; rw [Nat.mul_add]; omega

theorem inc_val {l l' : List ℕ} (h : Carry 1 l l') : val l' = val l + 1 := carry_val h

/-- **Tail sharing**: with no carry in and limbs `< B`, the chain reproduces its input. -/
theorem carry_zero_eq {l l' : List ℕ} (hl : ∀ a ∈ l, a < B) (h : Carry 0 l l') : l' = l := by
  generalize hc : (0 : ℕ) = c at h
  induction h with
  | nil0 => rfl
  | nil1 => exact absurd hc (by decide)
  | @cons cin cout a a' l l' _ hco ha' he _ ih =>
    subst hc
    have ha := hl a (by simp)
    have hcout : cout = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hco with h0 | h1
      · exact h0
      · subst h1; omega
    subst hcout
    have : a' = a := by omega
    rw [this, ih (fun x hx => hl x (by simp [hx])) rfl]

/-- The chain stops: no carry out, the new tail is the OLD tail (one shared row). -/
theorem Carry.stop {cin a a' : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, x < B) (hcin : cin ≤ 1)
    (ha' : a' < B) (he : a' = a + cin) : Carry cin (a :: l) (a' :: l) := by
  refine Carry.cons hcin (le_of_lt Nat.zero_lt_one) ha' (by simpa using he) ?_
  clear he
  induction l with
  | nil => exact Carry.nil0
  | cons x l ih =>
    exact Carry.cons (Nat.zero_le _) (Nat.zero_le _) (hl x (by simp)) (by simp)
      (ih (fun y hy => hl y (by simp [hy])))

/-- **Uniqueness of the carries**: `c_out = (l + c_in) / B`, `l′ = (l + c_in) % B`. -/
theorem carry_cout {cin cout a a' : ℕ} (ha' : a' < B) (he : a' + B * cout = a + cin) :
    cout = (a + cin) / B ∧ a' = (a + cin) % B := by
  have hB : 0 < B := by norm_num [B]
  constructor
  · rw [← he, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt ha', zero_add]
  · rw [← he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha']

/-- **The result of the chain is determined.** -/
theorem carry_det {cin : ℕ} {l l₁ l₂ : List ℕ} (h₁ : Carry cin l l₁) (h₂ : Carry cin l l₂) :
    l₁ = l₂ := by
  induction h₁ generalizing l₂ with
  | nil0 => cases h₂; rfl
  | nil1 => cases h₂; rfl
  | cons _ _ ha' he _ ih =>
    cases h₂ with
    | cons _ _ hb' he' hr =>
      obtain ⟨c1, a1⟩ := carry_cout ha' he
      obtain ⟨c2, a2⟩ := carry_cout hb' he'
      subst c1 c2
      rw [a1, a2, ih hr]

/-- `getLast` of a list with at least two elements is the `getLast` of its tail. -/
theorem getLast_cons_cons' {a b : ℕ} {l : List ℕ} (h : (a :: b :: l) ≠ []) :
    (a :: b :: l).getLast h = (b :: l).getLast (by simp) := List.getLast_cons_cons

/-- **Canonical form is preserved** by the carry chain. -/
theorem carry_canonical {cin : ℕ} {l l' : List ℕ} (h : Carry cin l l') (hc : Canonical l) :
    Canonical l' := by
  induction h with
  | nil0 => exact hc
  | nil1 => exact ⟨by simp [B], by simp⟩
  | @cons cin cout a a' l l' hcin hco ha' he hr ih =>
    have hcl : Canonical l := ⟨fun x hx => hc.1 x (by simp [hx]),
      fun hne => by
        have := hc.2 (by simp)
        obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hne
        rwa [getLast_cons_cons'] at this⟩
    have ihl := ih hcl
    refine ⟨?_, fun _ => ?_⟩
    · intro x hx
      simp at hx
      rcases hx with rfl | hx
      · exact ha'
      · exact ihl.1 x hx
    · cases l' with
      | cons b t => rw [getLast_cons_cons']; exact ihl.2 (by simp)
      | nil =>
        -- the chain ended here with no appended limb: `cout = 0`, `l = []`
        cases hr
        have htop := hc.2 (by simp)
        simp at htop ⊢
        omega

/-- **Completeness**: every limb list with limbs `< B` has its carry chain. -/
theorem carry_exists {cin : ℕ} (hcin : cin ≤ 1) :
    ∀ {l : List ℕ}, (∀ a ∈ l, a < B) → ∃ l', Carry cin l l' := by
  intro l
  induction l generalizing cin with
  | nil =>
    intro _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcin with rfl | rfl
    · exact ⟨_, Carry.nil0⟩
    · exact ⟨_, Carry.nil1⟩
  | cons a l ih =>
    intro hl
    have ha := hl a (by simp)
    have hB : 0 < B := by norm_num [B]
    have hco : (a + cin) / B ≤ 1 := by
      rw [Nat.div_le_iff_le_mul_add_pred hB]; omega
    obtain ⟨l', hr⟩ := ih hco (fun x hx => hl x (by simp [hx]))
    refine ⟨(a + cin) % B :: l', Carry.cons hcin hco (Nat.mod_lt _ hB) ?_ hr⟩
    rw [Nat.mod_add_div]

/-- **The `+1` chain of a canonical atom is the canonical form of its successor.** -/
theorem inc_eq_limbs {l l' : List ℕ} (hc : Canonical l) (h : Carry 1 l l') :
    l' = limbs (val l + 1) := by
  rw [← inc_val h, limbs_val (carry_canonical h hc)]

/-- Big stays big under `+1`. -/
theorem inc_big {l l' : List ℕ} (h : Carry 1 l l') (hb : IsBig (val l)) : IsBig (val l') := by
  unfold IsBig at *; rw [inc_val h]; omega

/-- **The boundary crossing** `p − 1 ↦ p`: `[0, B−1] ↦ [1, B−1]`, a one-row stop. -/
theorem crossing : Carry 1 (limbs (p - 1)) (limbs p) := by
  rw [limbs_p_sub_one, limbs_p]
  exact Carry.stop (by intro x hx; simp at hx; subst hx; norm_num [B]) le_rfl (by norm_num [B])
    (by simp)

/-- The growth case: `[B−1, …, B−1] ↦ [0, …, 0, 1]` (one limb longer). -/
theorem carry_all_top (k : ℕ) :
    Carry 1 (List.replicate k (B - 1)) (List.replicate k 0 ++ [1]) := by
  induction k with
  | zero => exact Carry.nil1
  | succ k ih =>
    exact Carry.cons le_rfl le_rfl (by norm_num [B]) (by norm_num [B]) ih

end Nock.Atoms
