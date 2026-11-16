/-
  Measures the real cost.
-/
-- Retargeted from `Nock.Scratch.GlobalCarryRecognizer` to the promoted module: the
-- Scratch copy still declares into `Nock.GlobalCarryAxis`, so importing it alongside
-- the promoted `Nock/GlobalCarryAxis.lean` is a duplicate-declaration error.
import Nock.GlobalCarryRecognizer

namespace AtkP8a

open Nock Nock.GlobalCarryRecognizer

/-! ## 1.

    In `ZMod p_n` the cast then collapses `0` and `p_n`, both of which lie in
    `Iio Field.p`. -/

theorem hinj_is_false_at_small_primes :
    ¬ Set.InjOn (fun k : ℕ => (k : ZMod 13)) (Set.Iio Field.p) := by
  intro h
  have h0 : (0 : ℕ) ∈ Set.Iio Field.p := by
    simp only [Set.mem_Iio, Nock.Field.p]; norm_num
  have h13 : (13 : ℕ) ∈ Set.Iio Field.p := by
    simp only [Set.mem_Iio, Nock.Field.p]; norm_num
  have : (0 : ℕ) = 13 := h h0 h13 (by decide)
  omega

/-! ## 2.  `FieldEmbedding.Bounded` is `def Bounded : Noun → Prop |.atom n => n < p` with
    `p := Field.p` hard-wired.  Here is the modulus-parametric replacement plus the generalized
    soundness lemma, to show the Lean cost of the *recognizer* half is ~25 lines. -/

/-- Modulus-parametric field-noun predicate (the honest generalization of `FieldEmbedding.Bounded`). -/
def BoundedBy (q : ℕ) : Noun → Prop
  | .atom n   => n < q
  | .cell l r => BoundedBy q l ∧ BoundedBy q r

theorem boundedBy_leafList {q : ℕ} {n : Noun} (h : BoundedBy q n) :
    ∀ x ∈ n.leafList, x < q := by
  induction n with
  | atom k => intro x hx; simp only [Noun.leafList, List.mem_singleton] at hx; exact hx ▸ h
  | cell l r ihl ihr =>
      obtain ⟨hl, hr⟩ := h
      intro x hx
      simp only [Noun.leafList, List.mem_append] at hx
      rcases hx with hx | hx
      · exact ihl hl x hx
      · exact ihr hr x hx

variable {K : Type*} [Field K]

theorem leafList_map_inj' {q : ℕ}
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)) :
    ∀ {l l' : List ℕ}, (∀ x ∈ l, x < q) → (∀ x ∈ l', x < q) →
      l.map (fun k : ℕ => (k : K)) = l'.map (fun k : ℕ => (k : K)) → l = l' := by
  intro l
  induction l with
  | nil => intro l' _ _ h; cases l' with | nil => rfl | cons b bs => simp at h
  | cons a as ih =>
      intro l' hl hl' h
      cases l' with
      | nil => simp at h
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hab, htail⟩ := h
          have hab' : a = b :=
            hinj (Set.mem_Iio.mpr (hl a (by simp))) (Set.mem_Iio.mpr (hl' b (by simp))) hab
          rw [hab', ih (fun x hx => hl x (by simp [hx])) (fun x hx => hl' x (by simp [hx])) htail]

/-- **`noun_eq_of_enc_eq` at an ARBITRARY modulus `q`.**  Same proof as the Goldilocks version;
    only the bound moves.  So the recognizer-side re-parameterization really is mechanical. -/
theorem noun_eq_of_enc_eq' {q : ℕ} (z : K) (P Q : Noun)
    (hsep : SepSeed z P Q)
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbP : BoundedBy q P) (hbQ : BoundedBy q Q)
    (h : enc z P = enc z Q) : P = Q := by
  have hfield := field_noun_eq_of_sepSeed z P Q hsep h
  rw [Prod.ext_iff] at hfield
  obtain ⟨hleaf, hdyck⟩ := hfield
  have g_inj : Function.Injective (fun b : Bool => if b then (1 : K) else 0) := by
    intro a b hab
    cases a <;> cases b <;> simp only [if_true, if_false, Bool.false_eq_true] at hab <;>
      first
        | rfl
        | exact absurd hab one_ne_zero
        | exact absurd hab.symm one_ne_zero
  have hdw : P.dyckWord = Q.dyckWord :=
    List.map_injective_iff.mpr g_inj (by simpa only [NPR.dyckBits] using hdyck)
  have hll : P.leafList = Q.leafList :=
    leafList_map_inj' hinj (boundedBy_leafList hbP) (boundedBy_leafList hbQ)
      (by simpa only [NPR.leafF] using hleaf)
  exact Noun.noun_dyck_leaf_injective (by simp only [Prod.mk.injEq]; exact ⟨hdw, hll⟩)

/-! ## 3.  At a prime field `ZMod p` the generalized hypothesis IS dischargeable, with `q := p`. -/

theorem hinj_holds_at_ZMod (p : ℕ) [NeZero p] :
    Set.InjOn (fun k : ℕ => (k : ZMod p)) (Set.Iio p) := by
  intro a ha b hb hab
  have := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-! ## 4.  What the "assemble-first win" does NOT supply.

  `noun_eq_of_enc_eq` / `decompose_forces_cons` are *injectivity* statements: they take the nouns
  `P`, `L`, `R` as GIVEN and conclude `P = cell L R`.  P8d needs the opposite direction — from a
  trace of `FP K` fingerprint labels, PRODUCE a `Noun`.  No such decoder exists in the module:
  the only map is `enc : K → Noun → FP K`, and nothing inverts it. -/

noncomputable example (z : K) : Noun → ComputeTable.FP K := enc z   -- the only direction that exists

end AtkP8a

section Audit
#print axioms AtkP8a.hinj_is_false_at_small_primes
#print axioms AtkP8a.noun_eq_of_enc_eq'
#print axioms AtkP8a.hinj_holds_at_ZMod
end Audit
