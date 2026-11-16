import Nock.GlobalCarryAxis
import Nock.MemoryTable
import Nock.NounValidation
import Nock.FieldEmbedding

/-!
# NPR global-carry recognizer bridge

This production module connects the globally anchored axis tree to NPR fingerprints and the
memory/compute-table cons equations.  The collision-sensitive structural bridge is parameterized
by an arbitrary numeric leaf bound `q`; the previous Goldilocks statements remain available as
corollaries using `FieldEmbedding.Bounded`.

The result supplies fingerprint uniqueness (off the stated `SepSeed` bad event), structural cons
decomposition, and axis/formula soundness.  It deliberately does **not** define a decoder
`ComputeTable.FP K → Noun`: soundness starts from nouns whose encodings occupy the relevant rows.
-/

namespace Nock
namespace GlobalCarryRecognizer

open Nock (Noun)
open Polynomial
open scoped Classical

section Enc

variable {K : Type*} [Field K]

/-- The NPR noun fingerprint in memory/compute-table field order `(size,dyck,leaf)`. -/
noncomputable def enc (z : K) (n : Noun) : ComputeTable.FP K where
  size := z ^ n.leaves
  dyck := (NPR.listPoly (NPR.dyckBits (K := K) n)).eval z
  leaf := (NPR.listPoly (NPR.leafF (K := K) n)).eval z

@[simp] theorem enc_size (z : K) (n : Noun) : (enc z n).size = z ^ n.leaves := rfl

@[simp] theorem enc_dyck (z : K) (n : Noun) :
    (enc z n).dyck = (NPR.listPoly (NPR.dyckBits (K := K) n)).eval z := rfl

@[simp] theorem enc_leaf (z : K) (n : Noun) :
    (enc z n).leaf = (NPR.listPoly (NPR.leafF (K := K) n)).eval z := rfl

/-- `enc` is `NPR.fn`, with dyck and leaf components reordered to `FP` order. -/
theorem enc_eq_fn (z : K) (n : Noun) :
    enc z n = ⟨(NPR.fn n z).1, (NPR.fn n z).2.2, (NPR.fn n z).2.1⟩ := by
  simp only [enc, NPR.fn]

/-- NPR decomposition is exactly the `FP.cons` homomorphism at a nonzero seed. -/
theorem enc_cons {z : K} (hz : z ≠ 0) (x y : Noun) :
    enc z (Noun.cell x y) = ComputeTable.FP.cons z (enc z x) (enc z y) := by
  have hx1 : 1 ≤ x.leaves := x.one_le_leaves
  have hpow2 : z ^ x.leaves * z ^ x.leaves = z ^ (2 * x.leaves) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow1 : z ^ x.leaves * z ^ x.leaves * z⁻¹ = z ^ (2 * x.leaves - 1) := by
    have hstep : z ^ (2 * x.leaves - 1) * z = z ^ (2 * x.leaves) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow2, ← hstep, mul_assoc, mul_inv_cancel₀ hz, mul_one]
  have h3 : NPR.listPoly (NPR.dyckBits (K := K) (Noun.cell x y))
      = X * NPR.listPoly (NPR.dyckBits (K := K) x) + X ^ (2 * x.leaves - 1)
        + X ^ (2 * x.leaves) * NPR.listPoly (NPR.dyckBits (K := K) y) := by
    simpa only [NPR.Φ_snd_snd] using NPR.Phi3_cons (K := K) x y
  have h2 : NPR.listPoly (NPR.leafF (K := K) (Noun.cell x y))
      = NPR.listPoly (NPR.leafF (K := K) x)
        + X ^ x.leaves * NPR.listPoly (NPR.leafF (K := K) y) := by
    simpa only [NPR.Φ_snd_fst] using NPR.Phi2_cons (K := K) x y
  refine ComputeTable.FP.ext ?_ ?_ ?_
  · simp only [enc_size, Noun.leaves, ComputeTable.FP.cons, pow_add]
  · simp only [enc_dyck, enc_size, ComputeTable.FP.cons]
    rw [h3]
    simp only [eval_add, eval_mul, eval_X, eval_X_pow]
    rw [hpow1, hpow2]
  · simp only [enc_leaf, enc_size, ComputeTable.FP.cons]
    rw [h2]
    simp only [eval_add, eval_mul, eval_X_pow]

/-- Atom encodings agree with the table's atom fingerprint. -/
theorem enc_atom (z : K) (k : ℕ) : enc z (Noun.atom k) = ComputeTable.FP.atomFP z (k : K) := by
  have hdyck : NPR.dyckBits (K := K) (Noun.atom k) = [] := by
    simp [NPR.dyckBits, Noun.dyckWord, Noun.shape, Nock.BTree.encode]
  have hleaf : NPR.leafF (K := K) (Noun.atom k) = [(k : K)] := by
    simp [NPR.leafF, Noun.leafList]
  refine ComputeTable.FP.ext ?_ ?_ ?_
  · simp [enc_size, Noun.leaves, ComputeTable.FP.atomFP]
  · simp [enc_dyck, hdyck, ComputeTable.FP.atomFP]
  · simp [enc_leaf, hleaf, NPR.listPoly_cons, ComputeTable.FP.atomFP]

/-- Equality of `enc` values implies equality of `NPR.fn` values. -/
theorem enc_eq_imp_fn_eq (z : K) (P Q : Noun) (h : enc z P = enc z Q) :
    NPR.fn P z = NPR.fn Q z := by
  have hs := congrArg ComputeTable.FP.size h
  have hd := congrArg ComputeTable.FP.dyck h
  have hl := congrArg ComputeTable.FP.leaf h
  simp only [enc_size, enc_dyck, enc_leaf] at hs hd hl
  simp only [NPR.fn]
  exact Prod.ext hs (Prod.ext hl hd)

end Enc

section Collision

variable {K : Type*} [Field K]

/-- The good event that `z` separates distinct NPR leaf/dyck data for `P` and `Q`. -/
def SepSeed (z : K) (P Q : Noun) : Prop :=
  (NPR.leafF (K := K) P, NPR.dyckBits (K := K) P)
      ≠ (NPR.leafF (K := K) Q, NPR.dyckBits (K := K) Q) →
    NPR.fn P z ≠ NPR.fn Q z

/-- At a separating seed, equal encodings have equal field-valued leaf/dyck data. -/
theorem field_noun_eq_of_sepSeed (z : K) (P Q : Noun)
    (hsep : SepSeed z P Q) (h : enc z P = enc z Q) :
    (NPR.leafF (K := K) P, NPR.dyckBits (K := K) P)
      = (NPR.leafF (K := K) Q, NPR.dyckBits (K := K) Q) := by
  by_contra hne
  exact hsep hne (enc_eq_imp_fn_eq z P Q h)

/-- Every leaf of a `BoundedBy q` noun is `< q`. -/
theorem bounded_leafList {q : ℕ} {n : Noun} (h : FieldEmbedding.BoundedBy q n) :
    ∀ x ∈ n.leafList, x < q := by
  induction n with
  | atom k =>
      simp only [FieldEmbedding.BoundedBy_atom] at h
      intro x hx
      simp only [Noun.leafList, List.mem_singleton] at hx
      exact hx ▸ h
  | cell l r ihl ihr =>
      obtain ⟨hl, hr⟩ := FieldEmbedding.BoundedBy_cell.mp h
      intro x hx
      simp only [Noun.leafList, List.mem_append] at hx
      rcases hx with hx | hx
      · exact ihl hl x hx
      · exact ihr hr x hx

theorem bounded_leafList_goldilocks {n : Noun} (h : FieldEmbedding.Bounded n) :
    ∀ x ∈ n.leafList, x < Field.p :=
  bounded_leafList h

/-- List-map injectivity when the map is injective only on the bounded residue range `[0,q)`. -/
theorem leafList_map_inj {q : ℕ}
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q)) :
    ∀ {l l' : List ℕ}, (∀ x ∈ l, x < q) → (∀ x ∈ l', x < q) →
      l.map (fun k : ℕ => (k : K)) = l'.map (fun k : ℕ => (k : K)) → l = l' := by
  intro l
  induction l with
  | nil =>
      intro l' _ _ h
      cases l' with
      | nil => rfl
      | cons b bs => simp at h
  | cons a as ih =>
      intro l' hl hl' h
      cases l' with
      | nil => simp at h
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hab, htail⟩ := h
          have ha : a < q := hl a (List.mem_cons.mpr (Or.inl rfl))
          have hb : b < q := hl' b (List.mem_cons.mpr (Or.inl rfl))
          have hab' : a = b := hinj (Set.mem_Iio.mpr ha) (Set.mem_Iio.mpr hb) hab
          have htl : as = bs :=
            ih (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx)))
              (fun x hx => hl' x (List.mem_cons.mpr (Or.inr hx))) htail
          rw [hab', htl]

theorem leafList_map_inj_goldilocks
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio Field.p)) :
    ∀ {l l' : List ℕ}, (∀ x ∈ l, x < Field.p) → (∀ x ∈ l', x < Field.p) →
      l.map (fun k : ℕ => (k : K)) = l'.map (fun k : ℕ => (k : K)) → l = l' :=
  leafList_map_inj hinj

/-- Equal encodings of `q`-bounded nouns imply structural noun equality at a separating seed. -/
theorem noun_eq_of_enc_eq (z : K) (P Q : Noun) {q : ℕ}
    (hsep : SepSeed z P Q)
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbP : FieldEmbedding.BoundedBy q P) (hbQ : FieldEmbedding.BoundedBy q Q)
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
    leafList_map_inj hinj (bounded_leafList hbP) (bounded_leafList hbQ)
      (by simpa only [NPR.leafF] using hleaf)
  exact Noun.noun_dyck_leaf_injective (by simp only [Prod.mk.injEq]; exact ⟨hdw, hll⟩)

theorem noun_eq_of_enc_eq_goldilocks (z : K) (P Q : Noun)
    (hsep : SepSeed z P Q)
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio Field.p))
    (hbP : FieldEmbedding.Bounded P) (hbQ : FieldEmbedding.Bounded Q)
    (h : enc z P = enc z Q) : P = Q :=
  noun_eq_of_enc_eq z P Q hsep hinj hbP hbQ h

variable [Fintype K] [DecidableEq K]

/-- At most `2*Λ-1` seeds fail to separate nouns with at most `Λ` leaves. -/
theorem sepSeed_bad_card_le (Λ : ℕ) (P Q : Noun) (hP : P.leaves ≤ Λ) (hQ : Q.leaves ≤ Λ) :
    (Finset.univ.filter (fun z : K => ¬ SepSeed z P Q)).card ≤ 2 * Λ - 1 := by
  by_cases hfn : (NPR.leafF (K := K) P, NPR.dyckBits (K := K) P)
      = (NPR.leafF (K := K) Q, NPR.dyckBits (K := K) Q)
  · have hempty : (Finset.univ.filter (fun z : K => ¬ SepSeed z P Q)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro z _ hbad
      exact hbad (fun hdiff => absurd hfn hdiff)
    rw [hempty]
    simp
  · refine le_trans (Finset.card_le_card ?_) (NPR.collision_card_le_tight Λ P Q hP hQ hfn)
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    by_contra hne
    exact hz.2 (fun _ => hne)

end Collision

section Reconstruct

/-- Structural reconstruction with the global axis carry started at `a`. -/
def ofNoun : Noun → Nat → GlobalCarryAxis.MemTree
  | Noun.atom k, a => GlobalCarryAxis.MemTree.leaf (Noun.atom k) a
  | Noun.cell l r, a =>
      GlobalCarryAxis.MemTree.node (Noun.cell l r) a
        (ofNoun l (2 * a)) (ofNoun r (2 * a + 1))

@[simp] theorem ofNoun_nounOf (n : Noun) (a : Nat) :
    GlobalCarryAxis.nounOf (ofNoun n a) = n := by cases n <;> rfl

@[simp] theorem ofNoun_axisOf (n : Noun) (a : Nat) :
    GlobalCarryAxis.axisOf (ofNoun n a) = a := by cases n <;> rfl

/-- The structural reconstruction satisfies all cons and carry constraints. -/
theorem ofNoun_wf (n : Noun) (a : Nat) : GlobalCarryAxis.WF (ofNoun n a) := by
  induction n generalizing a with
  | atom k => rfl
  | cell l r ihl ihr =>
      refine ⟨?_, ?_, ?_, ihl (2 * a), ihr (2 * a + 1)⟩
      · rw [ofNoun_nounOf, ofNoun_nounOf]
      · rw [ofNoun_axisOf]
      · rw [ofNoun_axisOf]

@[simp] theorem ofNoun_root_axis (s : Noun) : GlobalCarryAxis.axisOf (ofNoun s 1) = 1 :=
  ofNoun_axisOf s 1

@[simp] theorem ofNoun_root_noun (s : Noun) : GlobalCarryAxis.nounOf (ofNoun s 1) = s :=
  ofNoun_nounOf s 1

end Reconstruct

section Capstone

/-- Every served lookup in the anchored reconstruction is the true Nock slot. -/
theorem axis_sound_recognizer (s : Noun) {a : Nat} {v : Noun}
    (hserved : ∃ m, GlobalCarryAxis.Sub m (ofNoun s 1)
      ∧ GlobalCarryAxis.axisOf m = a ∧ GlobalCarryAxis.nounOf m = v) :
    Noun.slot a s = some v :=
  GlobalCarryAxis.lookup_sound (ofNoun s 1) (ofNoun_wf s 1) (ofNoun_root_axis s)
    (ofNoun_root_noun s) hserved

/-- `ServedLookup`-packaged form of `axis_sound_recognizer`. -/
theorem axis_sound_recognizer' (s : Noun) {a : Nat} {v : Noun}
    (hserved : GlobalCarryAxis.ServedLookup (ofNoun s 1) a v) :
    Noun.slot a s = some v :=
  GlobalCarryAxis.axis_sound_globalcarry (ofNoun s 1) (ofNoun_wf s 1) (ofNoun_root_axis s)
    (ofNoun_root_noun s) hserved

/-- A false `(axis,noun)` tuple cannot be served by the anchored reconstruction. -/
theorem forgery_rejected_recognizer (s : Noun) {a : Nat} {v v' : Noun}
    (hgen : Noun.slot a s = some v') (hne : v ≠ v') :
    ¬ ∃ m, GlobalCarryAxis.Sub m (ofNoun s 1)
        ∧ GlobalCarryAxis.axisOf m = a ∧ GlobalCarryAxis.nounOf m = v :=
  GlobalCarryAxis.forgery_rejected (ofNoun s 1) (ofNoun_wf s 1) (ofNoun_root_axis s)
    (ofNoun_root_noun s) hgen hne

end Capstone

section EqBlkBridge

variable {K : Type*} [Field K]

/-- Honest `decompose` row for an internal noun node. -/
noncomputable def decomposeRow (z : K) (l r : Noun) : MemoryTable.Pub K where
  st := MemoryTable.MState.decompose
  pt := { noun := enc z (Noun.cell l r), indicator := 0, counts := 0 }
  lc := { noun := enc z l, indicator := 0, counts := 0 }
  rc := { noun := enc z r, indicator := 0, counts := 0 }
  lcSt := MemoryTable.MState.halt
  rcSt := MemoryTable.MState.halt
  mem := ComputeTable.MemRec.zero
  ipre := 0
  icur := 0

/-- Honest noun decomposition satisfies the memory-table `eqBlk`. -/
theorem decomposeRow_eqBlk {z : K} (hz : z ≠ 0) (β γ : K) (l r : Noun) :
    MemoryTable.eqBlk { z := z, β := β, γ := γ } (decomposeRow z l r) := by
  unfold MemoryTable.eqBlk
  simp [decomposeRow, MemoryTable.Pub.lambda]
  exact enc_cons hz l r

/-- A fingerprint decomposition of `q`-bounded nouns forces the structural cons off collisions. -/
theorem decompose_forces_cons {z : K} (hz : z ≠ 0) (P L R : Noun) {q : ℕ}
    (hsep : SepSeed z P (Noun.cell L R))
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbP : FieldEmbedding.BoundedBy q P) (hbL : FieldEmbedding.BoundedBy q L)
    (hbR : FieldEmbedding.BoundedBy q R)
    (hdec : enc z P = ComputeTable.FP.cons z (enc z L) (enc z R)) :
    P = Noun.cell L R := by
  have henc : enc z P = enc z (Noun.cell L R) := by
    rw [hdec, ← enc_cons hz L R]
  exact noun_eq_of_enc_eq z P (Noun.cell L R) hsep hinj hbP
    (FieldEmbedding.BoundedBy_cell.mpr ⟨hbL, hbR⟩) henc

theorem decompose_forces_cons_goldilocks {z : K} (hz : z ≠ 0) (P L R : Noun)
    (hsep : SepSeed z P (Noun.cell L R))
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio Field.p))
    (hbP : FieldEmbedding.Bounded P) (hbL : FieldEmbedding.Bounded L)
    (hbR : FieldEmbedding.Bounded R)
    (hdec : enc z P = ComputeTable.FP.cons z (enc z L) (enc z R)) :
    P = Noun.cell L R :=
  decompose_forces_cons hz P L R hsep hinj hbP hbL hbR hdec

end EqBlkBridge

section Formula

/-- A structural cons equation determines the relative-axis-2 value. -/
theorem local_cons_head (root child sib : Noun) (h : root = Noun.cell child sib) :
    Noun.slot 2 root = some child := by
  subst h
  simp [Noun.slot]

/-- A structural cons equation determines the relative-axis-3 value. -/
theorem local_cons_tail (root child sib : Noun) (h : root = Noun.cell child sib) :
    Noun.slot 3 root = some sib := by
  subst h
  simp [Noun.slot]

/-- Structural cons children are unique. -/
theorem local_cons_unique {c s c' s' : Noun} (h : Noun.cell c s = Noun.cell c' s') :
    c = c' ∧ s = s' :=
  Noun.cons_children_unique h

variable {K : Type*} [Field K]

/-- A local fingerprint cons of `q`-bounded nouns forces both relative-axis lookups. -/
theorem formula_cons_sound {z : K} (hz : z ≠ 0) (R H Tl : Noun) {q : ℕ}
    (hsep : SepSeed z R (Noun.cell H Tl))
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hbR : FieldEmbedding.BoundedBy q R) (hbH : FieldEmbedding.BoundedBy q H)
    (hbTl : FieldEmbedding.BoundedBy q Tl)
    (hlink : ComputeTable.FP.cons z (enc z H) (enc z Tl) = enc z R) :
    Noun.slot 2 R = some H ∧ Noun.slot 3 R = some Tl := by
  have hcons : R = Noun.cell H Tl :=
    decompose_forces_cons hz R H Tl hsep hinj hbR hbH hbTl hlink.symm
  exact ⟨local_cons_head R H Tl hcons, local_cons_tail R H Tl hcons⟩

theorem formula_cons_sound_goldilocks {z : K} (hz : z ≠ 0) (R H Tl : Noun)
    (hsep : SepSeed z R (Noun.cell H Tl))
    (hinj : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio Field.p))
    (hbR : FieldEmbedding.Bounded R) (hbH : FieldEmbedding.Bounded H)
    (hbTl : FieldEmbedding.Bounded Tl)
    (hlink : ComputeTable.FP.cons z (enc z H) (enc z Tl) = enc z R) :
    Noun.slot 2 R = some H ∧ Noun.slot 3 R = some Tl :=
  formula_cons_sound hz R H Tl hsep hinj hbR hbH hbTl hlink

end Formula

end GlobalCarryRecognizer
end Nock
