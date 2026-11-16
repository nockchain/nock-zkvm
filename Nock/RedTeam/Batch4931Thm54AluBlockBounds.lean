/-
  Sizes are bounds on list lengths, never table evaluation.
-/
import Nock.RedTeam.Batch4921Thm54J9ALComplToy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch4931

open Nock Nock.Edit Nock.Edit.GenX Nock.Jet Nock.Jet.Prim
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
open Nock.RedTeam.Batch4921 (addL_len packQ1_len handle_words)

theorem qslot_words' (o : PrimOp) (pk : Bool) (qs : List ℤ) : (qSlot o pk qs).words.length ≤ 1 + qs.length := by
  cases pk
  · by_cases h : qs.map Int.toNat = []
    · simp [qSlot, h]
    · simp [qSlot, h]
  · exact Nock.RedTeam.Batch4921.qslot_words o qs

theorem wit_words (o : PrimOp) (lb r w : ℕ) : (witSlot o lb r w).words.length ≤ 1 + (Nock.Atoms.limbs w).length := by
  unfold witSlot wordsOf
  split_ifs <;> simp

theorem addL_length : ∀ a b : List ℤ, (CarrySZ.addL a b).length = max a.length b.length
  | [], bs => by simp [CarrySZ.addL]
  | a :: as, [] => by simp [CarrySZ.addL]
  | a :: as, b :: bs => by
    simp only [CarrySZ.addL, List.length_cons, addL_length as bs]
    omega

theorem wit_vw (o : PrimOp) (lb r w : ℕ) (h : (Nock.Atoms.limbs w).length ≤ 6) :
    (witSlot o lb r w).vw.length ≤ 8 := by
  unfold witSlot wordsOf; split_ifs <;> simp <;> omega

theorem mulL_len : ∀ as bs : List ℤ, (mulL as bs).length ≤ as.length + bs.length
  | [], _ => by simp [mulL]
  | a :: as, bs => by
    have h1 := mulL_len as bs
    simp only [mulL, addL_length, List.length_map, List.length_cons]
    omega

theorem wL_len (A B : List ℕ) (hA : A.length ≤ 8) (hB : B.length ≤ 8) : (wL A B).length ≤ 100 := by
  have h1 := mulL_len (zl A) (zl B)
  have h2 := mulL_len (zl (hiL A)) (zl (hiL B))
  have h3 := mulL_len [-(Bn : ℤ), 1] (mulL (zl (hiL A)) (zl (hiL B)))
  have h4 := addL_len (mulL (zl A) (zl B)) (mulL [-(Bn : ℤ), 1] (mulL (zl (hiL A)) (zl (hiL B))))
  simp only [zl, hiL, List.length_map] at h1 h2 h3 h4 ⊢
  unfold wL
  simp only [zl, hiL, List.length_map, List.length_cons, List.length_nil] at h1 h2 h3 h4 ⊢
  omega

theorem lim_le (a : ℕ) (k : ℕ) (h : a < 2 ^ (32 * k)) : (Nock.Atoms.limbs a).length ≤ k := by
  unfold Nock.Atoms.limbs Nock.Atoms.B
  rw [Nat.digits_length_le_iff (by norm_num)]
  calc a < 2 ^ (32 * k) := h
    _ = (2 ^ 32) ^ k := by rw [pow_mul]

theorem qmul_len (A B C : List ℕ) (hA : A.length ≤ 8) (hB : B.length ≤ 8) (hC : C.length ≤ 8) :
    (qSlot .mul false (CarrySZ.carr (↑Bn) 0 (CarrySZ.addL (wL A B) (CarrySZ.negL (zl C))))).words.length ≤ 300 := by
  refine (qslot_words' _ _ _).trans ?_
  have := wL_len A B hA hB
  rw [CarrySZ.carr_length, addL_length]
  simp only [CarrySZ.negL, zl, List.length_map]
  omega

theorem qdiv1_len (X B Y A : List ℕ) (hX : X.length ≤ 8) (hB : B.length ≤ 8) (hY : Y.length ≤ 8) (hA : A.length ≤ 8) :
    (qSlot .div false (CarrySZ.carr (↑Bn) 0 (CarrySZ.addL (CarrySZ.addL (wL X B) (zl Y))
      (CarrySZ.negL (zl A))))).words.length ≤ 300 := by
  refine (qslot_words' _ _ _).trans ?_
  have := wL_len X B hX hB
  rw [CarrySZ.carr_length, addL_length, addL_length]
  simp only [CarrySZ.negL, zl, List.length_map]
  omega

theorem qdiv2_len (Y S B : List ℕ) (hY : Y.length ≤ 8) (hS : S.length ≤ 8) (hB : B.length ≤ 8) :
    (qSlot .div true (CarrySZ.carr (↑Bn) 0 (CarrySZ.addL (CarrySZ.addL (CarrySZ.addL (zl Y) (zl S)) [1])
      (CarrySZ.negL (zl B))))).words.length ≤ 300 := by
  refine (qslot_words' _ _ _).trans ?_
  rw [CarrySZ.carr_length, addL_length, addL_length, addL_length]
  simp only [CarrySZ.negL, zl, List.length_map, List.length_cons, List.length_nil]
  omega

theorem qlt_len (X Y D : List ℕ) (s t e : ℤ) (hX : X.length ≤ 8) (hY : Y.length ≤ 8) (hD : D.length ≤ 8) :
    (qSlot .lt true (CarrySZ.carr (↑Bn) 0 (CarrySZ.addL (CarrySZ.addL (CarrySZ.addL
      ((zl X).map (s * ·)) ((zl Y).map (t * ·))) (zl D)) [e]))).words.length ≤ 300 := by
  refine (qslot_words' _ _ _).trans ?_
  rw [CarrySZ.carr_length, addL_length, addL_length, addL_length]
  simp only [zl, List.length_map, List.length_cons, List.length_nil]
  omega

variable {F : Type} [Field F]

theorem blockB_len (p : ℕ) (cl : CallL) :
    (blockB (F := F) p cl).length = 1 + ((slotsOf p cl).map fun s => s.words.length).sum := by
  simp only [blockB, slotRows, List.length_cons, List.length_flatMap, List.length_map, List.length_range]
  omega

theorem blockB_le_of (p : ℕ) (cl : CallL) (h7 : (slotsOf p cl).length ≤ 7)
    (h : ∀ s ∈ slotsOf p cl, s.words.length ≤ 300) : (blockB (F := F) p cl).length ≤ 2 ^ 20 := by
  rw [blockB_len]
  have : ((slotsOf p cl).map fun s => s.words.length).sum ≤ (slotsOf p cl).length * 300 := by
    refine (List.sum_le_length_nsmul _ 300 ?_).trans (by simp)
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    exact h s hs
  have h2 : (slotsOf p cl).length * 300 ≤ 7 * 300 := Nat.mul_le_mul_right _ h7
  have : (2 : ℕ) ^ 20 ≥ 2200 := by norm_num
  omega

theorem blockB_lt_le (p : ℕ) (cl : CallL) (hop : cl.op = .lt)
    (ha : (Nock.Atoms.limbs cl.a).length ≤ 6) (hb : (Nock.Atoms.limbs cl.b).length ≤ 6)
    (hw : (Nock.Atoms.limbs (ltWit cl.a cl.b)).length ≤ 6) : (blockB (F := F) p cl).length ≤ 2 ^ 20 := by
  obtain ⟨op, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩ := cl
  simp only at hop ha hb hw
  subst hop
  obtain ⟨hA1, hA2⟩ := handle_words p .lt (CallL.lbv ⟨.lt, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 0 a kA vA
  obtain ⟨hB1, hB2⟩ := handle_words p .lt (CallL.lbv ⟨.lt, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 1 b kB vB
  have hD := wit_words .lt (CallL.lbv ⟨.lt, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 3 (ltWit a b)
  have hD' := wit_vw .lt (CallL.lbv ⟨.lt, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 3 (ltWit a b) hw
  refine blockB_le_of p _ (by simp [slotsOf]) ?_
  intro s hs
  simp only [slotsOf, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · exact qlt_len _ _ _ _ _ _ (by omega) (by omega) (by omega)

theorem blockB_mul_le (p : ℕ) (cl : CallL) (hop : cl.op = .mul)
    (ha : (Nock.Atoms.limbs cl.a).length ≤ 6) (hb : (Nock.Atoms.limbs cl.b).length ≤ 6)
    (hc : (Nock.Atoms.limbs cl.c).length ≤ 6) : (blockB (F := F) p cl).length ≤ 2 ^ 20 := by
  obtain ⟨op, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩ := cl
  simp only at hop ha hb hc
  subst hop
  obtain ⟨hA1, hA2⟩ := handle_words p .mul (CallL.lbv ⟨.mul, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 0 a kA vA
  obtain ⟨hB1, hB2⟩ := handle_words p .mul (CallL.lbv ⟨.mul, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 1 b kB vB
  obtain ⟨hC1, hC2⟩ := handle_words p .mul (CallL.lbv ⟨.mul, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 2 c kE vE
  refine blockB_le_of p _ (by simp [slotsOf]) ?_
  intro s hs
  simp only [slotsOf, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · exact qmul_len _ _ _ (by omega) (by omega) (by omega)

theorem blockB_div_le (p : ℕ) (cl : CallL) (hop : cl.op = .div)
    (ha : (Nock.Atoms.limbs cl.a).length ≤ 6) (hb : (Nock.Atoms.limbs cl.b).length ≤ 6)
    (hc : (Nock.Atoms.limbs cl.c).length ≤ 6) (hy : (Nock.Atoms.limbs (cl.a % cl.b)).length ≤ 6)
    (hs : (Nock.Atoms.limbs (cl.b - cl.a % cl.b - 1)).length ≤ 6) : (blockB (F := F) p cl).length ≤ 2 ^ 20 := by
  obtain ⟨op, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩ := cl
  simp only at hop ha hb hc hy hs
  subst hop
  obtain ⟨hA1, hA2⟩ := handle_words p .div (CallL.lbv ⟨.div, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 0 a kA vA
  obtain ⟨hB1, hB2⟩ := handle_words p .div (CallL.lbv ⟨.div, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 1 b kB vB
  obtain ⟨hX1, hX2⟩ := handle_words p .div (CallL.lbv ⟨.div, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 4 c kE vE
  have hY1 := wit_words .div (CallL.lbv ⟨.div, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 5 (a % b)
  have hY2 := wit_vw .div (CallL.lbv ⟨.div, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 5 (a % b) hy
  have hS1 := wit_words .div (CallL.lbv ⟨.div, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 6 (b - a % b - 1)
  have hS2 := wit_vw .div (CallL.lbv ⟨.div, id, vc, vS, kA, vA, kB, vB, kE, vE, a, b, c⟩) 6 (b - a % b - 1) hs
  refine blockB_le_of p _ (by simp [slotsOf]) ?_
  intro s hs'
  simp only [slotsOf, List.mem_cons, List.not_mem_nil, or_false] at hs'
  rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact qdiv1_len _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  · exact qdiv2_len _ _ _ (by omega) (by omega) (by omega)

end Nock.RedTeam.Batch4931
