/-
  Nock/NockVMROM/Thm54/VclL/Handle/PoleFree.lean

  Additive.

  The honest inverse of a slot is `A / D` (`slotGate_honest`), with `D = Σ act·den (+ pr·den_a·den_b)`,
  `A = Σ act (+ pr·(den_a + den_b))` and `den r = ρ + c_r` (`c_r` reads the trace and `γ`, never `ρ`).
  The honest BAD EVENT of a (row, slot) is `D = 0 ∧ A ≠ 0` at the coin `ρ`.  As a function of `ρ`:
  * `pr = 0` (slots 0, 1, no pair): `D = A0·ρ + C`, `A = A0`: at most `1` bad `ρ`;
  * `pr ≠ 0` (slot 2 pair): `D = pr·ρ² + (A0 + pr(ca+cb))·ρ + (C + pr·ca·cb)`, a degree-2 polynomial
    with non-zero leading coefficient: at most `2` bad `ρ`.
  So over `N` rows, at most `4·N` coins `ρ` (for any fixed `γ`) are bad (`pole_free_but_few`): a
  completeness summand `4N / |𝕂|`, no hypothesis.  (The brief's `rows × slots` is `3N`; the pair slot has
  two roots, so the exact count is `4N`.)
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestLookups

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL.Handle

open Nock Nock.Noun Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH

noncomputable section

section Pole
variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The environment with the `ρ` coin replaced. -/
def withRho (e : Env K) (ρ : K) : Env K :=
  ⟨e.trace, e.traceNext, Function.update e.chal chalRhoL ρ, e.pub⟩

/-- `D` of a slot (the inverse's denominator). -/
def slotD (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) : K :=
  (S.ents.map fun x => algebraMap F K (evalQ x.act eF) * evalMQ (den x.rcd) eK eF).sum +
    (match S.pair with
     | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF * evalMQ (den b) eK eF)
     | none => 0)

/-- `A` of a slot (the inverse's numerator). -/
def slotA (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) : K :=
  algebraMap F K ((S.ents.map fun x => evalQ x.act eF).sum) +
    (match S.pair with
     | some (fl, a, b) => algebraMap F K (evalQ (cc fl) eF) * (evalMQ (den a) eK eF + evalMQ (den b) eK eF)
     | none => 0)

/-- **The honest bad event** of a (row, slot): a vanishing denominator with a non-zero numerator. -/
def SlotBad (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) : Prop :=
  slotD S eK eF = 0 ∧ slotA S eK eF ≠ 0

/-- **The pole-free condition is `¬ SlotBad`**: then the honest inverse `A / D` satisfies the gate. -/
theorem slotGate_honest_of_not_bad (S : SlotSpec ℚ) (eK : Env K) (eF : Env F)
    (hnb : ¬ SlotBad S eK eF) (hinv : eK.trace S.inv = slotA S eK eF * (slotD S eK eF)⁻¹) :
    evalMQ (slotGate S) eK eF = 0 := by
  refine slotGate_honest S eK eF (slotD S eK eF) (slotA S eK eF) rfl rfl hinv ?_
  by_cases h : slotD S eK eF = 0
  · right; by_contra h'; exact hnb ⟨h, h'⟩
  · left; exact h

/-- NC: at a bad coin NO inverse satisfies the slot gate (so the event is a genuine completeness loss,
and `¬ SlotBad` is the exact condition for the honest inverse to exist). -/
theorem slotGate_bad_unsat (S : SlotSpec ℚ) (eK : Env K) (eF : Env F) (hb : SlotBad S eK eF) :
    evalMQ (slotGate S) eK eF ≠ 0 := by
  have e : evalMQ (slotGate S) eK eF = eK.trace S.inv * slotD S eK eF - slotA S eK eF :=
    evalMQ_slotGate S eK eF
  rw [e, hb.1, mul_zero, zero_sub]
  exact neg_ne_zero.mpr hb.2

theorem evalMQ_rlcKey_withRho (kind : VarKind) (γ : ℕ) (hγ : γ ≠ chalRhoL) (e : Env K) (eF : Env F)
    (ρ : K) : ∀ (n : ℕ) (r : List ℕ),
    evalMQ (rlcKey (F := ℚ) kind γ n r) (withRho e ρ) eF = evalMQ (rlcKey (F := ℚ) kind γ n r) e eF := by
  intro n r
  induction r generalizing n with
  | nil => rfl
  | cons i r ih =>
    simp only [rlcKey, evalMQ]
    rw [ih (n + 1)]
    cases kind <;> simp [evalMQ, withRho, Function.update_of_ne hγ]

theorem evalMQ_den_withRho (r : List ℕ) (e : Env K) (eF : Env F) (ρ : K) :
    evalMQ (den (F := ℚ) r) (withRho e ρ) eF = ρ + evalMQ (rlcKey (F := ℚ) .traceCur chalGammaL 0 r) e eF := by
  simp only [den, evalMQ]
  rw [evalMQ_rlcKey_withRho _ _ (by decide)]
  simp [withRho]

theorem list_sum_affine {ι : Type} (l : List ι) (a : ι → K) (c : ι → K) (ρ : K) :
    (l.map fun x => a x * (ρ + c x)).sum = (l.map a).sum * ρ + (l.map fun x => a x * c x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The `ρ`-free data of a slot: `A0`, `C`, `pr`, `ca`, `cb`. -/
def slotData (S : SlotSpec ℚ) (e : Env K) (eF : Env F) : K × K × K × K × K :=
  (algebraMap F K ((S.ents.map fun x => evalQ x.act eF).sum),
   (S.ents.map fun x => algebraMap F K (evalQ x.act eF) *
      evalMQ (rlcKey (F := ℚ) .traceCur chalGammaL 0 x.rcd) e eF).sum,
   (match S.pair with | some (fl, _, _) => algebraMap F K (evalQ (cc fl) eF) | none => 0),
   (match S.pair with | some (_, a, _) => evalMQ (rlcKey (F := ℚ) .traceCur chalGammaL 0 a) e eF | none => 0),
   (match S.pair with | some (_, _, b) => evalMQ (rlcKey (F := ℚ) .traceCur chalGammaL 0 b) e eF | none => 0))

theorem slotD_withRho (S : SlotSpec ℚ) (e : Env K) (eF : Env F) (ρ : K) :
    slotD S (withRho e ρ) eF =
      (slotData S e eF).1 * ρ + (slotData S e eF).2.1 +
        (slotData S e eF).2.2.1 * ((ρ + (slotData S e eF).2.2.2.1) * (ρ + (slotData S e eF).2.2.2.2)) := by
  unfold slotD slotData
  simp only [evalMQ_den_withRho]
  rw [list_sum_affine (S.ents) (fun x => algebraMap F K (evalQ x.act eF))
    (fun x => evalMQ (rlcKey (F := ℚ) .traceCur chalGammaL 0 x.rcd) e eF) ρ]
  have hs : algebraMap F K (S.ents.map fun x => evalQ x.act eF).sum =
      (S.ents.map fun x => algebraMap F K (evalQ x.act eF)).sum := by
    rw [map_list_sum, List.map_map]; rfl
  rw [hs]
  cases S.pair with
  | none => simp
  | some p => obtain ⟨fl, a, b⟩ := p; simp

theorem slotA_withRho (S : SlotSpec ℚ) (e : Env K) (eF : Env F) (ρ : K) :
    slotA S (withRho e ρ) eF =
      (slotData S e eF).1 +
        (slotData S e eF).2.2.1 * ((ρ + (slotData S e eF).2.2.2.1) + (ρ + (slotData S e eF).2.2.2.2)) := by
  unfold slotA slotData
  simp only [evalMQ_den_withRho]
  cases S.pair with
  | none => simp
  | some p => obtain ⟨fl, a, b⟩ := p; simp

open Classical in
/-- **At most one bad `ρ` without a pair, at most two with one.** -/
theorem slot_bad_roots (S : SlotSpec ℚ) (e : Env K) (eF : Env F) :
    ∃ B : Finset K, B.card ≤ (if (slotData S e eF).2.2.1 = 0 then 1 else 2) ∧
      ∀ ρ : K, SlotBad S (withRho e ρ) eF → ρ ∈ B := by
  have hD := slotD_withRho S e eF
  have hA := slotA_withRho S e eF
  generalize slotData S e eF = d at hD hA ⊢
  obtain ⟨A0, C0, pr, ca, cb⟩ := d
  simp only at hD hA ⊢
  by_cases hpr : pr = 0
  · simp only [hpr, if_true, zero_mul, add_zero] at hD hA ⊢
    by_cases hA0 : A0 = 0
    · refine ⟨∅, by simp, ?_⟩
      intro ρ ⟨_, h2⟩
      exact absurd (by rw [hA, hA0]) h2
    · refine ⟨{-C0 / A0}, by simp, ?_⟩
      intro ρ ⟨h1, _⟩
      rw [hD] at h1
      simp only [Finset.mem_singleton]
      field_simp
      linear_combination h1
  · let P : K[X] := C pr * X ^ 2 + C (A0 + pr * (ca + cb)) * X + C (C0 + pr * (ca * cb))
    have hP : P.degree = 2 := degree_quadratic hpr
    have hP0 : P ≠ 0 := by intro h; rw [h] at hP; simp at hP
    refine ⟨P.roots.toFinset, ?_, ?_⟩
    · simp only [hpr, if_false]
      calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := card_roots' P
        _ = 2 := natDegree_quadratic hpr
    · intro ρ ⟨h1, _⟩
      rw [hD] at h1
      rw [Multiset.mem_toFinset, mem_roots hP0]
      simp only [IsRoot, P, eval_add, eval_mul, eval_C, eval_pow, eval_X]
      linear_combination h1

end Pole

/-- **The honest pole-free summand**: for any `N` rows (any `ρ`-free environments), at most `4·N`
coins `ρ` make some slot of some row bad (`slots` = the three slots of `computeChipVCLH`). -/
theorem pole_free_but_few {F K : Type} [Field F] [Field K] [Algebra F K] (N : ℕ)
    (es : ℕ → Env K) (eFs : ℕ → Env F) :
    ∃ B : Finset K, B.card ≤ 4 * N ∧ ∀ ρ : K, ρ ∉ B →
      ∀ i < N, ∀ S ∈ (slots : List (SlotSpec ℚ)), ¬ SlotBad S (withRho (es i) ρ) (eFs i) := by
  classical
  have hne : ∀ (S : SlotSpec ℚ) (c : ℕ), S.pair = none → ∀ i,
      ∃ B : Finset K, B.card ≤ 1 ∧ ∀ ρ : K, SlotBad S (withRho (es i) ρ) (eFs i) → ρ ∈ B := by
    intro S c hn i
    obtain ⟨B, hB, hmem⟩ := slot_bad_roots S (es i) (eFs i)
    have : (slotData S (es i) (eFs i)).2.2.1 = 0 := by simp [slotData, hn]
    simp only [this, if_true] at hB
    exact ⟨B, hB, hmem⟩
  have h0 := hne slot0 0 rfl
  have h1 := hne slot1 0 rfl
  have h2 : ∀ i, ∃ B : Finset K, B.card ≤ 2 ∧
      ∀ ρ : K, SlotBad slot2 (withRho (es i) ρ) (eFs i) → ρ ∈ B := by
    intro i
    obtain ⟨B, hB, hmem⟩ := slot_bad_roots slot2 (es i) (eFs i)
    refine ⟨B, ?_, hmem⟩
    split at hB <;> omega
  choose B0 hB0 hm0 using h0
  choose B1 hB1 hm1 using h1
  choose B2 hB2 hm2 using h2
  refine ⟨(Finset.range N).biUnion fun i => B0 i ∪ B1 i ∪ B2 i, ?_, ?_⟩
  · calc _ ≤ ∑ i ∈ Finset.range N, (B0 i ∪ B1 i ∪ B2 i).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ Finset.range N, 4 := by
        apply Finset.sum_le_sum
        intro i _
        calc (B0 i ∪ B1 i ∪ B2 i).card ≤ (B0 i ∪ B1 i).card + (B2 i).card := Finset.card_union_le _ _
          _ ≤ (B0 i).card + (B1 i).card + (B2 i).card := by
            have := Finset.card_union_le (B0 i) (B1 i); omega
          _ ≤ 4 := by have := hB0 i; have := hB1 i; have := hB2 i; omega
      _ = 4 * N := by simp [mul_comm]
  · intro ρ hρ i hi S hS hbad
    apply hρ
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl | rfl
    · simp [hm0 i ρ hbad]
    · simp [hm1 i ρ hbad]
    · simp [hm2 i ρ hbad]

end

end Nock.NockVMROM.Thm54.VclL.Handle
