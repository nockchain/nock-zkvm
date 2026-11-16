import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness

/-!
# The ten-slot record of the thirty-first move (the pre-`α` exponent carrier)

This module holds the slot-generic facts both sides use:

* `withExp r x` — the nine-slot record `r` with tenth slot `x` (`Fin.snoc`);
  `rlc_withExp : Walk.rlc γ (withExp r x) = Walk.rlc γ r + γ⁹ · x` (the RLC gains exactly one
  `γ`-power; its trace degree is unchanged);
* the **honest** tenth slot of a record: its `1`-based position in the request list `L`
  (`honestExp`), so that the honest request list's exponents are `1, …, |L|` and every honest
  response carries the exponent of the request it answers.  `extRec L` / `extRecords L` extend a
  nine-slot record (list pair) by it; `IO.LIO` transfers in both directions
  (`lio_extRecords`, `lio_of_lio_extRecords`);

The honest exponent is the prover's fill, not a verifier mechanism: no gate reads a position.
-/

set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54
namespace RecordCarrier

open Nock
open Nock.NockVMROM.Thm54.FiniteIO

noncomputable section

section Slot

variable {K : Type*} [Field K]

/-- The nine-slot record `r` with tenth slot `x`. -/
def withExp (r : Fin 9 → K) (x : K) : Fin 10 → K := Fin.snoc r x

@[simp] theorem withExp_castSucc (r : Fin 9 → K) (x : K) (c : Fin 9) :
    withExp r x c.castSucc = r c := by
  simp [withExp]

theorem withExp_last (r : Fin 9 → K) (x : K) : withExp r x (Fin.last 9) = x :=
  Fin.snoc_last (α := fun _ => K) (p := r) x

@[simp] theorem withExp_nine (r : Fin 9 → K) (x : K) : withExp r x 9 = x := withExp_last r x

theorem withExp_inj {r r' : Fin 9 → K} {x x' : K} (h : withExp r x = withExp r' x') :
    r = r' ∧ x = x' := by
  refine ⟨funext fun c => ?_, ?_⟩
  · have := congrFun h c.castSucc
    simpa using this
  · have := congrFun h 9
    simpa using this

/-- The record RLC gains exactly the term `γ⁹ · x`. -/
theorem rlc_withExp (γ : K) (r : Fin 9 → K) (x : K) :
    Walk.rlc γ (withExp r x) = Walk.rlc γ r + γ ^ 9 * x := by
  rw [Walk.rlc, Walk.rlc, Fin.sum_univ_castSucc]
  simp only [withExp_castSucc, Fin.val_castSucc, Fin.val_last]
  rw [withExp_last, mul_comm (γ ^ 9) x, mul_comm x]

/-- A ten-slot record is its nine-slot prefix with its tenth slot. -/
theorem eq_withExp (v : Fin 10 → K) :
    v = withExp (fun c : Fin 9 => v c.castSucc) (v (Fin.last 9)) := by
  funext c
  refine Fin.lastCases ?_ (fun c => ?_) c
  · rw [withExp_last]
  · simp

end Slot

section Honest

variable {K : Type*} [Field K] [DecidableEq K]

/-- **The honest exponent of a record**: its `1`-based position in the request list `L`.  Every request of a duplicate-free list gets its own exponent;
duplicate *lookups* are distinct records (their timestamps differ), so they get distinct
exponents. -/
def honestExp (L : List (Fin 9 → K)) (r : Fin 9 → K) : ℕ := L.idxOf r + 1

/-- The honest ten-slot record. -/
def extRec (L : List (Fin 9 → K)) (r : Fin 9 → K) : Fin 10 → K :=
  withExp r ((honestExp L r : ℕ) : K)

theorem extRec_injective (L : List (Fin 9 → K)) : Function.Injective (extRec L) := by
  intro r r' h
  exact (withExp_inj h).1

/-- The honest ten-slot record lists, indexed by the request list `L`. -/
def extRecords (L : List (Fin 9 → K)) (rs : PreChallengeRecords K 9) :
    PreChallengeRecords K 10 :=
  ⟨rs.requests.map (extRec L), rs.responses.map (extRec L)⟩

@[simp] theorem extRecords_requests (L : List (Fin 9 → K)) (rs : PreChallengeRecords K 9) :
    (extRecords L rs).requests = rs.requests.map (extRec L) := rfl

@[simp] theorem extRecords_responses (L : List (Fin 9 → K)) (rs : PreChallengeRecords K 9) :
    (extRecords L rs).responses = rs.responses.map (extRec L) := rfl

/-- **The honest exponent of a flattened record is its row prefix plus its slot**: in a
duplicate-free request list made row by row, the `j`-th record of row `i` sits at position
`Σ_{i' < i} |row i'| + j`, so its exponent is that plus one. -/
theorem honestExp_flatMap {α : Type*} (rows : List α) (f : α → List (Fin 9 → K))
    (hnd : (rows.flatMap f).Nodup) (i : ℕ) (hi : i < rows.length) (j : ℕ)
    (hj : j < (f rows[i]).length) :
    honestExp (rows.flatMap f) ((f rows[i])[j]) =
      ((rows.take i).map (fun r => (f r).length)).sum + j + 1 := by
  have hsplit : rows.flatMap f =
      (rows.take i).flatMap f ++ (f rows[i] ++ (rows.drop (i + 1)).flatMap f) := by
    conv_lhs => rw [← List.take_append_drop i rows]
    rw [List.flatMap_append, List.drop_eq_getElem_cons hi, List.flatMap_cons]
  have hnd' := hnd
  rw [hsplit] at hnd'
  have hmem : (f rows[i])[j] ∈ f rows[i] := List.getElem_mem hj
  have hnot : (f rows[i])[j] ∉ (rows.take i).flatMap f := by
    intro h
    exact (List.disjoint_of_nodup_append hnd') h
      (List.mem_append_left _ hmem)
  have hnd2 : (f rows[i]).Nodup :=
    ((List.nodup_append.mp hnd').2.1).sublist (List.sublist_append_left _ _)
  unfold honestExp
  rw [hsplit, List.idxOf_append_of_notMem hnot, List.idxOf_append_of_mem hmem]
  have hidx : List.idxOf (f rows[i])[j] (f rows[i]) = j := by
    have := List.get_idxOf hnd2 ⟨j, hj⟩
    simpa using this
  rw [hidx]
  simp [List.length_flatMap, List.map_take]

/-- `IO.LIO` survives the honest extension. -/
theorem lio_extRecords {Ksz : ℕ} (L : List (Fin 9 → K)) {a b : List (Fin 9 → K)}
    (h : IO.LIO Ksz a b) : IO.LIO Ksz (a.map (extRec L)) (b.map (extRec L)) := by
  obtain ⟨hr, hn, hp⟩ := h
  refine ⟨?_, (List.nodup_map_iff (extRec_injective L)).mpr hn, hp.map _⟩
  simpa using hr

/-- And is reflected by it. -/
theorem lio_of_lio_extRecords {Ksz : ℕ} (L : List (Fin 9 → K)) {a b : List (Fin 9 → K)}
    (h : IO.LIO Ksz (a.map (extRec L)) (b.map (extRec L))) : IO.LIO Ksz a b := by
  obtain ⟨hr, hn, hp⟩ := h
  refine ⟨by simpa using hr, (List.nodup_map_iff (extRec_injective L)).mp hn, ?_⟩
  obtain ⟨g, hg⟩ := (extRec_injective L).hasLeftInverse
  have := hp.map g
  simpa [List.map_map, Function.LeftInverse.comp_eq_id hg] using this

end Honest

section Events

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {m : ℕ}

/-- At `γ = 0` the RLC reads slot `0` only, so the tenth slot is invisible. -/
theorem rlc_withExp_zero (r : Fin 9 → K) (x : K) :
    Walk.rlc (0 : K) (withExp r x) = Walk.rlc 0 r := by
  rw [rlc_withExp]; simp

/-- At `γ = 0` the honest extension does not change the pole-hit event. -/
theorem IOPoleHitEvent_extRecords_zero (L : List (Fin 9 → K)) (rs : PreChallengeRecords K 9) :
    IOPoleHitEvent (extRecords L rs) 0 = IOPoleHitEvent rs 0 := by
  ext z
  simp only [IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and, extRecords_requests,
    extRecords_responses, ← List.map_append, List.mem_map]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, hz⟩
    exact ⟨v, hv, by simpa [extRec, rlc_withExp_zero] using hz⟩
  · rintro ⟨v, hv, hz⟩
    exact ⟨_, ⟨v, hv, rfl⟩, by simpa [extRec, rlc_withExp_zero] using hz⟩

/-- **Fixture form.**  A single request answered by a single response, coins with `γ = 0` whose
pole misses the nine-slot hit event: the coins miss the ten-slot failure event. -/
theorem notMem_IOFailureEvent_extRecords_single (L : List (Fin 9 → K)) (a : Fin 9 → K)
    (coins : IOCoins K) (hγ : coins.gamma = 0)
    (hhit : coins.pole ∉ IOPoleHitEvent (⟨[a], [a]⟩ : PreChallengeRecords K 9) 0) :
    (coins.gamma, coins.pole) ∉ IOFailureEvent (extRecords L ⟨[a], [a]⟩) := by
  rw [hγ]
  refine notMem_IOFailureEvent_of ?_ ?_ ?_
  · simp [IORLCCollisionEvent]
  · rw [IOPoleHitEvent_extRecords_zero]; exact hhit
  · rw [IOLogDerivEvent_eq_empty_of_perm _ _ (List.Perm.refl _)]
    exact Finset.notMem_empty _

/-- **Coins outside two IO failure events at once.** -/
theorem exists_io_coins_two {m₁ m₂ : ℕ} (r₁ : PreChallengeRecords K m₁)
    (r₂ : PreChallengeRecords K m₂)
    (hcard : (IOFailureEvent r₁).card + (IOFailureEvent r₂).card < Fintype.card (K × K)) :
    ∃ coins : IOCoins K, (coins.gamma, coins.pole) ∉ IOFailureEvent r₁ ∧
      (coins.gamma, coins.pole) ∉ IOFailureEvent r₂ := by
  have hlt : (IOFailureEvent r₁ ∪ IOFailureEvent r₂).card < Fintype.card (K × K) :=
    lt_of_le_of_lt (Finset.card_union_le _ _) hcard
  have hne : IOFailureEvent r₁ ∪ IOFailureEvent r₂ ≠ Finset.univ := by
    intro hEq
    rw [hEq, Finset.card_univ] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨q, -, hq⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  rw [Finset.mem_union, not_or] at hq
  exact ⟨⟨q.1, q.2⟩, hq.1, hq.2⟩

/-- The two-event bound from the two union bounds. -/
theorem exists_io_coins_two_of_bounds {m₁ m₂ : ℕ} (r₁ : PreChallengeRecords K m₁)
    (r₂ : PreChallengeRecords K m₂)
    (hcard : ioFailureUnionBound m₁ r₁.requests.length r₁.responses.length (Fintype.card K) +
        ioFailureUnionBound m₂ r₂.requests.length r₂.responses.length (Fintype.card K) <
      Fintype.card (K × K)) :
    ∃ coins : IOCoins K, (coins.gamma, coins.pole) ∉ IOFailureEvent r₁ ∧
      (coins.gamma, coins.pole) ∉ IOFailureEvent r₂ :=
  exists_io_coins_two r₁ r₂
    (lt_of_le_of_lt (Nat.add_le_add (IOFailureEvent_card_le r₁) (IOFailureEvent_card_le r₂))
      hcard)

def honestIOBound (n₁ n₂ cardK : ℕ) : ℕ :=
  ioFailureUnionBound 9 n₁ n₂ cardK + ioFailureUnionBound 10 n₁ n₂ cardK

/-- `honestIOBound n n |K| = |K| · (68 n² + 8 n)`. -/
theorem honestIOBound_eq (n cardK : ℕ) :
    honestIOBound n n cardK = cardK * (68 * n * n + 8 * n) := by
  simp only [honestIOBound, ioFailureUnionBound]
  ring

theorem honestIOBound_mono {k₁ k₂ n : ℕ} (cardK : ℕ) (h1 : k₁ ≤ n) (h2 : k₂ ≤ n) :
    honestIOBound k₁ k₂ cardK ≤ honestIOBound n n cardK := by
  simp only [honestIOBound, ioFailureUnionBound]
  have hs : k₁ + k₂ ≤ n + n := Nat.add_le_add h1 h2
  have hss : (k₁ + k₂) * (k₁ + k₂) ≤ (n + n) * (n + n) := Nat.mul_le_mul hs hs
  gcongr

/-- **Honest coins outside both IO failure events** (nine-slot `rs`, ten-slot `extRecords L rs`),
from the honest budget at a common length bound `n`. -/
theorem exists_io_coins_ext (L : List (Fin 9 → K)) (rs : PreChallengeRecords K 9) {n : ℕ}
    (hreq : rs.requests.length ≤ n) (hresp : rs.responses.length ≤ n)
    (hcard : honestIOBound n n (Fintype.card K) < Fintype.card (K × K)) :
    ∃ coins : IOCoins K, (coins.gamma, coins.pole) ∉ IOFailureEvent rs ∧
      (coins.gamma, coins.pole) ∉ IOFailureEvent (extRecords L rs) := by
  apply exists_io_coins_two_of_bounds
  refine lt_of_le_of_lt ?_ hcard
  have hmono := honestIOBound_mono (Fintype.card K) hreq hresp
  simpa [honestIOBound, extRecords_requests, extRecords_responses] using hmono

/-- **An internal pole outside both pole-hit events** (and nonzero), at a fixed `γ`. -/
theorem exists_pole_ext (L : List (Fin 9 → K)) (rs : PreChallengeRecords K 9) (γ : K)
    (hcard : 2 * (rs.requests.length + rs.responses.length) + 1 < Fintype.card K) :
    ∃ pole : K, pole ∉ IOPoleHitEvent rs γ ∧ pole ∉ IOPoleHitEvent (extRecords L rs) γ ∧
      pole ≠ 0 := by
  set bad := IOPoleHitEvent rs γ ∪ IOPoleHitEvent (extRecords L rs) γ ∪ {0}
  have h1 := IOPoleHitEvent_card_le rs γ
  have h2 := IOPoleHitEvent_card_le (extRecords L rs) γ
  simp only [extRecords_requests, extRecords_responses, List.length_map] at h2
  have hlt : bad.card < Fintype.card K := by
    refine lt_of_le_of_lt (le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add (Finset.card_union_le _ _) le_rfl)) ?_
    have : ({0} : Finset K).card = 1 := Finset.card_singleton 0
    omega
  have hne : bad ≠ Finset.univ := by
    intro hEq
    rw [hEq, Finset.card_univ] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨z, -, hz⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  simp only [bad, Finset.mem_union, Finset.mem_singleton, not_or] at hz
  exact ⟨z, hz.1.1, hz.1.2, hz.2⟩

end Events

end


section NatLift

variable {F : Type*} [Field F]

open Classical in
/-- **`natLift x`**: the least `n < ringChar F` with `(n : F) = x`, `0` if there is none.  The
memory carrier `reqIdx` is a base-field column; `natLift` reads it back as the exponent it
carries. -/
noncomputable def natLift (x : F) : ℕ :=
  if h : ∃ n, n < ringChar F ∧ (n : F) = x then Nat.find h else 0

/-- Below the characteristic, `natLift` inverts the cast. -/
theorem natLift_natCast {n : ℕ} (hn : n < ringChar F) : natLift (n : F) = n := by
  classical
  have hex : ∃ m, m < ringChar F ∧ (m : F) = (n : F) := ⟨n, hn, rfl⟩
  unfold natLift
  rw [dif_pos hex]
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ n := Nat.find_min' hex ⟨hn, rfl⟩
  haveI : CharP F (ringChar F) := ringChar.charP F
  exact CharP.natCast_injOn_Iio F (ringChar F) (Set.mem_Iio.2 hspec.1) (Set.mem_Iio.2 hn)
    hspec.2

end NatLift

end RecordCarrier
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.RecordCarrier.rlc_withExp
#print axioms Nock.NockVMROM.Thm54.RecordCarrier.lio_extRecords
#print axioms Nock.NockVMROM.Thm54.RecordCarrier.lio_of_lio_extRecords
#print axioms Nock.NockVMROM.Thm54.RecordCarrier.exists_io_coins_two
#print axioms Nock.NockVMROM.Thm54.RecordCarrier.natLift_natCast
