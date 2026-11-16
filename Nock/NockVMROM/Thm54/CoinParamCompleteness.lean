/-
  Nock/NockVMROM/Thm54/CoinParamCompleteness.lean

  Perfect completeness of the deployed chip family
  `computeChipAt c` / `memoryChipAt c` (`DeployedAcceptanceAt`) at an honest fill, at every
  sampled tuple `c` outside the IO-pole hit event.

  The family chips take only their
  challenge map and the walk block from `c`.  Every other gate-read public is the package's own
  fixed map, and that includes the post-challenge LogUp terminal `requests`:
  * compute publics `6..8`: `familyComputePublic_coin_free`, `familyComputePublic_requests`;
  * memory publics `12..14`, and the memory walk seed `9..11`: `familyMemoryPublic_coin_free`.
  In the paper, `requests` is the prover's terminal output of `acc_prog` after `(α, β)` are
  drawn.  The memory table is seeded with it "as-is" (`:597`, `:599`).
  It is a prover message of the last round, so its value depends on the coins.

  So every accepted family memory trace has
  `Σ_{r ∈ responses} (pole + RLC^γ r)⁻¹ = pkgRequests P` (`requests_forced_at`), where the right
  side is the same at every `c`.  Fix every coordinate except the pole, and fix the committed
  response records, as the round structure requires (`:507-509`; records are committed before
  `(γ, pole)`).  Then the left side is a nonconstant rational function of the pole, so at most
  `|responses|` poles are accepted (`accepted_poles_card_le`, from `logup_fibre_card_le`).
  `exists_good_pole_rejected` then gives a pole outside the IO-pole hit event at which the fill
  is rejected.  This needs only `|requests| + 2·|responses| < |𝕂|`.

  Hence "`DeployedAcceptanceAt` at every `c ∉ IOPoleHitEvent`" is FALSE for any fill whose
  records do not move with the pole.  Before the chips can be complete at every sampled coin,
  `requests` (and the memory seed) must become post-challenge prover publics of the chip family.

  At a pole that hits a committed response record, the
  denominator vanishes and the trace is rejected (`rejected_of_response_poleHit_at`).
-/
import Nock.NockVMROM.Thm54.FamilyIOChainMemory
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.CoinParamCompleteness

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open OptimizedStrictPackage
open OptimizedStrictFullPackage
open DeployedChipFamily
open FamilyIOChain

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## A. The LogUp fibre over the pole (pure algebra) -/

section Algebra

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The numerator of `S − Σ_{x ∈ s} (X + x)⁻¹` after clearing denominators. -/
def logUpNumer (s : Finset K) (S : K) : K[X] :=
  C S * ∏ x ∈ s, (X + C x) - ∑ x ∈ s, ∏ y ∈ s.erase x, (X + C y)

theorem logUpNumer_natDegree_le (s : Finset K) (S : K) :
    (logUpNumer s S).natDegree ≤ s.card := by
  unfold logUpNumer
  have hprod : ∀ t : Finset K, (∏ x ∈ t, (X + C x)).natDegree ≤ t.card := by
    intro t
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun x _ => (Polynomial.natDegree_X_add_C x).le).trans ?_
    simp
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (hprod s)
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x hx => ?_
    exact (hprod _).trans (Finset.card_erase_le)

/-- At `X = −x₀` with `x₀ ∈ s`, the numerator is `−Π_{y ≠ x₀}(y − x₀) ≠ 0`. -/
theorem logUpNumer_ne_zero (s : Finset K) (S : K) {x₀ : K} (hx₀ : x₀ ∈ s) :
    logUpNumer s S ≠ 0 := by
  intro h0
  have hev := congrArg (Polynomial.eval (-x₀)) h0
  simp only [logUpNumer, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_finsetSum,
    Polynomial.eval_zero] at hev
  have hz : ∏ x ∈ s, (-x₀ + x) = 0 :=
    Finset.prod_eq_zero hx₀ (by ring)
  rw [hz, mul_zero, zero_sub, neg_eq_zero] at hev
  rw [Finset.sum_eq_single x₀] at hev
  · refine (Finset.prod_ne_zero_iff.mpr fun y hy => ?_) hev
    have hne : y ≠ x₀ := Finset.ne_of_mem_erase hy
    intro h
    exact hne (by linear_combination h)
  · intro x hx hne
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hne, hx₀⟩) (by ring)
  · intro h; exact absurd hx₀ h

/-- A good pole that meets the target sum is a root of the numerator. -/
theorem logUpNumer_eval_eq_zero (s : Finset K) (S p : K) (hgood : ∀ x ∈ s, p + x ≠ 0)
    (hsum : ∑ x ∈ s, (p + x)⁻¹ = S) : (logUpNumer s S).eval p = 0 := by
  simp only [logUpNumer, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_finsetSum]
  have herase : ∀ x ∈ s, ∏ y ∈ s.erase x, (p + y) = (∏ y ∈ s, (p + y)) * (p + x)⁻¹ := by
    intro x hx
    rw [← Finset.prod_erase_mul s (fun y => p + y) hx, mul_assoc,
      mul_inv_cancel₀ (hgood x hx), mul_one]
  rw [Finset.sum_congr rfl herase, ← Finset.mul_sum, hsum, sub_eq_zero, mul_comm]

/-- **The LogUp fibre bound.**  For `n` distinct record values, at most `n` poles that hit no
record give the LogUp sum `Σ (pole + x)⁻¹` any fixed value `S`. -/
theorem logup_fibre_card_le (s : Finset K) (hne : s.Nonempty) (S : K) :
    (Finset.univ.filter fun p : K => (∀ x ∈ s, p + x ≠ 0) ∧ ∑ x ∈ s, (p + x)⁻¹ = S).card ≤
      s.card := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hQ := logUpNumer_ne_zero s S hx₀
  calc _ ≤ (logUpNumer s S).roots.toFinset.card := by
        refine Finset.card_le_card fun p hp => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
        exact logUpNumer_eval_eq_zero s S p hp.1 hp.2
    _ ≤ (logUpNumer s S).roots.card := Multiset.toFinset_card_le _
    _ ≤ (logUpNumer s S).natDegree := Polynomial.card_roots' _
    _ ≤ s.card := logUpNumer_natDegree_le s S

/-- List form: a duplicate-free list of record values. -/
theorem logup_fibre_card_le_list (xs : List K) (hnd : xs.Nodup) (hne : xs ≠ []) (S : K) :
    (Finset.univ.filter fun p : K =>
        (∀ x ∈ xs, p + x ≠ 0) ∧ (xs.map fun x => (p + x)⁻¹).sum = S).card ≤ xs.length := by
  have hs : xs.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil xs hne
    exact ⟨x, List.mem_toFinset.mpr hx⟩
  have hsum : ∀ p : K, (xs.map fun x => (p + x)⁻¹).sum = ∑ x ∈ xs.toFinset, (p + x)⁻¹ := by
    intro p
    rw [List.sum_toFinset _ hnd]
  have h := logup_fibre_card_le xs.toFinset hs S
  rw [List.toFinset_card_of_nodup hnd] at h
  refine le_trans (Finset.card_le_card fun p hp => ?_) h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset] at hp ⊢
  exact ⟨hp.1, (hsum p) ▸ hp.2⟩

/-- Concrete receipt (𝔽₇, two records `0, 1`): the LogUp sum moves with the pole.  At
pole `1` it is `1⁻¹ + 2⁻¹`, at pole `2` it is `2⁻¹ + 3⁻¹`, and these differ.  Both poles hit
neither record. -/
theorem logup_sum_moves_with_pole_F7 :
    (1 : ZMod 7)⁻¹ + (2 : ZMod 7)⁻¹ ≠ (2 : ZMod 7)⁻¹ + (3 : ZMod 7)⁻¹ ∧
      (∀ x ∈ ([0, 1] : List (ZMod 7)), (1 : ZMod 7) + x ≠ 0) ∧
      (∀ x ∈ ([0, 1] : List (ZMod 7)), (2 : ZMod 7) + x ≠ 0) := by
  have e2 : (2 : ZMod 7) * 4 = 1 := by decide
  have e3 : (3 : ZMod 7) * 5 = 1 := by decide
  have hne : (1 : ZMod 7) + 4 ≠ 4 + 5 := by decide
  have h1 : ∀ x ∈ ([0, 1] : List (ZMod 7)), (1 : ZMod 7) + x ≠ 0 := by decide
  have h2' : ∀ x ∈ ([0, 1] : List (ZMod 7)), (2 : ZMod 7) + x ≠ 0 := by decide
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h2 : (2 : ZMod 7)⁻¹ = 4 := inv_eq_of_mul_eq_one_right e2
  have h3 : (3 : ZMod 7)⁻¹ = 5 := inv_eq_of_mul_eq_one_right e3
  refine ⟨?_, h1, h2'⟩
  rw [inv_one, h2, h3]
  exact hne

end Algebra

/-! ## B. What the family chips take from `c`, and what they do not -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The tuple `c` with its IO pole replaced by `p`.  Every other coordinate stays put. -/
def withPole (c : OptimizedProductionChallengeTuple K F) (p : K) :
    OptimizedProductionChallengeTuple K F :=
  (c.1, ((c.2.1.1, p), c.2.2))

@[simp] theorem withPole_gamma (c : OptimizedProductionChallengeTuple K F) (p : K) :
    (withPole c p).2.1.1 = c.2.1.1 := rfl

@[simp] theorem withPole_pole (c : OptimizedProductionChallengeTuple K F) (p : K) :
    (withPole c p).2.1.2 = p := rfl

/-- The pole is read at memory `𝕂` slot `5`, and only there. -/
theorem memoryKOfTuple_withPole (c : OptimizedProductionChallengeTuple K F) (p : K) (q : ℕ) :
    memoryKOfTuple (withPole c p) q = if q = 5 then p else memoryKOfTuple c q := by
  rcases q with _ | _ | _ | _ | _ | _ | _ | _ | _ | q <;> rfl

/-- The pole is read at compute `𝕂` slot `8`, and only there. -/
theorem computeKOfTuple_withPole (c : OptimizedProductionChallengeTuple K F) (p : K) (q : ℕ) :
    computeKOfTuple (withPole c p) q = if q = 8 then p else computeKOfTuple c q := by
  rcases q with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | q <;> rfl

/-- **Coin-free compute publics.**  Off the walk block `0..5`, the family compute public map is
the same at every tuple.  This includes the IO terminal `requests` at `6..8`. -/
theorem familyComputePublic_coin_free (c c' : OptimizedProductionChallengeTuple K F) (j : ℕ)
    (hj : 6 ≤ j) : P.familyComputePublic c j = P.familyComputePublic c' j := by
  simp only [OptimizedFullStrictNockVMROMPackage.familyComputePublic]
  rw [computePublicOfTuple_eq_pkg_off_seed _ _ _ _ _ (by omega),
    computePublicOfTuple_eq_pkg_off_seed _ _ _ _ _ (by omega)]

/-- The compute `requests` public (slots `6..8`) is the package's, at every tuple. -/
theorem familyComputePublic_requests (c : OptimizedProductionChallengeTuple K F) (k : Fin 3) :
    P.familyComputePublic c (6 + (k : ℕ)) = P.optimized.computePublic (6 + (k : ℕ)) :=
  computePublicOfTuple_eq_pkg_off_seed _ _ _ _ _ (by omega)

/-- **Coin-free memory publics.**  Off the memory `initial_count` block `6..8`, the family
memory public map is the same at every tuple.  This includes the walk seed (`9..11`) and
`requests` (`12..14`). -/
theorem familyMemoryPublic_coin_free (c c' : OptimizedProductionChallengeTuple K F) (j : ℕ)
    (hj : ¬ (6 ≤ j ∧ j < 9)) : P.familyMemoryPublic c j = P.familyMemoryPublic c' j := by
  simp only [OptimizedFullStrictNockVMROMPackage.familyMemoryPublic]
  rw [memoryPublicOfTuple_eq_pkg _ _ _ _ _ _ hj, memoryPublicOfTuple_eq_pkg _ _ _ _ _ _ hj]

/-- The package's `requests` value, read off memory publics `12..14`.  No `c` occurs. -/
def pkgRequests : K :=
  ∑ k : Fin 3, P.optimized.memoryPublic (12 + (k : ℕ)) • P.optimized.basis k

/-! ## C. Acceptance pins the LogUp sum to a coin-free value -/

/-- **Acceptance forces the LogUp sum.**  At every tuple `c`, every accepted family memory
trace satisfies `Σ_{r ∈ responses} (compress c.2.1 r)⁻¹ = pkgRequests P`.  The right side does
not depend on `c`. -/
theorem requests_forced_at (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) :
    ((hostileResponsesAt P c Qm).map fun r => (FiniteIO.compress (chipCoinsAt c) r)⁻¹).sum =
      pkgRequests P := by
  rw [← hostile_responses_eq_sum_compress_at P c Qm hsat,
    ← hostile_requests_eq_sum_memRowTerms_at P c Qm hsat,
    gathered_requests_mem_at P c Qm]
  rfl

/-- **Negative control.**  A pole that hits a committed response record makes that record's
denominator vanish, and the family memory chip rejects the trace. -/
theorem rejected_of_response_poleHit_at (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hhit : ∃ r ∈ hostileResponsesAt P c Qm, c.2.1.2 + Walk.rlc c.2.1.1 r = 0) :
    ¬ RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm := by
  intro hsat
  obtain ⟨r, hr, h0⟩ := hhit
  exact compress_response_ne_zero_at P c Qm hsat hr h0

/-- The same rejection, stated through `IOPoleHitEvent` on any records whose responses are the
committed ones: a pole in the event (hit on the response side) is rejected. -/
theorem rejected_of_mem_poleHit_responses (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hhit : c.2.1.2 ∈ FiniteIO.IOPoleHitEvent
      (⟨[], hostileResponsesAt P c Qm⟩ : FiniteIO.PreChallengeRecords K 10) c.2.1.1) :
    ¬ RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm := by
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    List.nil_append] at hhit
  exact rejected_of_response_poleHit_at P c Qm hhit

/-! ## D. -/

/-- Off the RLC collision event, distinct records have distinct RLC values. -/
theorem nodup_rlc_of_not_collision (R : FiniteIO.PreChallengeRecords K 10) (γ : K)
    (hnd : R.responses.Nodup) (hγ : γ ∉ FiniteIO.IORLCCollisionEvent R) :
    (R.responses.map (Walk.rlc γ)).Nodup := by
  refine List.Nodup.map_on (fun u hu v hv huv => ?_) hnd
  by_contra hne
  apply hγ
  simp only [FiniteIO.IORLCCollisionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨u, List.mem_append_right _ hu, v, List.mem_append_right _ hv, hne, huv⟩

open Classical in
/-- **The pole fibre bound.**  Fix `c` except its pole.  Take any pole-indexed family of memory
traces `Qm p` whose committed response records are one list `rs` (the records are round-0/1
columns, committed before `(γ, pole)` per the paper), with distinct RLC values.  Then
at most `|rs|` poles are accepted. -/
theorem accepted_poles_card_le (c : OptimizedProductionChallengeTuple K F)
    (Qm : ∀ p : K, Fin (P.memoryChipAt (withPole c p)).rap.w → F[X])
    (rs : List (Fin 10 → K)) (hrs : ∀ p, hostileResponsesAt P (withPole c p) (Qm p) = rs)
    (hnd : (rs.map (Walk.rlc c.2.1.1)).Nodup) (hne : rs ≠ []) :
    (Finset.univ.filter fun p : K =>
        RAP.SatisfiesWithPreprocessing (P.memoryChipAt (withPole c p)) (Qm p)).card ≤
      rs.length := by
  classical
  have hxs : rs.map (Walk.rlc c.2.1.1) ≠ [] := by simpa using hne
  have h := logup_fibre_card_le_list (rs.map (Walk.rlc c.2.1.1)) hnd hxs (pkgRequests P)
  rw [List.length_map] at h
  refine le_trans (Finset.card_le_card fun p hp => ?_) h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  have hcomp : ∀ r : Fin 10 → K,
      FiniteIO.compress (chipCoinsAt (withPole c p)) r = p + Walk.rlc c.2.1.1 r := fun _ => rfl
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    have := compress_response_ne_zero_at P (withPole c p) (Qm p) hp (by rw [hrs p]; exact hr)
    rwa [hcomp] at this
  · have := requests_forced_at P (withPole c p) (Qm p) hp
    rw [hrs p] at this
    simpa [List.map_map, Function.comp_def, hcomp] using this

open Classical in
/-- Under the hypotheses of `accepted_poles_card_le`, and for any
honest records `R` whose responses are `rs`, a pole exists that is OUTSIDE the IO-pole hit event
of `R` and at which the fill is REJECTED.  The only condition is
`|R.requests| + 2·|rs| < |𝕂|`.  So "`DeployedAcceptanceAt` at every `c ∉ IOPoleHitEvent`" fails
at the deployed chip family for every fill whose records do not move with the pole. -/
theorem exists_good_pole_rejected (c : OptimizedProductionChallengeTuple K F)
    (Qm : ∀ p : K, Fin (P.memoryChipAt (withPole c p)).rap.w → F[X])
    (R : FiniteIO.PreChallengeRecords K 10)
    (hrs : ∀ p, hostileResponsesAt P (withPole c p) (Qm p) = R.responses)
    (hnd : (R.responses.map (Walk.rlc c.2.1.1)).Nodup) (hne : R.responses ≠ [])
    (hK : R.requests.length + 2 * R.responses.length < Fintype.card K) :
    ∃ p : K, p ∉ FiniteIO.IOPoleHitEvent R c.2.1.1 ∧
      ¬ RAP.SatisfiesWithPreprocessing (P.memoryChipAt (withPole c p)) (Qm p) := by
  classical
  by_contra hall
  push Not at hall
  have hcover : (Finset.univ : Finset K) ⊆
      FiniteIO.IOPoleHitEvent R c.2.1.1 ∪
        Finset.univ.filter fun p : K =>
          RAP.SatisfiesWithPreprocessing (P.memoryChipAt (withPole c p)) (Qm p) := by
    intro p _
    by_cases hp : p ∈ FiniteIO.IOPoleHitEvent R c.2.1.1
    · exact Finset.mem_union_left _ hp
    · exact Finset.mem_union_right _ (by simpa using hall p hp)
  have h1 := FiniteIO.IOPoleHitEvent_card_le R c.2.1.1
  have h2 := accepted_poles_card_le P c Qm R.responses hrs hnd hne
  have := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ] at this
  omega

/-- The same existence, for the full two-chip
acceptance: some pole outside the honest IO-pole hit event admits no compute trace at all that
pairs with the fill's memory trace. -/
theorem exists_good_pole_not_deployed (c : OptimizedProductionChallengeTuple K F)
    (Qm : ∀ p : K, Fin (P.memoryChipAt (withPole c p)).rap.w → F[X])
    (R : FiniteIO.PreChallengeRecords K 10)
    (hrs : ∀ p, hostileResponsesAt P (withPole c p) (Qm p) = R.responses)
    (hnd : (R.responses.map (Walk.rlc c.2.1.1)).Nodup) (hne : R.responses ≠ [])
    (hK : R.requests.length + 2 * R.responses.length < Fintype.card K) :
    ∃ p : K, p ∉ FiniteIO.IOPoleHitEvent R c.2.1.1 ∧
      ∀ Qc : Fin (P.computeChipAt (withPole c p)).rap.w → F[X],
        ¬ DeployedAcceptanceAt P (withPole c p) Qc (Qm p) := by
  obtain ⟨p, hp, hrej⟩ := exists_good_pole_rejected P c Qm R hrs hnd hne hK
  exact ⟨p, hp, fun _ hacc => hrej hacc.memory_satisfies⟩

end

end Nock.NockVMROM.Thm54.CoinParamCompleteness

#print axioms Nock.NockVMROM.Thm54.CoinParamCompleteness.logup_fibre_card_le
#print axioms Nock.NockVMROM.Thm54.CoinParamCompleteness.requests_forced_at
#print axioms Nock.NockVMROM.Thm54.CoinParamCompleteness.accepted_poles_card_le
#print axioms Nock.NockVMROM.Thm54.CoinParamCompleteness.exists_good_pole_rejected
#print axioms Nock.NockVMROM.Thm54.CoinParamCompleteness.exists_good_pole_not_deployed
