import Nock.NockVMROM.Thm54.FiniteFieldIOAIR

/-!
# Counted soundness of the prover-committed finite-field IO argument

`FiniteIO.FiniteIOAccepts` is an acceptance predicate over a plain finite field `K`; the two
coins `gamma` and `pole` are *sampled*.  Accordingly **no zero-error claim is made**: this module
identifies exactly three finite-field failure events, gives each a nonzero-polynomial certificate
and an explicit cardinality bound, and proves that outside those events acceptance implies the
record-level IO language `IO.LIO`.

## The three counted events

1. `IOPoleHitEvent records gamma` — the sampled pole hits a compressed record, so a denominator
   vanishes.  `card ≤ |requests| + |responses|`.  This event is *rejected* rather than
   mis-accepted: the inverse gate has no solution there (`request_compress_ne_zero`); it is the
   completeness-side obstruction (`finiteIO_complete_of_LIO`).
2. `IORLCCollisionEvent records` — two unequal records among `requests ++ responses` collide
   under `RLC^gamma`.  `card ≤ (|requests| + |responses|)² · (m − 1)` (union bound over index
   pairs of the single-pair Schwartz–Zippel bound `Walk.rlc_collision_card_le`).
3. `IOLogDerivEvent records gamma` — the cleared-denominator log-derivative difference
   polynomial `ioQP` is nonzero yet vanishes at the sampled pole.
   |responses|` (univariate Schwartz–Zippel, `Walk.card_roots_le`).

`finiteIO_sound` concludes `IO.LIO` from acceptance outside events (2) and (3); event (1) is
automatically excluded by acceptance itself.  The joint `(gamma, pole)` failure set
`IOFailureEvent` collects all three with an explicit union bound for the cost/failure-union
accounting.
-/

namespace Nock.NockVMROM.Thm54.FiniteIO

open Nock
open Polynomial
open scoped BigOperators

/-! ## A generic reciprocal-sum identity -/

/-- Clearing all denominators of a sum of reciprocals: `(Σ 1/dᵢ)·∏ dᵢ = Σ ∏_{i'≠i} d_{i'}`. -/
theorem sum_inv_mul_prod {L : Type*} [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → L) (hd : ∀ i, d i ≠ 0) :
    (∑ i, (d i)⁻¹) * (∏ i, d i) = ∑ i, ∏ i' ∈ Finset.univ.erase i, d i' := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i), inv_mul_cancel_left₀ (hd i)]

variable {K : Type*} [Field K] {m : ℕ}

/-! ## The cleared-denominator polynomials -/

/-- `∏ᵢ (X + aᵢ)`, the common denominator of a log-derivative sum. -/
noncomputable def denomP {n : ℕ} (a : Fin n → K) : K[X] := ∏ i, (X + C (a i))

/-- `Σᵢ ∏_{i'≠i} (X + a_{i'})`, the cleared-denominator numerator of a log-derivative sum. -/
noncomputable def numerP {n : ℕ} (a : Fin n → K) : K[X] :=
  ∑ i, ∏ i' ∈ Finset.univ.erase i, (X + C (a i'))

theorem denomP_ne_zero {n : ℕ} (a : Fin n → K) : denomP a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => SetEq.poleP_ne_zero (a i))

theorem denomP_natDegree_le {n : ℕ} (a : Fin n → K) : (denomP a).natDegree ≤ n := by
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  have h1 : (∑ i : Fin n, (X + C (a i)).natDegree) = n := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => Polynomial.natDegree_X_add_C (a i))]
    simp
  exact le_of_eq h1

theorem numerP_natDegree_le {n : ℕ} (a : Fin n → K) : (numerP a).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  calc (∑ i' ∈ Finset.univ.erase i, (X + C (a i')).natDegree)
      = ∑ _i' ∈ Finset.univ.erase i, 1 :=
        Finset.sum_congr rfl (fun i' _ => Polynomial.natDegree_X_add_C (a i'))
    _ = (Finset.univ.erase i).card := by simp
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.erase_subset _ _)
    _ = n := by simp

theorem denomP_eval {n : ℕ} (a : Fin n → K) (z : K) :
    (denomP a).eval z = ∏ i, (z + a i) := by
  simp [denomP, Polynomial.eval_prod]

theorem numerP_eval {n : ℕ} (a : Fin n → K) (z : K) :
    (numerP a).eval z = ∑ i, ∏ i' ∈ Finset.univ.erase i, (z + a i') := by
  simp [numerP, Polynomial.eval_finsetSum, Polynomial.eval_prod]

/-- The numeric (finite-field) clearing identity at a point where no denominator vanishes. -/
theorem sum_inv_eval {n : ℕ} (a : Fin n → K) (z : K) (hz : ∀ i, z + a i ≠ 0) :
    (∑ i, (z + a i)⁻¹) * (denomP a).eval z = (numerP a).eval z := by
  rw [denomP_eval, numerP_eval]
  exact sum_inv_mul_prod (fun i => z + a i) hz

/-- The symbolic (`RatFunc`) clearing identity: the same computation with the log-derivative
    variable left symbolic.  This is the bridge back to `SetEq.frac`. -/
theorem frac_sum_mul_denom {n : ℕ} (a : Fin n → K) :
    (∑ i, SetEq.frac (a i)) * algebraMap K[X] (RatFunc K) (denomP a)
      = algebraMap K[X] (RatFunc K) (numerP a) := by
  have hd : algebraMap K[X] (RatFunc K) (denomP a)
      = ∏ i, algebraMap K[X] (RatFunc K) (X + C (a i)) := by
    rw [denomP]; exact map_prod _ _ _
  have hn : algebraMap K[X] (RatFunc K) (numerP a)
      = ∑ i, ∏ i' ∈ Finset.univ.erase i, algebraMap K[X] (RatFunc K) (X + C (a i')) := by
    rw [numerP, map_sum]
    exact Finset.sum_congr rfl (fun i _ => map_prod _ _ _)
  rw [hd, hn]
  exact sum_inv_mul_prod (fun i => algebraMap K[X] (RatFunc K) (X + C (a i)))
    (fun i => SetEq.algebraMap_poleP_ne_zero (a i))

/-! ## The compressed request/response values and the difference polynomial -/

variable [Fintype K] [DecidableEq K]

/-- The `gamma`-compressed request values. -/
def reqVals (records : PreChallengeRecords K m) (γ : K) :
    Fin records.requests.length → K :=
  fun i => Walk.rlc γ (records.requests.get i)

/-- The `gamma`-compressed response values. -/
def respVals (records : PreChallengeRecords K m) (γ : K) :
    Fin records.responses.length → K :=
  fun j => Walk.rlc γ (records.responses.get j)

/-- **The log-derivative difference polynomial.**  `ioQP = 0` says the two log-derivative sums
    coincide identically in the pole variable; the sampled-pole check only tests `ioQP(pole) = 0`,
    which is why event (3) below must be counted. -/
noncomputable def ioQP (records : PreChallengeRecords K m) (γ : K) : K[X] :=
  numerP (reqVals records γ) * denomP (respVals records γ)
    - numerP (respVals records γ) * denomP (reqVals records γ)

/-- `denomP` is the product of `(X + aᵢ)`, so its derivative is `numerP`. -/
theorem derivative_denomP {n : ℕ} (a : Fin n → K) :
    (denomP a).derivative = numerP a := by
  simp only [denomP, numerP]
  rw [Polynomial.derivative_prod_finset]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.derivative_X_add_C, mul_one]

/-- The `Fin`-indexed product agrees with the list product. -/
theorem denomP_eq_list_prod {n : ℕ} (a : Fin n → K) :
    denomP a = (List.ofFn fun i => (X + C (a i) : K[X])).prod := by
  simp [denomP, List.prod_ofFn]

theorem ofFn_reqVals (records : PreChallengeRecords K m) (γ : K) :
    List.ofFn (reqVals records γ) = records.requests.map (Walk.rlc γ) := by
  apply List.ext_get
  · simp
  · intro n h1 h2
    simp [reqVals]

theorem ofFn_respVals (records : PreChallengeRecords K m) (γ : K) :
    List.ofFn (respVals records γ) = records.responses.map (Walk.rlc γ) := by
  apply List.ext_get
  · simp
  · intro n h1 h2
    simp [respVals]

/-- If the two columns are a permutation, `ioQP` is identically zero — no characteristic bound. -/
theorem ioQP_eq_zero_of_perm (records : PreChallengeRecords K m) (γ : K)
    (h : records.requests.Perm records.responses) :
    ioQP records γ = 0 := by
  have hlen := h.length_eq
  have hmap : (records.requests.map (Walk.rlc γ)).Perm
      (records.responses.map (Walk.rlc γ)) := h.map _
  have hperm : (List.ofFn (reqVals records γ)).Perm (List.ofFn (respVals records γ)) := by
    simpa [ofFn_reqVals, ofFn_respVals] using hmap
  have hden : denomP (reqVals records γ) = denomP (respVals records γ) := by
    rw [denomP_eq_list_prod, denomP_eq_list_prod]
    have h1 : (List.ofFn fun i => (X + C (reqVals records γ i) : K[X])) =
        (List.ofFn (reqVals records γ)).map (fun t => X + C t) := by
      rw [List.map_ofFn]; rfl
    have h2 : (List.ofFn fun i => (X + C (respVals records γ i) : K[X])) =
        (List.ofFn (respVals records γ)).map (fun t => X + C t) := by
      rw [List.map_ofFn]; rfl
    rw [h1, h2]
    exact (hperm.map (fun t => (X + C t : K[X]))).prod_eq
  have hnum : numerP (reqVals records γ) = numerP (respVals records γ) := by
    rw [← derivative_denomP, ← derivative_denomP, hden]
  simp [ioQP, hden, hnum]

theorem ioQP_natDegree_le (records : PreChallengeRecords K m) (γ : K) :
    (ioQP records γ).natDegree
      ≤ records.requests.length + records.responses.length := by
  refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
  rw [max_le_iff]
  constructor
  · exact le_trans (Polynomial.natDegree_mul_le)
      (Nat.add_le_add (numerP_natDegree_le _) (denomP_natDegree_le _))
  · exact le_trans (Polynomial.natDegree_mul_le)
      (le_trans (Nat.add_le_add (numerP_natDegree_le _) (denomP_natDegree_le _))
        (by omega))

/-! ## The three counted events -/

/-- **Event (1): the sampled pole hits a compressed record.**  Then the corresponding denominator
    `pole + RLC^gamma(record)` vanishes and the inverse gate is unsatisfiable. -/
def IOPoleHitEvent (records : PreChallengeRecords K m) (γ : K) : Finset K :=
  Finset.univ.filter
    (fun z => ∃ v ∈ records.requests ++ records.responses, z + Walk.rlc γ v = 0)

/-- **Event (2): two unequal records collide under the record-RLC challenge.** -/
def IORLCCollisionEvent (records : PreChallengeRecords K m) : Finset K :=
  Finset.univ.filter
    (fun γ => ∃ u ∈ records.requests ++ records.responses,
      ∃ v ∈ records.requests ++ records.responses, u ≠ v ∧ Walk.rlc γ u = Walk.rlc γ v)

open Classical in
/-- **Event (3): unequal log-derivative sums agree at the sampled pole.**  The certificate is the
    nonzero polynomial `ioQP records gamma`. -/
noncomputable def IOLogDerivEvent (records : PreChallengeRecords K m) (γ : K) : Finset K :=
  Finset.univ.filter (fun z => ioQP records γ ≠ 0 ∧ (ioQP records γ).eval z = 0)

/-- **Event (1) bound:** at most one bad pole per record. -/
theorem IOPoleHitEvent_card_le (records : PreChallengeRecords K m) (γ : K) :
    (IOPoleHitEvent records γ).card
      ≤ records.requests.length + records.responses.length := by
  classical
  have hsub : IOPoleHitEvent records γ ⊆
      ((records.requests ++ records.responses).map (fun v => -Walk.rlc γ v)).toFinset := by
    intro z hz
    simp only [IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨v, hv, hzv⟩ := hz
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨v, hv, (add_eq_zero_iff_eq_neg.mp hzv).symm⟩
  calc (IOPoleHitEvent records γ).card
      ≤ ((records.requests ++ records.responses).map (fun v => -Walk.rlc γ v)).toFinset.card :=
        Finset.card_le_card hsub
    _ ≤ ((records.requests ++ records.responses).map (fun v => -Walk.rlc γ v)).length :=
        List.toFinset_card_le _
    _ = records.requests.length + records.responses.length := by simp

/-- **Event (2) bound:** the union bound over ordered index pairs of the single-pair RLC
    collision bound `Walk.rlc_collision_card_le` (`≤ m − 1` challenges per pair). -/
theorem IORLCCollisionEvent_card_le (records : PreChallengeRecords K m) :
    (IORLCCollisionEvent records).card
      ≤ (records.requests.length + records.responses.length)
          * (records.requests.length + records.responses.length) * (m - 1) := by
  classical
  set l := records.requests ++ records.responses with hl
  set n := l.length with hn
  set g : ℕ × ℕ → Finset K := fun q =>
    Finset.univ.filter (fun γ : K => l.getD q.1 0 ≠ l.getD q.2 0 ∧
      Walk.rlc γ (l.getD q.1 0) = Walk.rlc γ (l.getD q.2 0)) with hg
  have hgetD : ∀ (i : ℕ) (h : i < l.length), l.getD i 0 = l[i] := by
    intro i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  have hsub : IORLCCollisionEvent records
      ⊆ (Finset.range n ×ˢ Finset.range n).biUnion g := by
    intro γ hγ
    simp only [IORLCCollisionEvent, Finset.mem_filter, Finset.mem_univ, true_and, ← hl] at hγ
    obtain ⟨u, hu, v, hv, hne, heq⟩ := hγ
    obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hu
    obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hv
    refine Finset.mem_biUnion.mpr ⟨(i, j), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨hi, hj⟩
    · have e1 : l.getD i 0 = u := by rw [hgetD i hi]; exact hgi
      have e2 : l.getD j 0 = v := by rw [hgetD j hj]; exact hgj
      simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and, e1, e2]
      exact ⟨hne, heq⟩
  have hcard : ∀ q ∈ Finset.range n ×ˢ Finset.range n, (g q).card ≤ m - 1 := by
    intro q _
    by_cases hd : l.getD q.1 0 = l.getD q.2 0
    · have hempty : g q = ∅ := by
        simp only [hg, Finset.filter_eq_empty_iff]
        intro γ _
        rintro ⟨hne, -⟩
        exact hne hd
      rw [hempty]; simp
    · refine le_trans (Finset.card_le_card ?_) (Walk.rlc_collision_card_le hd)
      intro γ hγ
      simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      exact hγ.2
  calc (IORLCCollisionEvent records).card
      ≤ ((Finset.range n ×ˢ Finset.range n).biUnion g).card := Finset.card_le_card hsub
    _ ≤ ∑ _q ∈ Finset.range n ×ˢ Finset.range n, (m - 1) :=
        le_trans Finset.card_biUnion_le (Finset.sum_le_sum hcard)
    _ = n * n * (m - 1) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, smul_eq_mul, mul_assoc]
    _ = (records.requests.length + records.responses.length)
          * (records.requests.length + records.responses.length) * (m - 1) := by
        rw [hn, hl, List.length_append]

/-- **Event (3) bound:** univariate Schwartz–Zippel on the nonzero certificate `ioQP`. -/
theorem IOLogDerivEvent_card_le (records : PreChallengeRecords K m) (γ : K) :
    (IOLogDerivEvent records γ).card
      ≤ records.requests.length + records.responses.length := by
  by_cases hQ : ioQP records γ = 0
  · have hzero : (IOLogDerivEvent records γ).card = 0 := by
      rw [Finset.card_eq_zero, IOLogDerivEvent, Finset.filter_eq_empty_iff]
      intro z _
      rintro ⟨hne, -⟩
      exact hne hQ
    omega
  · refine le_trans (Finset.card_le_card (?_ : IOLogDerivEvent records γ ⊆
        Finset.univ.filter (fun z : K => (ioQP records γ).eval z = 0))) ?_
    · intro z hz
      simp only [IOLogDerivEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hz.2
    · exact le_trans (Walk.card_roots_le _ hQ) (ioQP_natDegree_le records γ)

/-! ## The joint failure event (for the failure-union / cost accounting) -/

open Classical in
/-- All three counted events, as a single subset of the `(gamma, pole)` coin space. -/
noncomputable def IOFailureEvent (records : PreChallengeRecords K m) : Finset (K × K) :=
  Finset.univ.filter (fun q => q.1 ∈ IORLCCollisionEvent records
    ∨ q.2 ∈ IOPoleHitEvent records q.1 ∨ q.2 ∈ IOLogDerivEvent records q.1)

/-- Component-wise exclusion of the three counted events. -/
theorem notMem_IOFailureEvent_of {records : PreChallengeRecords K m} {γ pole : K}
    (hγ : γ ∉ IORLCCollisionEvent records)
    (hhit : pole ∉ IOPoleHitEvent records γ)
    (hlog : pole ∉ IOLogDerivEvent records γ) :
    (γ, pole) ∉ IOFailureEvent records := by
  intro h
  simp only [IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rcases h with h | h | h
  · exact hγ h
  · exact hhit h
  · exact hlog h

theorem mem_IOFailureEvent_iff {records : PreChallengeRecords K m} {γ pole : K} :
    (γ, pole) ∈ IOFailureEvent records ↔
      γ ∈ IORLCCollisionEvent records ∨
      pole ∈ IOPoleHitEvent records γ ∨
      pole ∈ IOLogDerivEvent records γ := by
  simp [IOFailureEvent]

theorem IOLogDerivEvent_eq_empty_of_perm (records : PreChallengeRecords K m) (γ : K)
    (h : records.requests.Perm records.responses) :
    IOLogDerivEvent records γ = ∅ := by
  classical
  have hQ : ioQP records γ = 0 := ioQP_eq_zero_of_perm records γ h
  rw [IOLogDerivEvent, Finset.filter_eq_empty_iff]
  intro z _
  rintro ⟨hne, -⟩
  exact hne hQ

theorem IORLCCollisionEvent_of_mem_subset
    {R1 R2 : PreChallengeRecords K m}
    (hsub : ∀ v, v ∈ R1.requests ++ R1.responses → v ∈ R2.requests ++ R2.responses)
    {γ : K} (h : γ ∈ IORLCCollisionEvent R1) :
    γ ∈ IORLCCollisionEvent R2 := by
  simp only [IORLCCollisionEvent, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  obtain ⟨u, hu, v, hv, hne, heq⟩ := h
  exact ⟨u, hsub u hu, v, hsub v hv, hne, heq⟩

/-- Concatenation membership is symmetric in the two columns. -/
theorem mem_requests_append_responses_swap {A B : List (Fin m → K)} {v : Fin m → K} :
    v ∈ A ++ B ↔ v ∈ B ++ A := by
  simp [List.mem_append, or_comm]

theorem IORLCCollisionEvent_swap (A B : List (Fin m → K)) :
    IORLCCollisionEvent ⟨A, B⟩ = IORLCCollisionEvent ⟨B, A⟩ := by
  ext γ
  simp only [IORLCCollisionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro ⟨u, hu, v, hv, hne, heq⟩
  · exact ⟨u, (mem_requests_append_responses_swap).1 hu, v,
      (mem_requests_append_responses_swap).1 hv, hne, heq⟩
  · exact ⟨u, (mem_requests_append_responses_swap).1 hu, v,
      (mem_requests_append_responses_swap).1 hv, hne, heq⟩

theorem IOPoleHitEvent_swap (A B : List (Fin m → K)) (γ : K) :
    IOPoleHitEvent ⟨A, B⟩ γ = IOPoleHitEvent ⟨B, A⟩ γ := by
  ext z
  simp only [IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro ⟨v, hv, hz⟩
  · exact ⟨v, (mem_requests_append_responses_swap).1 hv, hz⟩
  · exact ⟨v, (mem_requests_append_responses_swap).1 hv, hz⟩

theorem ioQP_swap (A B : List (Fin m → K)) (γ : K) :
    ioQP ⟨A, B⟩ γ = - ioQP ⟨B, A⟩ γ := by
  simp only [ioQP]
  have h1 : reqVals (⟨A, B⟩ : PreChallengeRecords K m) γ =
      respVals (⟨B, A⟩ : PreChallengeRecords K m) γ := rfl
  have h2 : respVals (⟨A, B⟩ : PreChallengeRecords K m) γ =
      reqVals (⟨B, A⟩ : PreChallengeRecords K m) γ := rfl
  rw [h1, h2]
  ring

theorem IOLogDerivEvent_swap (A B : List (Fin m → K)) (γ : K) :
    IOLogDerivEvent ⟨A, B⟩ γ = IOLogDerivEvent ⟨B, A⟩ γ := by
  ext z
  have hQ : ioQP ⟨A, B⟩ γ = - ioQP ⟨B, A⟩ γ := ioQP_swap A B γ
  have hne : ioQP ⟨A, B⟩ γ ≠ 0 ↔ ioQP ⟨B, A⟩ γ ≠ 0 := by
    constructor
    · intro h h0; exact h (by rw [hQ, h0, neg_zero])
    · intro h h0; exact h (neg_eq_zero.mp (by rw [← hQ, h0]))
  have hev : (ioQP ⟨A, B⟩ γ).eval z = 0 ↔ (ioQP ⟨B, A⟩ γ).eval z = 0 := by
    rw [hQ, Polynomial.eval_neg, neg_eq_zero]
  simp only [IOLogDerivEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr hne hev

theorem IOFailureEvent_swap (A B : List (Fin m → K)) :
    IOFailureEvent ⟨A, B⟩ = IOFailureEvent ⟨B, A⟩ := by
  ext q
  rw [mem_IOFailureEvent_iff, mem_IOFailureEvent_iff,
    IORLCCollisionEvent_swap A B, IOPoleHitEvent_swap A B, IOLogDerivEvent_swap A B]

/-- Acceptance itself excludes the pole-hit component at the exact sampled pole. -/
theorem pole_not_hit_of_accepts
    {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins}
    (h : FiniteIOAccepts records coins w) :
    coins.pole ∉ IOPoleHitEvent records coins.gamma := by
  intro hhit
  simp only [IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hhit
  obtain ⟨v, hv, hzero⟩ := hhit
  rw [List.mem_append] at hv
  rcases hv with hv | hv
  · obtain ⟨i, rfl⟩ := List.get_of_mem hv
    exact request_compress_ne_zero h i (by simpa [compress] using hzero)
  · obtain ⟨i, rfl⟩ := List.get_of_mem hv
    exact response_compress_ne_zero h i (by simpa [compress] using hzero)

/-- The exported IO failure-union workload: the counted `(gamma, pole)` failure mass, for the
    cost/failure-union accounting a downstream packet folds in.  `CompleteProductionCost` is not
    mutated; this is the additive export. -/
def ioFailureUnionBound (m k₁ k₂ cardK : ℕ) : ℕ :=
  ((k₁ + k₂) * (k₁ + k₂) * (m - 1)) * cardK + cardK * (2 * (k₁ + k₂))

/-- **Joint failure bound.**  Over the `|K|²` coin pairs, the number of `(gamma, pole)` pairs in
    any of the three counted events is at most `ioFailureUnionBound`. -/
theorem IOFailureEvent_card_le (records : PreChallengeRecords K m) :
    (IOFailureEvent records).card
      ≤ ioFailureUnionBound m records.requests.length records.responses.length
          (Fintype.card K) := by
  classical
  set k₁ := records.requests.length with hk₁
  set k₂ := records.responses.length with hk₂
  set S : Finset (K × K) := (IORLCCollisionEvent records) ×ˢ Finset.univ with hS
  set T : Finset (K × K) := Finset.univ.biUnion (fun γ : K =>
    ({γ} : Finset K) ×ˢ (IOPoleHitEvent records γ ∪ IOLogDerivEvent records γ)) with hT
  have hsub : IOFailureEvent records ⊆ S ∪ T := by
    intro q hq
    simp only [IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rcases hq with h1 | h2 | h3
    · exact Finset.mem_union_left _ (by simp only [hS, Finset.mem_product]; exact ⟨h1, by simp⟩)
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_union]
      refine ⟨?_, Or.inl h2⟩
      trivial
    · refine Finset.mem_union_right _ ?_
      refine Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_union]
      refine ⟨?_, Or.inr h3⟩
      trivial
  have hScard : S.card ≤ (k₁ + k₂) * (k₁ + k₂) * (m - 1) * Fintype.card K := by
    rw [hS, Finset.card_product, Finset.card_univ]
    exact Nat.mul_le_mul_right _ (IORLCCollisionEvent_card_le records)
  have hTcard : T.card ≤ Fintype.card K * (2 * (k₁ + k₂)) := by
    refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ : K => 2 * (k₁ + k₂))
      (fun γ (_ : γ ∈ Finset.univ) => ?_)) ?_
    · rw [Finset.card_product, Finset.card_singleton, one_mul]
      refine le_trans (Finset.card_union_le _ _) ?_
      have := IOPoleHitEvent_card_le records γ
      have := IOLogDerivEvent_card_le records γ
      omega
    · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc (IOFailureEvent records).card ≤ (S ∪ T).card := Finset.card_le_card hsub
    _ ≤ S.card + T.card := Finset.card_union_le _ _
    _ ≤ (k₁ + k₂) * (k₁ + k₂) * (m - 1) * Fintype.card K
          + Fintype.card K * (2 * (k₁ + k₂)) := Nat.add_le_add hScard hTcard
    _ = ioFailureUnionBound m k₁ k₂ (Fintype.card K) := rfl

/-! ## RLC injectivity outside event (2) -/

/-- Outside the RLC-collision event the compression `RLC^gamma` is injective on the records that
    actually occur. -/
theorem rlc_inj_of_not_collision {records : PreChallengeRecords K m} {γ : K}
    (hγ : γ ∉ IORLCCollisionEvent records) {u v : Fin m → K}
    (hu : u ∈ records.requests ++ records.responses)
    (hv : v ∈ records.requests ++ records.responses)
    (heq : Walk.rlc γ u = Walk.rlc γ v) : u = v := by
  by_contra hne
  exact hγ (by
    simp only [IORLCCollisionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, hu, v, hv, hne, heq⟩)

/-! ## The counted soundness theorem -/

variable {p : ℕ} [CharP K p]

/-- Everything the
soundness argument uses of the accepted witness is (i) every compressed denominator is nonzero
and (ii) the sampled-pole log-derivative identity between the two sums. -/
theorem finiteIO_sound_of_identity {Ksz : ℕ} (records : PreChallengeRecords K m)
    (coins : IOCoins K)
    (hdA : ∀ i, coins.pole + reqVals records coins.gamma i ≠ 0)
    (hdB : ∀ j, coins.pole + respVals records coins.gamma j ≠ 0)
    (hend : (∑ i, (coins.pole + reqVals records coins.gamma i)⁻¹) =
      ∑ j, (coins.pole + respVals records coins.gamma j)⁻¹)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup) (hrespnd : records.responses.Nodup)
    (hγ : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    IO.LIO Ksz records.requests records.responses := by
  classical
  set A := reqVals records coins.gamma with hA
  set B := respVals records coins.gamma with hB
  -- hence the difference polynomial vanishes at the pole
  have hQeval : (ioQP records coins.gamma).eval coins.pole = 0 := by
    have hSA := sum_inv_eval A coins.pole hdA
    have hSB := sum_inv_eval B coins.pole hdB
    simp only [ioQP, Polynomial.eval_sub, Polynomial.eval_mul, ← hA, ← hB]
    have h1 : (numerP A).eval coins.pole * (denomP B).eval coins.pole
        = ((∑ i, (coins.pole + A i)⁻¹) * (denomP A).eval coins.pole)
            * (denomP B).eval coins.pole := by rw [hSA]
    have h2 : (numerP B).eval coins.pole * (denomP A).eval coins.pole
        = ((∑ j, (coins.pole + B j)⁻¹) * (denomP B).eval coins.pole)
            * (denomP A).eval coins.pole := by rw [hSB]
    rw [h1, h2, hend]
    ring
  -- outside event (3), the difference polynomial is identically zero
  have hQ : ioQP records coins.gamma = 0 := by
    by_contra hQ0
    exact hpole (by
      simp only [IOLogDerivEvent, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hQ0, hQeval⟩)
  -- lift to the symbolic log-derivative identity in `RatFunc K`
  have hQ' : numerP A * denomP B = numerP B * denomP A := by
    have hh := hQ
    unfold ioQP at hh
    rw [← hA, ← hB, sub_eq_zero] at hh
    exact hh
  have hmapQ : algebraMap K[X] (RatFunc K) (numerP A) * algebraMap K[X] (RatFunc K) (denomP B)
      = algebraMap K[X] (RatFunc K) (numerP B) * algebraMap K[X] (RatFunc K) (denomP A) := by
    rw [← map_mul, ← map_mul, hQ']
  have hdAne : algebraMap K[X] (RatFunc K) (denomP A) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact denomP_ne_zero A
  have hdBne : algebraMap K[X] (RatFunc K) (denomP B) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact denomP_ne_zero B
  have hfrac : (∑ i, SetEq.frac (A i)) = ∑ j, SetEq.frac (B j) := by
    have hA' := frac_sum_mul_denom A
    have hB' := frac_sum_mul_denom B
    have hkey : (∑ i, SetEq.frac (A i))
          * (algebraMap K[X] (RatFunc K) (denomP A) * algebraMap K[X] (RatFunc K) (denomP B))
        = (∑ j, SetEq.frac (B j))
          * (algebraMap K[X] (RatFunc K) (denomP A) * algebraMap K[X] (RatFunc K) (denomP B)) := by
      calc (∑ i, SetEq.frac (A i))
            * (algebraMap K[X] (RatFunc K) (denomP A) * algebraMap K[X] (RatFunc K) (denomP B))
          = ((∑ i, SetEq.frac (A i)) * algebraMap K[X] (RatFunc K) (denomP A))
              * algebraMap K[X] (RatFunc K) (denomP B) := by ring
        _ = algebraMap K[X] (RatFunc K) (numerP A) * algebraMap K[X] (RatFunc K) (denomP B) := by
              rw [hA']
        _ = algebraMap K[X] (RatFunc K) (numerP B) * algebraMap K[X] (RatFunc K) (denomP A) :=
              hmapQ
        _ = ((∑ j, SetEq.frac (B j)) * algebraMap K[X] (RatFunc K) (denomP B))
              * algebraMap K[X] (RatFunc K) (denomP A) := by rw [hB']
        _ = (∑ j, SetEq.frac (B j))
              * (algebraMap K[X] (RatFunc K) (denomP A)
                  * algebraMap K[X] (RatFunc K) (denomP B)) := by ring
    exact mul_right_cancel₀ (mul_ne_zero hdAne hdBne) hkey
  -- responses compress injectively outside event (2)
  have hBinj : Function.Injective B := by
    intro j₁ j₂ hj
    have hmem : ∀ j : Fin records.responses.length,
        records.responses.get j ∈ records.requests ++ records.responses :=
      fun j => List.mem_append_right _ (List.get_mem _ _)
    have hrec := rlc_inj_of_not_collision hγ (hmem j₁) (hmem j₂) hj
    exact List.nodup_iff_injective_get.mp hrespnd hrec
  -- the multiplicities are all `1`
  haveI : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero K (by omega)⟩
  have hone : ∀ j : Fin records.responses.length, (1 : ZMod p) ≠ 0 := fun _ => one_ne_zero
  have hsumcast : (∑ i, SetEq.frac (A i))
      = ∑ j, ((SetEq.castZ p (1 : ZMod p) : K)) • SetEq.frac (B j) := by
    rw [hfrac, map_one]
    exact Finset.sum_congr rfl (fun j _ => (one_smul _ _).symm)
  have himg0 :=
    SetEq.set_inclusion_eq_of_injective (p := p)
      (lt_of_le_of_lt hKreq.2 hKp) (lt_of_le_of_lt hKresp hKp) A B hBinj
      (fun _ => (1 : ZMod p)) hone hsumcast
  rw [Finset.ext_iff] at himg0
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at himg0
  -- `himg0 : ∀ x, (∃ i, A i = x) ↔ (∃ j, B j = x)`, free of any decidability instance
  -- lift the compressed-value set equality back to records
  have hfin : records.requests.toFinset = records.responses.toFinset := by
    apply Finset.Subset.antisymm
    · intro u hu
      rw [List.mem_toFinset] at hu
      obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hu
      have hget : records.requests.get ⟨i, hi⟩ = u := by
        rw [List.get_eq_getElem]; exact hgi
      obtain ⟨j, hj⟩ := (himg0 (Walk.rlc coins.gamma u)).mp
        ⟨⟨i, hi⟩, by rw [hA]; show Walk.rlc coins.gamma (records.requests.get ⟨i, hi⟩) = _
                     rw [hget]⟩
      have hueq : records.responses.get j = u := by
        refine rlc_inj_of_not_collision hγ (List.mem_append_right _ (List.get_mem _ _))
          (List.mem_append_left _ hu) ?_
        rw [hB] at hj
        exact hj
      rw [List.mem_toFinset, ← hueq]
      exact List.get_mem _ _
    · intro v hv
      rw [List.mem_toFinset] at hv
      obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hv
      have hget : records.responses.get ⟨j, hj⟩ = v := by
        rw [List.get_eq_getElem]; exact hgj
      obtain ⟨i, hi⟩ := (himg0 (Walk.rlc coins.gamma v)).mpr
        ⟨⟨j, hj⟩, by rw [hB]; show Walk.rlc coins.gamma (records.responses.get ⟨j, hj⟩) = _
                     rw [hget]⟩
      have hveq : records.requests.get i = v := by
        refine rlc_inj_of_not_collision hγ (List.mem_append_left _ (List.get_mem _ _))
          (List.mem_append_right _ hv) ?_
        rw [hA] at hi
        exact hi
      rw [List.mem_toFinset, ← hveq]
      exact List.get_mem _ _
  have hperm : records.requests.Perm records.responses :=
    List.perm_of_nodup_nodup_toFinset_eq hreqnd hrespnd hfin
  exact ⟨⟨by rw [← hperm.length_eq]; exact hKreq.1,
          by rw [← hperm.length_eq]; exact hKreq.2⟩, hrespnd, hperm⟩

/-- **`finiteIO_sound` — counted soundness.**  Acceptance of the prover-committed finite-field IO
    argument implies the record-level IO language `IO.LIO Ksz requests responses`, provided the
    sampled coins avoid the two soundness events (2) and (3).  Event (1) needs no hypothesis: the
    inverse gate already rejects a pole that hits a compressed record.

    This is emphatically *not* a zero-error statement.  The excluded events are counted by
    `IORLCCollisionEvent_card_le` and `IOLogDerivEvent_card_le`.

    The unique-request / unique-response hypotheses are exactly those of the symbolic
    `IO.io_result_LIO`. -/
theorem finiteIO_sound {Ksz : ℕ} {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins}
    (h : FiniteIOAccepts records coins w)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup) (hrespnd : records.responses.Nodup)
    (hγ : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    IO.LIO Ksz records.requests records.responses :=
  finiteIO_sound_of_identity records coins
    (fun i => request_compress_ne_zero h i) (fun j => response_compress_ne_zero h j)
    (endpoint_sum_eq h) hKp hKreq hKresp hreqnd hrespnd hγ hpole

/-! ## C2 — the bridge for downstream consumption -/

/-- **`finiteIO_lio_of_accepts` — the finite-`K` analogue of `RawMessage.lio_of_accepts`.**  This
    is the exact endpoint the language bridge consumes, so a downstream packet may swap the
    symbolic `RatFunc (RatFunc K)` IO path for this finite-field one without changing the
    interface. -/
theorem finiteIO_lio_of_accepts {Ksz : ℕ} {records : PreChallengeRecords K m} {coins : IOCoins K}
    (w : PostChallengeIOWitness records coins)
    (h : FiniteIOAccepts records coins w)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup) (hrespnd : records.responses.Nodup)
    (hγ : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma) :
    IO.LIO Ksz records.requests records.responses :=
  finiteIO_sound h hKp hKreq hKresp hreqnd hrespnd hγ hpole

/-- **The finite-field IO strategy — the embedding API for the next packet.**  A single bundle
    carrying the chronologically ordered data, the acceptance proof, the uniqueness and range
    side conditions, and the two counted-event exclusions. -/
structure FiniteIOStrategy (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (m Ksz p : ℕ) [CharP K p] where
  /-- Stage 1: the committed records. -/
  records : PreChallengeRecords K m
  /-- Stage 2: the sampled coins. -/
  coins : IOCoins K
  /-- Stage 3: the committed post-challenge columns. -/
  witness : PostChallengeIOWitness records coins
  /-- The finite-field IO gates hold. -/
  accepts : FiniteIOAccepts records coins witness
  /-- Unique request. -/
  uniqueRequest : records.requests.Nodup
  /-- Unique response. -/
  uniqueResponse : records.responses.Nodup
  /-- `1 ≤ |requests| ≤ Ksz`. -/
  requestRange : IO.InRange Ksz records.requests.length
  /-- `|responses| ≤ Ksz`. -/
  responseRange : records.responses.length ≤ Ksz
  /-- `char K > Ksz`. -/
  charBound : Ksz < p
  /-- The sampled `gamma` is outside the counted RLC-collision event. -/
  gammaGood : coins.gamma ∉ IORLCCollisionEvent records
  /-- The sampled `pole` is outside the counted log-derivative event. -/
  poleGood : coins.pole ∉ IOLogDerivEvent records coins.gamma

namespace FiniteIOStrategy

variable {Ksz : ℕ} (S : FiniteIOStrategy K m Ksz p)

/-- Number of request-side accumulator rows of the list prototype: one per record plus the
    terminal row.  **No** claim is made that this equals the paper's `N` or `M + 2L` row count; matching those is downstream work. -/
def progRows : ℕ := S.records.requests.length + 1

/-- Number of response-side accumulator rows, same prototype convention. -/
def memRows : ℕ := S.records.responses.length + 1

@[simp] theorem progRows_eq : S.progRows = S.records.requests.length + 1 := rfl
@[simp] theorem memRows_eq : S.memRows = S.records.responses.length + 1 := rfl

/-- **The exported endpoint.**  A finite-field IO strategy delivers the same `IO.LIO` conclusion
    the symbolic path delivers. -/
theorem lio : IO.LIO Ksz S.records.requests S.records.responses :=
  finiteIO_sound S.accepts S.charBound S.requestRange S.responseRange
    S.uniqueRequest S.uniqueResponse S.gammaGood S.poleGood

/-- The counted failure mass this strategy's coins had to avoid. -/
theorem failure_bound :
    (IOFailureEvent S.records).card
      ≤ ioFailureUnionBound m S.records.requests.length S.records.responses.length
          (Fintype.card K) :=
  IOFailureEvent_card_le S.records

/-- The strategy's exact accepted coin pair is outside the complete three-part IO event. -/
theorem coins_not_failure :
    (S.coins.gamma, S.coins.pole) ∉ IOFailureEvent S.records := by
  intro h
  simp only [IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rcases h with h | h | h
  · exact S.gammaGood h
  · exact pole_not_hit_of_accepts S.accepts h
  · exact S.poleGood h

end FiniteIOStrategy

/-! ## Oracle equivalence with the symbolic `RatFunc` path -/

/-- **Regression: the finite-field path agrees with the symbolic `RatFunc (RatFunc K)` oracle.**
    On records with unique requests and responses, and coins outside all three counted events,
    a finite-field IO witness exists exactly when the symbolic accumulator system of
    `IO.io_result_LIO` is satisfiable.  This is a regression receipt against the preserved
    symbolic construction, not an additional soundness claim: both sides are separately
    characterized by `IO.LIO`. -/
theorem finiteIO_oracle_agreement {Ksz : ℕ} (records : PreChallengeRecords K m)
    (coins : IOCoins K)
    (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz records.requests.length)
    (hKresp : records.responses.length ≤ Ksz)
    (hreqnd : records.requests.Nodup) (hrespnd : records.responses.Nodup)
    (hγ : coins.gamma ∉ IORLCCollisionEvent records)
    (hpole : coins.pole ∉ IOLogDerivEvent records coins.gamma)
    (hhit : coins.pole ∉ IOPoleHitEvent records coins.gamma) :
    (∃ w : PostChallengeIOWitness records coins, FiniteIOAccepts records coins w)
      ↔ (∃ (mu : Fin records.responses.length → ZMod p)
             (accP accM : ℕ → RatFunc (RatFunc K))
             (requests responses out_mem : RatFunc (RatFunc K)),
            (∀ j, mu j ≠ 0)
            ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt records.requests i)) accP requests
                records.requests.length
            ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt records.responses i)) (IO.castμ mu)
                accM responses out_mem records.responses.length
            ∧ requests = responses ∧ out_mem = 0) := by
  have hsym := IO.io_result_LIO (𝔽 := K) (p := p) (M := m) Ksz hKp
    records.requests records.responses hKreq hKresp hreqnd hrespnd
  rw [hsym]
  constructor
  · rintro ⟨w, hw⟩
    exact finiteIO_sound hw hKp hKreq hKresp hreqnd hrespnd hγ hpole
  · intro hlio
    refine finiteIO_complete_of_LIO (Ksz := Ksz) records coins hlio (fun v hv => ?_)
    intro hzero
    exact hhit (by
      simp only [IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v, hv, hzero⟩)

end Nock.NockVMROM.Thm54.FiniteIO
