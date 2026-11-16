import Nock.IO
import Nock.Walk

/-!
# Prover-committed finite-field IO: typed chronology, witness, and completeness

The symbolic IO path (`Nock/AIR.lean`, IO section, and `Nock/IO.lean`) evaluates the LogUp
accumulators over `RatFunc (RatFunc 𝔽)`, where the per-row fraction `1/(X + RLC(record))` is
*verifier reconstructed* (`SetEq.frac`) rather than prover committed; the header of the IO block
in `Nock/AIR.lean` records that "a finite-`K`, prover-committed replacement would need such an
inverse gate".  This module is that replacement's data layer.

Everything here lives over a plain field `K`.

## Chronology (part of the strategy type)

The type-level dependency order encodes the interactive chronology of the argument:

1. `PreChallengeRecords K m` — the request/response record lists are committed first;
2. `IOCoins K` — then the verifier samples `gamma` (the record-RLC compression challenge) and
   `pole` (the LogUp pole).  `pole` is a *separate* sampled coin; it is emphatically not the
   orbit-coset shift `RAP.β` (see `Nock/RedTeam/Batch18Thm54IOAudit.lean`,
   `b18_memory_table_rap_beta_roles`);
3. `PostChallengeIOWitness records coins` — only then are the inverse and accumulator columns
   committed.  The witness type is indexed by both the records and the coins, so a witness
   committed for one coin pair is not, as a matter of typing, a witness for another; the explicit
   `transport` reinterpretation makes a chronology violation nameable and refutable.

Because a challenge is sampled, no zero-error claim is made anywhere in this packet.  The
soundness direction lives in `Nock/NockVMROM/Thm54/FiniteFieldIOSoundness.lean` and is stated
outside three explicitly counted finite-field events.
-/

namespace Nock.NockVMROM.Thm54.FiniteIO

open Nock
open scoped BigOperators

/-! ## The typed chronology -/

/-- **Stage 1 — pre-challenge commitment.**  The request and response memory-record lists, each
    a list of width-`m` vectors over `K`.  This is the finite-field analogue of the derived IO
    record lists consumed by the symbolic path (`IO.LIO`, `RawMessage.lio_of_accepts`). -/
structure PreChallengeRecords (K : Type*) (m : ℕ) where
  /-- The compute table's memory requests, as records. -/
  requests : List (Fin m → K)
  /-- The memory table's responses, as records. -/
  responses : List (Fin m → K)

/-- **Stage 2 — the sampled coins.**  `gamma` compresses a width-`m` record to a scalar
    (`Walk.rlc`); `pole` is the LogUp pole at which the log-derivative identity is tested.  These
    are two distinct coins and neither is the orbit coset base `RAP.β`. -/
structure IOCoins (K : Type*) where
  /-- Record-RLC compression challenge. -/
  gamma : K
  /-- LogUp pole challenge (NOT the orbit coset shift `RAP.β`). -/
  pole : K

variable {K : Type*} [Field K] {m : ℕ}

/-- The compressed denominator of a record at the sampled coins: `pole + RLC^gamma(record)`.
    Writing the denominator additively matches `SetEq.frac c = (X + C c)⁻¹` with the
    log-derivative variable `X` specialized to the sampled `pole`, which is what lets the finite
    path be compared against the symbolic oracle. -/
def compress (coins : IOCoins K) (v : Fin m → K) : K :=
  coins.pole + Walk.rlc coins.gamma v

/-- **Stage 3 — the post-challenge committed columns.**  `requestInv`/`responseInv` are the
    prover-committed reciprocals of the compressed denominators (the columns the symbolic path
    reconstructs as `SetEq.frac`); `multiplicity`/`multInv` are the explicit `K`-valued
    multiplicity column and its inverse pin; `requestAcc` and
    `responseAcc` are the two accumulators, each with one more row than records. -/
structure PostChallengeIOWitness (records : PreChallengeRecords K m) (coins : IOCoins K) where
  /-- Committed reciprocal of `pole + RLC^gamma(request i)`. -/
  requestInv : Fin records.requests.length → K
  /-- Committed reciprocal of `pole + RLC^gamma(response j)`. -/
  responseInv : Fin records.responses.length → K
  /-- Committed multiplicity column (`ver`). -/
  multiplicity : Fin records.responses.length → K
  /-- Committed inverse of the multiplicity, pinning it nonzero. -/
  multInv : Fin records.responses.length → K
  /-- Request-side accumulator, `requests.length + 1` rows. -/
  requestAcc : Fin (records.requests.length + 1) → K
  /-- Response-side accumulator, `responses.length + 1` rows. -/
  responseAcc : Fin (records.responses.length + 1) → K
  /-- The shared public terminal value both accumulators must reach. -/
  terminal : K

namespace PostChallengeIOWitness

/-- **Chronology transport.**  Reinterpret columns committed against `c₁` as a candidate witness
    against `c₂`.  Nothing in the witness type forces the columns to be recomputed, so this is the
    exact shape of a chronology violation: `FiniteIOAccepts` for `c₂` is what refutes it. -/
def transport {records : PreChallengeRecords K m} {c₁ c₂ : IOCoins K}
    (w : PostChallengeIOWitness records c₁) : PostChallengeIOWitness records c₂ where
  requestInv := w.requestInv
  responseInv := w.responseInv
  multiplicity := w.multiplicity
  multInv := w.multInv
  requestAcc := w.requestAcc
  responseAcc := w.responseAcc
  terminal := w.terminal

end PostChallengeIOWitness

/-! ## The acceptance predicate -/

/-- **Finite-field IO acceptance.**  The inverse pins, the multiplicity gates, the two
    accumulator recurrences with their zero initial rows, and the shared terminal endpoint.  No
    `RatFunc` appears: every equation is an equation in `K`. -/
structure FiniteIOAccepts (records : PreChallengeRecords K m) (coins : IOCoins K)
    (w : PostChallengeIOWitness records coins) : Prop where
  /-- Inverse gate on the request side: `(pole + RLC^gamma(req i)) · inv i = 1`. -/
  requestInvPin : ∀ i, compress coins (records.requests.get i) * w.requestInv i = 1
  /-- Inverse gate on the response side. -/
  responseInvPin : ∀ j, compress coins (records.responses.get j) * w.responseInv j = 1
  /-- Booleanity of the multiplicity column. -/
  multBool : ∀ j, w.multiplicity j * (w.multiplicity j - 1) = 0
  multInvPin : ∀ j, w.multiplicity j * w.multInv j = 1
  /-- The request accumulator starts empty. -/
  requestInit : w.requestAcc 0 = 0
  /-- Request accumulation: add the committed reciprocal. -/
  requestStep : ∀ i : Fin records.requests.length,
      w.requestAcc i.succ = w.requestAcc i.castSucc + w.requestInv i
  /-- The response accumulator starts empty. -/
  responseInit : w.responseAcc 0 = 0
  /-- Response accumulation: add multiplicity times the committed reciprocal. -/
  responseStep : ∀ j : Fin records.responses.length,
      w.responseAcc j.succ = w.responseAcc j.castSucc + w.multiplicity j * w.responseInv j
  /-- Request terminal endpoint. -/
  requestTerm : w.requestAcc (Fin.last _) = w.terminal
  /-- Response terminal endpoint (the same public value: this is the IO consistency check). -/
  responseTerm : w.responseAcc (Fin.last _) = w.terminal

/-! ## Elementary consequences of acceptance -/

/-- Telescoping an accumulator column with a zero initial row. -/
theorem acc_telescope {n : ℕ} (f : Fin (n + 1) → K) (g : Fin n → K)
    (h0 : f 0 = 0) (hs : ∀ i : Fin n, f i.succ = f i.castSucc + g i) :
    f (Fin.last n) = ∑ i, g i := by
  induction n with
  | zero =>
    show f (Fin.last 0) = ∑ i : Fin 0, g i
    rw [Fin.sum_univ_zero]
    exact h0
  | succ k ih =>
    have hstep := hs (Fin.last k)
    rw [Fin.succ_last] at hstep
    have hrec : (f ∘ Fin.castSucc) (Fin.last k) = ∑ i : Fin k, (g ∘ Fin.castSucc) i := by
      refine ih (f ∘ Fin.castSucc) (g ∘ Fin.castSucc) ?_ ?_
      · simpa using h0
      · intro i
        have h2 := hs i.castSucc
        rw [Fin.succ_castSucc] at h2
        exact h2
    rw [hstep, Fin.sum_univ_castSucc]
    simp only [Function.comp_apply] at hrec
    rw [hrec]

/-- Acceptance forces the compressed denominators to be nonzero: the inverse gate is exactly the
    statement that the sampled pole does not hit a compressed record.  So a pole collision is
    *rejected* by the gate rather than silently accepted. -/
theorem request_compress_ne_zero {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins} (h : FiniteIOAccepts records coins w)
    (i : Fin records.requests.length) : compress coins (records.requests.get i) ≠ 0 :=
  left_ne_zero_of_mul_eq_one (h.requestInvPin i)

/-- Response-side analogue of `request_compress_ne_zero`. -/
theorem response_compress_ne_zero {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins} (h : FiniteIOAccepts records coins w)
    (j : Fin records.responses.length) : compress coins (records.responses.get j) ≠ 0 :=
  left_ne_zero_of_mul_eq_one (h.responseInvPin j)

/-- The committed reciprocal is the actual reciprocal. -/
theorem requestInv_eq {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins} (h : FiniteIOAccepts records coins w)
    (i : Fin records.requests.length) :
    w.requestInv i = (compress coins (records.requests.get i))⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.requestInvPin i)

/-- Response-side analogue of `requestInv_eq`. -/
theorem responseInv_eq {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins} (h : FiniteIOAccepts records coins w)
    (j : Fin records.responses.length) :
    w.responseInv j = (compress coins (records.responses.get j))⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.responseInvPin j)

/-- **Booleanity plus the inverse pin forces `multiplicity = 1`.**  This is the paper's
    unique-response specialization `ver ≡ 1` realized by two genuine gates
    rather than by fiat. -/
theorem multiplicity_eq_one {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins} (h : FiniteIOAccepts records coins w)
    (j : Fin records.responses.length) : w.multiplicity j = 1 := by
  rcases mul_eq_zero.mp (h.multBool j) with h0 | h1
  · exact absurd (h.multInvPin j) (by rw [h0, zero_mul]; exact zero_ne_one)
  · exact sub_eq_zero.mp h1

/-- The request accumulator reaches the sum of the committed reciprocals. -/
theorem requestAcc_last {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins} (h : FiniteIOAccepts records coins w) :
    w.terminal = ∑ i, w.requestInv i := by
  rw [← h.requestTerm]
  exact acc_telescope _ _ h.requestInit h.requestStep

/-- The response accumulator reaches the sum of the committed reciprocals (multiplicity `1`). -/
theorem responseAcc_last {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins} (h : FiniteIOAccepts records coins w) :
    w.terminal = ∑ j, w.responseInv j := by
  rw [← h.responseTerm]
  refine (acc_telescope _ _ h.responseInit h.responseStep).trans ?_
  exact Finset.sum_congr rfl (fun j _ => by rw [multiplicity_eq_one h j, one_mul])

/-- **The endpoint identity extracted from acceptance.**  The two committed accumulators agreeing
    at the shared public terminal is exactly the numeric log-derivative identity
    `Σ_i 1/(pole + RLC^γ(req i)) = Σ_j 1/(pole + RLC^γ(resp j))` at the sampled coins. -/
theorem endpoint_sum_eq {records : PreChallengeRecords K m} {coins : IOCoins K}
    {w : PostChallengeIOWitness records coins} (h : FiniteIOAccepts records coins w) :
    (∑ i, (compress coins (records.requests.get i))⁻¹)
      = ∑ j, (compress coins (records.responses.get j))⁻¹ := by
  have hr : (∑ i, (compress coins (records.requests.get i))⁻¹) = ∑ i, w.requestInv i :=
    Finset.sum_congr rfl (fun i _ => (requestInv_eq h i).symm)
  have hs : (∑ j, (compress coins (records.responses.get j))⁻¹) = ∑ j, w.responseInv j :=
    Finset.sum_congr rfl (fun j _ => (responseInv_eq h j).symm)
  rw [hr, hs, ← requestAcc_last h, ← responseAcc_last h]

/-! ## Completeness -/

/-- List/`Fin` sum bridge. -/
theorem sum_fin_get {α : Type*} (l : List α) (f : α → K) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    show ∑ i : Fin (t.length + 1), f ((a :: t).get i) = (List.map f (a :: t)).sum
    rw [Fin.sum_univ_succ]
    simp [ih]

/-- **`finiteIO_complete_of_LIO` — completeness.**  An honest record set (in `IO.LIO`: distinct
    responses which the requests permute) admits a `PostChallengeIOWitness` satisfying
    `FiniteIOAccepts`, provided the sampled pole does not hit any compressed record.  The
    denominator hypothesis is unavoidable and is exactly counted event (1) of the soundness
    analysis (`FiniteFieldIOSoundness.IOPoleHitEvent`). -/
theorem finiteIO_complete_of_LIO {Ksz : ℕ} (records : PreChallengeRecords K m)
    (coins : IOCoins K)
    (hlio : IO.LIO Ksz records.requests records.responses)
    (hpole : ∀ v ∈ records.requests ++ records.responses, compress coins v ≠ 0) :
    ∃ w : PostChallengeIOWitness records coins, FiniteIOAccepts records coins w := by
  classical
  set k₁ := records.requests.length with hk₁
  set k₂ := records.responses.length with hk₂
  set ri : Fin k₁ → K := fun i => (compress coins (records.requests.get i))⁻¹ with hri
  set si : Fin k₂ → K := fun j => (compress coins (records.responses.get j))⁻¹ with hsi
  set riN : ℕ → K := fun i => if h : i < k₁ then ri ⟨i, h⟩ else 0 with hriN
  set siN : ℕ → K := fun j => if h : j < k₂ then si ⟨j, h⟩ else 0 with hsiN
  -- the two sums agree because the record multisets agree
  have hsum : (∑ i, ri i) = ∑ j, si j := by
    have h1 : (∑ i, ri i)
        = (records.requests.map (fun v => (compress coins v)⁻¹)).sum :=
      sum_fin_get records.requests (fun v => (compress coins v)⁻¹)
    have h2 : (∑ j, si j)
        = (records.responses.map (fun v => (compress coins v)⁻¹)).sum :=
      sum_fin_get records.responses (fun v => (compress coins v)⁻¹)
    rw [h1, h2]
    exact (hlio.2.2.map (fun v => (compress coins v)⁻¹)).sum_eq
  refine ⟨{ requestInv := ri
            responseInv := si
            multiplicity := fun _ => 1
            multInv := fun _ => 1
            requestAcc := fun j => ∑ i ∈ Finset.range (j : ℕ), riN i
            responseAcc := fun j => ∑ i ∈ Finset.range (j : ℕ), siN i
            terminal := ∑ i, ri i }, ?_⟩
  refine
    { requestInvPin := ?_, responseInvPin := ?_, multBool := ?_, multInvPin := ?_,
      requestInit := ?_, requestStep := ?_, responseInit := ?_, responseStep := ?_,
      requestTerm := ?_, responseTerm := ?_ }
  · intro i
    exact mul_inv_cancel₀ (hpole _ (List.mem_append_left _ (List.get_mem _ _)))
  · intro j
    exact mul_inv_cancel₀ (hpole _ (List.mem_append_right _ (List.get_mem _ _)))
  · intro _; ring
  · intro _; ring
  · simp
  · intro i
    show (∑ q ∈ Finset.range ((i.succ : Fin (k₁ + 1)) : ℕ), riN q)
      = (∑ q ∈ Finset.range ((i.castSucc : Fin (k₁ + 1)) : ℕ), riN q) + ri i
    have hval : riN (i : ℕ) = ri i := by simp only [hriN]; exact dif_pos i.isLt
    rw [Fin.val_succ, Fin.val_castSucc, Finset.sum_range_succ, hval]
  · simp
  · intro j
    show (∑ q ∈ Finset.range ((j.succ : Fin (k₂ + 1)) : ℕ), siN q)
      = (∑ q ∈ Finset.range ((j.castSucc : Fin (k₂ + 1)) : ℕ), siN q) + 1 * si j
    have hval : siN (j : ℕ) = si j := by simp only [hsiN]; exact dif_pos j.isLt
    rw [Fin.val_succ, Fin.val_castSucc, Finset.sum_range_succ, one_mul, hval]
  · show (∑ q ∈ Finset.range ((Fin.last k₁ : Fin (k₁ + 1)) : ℕ), riN q) = ∑ i, ri i
    rw [Fin.val_last, Finset.sum_range]
    exact Finset.sum_congr rfl
      (fun i _ => by simp only [hriN]; exact dif_pos i.isLt)
  · show (∑ q ∈ Finset.range ((Fin.last k₂ : Fin (k₂ + 1)) : ℕ), siN q) = ∑ i, ri i
    rw [Fin.val_last, Finset.sum_range, hsum]
    exact Finset.sum_congr rfl
      (fun j _ => by simp only [hsiN]; exact dif_pos j.isLt)

end Nock.NockVMROM.Thm54.FiniteIO
