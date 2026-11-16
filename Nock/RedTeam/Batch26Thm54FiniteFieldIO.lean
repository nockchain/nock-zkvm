import Nock.NockVMROM.Thm54.FiniteFieldIOSoundness
import Mathlib.Tactic.NormNum.Prime

/-!
# Prover-committed finite-field IO: concrete witnesses and mutation regressions

Adversarial receipts for `Nock/NockVMROM/Thm54/FiniteFieldIO*.lean`, all over the concrete field
`ZMod 7`:

* **non-vacuity / completeness** — an honest single-record instance admits a
  `PostChallengeIOWitness` satisfying `FiniteIOAccepts`, and any accepting witness yields
  `IO.LIO`;
* **counted events are real** — a two-record instance whose unequal records genuinely collide
  under `RLC^gamma` at `gamma = 1` lands in `IORLCCollisionEvent` (which is nonetheless bounded),
  and a pole that hits a compressed record is *rejected* by the inverse gate while sitting in the
  counted `IOPoleHitEvent`;
* **mutations are rejected** — malformed inverse, wrong accumulator step, wrong endpoint, wrong
  multiplicity, and a chronology violation (columns committed against one coin pair, replayed
  against another) each refute `FiniteIOAccepts`;
* **oracle agreement** — on the honest instance the finite-field acceptance is equivalent to the
  preserved symbolic `RatFunc (RatFunc K)` accumulator system of `IO.io_result_LIO`.

No zero-error claim is made anywhere: `finiteIO_sound` is consumed with its two counted-event
exclusions as explicit hypotheses, discharged here by *computing* that the events are empty for
the honest instance.
-/

namespace Nock.RedTeam.Batch26

open Nock
open Nock.NockVMROM.Thm54.FiniteIO

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

abbrev F7 : Type := ZMod 7

/-! ## A. The honest single-record instance -/

/-- A width-`1` memory record. -/
def rec3 : Fin 1 → F7 := fun _ => 3

/-- Honest records: the single request is answered by the single response. -/
def honestRecords : PreChallengeRecords F7 1 := ⟨[rec3], [rec3]⟩

/-- Honest coins: `gamma = 1`, `pole = 1`.  The compressed denominator is `1 + 3 = 4 ≠ 0`. -/
def honestCoins : IOCoins F7 := ⟨1, 1⟩

theorem rlc_rec3 (γ : F7) : Walk.rlc γ rec3 = 3 := by
  simp [Walk.rlc, rec3]

/-- The honest instance has no RLC collision: with a single distinct record there is no unequal
    pair to collide. -/
theorem b26_honest_no_rlc_collision : IORLCCollisionEvent honestRecords = ∅ := by
  rw [IORLCCollisionEvent, Finset.filter_eq_empty_iff]
  intro γ _
  rintro ⟨u, hu, v, hv, hne, -⟩
  have hu' : u = rec3 := by simpa [honestRecords] using hu
  have hv' : v = rec3 := by simpa [honestRecords] using hv
  exact hne (hu'.trans hv'.symm)

/-- On the honest instance the log-derivative difference polynomial is identically zero — there
    is nothing for the sampled pole to accidentally certify. -/
theorem b26_honest_ioQP_zero (γ : F7) : ioQP honestRecords γ = 0 := by
  unfold ioQP
  exact sub_eq_zero.mpr rfl

theorem b26_honest_no_logderiv :
    IOLogDerivEvent honestRecords honestCoins.gamma = ∅ := by
  rw [IOLogDerivEvent, Finset.filter_eq_empty_iff]
  intro z _
  rintro ⟨hne, -⟩
  exact hne (b26_honest_ioQP_zero _)

theorem b26_honest_lio : IO.LIO 2 honestRecords.requests honestRecords.responses :=
  ⟨⟨le_refl 1, by decide⟩, by simp [honestRecords], List.Perm.refl _⟩

/-- **Completeness fires on a real instance.**  The honest record set admits an accepting
    prover-committed finite-field IO witness. -/
theorem b26_honest_completeness :
    ∃ w : PostChallengeIOWitness honestRecords honestCoins,
      FiniteIOAccepts honestRecords honestCoins w := by
  refine finiteIO_complete_of_LIO (Ksz := 2) honestRecords honestCoins b26_honest_lio ?_
  intro v hv
  have hv' : v = rec3 := by simpa [honestRecords] using hv
  subst hv'
  show (1 : F7) + Walk.rlc 1 rec3 ≠ 0
  rw [rlc_rec3]
  decide

/-- **Endpoint ⟹ `IO.LIO`, on the concrete instance.**  Every accepting witness for the honest
    coins forces the record-level IO language.  The two counted-event exclusions are discharged
    by computing that both events are empty here. -/
theorem b26_honest_endpoint_gives_LIO
    (w : PostChallengeIOWitness honestRecords honestCoins)
    (h : FiniteIOAccepts honestRecords honestCoins w) :
    IO.LIO 2 honestRecords.requests honestRecords.responses :=
  finiteIO_sound (p := 7) (Ksz := 2) h (by norm_num)
    ⟨le_refl 1, by decide⟩ (by decide)
    (by simp [honestRecords]) (by simp [honestRecords])
    (by rw [b26_honest_no_rlc_collision]; simp)
    (by rw [b26_honest_no_logderiv]; simp)

/-! ## B. An explicit honest witness, and its mutations -/

/-- The explicit accepting witness: `4⁻¹ = 2` in `ZMod 7`, multiplicity `1`, accumulators
    `0 → 2`, shared terminal `2`. -/
def honestWitness : PostChallengeIOWitness honestRecords honestCoins where
  requestInv := fun _ => 2
  responseInv := fun _ => 2
  multiplicity := fun _ => 1
  multInv := fun _ => 1
  requestAcc := fun i => if i = 0 then 0 else 2
  responseAcc := fun i => if i = 0 then 0 else 2
  terminal := 2

theorem b26_honestWitness_accepts :
    FiniteIOAccepts honestRecords honestCoins honestWitness := by
  refine
    { requestInvPin := ?_, responseInvPin := ?_, multBool := ?_, multInvPin := ?_,
      requestInit := ?_, requestStep := ?_, responseInit := ?_, responseStep := ?_,
      requestTerm := ?_, responseTerm := ?_ }
  · intro i
    fin_cases i
    show ((1 : F7) + Walk.rlc 1 rec3) * 2 = 1
    rw [rlc_rec3]; decide
  · intro j
    fin_cases j
    show ((1 : F7) + Walk.rlc 1 rec3) * 2 = 1
    rw [rlc_rec3]; decide
  · intro j
    show (1 : F7) * ((1 : F7) - 1) = 0
    decide
  · intro j
    show (1 : F7) * (1 : F7) = 1
    decide
  · decide
  · intro i; fin_cases i; decide
  · decide
  · intro j; fin_cases j; decide
  · decide
  · decide

/-- Mutation: the committed reciprocal column is zeroed. -/
def malformedInvWitness : PostChallengeIOWitness honestRecords honestCoins :=
  { honestWitness with requestInv := fun _ => 0 }

/-- **Malformed inverse is rejected** — the inverse gate has no solution. -/
theorem b26_malformed_inverse_rejected :
    ¬ FiniteIOAccepts honestRecords honestCoins malformedInvWitness := by
  intro h
  have hp := h.requestInvPin ⟨0, by decide⟩
  rw [show malformedInvWitness.requestInv ⟨0, by decide⟩ = 0 from rfl, mul_zero] at hp
  exact zero_ne_one hp

/-- Mutation: the accumulator never advances. -/
def wrongAccWitness : PostChallengeIOWitness honestRecords honestCoins :=
  { honestWitness with requestAcc := fun _ => 0 }

/-- **A wrong accumulator step is rejected.** -/
theorem b26_wrong_accumulator_rejected :
    ¬ FiniteIOAccepts honestRecords honestCoins wrongAccWitness := by
  intro h
  have hs := h.requestStep ⟨0, by decide⟩
  revert hs
  decide

/-- Mutation: the public terminal disagrees with the accumulator. -/
def wrongEndpointWitness : PostChallengeIOWitness honestRecords honestCoins :=
  { honestWitness with terminal := 3 }

/-- **A wrong endpoint is rejected.** -/
theorem b26_wrong_endpoint_rejected :
    ¬ FiniteIOAccepts honestRecords honestCoins wrongEndpointWitness := by
  intro h
  have ht := h.requestTerm
  revert ht
  decide

/-- Mutation: a zero multiplicity (the paper's `m_j ≠ 0` violated). -/
def wrongMultWitness : PostChallengeIOWitness honestRecords honestCoins :=
  { honestWitness with multiplicity := fun _ => 0 }

/-- **A wrong multiplicity is rejected** by the multiplicity-inverse pin. -/
theorem b26_wrong_multiplicity_rejected :
    ¬ FiniteIOAccepts honestRecords honestCoins wrongMultWitness := by
  intro h
  have hm := h.multInvPin ⟨0, by decide⟩
  revert hm
  decide

/-! ## C. Chronology violation -/

/-- A second coin pair, sampled after the columns were committed against `honestCoins`. -/
def shiftedCoins : IOCoins F7 := ⟨1, 2⟩

/-- **A chronology violation is rejected.**  Replaying post-challenge columns committed against
    `honestCoins` as a witness for the freshly sampled `shiftedCoins` breaks the inverse gate:
    `(2 + 3) · 2 = 3 ≠ 1` in `ZMod 7`. -/
theorem b26_chronology_violation_rejected :
    ¬ FiniteIOAccepts honestRecords shiftedCoins
        (honestWitness.transport (c₂ := shiftedCoins)) := by
  intro h
  have hp := h.requestInvPin ⟨0, by decide⟩
  have hc : compress shiftedCoins (honestRecords.requests.get ⟨0, by decide⟩)
      = (2 : F7) + Walk.rlc 1 rec3 := rfl
  have hi : (honestWitness.transport (c₂ := shiftedCoins)).requestInv ⟨0, by decide⟩
      = (2 : F7) := rfl
  rw [hc, hi, rlc_rec3] at hp
  revert hp
  decide

/-! ## D. The counted events are genuinely inhabited -/

/-- A pole that hits the compressed record: `4 + 3 = 0` in `ZMod 7`. -/
def badPoleCoins : IOCoins F7 := ⟨1, 4⟩

/-- **The pole-hit event is inhabited and counted.** -/
theorem b26_pole_hit_counted : (4 : F7) ∈ IOPoleHitEvent honestRecords 1 := by
  simp only [IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨rec3, by simp [honestRecords], ?_⟩
  rw [rlc_rec3]
  decide

/-- Its counting bound (`≤ |requests| + |responses|`). -/
theorem b26_pole_hit_bound :
    (IOPoleHitEvent honestRecords 1).card ≤ 1 + 1 :=
  IOPoleHitEvent_card_le honestRecords 1

/-- **A pole hitting a compressed record is rejected, not silently accepted.** -/
theorem b26_pole_hit_rejected :
    ¬ ∃ w : PostChallengeIOWitness honestRecords badPoleCoins,
        FiniteIOAccepts honestRecords badPoleCoins w := by
  rintro ⟨w, h⟩
  refine request_compress_ne_zero h ⟨0, by decide⟩ ?_
  show (4 : F7) + Walk.rlc 1 rec3 = 0
  rw [rlc_rec3]
  decide

/-- Two unequal width-`2` records, `(0,1)` and `(1,0)`. -/
def recU : Fin 2 → F7 := fun i => if i = 0 then 0 else 1
/-- The second colliding record. -/
def recV : Fin 2 → F7 := fun i => if i = 0 then 1 else 0

/-- A record set whose request and response records are unequal yet collide at `gamma = 1`. -/
def collisionRecords : PreChallengeRecords F7 2 := ⟨[recU], [recV]⟩

theorem b26_recU_ne_recV : recU ≠ recV := by
  intro hc
  have h0 := congrFun hc 0
  revert h0
  decide

/-- **The RLC-collision event is inhabited.**  At `gamma = 1` the unequal records `(0,1)` and
    `(1,0)` compress to the same scalar, so the collision event is not vacuous — which is exactly
    why the soundness theorem must exclude and count it. -/
theorem b26_rlc_collision_counted : (1 : F7) ∈ IORLCCollisionEvent collisionRecords := by
  simp only [IORLCCollisionEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨recU, by simp [collisionRecords], recV, by simp [collisionRecords],
    b26_recU_ne_recV, ?_⟩
  show Walk.rlc (1 : F7) recU = Walk.rlc 1 recV
  simp [Walk.rlc, Fin.sum_univ_two, recU, recV]

/-- Its counting bound: `≤ (k₁ + k₂)² · (m − 1) = 4`, even though the event is nonempty. -/
theorem b26_rlc_collision_bound :
    (IORLCCollisionEvent collisionRecords).card ≤ (1 + 1) * (1 + 1) * (2 - 1) :=
  IORLCCollisionEvent_card_le collisionRecords

/-! ## E. Oracle agreement with the preserved symbolic path -/

/-- **Oracle-agreement receipt.**  On the honest instance the prover-committed finite-field IO
    acceptance is equivalent to the symbolic `RatFunc (RatFunc F7)` accumulator system that the
    existing construction uses (`IO.io_result_LIO`).  Both sides are inhabited
    (`b26_honest_completeness`), so this is not a vacuous equivalence. -/
theorem b26_oracle_agreement :
    (∃ w : PostChallengeIOWitness honestRecords honestCoins,
        FiniteIOAccepts honestRecords honestCoins w)
      ↔ (∃ (mu : Fin honestRecords.responses.length → ZMod 7)
             (accP accM : ℕ → RatFunc (RatFunc F7))
             (requests responses out_mem : RatFunc (RatFunc F7)),
            (∀ j, mu j ≠ 0)
            ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt honestRecords.requests i)) accP
                requests honestRecords.requests.length
            ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt honestRecords.responses i))
                (IO.castμ mu) accM responses out_mem honestRecords.responses.length
            ∧ requests = responses ∧ out_mem = 0) :=
  finiteIO_oracle_agreement (p := 7) (Ksz := 2) honestRecords honestCoins (by norm_num)
    ⟨le_refl 1, by decide⟩ (by decide)
    (by simp [honestRecords]) (by simp [honestRecords])
    (by rw [b26_honest_no_rlc_collision]; simp)
    (by rw [b26_honest_no_logderiv]; simp)
    (by
      simp only [IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
      intro v
      simp only [not_and]
      intro hv
      have hv' : v = rec3 := by simpa [honestRecords] using hv
      subst hv'
      show ¬ (honestCoins.pole + Walk.rlc honestCoins.gamma rec3 = 0)
      rw [show honestCoins.gamma = 1 from rfl, show honestCoins.pole = 1 from rfl, rlc_rec3]
      decide)

end Nock.RedTeam.Batch26

#print axioms Nock.RedTeam.Batch26.b26_honest_completeness
#print axioms Nock.RedTeam.Batch26.b26_honest_endpoint_gives_LIO
#print axioms Nock.RedTeam.Batch26.b26_honestWitness_accepts
#print axioms Nock.RedTeam.Batch26.b26_malformed_inverse_rejected
#print axioms Nock.RedTeam.Batch26.b26_wrong_accumulator_rejected
#print axioms Nock.RedTeam.Batch26.b26_wrong_endpoint_rejected
#print axioms Nock.RedTeam.Batch26.b26_wrong_multiplicity_rejected
#print axioms Nock.RedTeam.Batch26.b26_chronology_violation_rejected
#print axioms Nock.RedTeam.Batch26.b26_pole_hit_counted
#print axioms Nock.RedTeam.Batch26.b26_pole_hit_rejected
#print axioms Nock.RedTeam.Batch26.b26_rlc_collision_counted
#print axioms Nock.RedTeam.Batch26.b26_rlc_collision_bound
#print axioms Nock.RedTeam.Batch26.b26_oracle_agreement
