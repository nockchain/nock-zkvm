/-
the path-local canonical selector of `AirDetStaged` and the finite-rounds trace combinatorics
of the protocol (`finalOf`).

* `canTr R n m0 tr χ`: a (choice-selected) accepted, summand-free trace for `m0` that agrees with `(tr, χ)` on the
  columns of rounds `< n` and on the coins sampled after blocks `< n`. It depends on `(tr, χ)` only through that
  agreement class (`canTr_congr`), and under `AirDetStaged` it is the round-`n` part of EVERY accepted summand-free
  trace in the class (`badC_sound`). `BadC m0₀ nb` says a trace is not canonical in some round `n < nb`.
* `finalOf_agree` / `finalOf_msg`: how the traces/coins written by a path depend on its first `n` rounds, and how
  equality of the written round-`n` commitments gives equality of the round-`n` message.
-/
import NockvmE2E.Ung.StagedDef
import NockvmE2E.Ung.Consist
import NockvmE2E.Rap.Bridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NockvmE2E.Ung

open NockvmE2E.Rap

section Canon

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {ι β : Type} {colRound : ι → ℕ}
  (R : RapStatement Φ K ι β colRound) [Nonempty (Tr ι β)]

open Classical in
/-- The canonical round-`n` completion of the agreement class of `(tr, χ)`. -/
noncomputable def canTr (n : ℕ) (m0 : R.M0) (tr : Tr ι β) (χ : Coins Φ K) : Tr ι β :=
  Classical.epsilon fun tr₂ : Tr ι β => ∃ (fin : R.Mfin) (χ₂ : Coins Φ K),
    R.Accepts m0 tr₂ fin χ₂ ∧ (∀ s ∈ R.summands m0, ¬ s.mem tr₂ χ₂) ∧
    (∀ j, colRound j < n → tr₂ j = tr j) ∧ (∀ i, Φ.sampledAfter i < n → χ₂ i = χ i)

theorem canTr_congr (n : ℕ) (m0 : R.M0) {tr tr' : Tr ι β} {χ χ' : Coins Φ K}
    (h1 : ∀ j, colRound j < n → tr j = tr' j) (h2 : ∀ i, Φ.sampledAfter i < n → χ i = χ' i) :
    canTr R n m0 tr χ = canTr R n m0 tr' χ' := by
  unfold canTr
  congr 1
  funext tr₂
  apply propext
  constructor
  · rintro ⟨fin, χ₂, ha, hs, hc, hk⟩
    exact ⟨fin, χ₂, ha, hs, fun j hj => (hc j hj).trans (h1 j hj), fun i hi => (hk i hi).trans (h2 i hi)⟩
  · rintro ⟨fin, χ₂, ha, hs, hc, hk⟩
    exact ⟨fin, χ₂, ha, hs, fun j hj => (hc j hj).trans (h1 j hj).symm,
      fun i hi => (hk i hi).trans (h2 i hi).symm⟩

/-- A trace is NOT CANONICAL if its round-0 message is not `m0₀`, or some column of some round `n < nb` is not the
canonical one for its agreement class. -/
def BadC (m0₀ : R.M0) (nb : ℕ) (m0 : R.M0) (tr : Tr ι β) (χ : Coins Φ K) : Prop :=
  m0 ≠ m0₀ ∨ ∃ n < nb, ∃ j, colRound j = n ∧ tr j ≠ canTr R n m0 tr χ j

/-- **Under `AirDetStaged`, an accepted summand-free trace is canonical.** -/
theorem badC_sound {m0₀ : R.M0} {nb : ℕ}
    (hm0 : ∀ (m0 : R.M0) (tr : Tr ι β) (fin : R.Mfin) (χ : Coins Φ K),
      R.Accepts m0 tr fin χ → (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → m0 = m0₀)
    (hcol : ∀ (n : ℕ) (m0 : R.M0) (tr tr' : Tr ι β) (fin fin' : R.Mfin) (χ χ' : Coins Φ K),
      R.Accepts m0 tr fin χ → R.Accepts m0 tr' fin' χ' →
      (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → (∀ s ∈ R.summands m0, ¬ s.mem tr' χ') →
      (∀ j, colRound j < n → tr j = tr' j) → (∀ i, Φ.sampledAfter i < n → χ i = χ' i) →
      ∀ j, colRound j = n → tr j = tr' j)
    (m0 : R.M0) (tr : Tr ι β) (fin : R.Mfin) (χ : Coins Φ K)
    (ha : R.Accepts m0 tr fin χ) (hs : ∀ s ∈ R.summands m0, ¬ s.mem tr χ) :
    ¬ BadC R m0₀ nb m0 tr χ := by
  rintro (h | ⟨n, _, j, hj, hne⟩)
  · exact h (hm0 m0 tr fin χ ha hs)
  · apply hne
    have hex : ∃ tr₂ : Tr ι β, ∃ (fin₂ : R.Mfin) (χ₂ : Coins Φ K),
        R.Accepts m0 tr₂ fin₂ χ₂ ∧ (∀ s ∈ R.summands m0, ¬ s.mem tr₂ χ₂) ∧
        (∀ j, colRound j < n → tr₂ j = tr j) ∧ (∀ i, Φ.sampledAfter i < n → χ₂ i = χ i) :=
      ⟨tr, fin, χ, ha, hs, fun _ _ => rfl, fun _ _ => rfl⟩
    classical
    obtain ⟨fin₂, χ₂, ha₂, hs₂, hc₂, hk₂⟩ := Classical.epsilon_spec hex
    exact (hcol n m0 tr _ fin fin₂ χ χ₂ ha ha₂ hs hs₂ (fun j hj => (hc₂ j hj).symm)
      (fun i hi => (hk₂ i hi).symm) j hj)

end Canon

end NockvmE2E.Ung
