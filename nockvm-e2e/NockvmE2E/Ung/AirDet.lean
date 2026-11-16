/-
`AirDet` — AIR determinism, the RAP-level premise of the positive
ungrindability theorem `rap_succinct_unique` (`Ung/Positive.lean`).

`AirDet R` has exactly the shape and pricing of `SoundG R` (`Rap/Frame.lean`, the `hsound` premise): it is
POINTWISE in the coin vector `χ` and priced by the summand list — "an accepted trace at a coin vector where no
bad summand fires is THE trace". Where `SoundG` concludes the statement-level `R.Holds`, `AirDet` concludes
`m0 = m0₀ ∧ tr = tr₀` for the canonical round-0 message and trace of the fixed claim.

DEVIATION from the brief's pairwise shape (`AirDetPair`: two traces accepted at the SAME `χ`, no summand firing on
either, same `m0` ⇒ equal). The pairwise form cannot be used by the protocol-level theorem: the two accepted paths
have DIFFERENT coin vectors (coins are RO outputs at different keys/commitments), so there is no common `χ`. The
canonical form is the pairwise form with a witness; `AirDet.pair` derives the pairwise form from it.
-/
import NockvmE2E.Rap.Frame
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NockvmE2E.Ung

open NockvmE2E.Rap

section Def

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {ι β : Type} {colRound : ι → ℕ}

/-- **AIR determinism** (per instance, pointwise, `hsound`-shaped): there is a canonical round-0 message `m0₀`
and trace `tr₀` such that every accepted `(m0, tr)` at a coin vector on which no summand of `R.summands m0`
fires is `(m0₀, tr₀)`. -/
def AirDet (R : RapStatement Φ K ι β colRound) : Prop :=
  ∃ (m0₀ : R.M0) (tr₀ : Tr ι β), ∀ (m0 : R.M0) (tr : Tr ι β) (fin : R.Mfin) (χ : Coins Φ K),
    R.Accepts m0 tr fin χ → (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → m0 = m0₀ ∧ tr = tr₀

/-- The brief's pairwise form: two traces accepted at the same coin vector, off all summands, are equal. -/
def AirDetPair (R : RapStatement Φ K ι β colRound) : Prop :=
  ∀ (m0 : R.M0) (tr tr' : Tr ι β) (fin fin' : R.Mfin) (χ : Coins Φ K),
    R.Accepts m0 tr fin χ → R.Accepts m0 tr' fin' χ →
    (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → (∀ s ∈ R.summands m0, ¬ s.mem tr' χ) → tr = tr'

theorem AirDet.pair {R : RapStatement Φ K ι β colRound} (h : AirDet R) : AirDetPair R := by
  obtain ⟨m0₀, tr₀, h⟩ := h
  intro m0 tr tr' fin fin' χ h1 h2 s1 s2
  exact (h m0 tr fin χ h1 s1).2.trans (h m0 tr' fin' χ h2 s2).2.symm

end Def

/-! ### Non-vacuity: a toy RAP with `AirDet` -/

section Toy

/-- One coin, sampled after block 0. -/
abbrev toyΦ : CoinFrame := ⟨1, fun _ => 0⟩

/-- Single summand: a nonzero committed value is caught only at the coin `0`. -/
def toySummand : BadSummand toyΦ (ZMod 2) (Tr Unit (ZMod 2)) (TracesStaged toyΦ (fun _ : Unit => 0)) where
  coins := {0}
  dep := ∅
  disj := by simp
  badSet tr _ := if tr () = 0 then ∅ else {fun _ => 0}
  weight := 1
  card_le tr χ := by split_ifs <;> simp
  readsOn Q hQ := by
    intro χ χ' _
    have h : Q χ () = Q χ' () := hQ () χ χ' (fun i hi => absurd hi (by simp))
    simp [h]

/-- The toy RAP: accepts the column `c` at coin `χ₀` iff `c * χ₀ = 0`. -/
def toyRap : RapStatement toyΦ (ZMod 2) Unit (ZMod 2) (fun _ => 0) where
  M0 := Unit
  Mfin := Unit
  summands _ := [toySummand]
  Accepts _ tr _ χ := tr () * χ 0 = 0
  Holds := True

/-- **Non-vacuity of `AirDet`**: the toy RAP is deterministic with canonical trace `0`. -/
theorem toyRap_airDet : AirDet toyRap := by
  refine ⟨(), fun _ => 0, ?_⟩
  intro m0 tr fin χ hacc hnf
  refine ⟨rfl, ?_⟩
  funext u
  cases u
  by_contra hne
  have hχ : χ 0 = 0 := by
    have h := hacc
    simp only [toyRap] at h
    have hz : ∀ a b : ZMod 2, a * b = 0 → a = 0 ∨ b = 0 := by decide
    rcases hz _ _ h with h | h
    · exact absurd h hne
    · exact h
  apply hnf toySummand (by simp [toyRap])
  have hb : toySummand.badSet tr χ = {fun _ => 0} := if_neg hne
  unfold BadSummand.mem
  rw [hb]
  refine Finset.mem_singleton.mpr (funext fun i => ?_)
  have : (i : Fin 1) = 0 := Subsingleton.elim _ _
  simp [this, hχ]

end Toy

end NockvmE2E.Ung
