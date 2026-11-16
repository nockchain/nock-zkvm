/-
`AirDetStaged` — round-wise AIR determinism for staged RAPs whose
columns committed after a coin block depend on the coins (every J-8 chip), the premise of
`rap_succinct_unique_staged` (`Ung/Staged.lean`).

`AirDetStaged R`: (a) the round-0 message `m0` is canonical (`∃ m0₀`, as in `AirDet`; `m0` is sent before any coin);
(b) for each round `n`, two accepted traces (accepted at their OWN full coin vectors, off every summand) for the same
`m0` that agree on all columns of rounds `< n` and on all coins sampled after blocks `< n` agree on the round-`n` columns.
DEVIATION from the brief ("evaluated at the SAME coin vector"): the two accepted paths of the protocol theorem have
different full coin vectors (they agree only on the coins before round `n`), and acceptance is a property of the full
vector; agreement on the coins a round-`n` column may read (`StagedCols`) is exactly what is available and enough.
-/
import NockvmE2E.Ung.AirDet

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NockvmE2E.Ung

open NockvmE2E.Rap

section Def

variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {ι β : Type} {colRound : ι → ℕ}

/-- Round-wise AIR determinism (see the file header). -/
def AirDetStaged (R : RapStatement Φ K ι β colRound) : Prop :=
  (∃ m0₀ : R.M0, ∀ (m0 : R.M0) (tr : Tr ι β) (fin : R.Mfin) (χ : Coins Φ K),
      R.Accepts m0 tr fin χ → (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → m0 = m0₀) ∧
  ∀ (n : ℕ) (m0 : R.M0) (tr tr' : Tr ι β) (fin fin' : R.Mfin) (χ χ' : Coins Φ K),
    R.Accepts m0 tr fin χ → R.Accepts m0 tr' fin' χ' →
    (∀ s ∈ R.summands m0, ¬ s.mem tr χ) → (∀ s ∈ R.summands m0, ¬ s.mem tr' χ') →
    (∀ j, colRound j < n → tr j = tr' j) → (∀ i, Φ.sampledAfter i < n → χ i = χ' i) →
    ∀ j, colRound j = n → tr j = tr' j

/-- `AirDet` (the one-shot, coin-independent canonical trace) implies the round-wise form. -/
theorem AirDet.staged {R : RapStatement Φ K ι β colRound} (h : AirDet R) : AirDetStaged R := by
  obtain ⟨m0₀, tr₀, h⟩ := h
  refine ⟨⟨m0₀, fun m0 tr fin χ ha hs => (h m0 tr fin χ ha hs).1⟩, ?_⟩
  intro n m0 tr tr' fin fin' χ χ' h1 h2 s1 s2 _ _ j _
  exact ((h m0 tr fin χ h1 s1).2.trans (h m0 tr' fin' χ' h2 s2).2.symm) ▸ rfl

end Def

/-! ### Non-vacuity: a toy RAP with a COIN-DEPENDENT round-1 column -/

section Toy

/-- One coin, sampled after block 0. -/
abbrev toy2Φ : CoinFrame := ⟨1, fun _ => 0⟩

/-- Two columns: `false` is committed in round 0, `true` in round 1 (after the coin). -/
abbrev toy2Round : Bool → ℕ := fun b => cond b 1 0

/-- Round 0: `a₀ = 1`. Round 1: `acc = χ₀ · a₀` — it depends on the coin `χ₀`. No summands. -/
def toy2Rap : RapStatement toy2Φ (ZMod 2) Bool (ZMod 2) toy2Round where
  M0 := Unit
  Mfin := Unit
  summands _ := []
  Accepts _ tr _ χ := tr false = 1 ∧ tr true = χ 0 * tr false
  Holds := True

/-- **Non-vacuity of `AirDetStaged`**: the toy RAP with a coin-dependent round-1 column is round-wise deterministic. -/
theorem toy2Rap_airDetStaged : AirDetStaged toy2Rap := by
  refine ⟨⟨(), fun _ _ _ _ _ _ => rfl⟩, ?_⟩
  intro n m0 tr tr' fin fin' χ χ' h1 h2 _ _ hcol hcoin j hj
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  cases j with
  | false => rw [a1, a2]
  | true =>
    have hn : n = 1 := by simpa [toy2Round] using hj.symm
    subst hn
    have hχ : χ 0 = χ' 0 := hcoin 0 (by simp)
    have ha : tr false = tr' false := by rw [a1, a2]
    rw [b1, b2, hχ, ha]

/-- ... and NOT deterministic in the one-shot sense of `AirDet`: the canonical-trace form is false for it
(this is the defect). -/
theorem toy2Rap_not_airDet : ¬ AirDet toy2Rap := by
  rintro ⟨m0₀, tr₀, h⟩
  have h0 := h () (fun b => if b then 0 else 1) () (fun _ => 0) ⟨by simp, by simp⟩ (by simp [toy2Rap])
  have h1 := h () (fun b => if b then 1 else 1) () (fun _ => 1) ⟨by simp, by simp⟩ (by simp [toy2Rap])
  have e := (h0.2.trans h1.2.symm)
  have := congrFun e true
  simp at this

end Toy

end NockvmE2E.Ung
