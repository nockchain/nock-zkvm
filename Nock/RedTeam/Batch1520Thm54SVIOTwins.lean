/-
  Nock/RedTeam/Batch1520Thm54SVIOTwins.lean

  **Receipts for the
  package-free IO twins and the removal of QA's completeness obstruction.**

  §A — the IO twins (`P8Core/SVIOCompute`, `SVIOMemory`, `SVIOAssembly`): `#print axioms` of
  the load-bearing theorems, and a positive control that the IO sub-bundle the twins read is no
  stronger than what the deployed 303 chain already read (`IORowObligations.of303`).

  `exists_good_pole_rejected` came from
  `accepted_poles_card_le`, whose right-hand side `pkgRequests P` is the same at every pole:
  a nonconstant rational function of the pole meets a constant in at most `|responses|` poles.
  With `requests` a B2 message the right-hand side is a function `ρ` of the tuple, pole included,
  and the fibre argument has no fixed target:
  * `requests_forced_by_message` — at the twelve-coin memory chip with ANY public map reading
    `ρ` at `12..14`, acceptance forces `Σ_resp compress⁻¹ = ρ`: the forced value is the message,
    not a package constant;
  * `obstruction_gone` — for any committed responses with distinct RLC values and any `γ`, the
    coin-indexed honest message `ρ(pole) := Σ (pole + RLC^γ r)⁻¹` meets the LogUp identity at
    EVERY pole that hits no record, so the poles meeting it number `≥ |𝕂| − |responses|`,
    which exceeds `|responses|` as soon as `2·|responses| < |𝕂|` — exactly the regime in which
    `accepted_poles_card_le` gave `≤ |responses|`;
  * negative control `constant_message_fibre_le` — at a constant message the old bound
    (`logup_fibre_card_le_list`) is back.
-/
import Nock.NockVMROM.Thm54.P8Core.SVIOAssembly
import Nock.NockVMROM.Thm54.CoinParamCompleteness

set_option autoImplicit false

namespace Nock.RedTeam.Batch1520

open Nock
open Nock.NockVMROM.Thm54
open Nock.Framework
open Nock.NockVMROM.Thm54.SVIO
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.PartA12
open Nock.NockVMROM.Thm54.PartA12.DeployedChipFamily12
open StrictExtension
open scoped Polynomial

noncomputable section

/-! ## B. QA's obstruction is gone -/

section QA

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [Fintype F] [DecidableEq K]

/-- **Acceptance forces the message, not a package constant.**  At the twelve-coin memory chip,
with any nodes / basis / orbit / `kMem` and any public map reading `ρ` at `12..14`, every
accepted trace has `Σ_{r ∈ responses} compress(c.2.1, r)⁻¹ = ρ`.  In the standalone verifier
`ρ = m.requests c` varies with `c`, pole included. -/
theorem requests_forced_by_message {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (hinj : Function.Injective nodes) (b : Module.Basis (Fin 3) F K) (pubM : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (hadj : ∀ (i : Fin n) (hi : (i : ℕ) + 1 < n), nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i)
    (c : OptimizedProductionChallengeTuple12 K F) (kMem : ℕ) (ρ : K)
    (hreqM : ∀ k : Fin 3, pubM (12 + (k : ℕ)) = coord b ρ k)
    (Qm : Fin (memoryChipAt12 hn nodes b pubM orbit c kMem).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (memoryChipAt12 hn nodes b pubM orbit c kMem) Qm) :
    ((memRows12 hn nodes hinj b pubM orbit hadj c kMem Qm hsat).responses.map
        fun r => (FiniteIO.compress ⟨c.2.1.1, c.2.1.2⟩ r)⁻¹).sum = ρ :=
  (memIOFacts12 hn nodes hinj b pubM orbit hadj c kMem ρ hreqM Qm hsat).sum_eq

end QA

section Fibre

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The coin-indexed honest message: the LogUp sum of the committed responses at the pole. -/
def honestMessage (γ : K) (rs : List (Fin 10 → K)) (pole : K) : K :=
  (rs.map fun r => (pole + Walk.rlc γ r)⁻¹).sum

/-- **The obstruction is gone.**  For any committed responses `rs` and any `γ`, the poles at
which the coin-indexed honest message meets the LogUp identity include every pole that hits no
record, so they number at least `|𝕂| − |rs|`; under `2·|rs| < |𝕂|` that is more than `|rs|`,
the most `accepted_poles_card_le` allowed at a constant message. -/
theorem obstruction_gone (γ : K) (rs : List (Fin 10 → K))
    (hK : 2 * rs.length < Fintype.card K) :
    rs.length < (Finset.univ.filter fun p : K =>
        (∀ x ∈ rs.map (Walk.rlc γ), p + x ≠ 0) ∧
          (rs.map fun r => (p + Walk.rlc γ r)⁻¹).sum = honestMessage γ rs p).card := by
  classical
  have hsub : (Finset.univ.filter fun p : K => ∃ x ∈ rs.map (Walk.rlc γ), p + x = 0) ⊆
      ((rs.map (Walk.rlc γ)).map (fun x => -x)).toFinset := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨x, hx, h0⟩ := hp
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨x, hx, by linear_combination -h0⟩
  have hbad : (Finset.univ.filter fun p : K => ∃ x ∈ rs.map (Walk.rlc γ), p + x = 0).card ≤
      rs.length := by
    refine (Finset.card_le_card hsub).trans ?_
    refine (List.toFinset_card_le _).trans ?_
    simp
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset K))
    (fun p : K => ∃ x ∈ rs.map (Walk.rlc γ), p + x = 0)
  have hgood : (Finset.univ.filter fun p : K =>
        (∀ x ∈ rs.map (Walk.rlc γ), p + x ≠ 0) ∧
          (rs.map fun r => (p + Walk.rlc γ r)⁻¹).sum = honestMessage γ rs p) =
      Finset.univ.filter fun p : K => ¬ ∃ x ∈ rs.map (Walk.rlc γ), p + x = 0 := by
    ext p
    simp [honestMessage]
  rw [hgood]
  rw [Finset.card_univ] at hsplit
  omega

/-- **Negative control: at a constant message the old fibre bound is back.** -/
theorem constant_message_fibre_le (γ : K) (rs : List (Fin 10 → K))
    (hnd : (rs.map (Walk.rlc γ)).Nodup) (hne : rs ≠ []) (S : K) :
    (Finset.univ.filter fun p : K =>
        (∀ x ∈ rs.map (Walk.rlc γ), p + x ≠ 0) ∧
          ((rs.map (Walk.rlc γ)).map fun x => (p + x)⁻¹).sum = S).card ≤ rs.length := by
  have h := CoinParamCompleteness.logup_fibre_card_le_list (rs.map (Walk.rlc γ)) hnd
    (by simpa using hne) S
  simpa using h

/-! ## C. The honest IO pole term -/

/-- **The honest IO pole term.**  At fixed honest records, the poles that hit a record number at
most `|req| + |resp|` at every `γ`: with `requests` chosen as the message, the honest LogUp
identity can only fail on these. -/
theorem honest_pole_hit_card_le (R : FiniteIO.PreChallengeRecords K 10) (γ : K) :
    (FiniteIO.IOPoleHitEvent R γ).card ≤ R.requests.length + R.responses.length :=
  FiniteIO.IOPoleHitEvent_card_le R γ

omit [Fintype K] [DecidableEq K] in
/-- At a good pole the honest message closes the honest memory identity exactly. -/
theorem honest_identity_at_good_pole (R : FiniteIO.PreChallengeRecords K 10)
    (coins : FiniteIO.IOCoins K) :
    (R.responses.map fun r => (FiniteIO.compress coins r)⁻¹).sum =
      honestMessage coins.gamma R.responses coins.pole := rfl

end Fibre

end

end Nock.RedTeam.Batch1520

/-! ## A. Axioms of the IO twins -/

#print axioms Nock.NockVMROM.Thm54.SVIO.IORowObligations.of303
#print axioms Nock.NockVMROM.Thm54.SVIO.IORowObligations.of309
#print axioms Nock.NockVMROM.Thm54.SVIO.IORows.requests_eq_sum_compress
#print axioms Nock.NockVMROM.Thm54.SVIO.IORows.requests_nodup
#print axioms Nock.NockVMROM.Thm54.SVIO.rows309
#print axioms Nock.NockVMROM.Thm54.SVIO.MemIORows.requests_eq_sum_compress
#print axioms Nock.NockVMROM.Thm54.SVIO.MemIORows.compress_response_ne_zero
#print axioms Nock.NockVMROM.Thm54.SVIO.memRows12
#print axioms Nock.NockVMROM.Thm54.SVIO.identity_of_common_requests
#print axioms Nock.NockVMROM.Thm54.SVIO.lio_of_common_requests
#print axioms Nock.NockVMROM.Thm54.SVIO.lio_at_chips
#print axioms Nock.RedTeam.Batch1520.requests_forced_by_message
#print axioms Nock.RedTeam.Batch1520.obstruction_gone
#print axioms Nock.RedTeam.Batch1520.constant_message_fibre_le
#print axioms Nock.RedTeam.Batch1520.honest_pole_hit_card_le
