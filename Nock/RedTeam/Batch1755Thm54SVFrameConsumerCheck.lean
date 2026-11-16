/-
  Nock/RedTeam/Batch1755Thm54SVFrameConsumerCheck.lean

  Production: `P8Core/SVFrame/{MemSoundnessFamily, JointSummands,
  StandaloneGeneric}.lean`.

  §A   The check: `VerifierData.Checks V consumerBound pIO` has the field
      `hcons : ∀ a, consumerBound a < pIO`; the statement checks it at `consumerBound CF MF V`
      (`= CF.reqBound V a + MF.internalBound V a`) and `ringChar Kio`.  It reads `V` (public sizes)
      only.  Negative control: at R-V2's corner `p = 97`, `N = P = 32` (heights `5`) every row bound
      and orbit fact holds and the check REJECTS (`decide`); any verifier datum there with an
      accumulator of bound `3N + P` fails `Checks`.  Positive control: `p = 193` accepts.
  §B   Threading: `consumer_count_of_checks` (the count from `hcons` and the two length
      bounds), `serves_holds_of_weighted_lookup` (`MF.serves`' own hypotheses give its conclusion);
      `standalone_generic` / `_at` / `_fixed` re-proved with no new hypothesis; axioms.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.StandaloneGeneric
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1755

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame

/-! ## §A  The check and its negative control -/

/-- **NC, R-V2's corner (`decide`).**  At `p = 97`, heights `5`, `N = P = 32`: the compute and path
row bounds (`3N < p`, `P < p`), the caps (`N, P ≤ 2^5`), the orbit order (`3·2^5 ∣ p − 1`) and the
floor (`25 ≤ p`) all hold, and the consumer-count check `3N + P < p` FAILS. -/
theorem corner_rowBounds_hold_check_rejects :
    (3 * 32 < 97 ∧ 32 < 97 ∧ 32 ≤ 2 ^ 5 ∧ 3 * 2 ^ 5 ∣ 97 - 1 ∧ 25 ≤ 97) ∧
      ¬ (3 * 32 + 32 < 97) := by
  decide

/-- **NC, per accumulator (`decide`).**  The check as the verifier decides it on a bound vector
(illustrative order `(validity 2D+2, export 3N+P, path N)`, `D = N = P = 32`): rejected at `p = 97`. -/
theorem corner_check_rejects_vector :
    ¬ ∀ a : Fin 3, (![2 * 32 + 2, 3 * 32 + 32, 32] : Fin 3 → ℕ) a < 97 := by
  decide

/-- Positive control (`decide`): the same sizes pass at `p = 193` (`3·2^5 ∣ 192`). -/
theorem check_accepts_at_193 :
    (∀ a : Fin 3, (![2 * 32 + 2, 3 * 32 + 32, 32] : Fin 3 → ℕ) a < 193) ∧ 3 * 2 ^ 5 ∣ 193 - 1 := by
  decide

/-- **NC at the frame's `Checks`**: no verifier datum with `N = 32`, a memory table of `32` rows and
an accumulator whose consumer bound is `3N + P` passes the checks at `pIO = 97`. -/
theorem checks_reject_export_corner {F K : Type} [Field F] [Field K] [Algebra F K] {hC : ℕ}
    {S : MemShape} (V : VerifierData F K hC S) {nAcc : ℕ} (cb : Fin nAcc → ℕ) (a : Fin nAcc)
    (t : Fin S.k) (hcb : cb a = 3 * V.N + V.memRows t) (hN : V.N = 32) (hP : V.memRows t = 32) :
    ¬ V.Checks cb 97 := by
  intro h
  have := h.hcons a
  omega

/-- The row bounds of `Checks` are consistent with the corner: `3N < 97` and `P < 97` — the new
field is the only one that rejects (the remaining fields do not mention `N + P`). -/
theorem corner_rows_not_rejected : 3 * 32 < 97 ∧ 32 < 97 := by decide

#check @Nock.NockVMROM.Thm54.SVFrame.VerifierData.Checks
#check @Nock.NockVMROM.Thm54.SVFrame.VerifierData.Checks.hcons
#check @Nock.NockVMROM.Thm54.SVFrame.consumerBound
#check @Nock.NockVMROM.Thm54.SVFrame.StandaloneThm54Statement.soundness
#check @Nock.NockVMROM.Thm54.SVFrame.MemSoundnessFamily.serves
#check @Nock.NockVMROM.Thm54.SVFrame.MemSoundnessFamily.response_sound

/-! ## §B  Threading and axioms -/

#check @Nock.NockVMROM.Thm54.SVFrame.consumer_count_of_checks
#check @Nock.NockVMROM.Thm54.SVFrame.serves_holds_of_weighted_lookup
#check @Nock.NockVMROM.Thm54.SVFrame.standalone_generic

#print axioms Nock.RedTeam.Batch1755.corner_rowBounds_hold_check_rejects
#print axioms Nock.RedTeam.Batch1755.corner_check_rejects_vector
#print axioms Nock.RedTeam.Batch1755.check_accepts_at_193
#print axioms Nock.RedTeam.Batch1755.checks_reject_export_corner
#print axioms Nock.NockVMROM.Thm54.SVFrame.consumer_count_of_checks
#print axioms Nock.NockVMROM.Thm54.SVFrame.serves_holds_of_weighted_lookup
#print axioms Nock.NockVMROM.Thm54.SVFrame.serves_of_weighted_lookup
#print axioms Nock.NockVMROM.Thm54.SVFrame.ctxW_of_accepts
#print axioms Nock.NockVMROM.Thm54.SVFrame.holdsF_of_accepts
#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_generic
#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_generic_at
#print axioms Nock.NockVMROM.Thm54.SVFrame.standalone_fixed

end Nock.RedTeam.Batch1755
