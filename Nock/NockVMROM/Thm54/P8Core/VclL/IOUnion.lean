/-
  Nock/NockVMROM/Thm54/P8Core/VclL/IOUnion.lean

  **T6, the three-accumulator union bound.**

  The only premises are the six length majorants (rule 8(b)).
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1540Thm54T0IOExt

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.VclL

open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.T0IOExt

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Fintype K] [Fintype L] [DecidableEq L]

/-- **The three-accumulator IO failure set** at one coin pair. -/
noncomputable def threeAccIOEvent [DecidableEq K] (mv mx mp : ℕ) (rv : PreChallengeRecords L mv)
    (rx : PreChallengeRecords L mx) (rp : PreChallengeRecords L mp) : Finset (K × K) :=
  IOFailureEventExt K rv ∪ IOFailureEventExt K rx ∪ IOFailureEventExt K rp

theorem ioFailureUnionBound_mono (m : ℕ) {a a' b b' : ℕ} (c : ℕ) (ha : a ≤ a') (hb : b ≤ b') :
    ioFailureUnionBound m a b c ≤ ioFailureUnionBound m a' b' c := by
  unfold ioFailureUnionBound
  have h : a + b ≤ a' + b' := Nat.add_le_add ha hb
  gcongr

theorem threeAccIOEvent_card_le [DecidableEq K] (mv mx mp : ℕ) (rv : PreChallengeRecords L mv)
    (rx : PreChallengeRecords L mx) (rp : PreChallengeRecords L mp)
    (k1v k2v k1x k2x k1p k2p : ℕ)
    (h1v : rv.requests.length ≤ k1v) (h2v : rv.responses.length ≤ k2v)
    (h1x : rx.requests.length ≤ k1x) (h2x : rx.responses.length ≤ k2x)
    (h1p : rp.requests.length ≤ k1p) (h2p : rp.responses.length ≤ k2p) :
    (threeAccIOEvent (K := K) mv mx mp rv rx rp).card ≤
      ioFailureUnionBound mv k1v k2v (Fintype.card K) + ioFailureUnionBound mx k1x k2x (Fintype.card K)
        + ioFailureUnionBound mp k1p k2p (Fintype.card K)
        + Fintype.card K * ((k1v + k2v) + (k1x + k2x) + (k1p + k2p)) := by
  unfold threeAccIOEvent
  refine (Finset.card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (Finset.card_union_le _ _) _).trans ?_
  have ev := (IOFailureEventExt_card_le (K := K) rv).trans (ioFailureUnionBound_mono mv _ h1v h2v)
  have ex := (IOFailureEventExt_card_le (K := K) rx).trans (ioFailureUnionBound_mono mx _ h1x h2x)
  have ep := (IOFailureEventExt_card_le (K := K) rp).trans (ioFailureUnionBound_mono mp _ h1p h2p)
  omega

/-- At option R's widths `6 / 10 / 8`. -/
theorem vclIOEvent_card_le [DecidableEq K] (rv : PreChallengeRecords L 6)
    (rx : PreChallengeRecords L 10) (rp : PreChallengeRecords L 8)
    (k1v k2v k1x k2x k1p k2p : ℕ)
    (h1v : rv.requests.length ≤ k1v) (h2v : rv.responses.length ≤ k2v)
    (h1x : rx.requests.length ≤ k1x) (h2x : rx.responses.length ≤ k2x)
    (h1p : rp.requests.length ≤ k1p) (h2p : rp.responses.length ≤ k2p) :
    (threeAccIOEvent (K := K) 6 10 8 rv rx rp).card ≤
      ioFailureUnionBound 6 k1v k2v (Fintype.card K) + ioFailureUnionBound 10 k1x k2x (Fintype.card K)
        + ioFailureUnionBound 8 k1p k2p (Fintype.card K)
        + Fintype.card K * ((k1v + k2v) + (k1x + k2x) + (k1p + k2p)) :=
  threeAccIOEvent_card_le 6 10 8 rv rx rp _ _ _ _ _ _ h1v h2v h1x h2x h1p h2p

theorem mem_threeAccIOEvent [DecidableEq K] {mv mx mp : ℕ} {rv : PreChallengeRecords L mv}
    {rx : PreChallengeRecords L mx} {rp : PreChallengeRecords L mp} {c : K × K} :
    c ∈ threeAccIOEvent (K := K) mv mx mp rv rx rp ↔
      c ∈ IOFailureEventExt K rv ∨ c ∈ IOFailureEventExt K rx ∨ c ∈ IOFailureEventExt K rp := by
  simp [threeAccIOEvent]

end Nock.NockVMROM.Thm54.VclL
