/-
  Nock/RedTeam/Batch4803Thm54J9bAttacks.lean

  **The two attacks, compiled.**
  * **Hostile `mb` row** (`LinkJ9A.hostile_mb_rejected`): a big claim leaf `n` whose serial points at an atom-table row of
    value `n' ≠ n` is REJECTED outside the events: on an `AcceptsJ9V`-accepted trace (absent layout), outside the J-8
    events, under the link and the census over the claim extension, the atom-table noun at the serial is `n`
    (`LinkJ9A.claimBig_ext`), so no such row exists.
  * **Kind mismatch** (`LinkJ9A.kind_big_is_two`, `LinkJ9A.kind_zero_rejected`): the public handle's kind is fixed by the verifier from
    the claim (`claimKH`: `n ≥ p ↦ 2`, `n < p ↦ 0`), so on an accepted trace row 0 carries kind `2` at a big claim
    leaf; a trace presenting the big leaf as a kind-0 handle `(0, n mod p)` is not accepted.  The J-8 wrap
    (`LinkJ8Q3.labelF_atom_wrap`: `v` and `v + p` have the SAME J-8 label) is blocked: `labelJ9_wrap_distinct`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ9G

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Nock.RedTeam.Batch4803

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS (claimNoun ClaimMsgVS labelF)
section

/-- **The J-8 wrap is blocked**: `atom v` (`v < p`, kind 0) and `atom (v + p)` (big, kind 2) have DIFFERENT J-9
labels, where the J-8 labels agree (`LinkJ8Q3.labelF_atom_wrap`). -/
theorem labelJ9_wrap_distinct {p : ℕ} [Fact p.Prime] (hp : 2 < p) (v : ℕ) (hv : v < p) (f e : Noun)
    (m : ClaimMsgVS) : labelJ9 p ⟨.atom v, f, e⟩ m ≠ labelJ9 p ⟨.atom (v + p), f, e⟩ m := by
  intro h
  have h0 := congrArg (fun l => l.getD 0 0) h
  have e1 : (labelJ9 p ⟨.atom v, f, e⟩ m).getD 0 0 = ((0 : ℕ) : ZMod p) := by
    simp [labelJ9, claimHJ9, claimKH, claimNoun, Nat.not_le.mpr hv]
  have e2 : (labelJ9 p ⟨.atom (v + p), f, e⟩ m).getD 0 0 = ((2 : ℕ) : ZMod p) := by
    simp [labelJ9, claimHJ9, claimKH, claimNoun]
  change (labelJ9 p ⟨.atom v, f, e⟩ m).getD 0 0 = (labelJ9 p ⟨.atom (v + p), f, e⟩ m).getD 0 0 at h0
  rw [e1, e2, ZMod.natCast_eq_natCast_iff', Nat.zero_mod, Nat.mod_eq_of_lt hp] at h0
  omega

/-- **The J-8 labels of the same two claims agree** (the J-8 finding, restated for contrast). -/
theorem labelF_wrap_same {p : ℕ} [Fact p.Prime] (v : ℕ) (f e : Noun) (m : ClaimMsgVS) :
    labelF (F := ZMod p) ⟨.atom v, f, e⟩ m = labelF (F := ZMod p) ⟨.atom (v + p), f, e⟩ m :=
  LinkJ8Q3.labelF_atom_wrap v f e m

end

#print axioms labelJ9_wrap_distinct
#print axioms LinkJ9A.hostile_mb_rejected
#print axioms LinkJ9A.mb_fp_ne
#print axioms LinkJ9A.hostile_key_not_served
#print axioms LinkJ9A.kind_big_is_two
#print axioms LinkJ9A.kind_zero_rejected

end Nock.RedTeam.Batch4803
