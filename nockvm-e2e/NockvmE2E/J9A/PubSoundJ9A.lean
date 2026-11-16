/-
  NockvmE2E/J9A/PubSoundJ9A.lean

  The J-9 A public relation for the exec chain parametrised by `PR` (`PubSound`):
  * `pubJ9P_canon`  : `PubJ9P` is stable under reduction of the public array mod `p` (twin of `pubJ8P_canon`, 8 slices);
  * `pubSound_J9`   : at `pubMode = 2` the executed check `PE.pubCheck9` is sound for `PubJ9P` (from `pubCheck9_sound`).
-/
import NockvmE2E.J9A.RVUJ9A
import NockvmE2E.Exec.E2EJ8P2
import NockvmE2E.Exec.SoundClosed
set_option autoImplicit false

namespace NockvmE2E.J9A.PubSoundJ9A
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.E2EJ8P2 NockvmE2E.J9A.RVUJ9A NockvmE2E.Merkle.RapFriQ

/-- `PubJ9P` is stable under canonicalising the public array, given the instance atoms are `< p` -/
theorem pubJ9P_canon (inp : PE.PubIn) (L : PE.PubLayout) (slotOf : Array ℕ) (slots : Array VF.K3) (pub : Array UInt64)
    (hat : ∀ a ∈ inp.atoms, a.2 < NockvmE2E.Exec.p) (h : PubJ9P inp L slotOf slots pub) :
    PubJ9P inp L slotOf slots (canonPub pub) := by
  obtain ⟨⟨cr, pr, h1, h2, h3⟩, hd⟩ := h
  obtain ⟨cr', h1', hq⟩ := claims_canon _ _ _ _ cr h1
  refine ⟨⟨cr', pr, ?_, h2, ?_⟩, ?_⟩
  · rw [slOf_map]; exact h1'
  · simp only [slOf_map, rhoOf_map, rhoSOf_map, pubK_map']
    rw [← hq]
    exact h3
  · rw [slOf_map]; exact computeDerived_canon _ _ _ hat hd

/-- **`pubSound_J9`**: at `pubMode = 2` the executed public check is sound for the J-9 A relation `PubJ9P` -/
theorem pubSound_J9 (XI : ExecInst) (hmode : XI.pubMode = 2) :
    PubSound XI (PubJ9P XI.pubIn XI.pubLay XI.slotOf) := by
  intro slots pub hs hp hinp hc
  have hc' : PE.pubCheck9 XI.pubIn XI.pubLay XI.slotOf slots pub = true := by
    simpa [ExecInst.pubCheck, hmode] using hc
  exact pubCheck9_sound XI.pubIn XI.pubLay XI.slotOf _ _ hs hp hinp hc'

end NockvmE2E.J9A.PubSoundJ9A
#print axioms NockvmE2E.J9A.PubSoundJ9A.pubJ9P_canon
#print axioms NockvmE2E.J9A.PubSoundJ9A.pubSound_J9
