/-
(A1c; twin of `J9A/PubSoundJ9A.lean`).  The J-9 AL public relation for the exec chain parametrised by `PR` (`PubSound`):
  * `pubJ9LP_canon`  : `PubJ9LP` is stable under reduction of the public array mod `p` (`primRecS` reads no `pub`);
  * `pubSound_J9L`   : at `pubMode = 3` the executed check `PE.pubCheck9L` is sound for `PubJ9LP`.
`PubSound` only supplies `InpCan`, so `PrimsCan` is an extra static argument (discharged from `PrimsLink` in `linkGate9L`).
Not zero-knowledge.
-/
import NockvmE2E.J9AL.RVUJ9AL
import NockvmE2E.Exec.E2EJ8P2
import NockvmE2E.Exec.SoundClosed
set_option autoImplicit false

namespace NockvmE2E.J9AL.PubSoundJ9AL
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.E2EJ8P2 NockvmE2E.J9AL.RVUJ9AL NockvmE2E.Merkle.RapFriQ

/-- `PubJ9LP` is stable under canonicalising the public array, given the instance atoms are `< p` -/
theorem pubJ9LP_canon (inp : PE.PubIn) (L : PE.PubLayout) (slotOf : Array ℕ) (slots : Array VF.K3) (pub : Array UInt64)
    (hat : ∀ a ∈ inp.atoms, a.2 < NockvmE2E.Exec.p) (h : PubJ9LP inp L slotOf slots pub) :
    PubJ9LP inp L slotOf slots (canonPub pub) := by
  obtain ⟨⟨cr, pr, qr, h1, h2, h4, h3⟩, hd⟩ := h
  obtain ⟨cr', h1', hq⟩ := claims_canon _ _ _ _ cr h1
  refine ⟨⟨cr', pr, qr, ?_, h2, h4, ?_⟩, ?_⟩
  · rw [slOf_map]; exact h1'
  · simp only [slOf_map, rhoOf_map, rhoSOf_map, pubK_map']
    rw [← hq]
    exact h3
  · rw [slOf_map]; exact computeDerived_canon _ _ _ hat hd

/-- **`pubSound_J9L`**: at `pubMode = 3` the executed public check is sound for the J-9 AL relation `PubJ9LP` -/
theorem pubSound_J9L (XI : ExecInst) (hmode : XI.pubMode = 3) (hP : PrimsCan XI.pubIn) :
    PubSound XI (PubJ9LP XI.pubIn XI.pubLay XI.slotOf) := by
  intro slots pub hs hp hinp hc
  have hc' : PE.pubCheck9L XI.pubIn XI.pubLay XI.slotOf slots pub = true := by
    simpa [ExecInst.pubCheck, hmode] using hc
  exact pubCheck9L_sound XI.pubIn XI.pubLay XI.slotOf _ _ hs hp hinp hP hc'

end NockvmE2E.J9AL.PubSoundJ9AL
#print axioms NockvmE2E.J9AL.PubSoundJ9AL.pubJ9LP_canon
#print axioms NockvmE2E.J9AL.PubSoundJ9AL.pubSound_J9L
