/-
`verifyReport_ok`: the exit code of the certified verifier is 0 only when the pure bytes verifier accepted.
`Exec/VerifyCertMain.lean`'s `main` prints `(verifyReport …).2` and exits with `(verifyReport …).1`; this lemma links that exit code to
`verifyBytesL` / `verifyBytesLJ`, whose soundness is `CertSound.verifyBytesL_sound` / `verifyBytesLJ_sound`.
-/
import NockvmE2E.Exec.CertBytes

namespace NockvmE2E.Exec.Cert

theorem verifyReport_ok {fam : String} {vkB instB : ByteArray} {chipBs : List ByteArray} {proofB fixB : ByteArray}
    (h : (verifyReport fam vkB instB chipBs proofB fixB).1 = 0) :
    ∃ c, (fam = "j9al" ∧ verifyBytesL vkB instB chipBs proofB fixB = .ok c) ∨
      (fam ≠ "j9al" ∧ fam = "j9alj" ∧ verifyBytesLJ vkB instB chipBs proofB fixB = .ok c) := by
  unfold verifyReport at h
  by_cases h1 : fam = "j9al"
  · subst h1
    simp only [beq_self_eq_true, ite_true] at h
    split at h
    · rename_i c hc; exact ⟨c, Or.inl ⟨rfl, hc⟩⟩
    · simp at h
  · have h1' : (fam == "j9al") = false := by simpa using h1
    by_cases h2 : fam = "j9alj"
    · subst h2
      simp only [h1', beq_self_eq_true, ite_true, Bool.false_eq_true, ite_false] at h
      split at h
      · rename_i c hc; exact ⟨c, Or.inr ⟨h1, rfl, hc⟩⟩
      · simp at h
    · have h2' : (fam == "j9alj") = false := by simpa using h2
      simp only [h1', h2', Bool.false_eq_true, ite_false] at h
      simp at h

end NockvmE2E.Exec.Cert

#print axioms NockvmE2E.Exec.Cert.verifyReport_ok
