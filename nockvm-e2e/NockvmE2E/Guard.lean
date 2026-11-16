/-
scaffold: the end-to-end project on Lean 4.35 + ArkLib.
Axiom guard for the imported ArkLib results the e2e theorem will rest on. Every theorem we add gets a line here.
-/
import ArkLib.ProofSystem.Fri.Spec.Soundness
import ArkLib.ProofSystem.BatchedFri.EndToEnd

#print axioms Fri.Spec.soundness
#print axioms Fri.Spec.soundness_proximity
#print axioms Fri.Spec.rbr_soundness
