/-
axiom guard for the batched FRI port (expected: propext, Classical.choice, Quot.sound only).
-/
import NockvmE2E.FriPort.BatchedSoundness

#print axioms NockvmE2E.FriPort.Batched.consExt_terminalState
#print axioms NockvmE2E.FriPort.Batched.consExt_preserving
#print axioms NockvmE2E.FriPort.Batched.consExt_bounded
#print axioms NockvmE2E.FriPort.Batched.singleSalt_soundness_cons
#print axioms NockvmE2E.FriPort.Batched.friState_challengeLaw_all
#print axioms NockvmE2E.FriPort.Batched.batchedFri_singleSalt_soundness
