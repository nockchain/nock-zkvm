/-
axiom guard for the FRI port (expected: propext, Classical.choice, Quot.sound only).
-/
import NockvmE2E.FriPort.Soundness

-- (Lift/Alternating.lean)
#print axioms NockvmE2E.Lift.Alternating.headExt_terminalState
#print axioms NockvmE2E.Lift.Alternating.headExt_preserving
#print axioms NockvmE2E.Lift.Alternating.headExt_bounded
-- (Lift/OfRbr.lean)
#print axioms NockvmE2E.Lift.Alternating.singleSalt_soundness_of_stateFamily
#print axioms NockvmE2E.Lift.Alternating.singleSalt_soundness_of_stateFamily'
#print axioms NockvmE2E.Lift.Alternating.singleSalt_soundness_of_rbrSoundness
#print axioms NockvmE2E.Lift.Alternating.sum_roundErrors
#print axioms NockvmE2E.Lift.Alternating.sup_roundErrors
-- F1 (FriPort/Rounds.lean)
#print axioms NockvmE2E.FriPort.friAlt
#print axioms NockvmE2E.FriPort.friRounds_length
-- F2 (FriPort/Accepts.lean)
#print axioms NockvmE2E.FriPort.friAccepts_run_true
#print axioms NockvmE2E.FriPort.friAccepts_run_false
-- F3 (FriPort/Soundness.lean)
#print axioms NockvmE2E.FriPort.friState_challengeLaw
#print axioms NockvmE2E.FriPort.fri_singleSalt_soundness
#print axioms NockvmE2E.FriPort.fri_singleSalt_soundness_trueGuards
