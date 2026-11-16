/-
Axiom guard for `Merkle/RapPaired.lean`.
-/
import NockvmE2E.Merkle.RapPaired

open NockvmE2E.Merkle.RapP

#print axioms perfectMaskData
#print axioms baseRounds_rapMask
#print axioms pairedRoundsK_rapMask
#print axioms rapPairedRounds_length
#print axioms rapRounds_length
#print axioms extColsP_terminal
#print axioms extColsP_preserving
#print axioms extColsP_bounded
#print axioms rapExtractorP_terminal
#print axioms rapExtractorP_preserving
#print axioms rapExtractorP_bounded
#print axioms rapExtractorP_output
#print axioms rapP_knowledge_soundness
#print axioms finalOfBK_forget
#print axioms rapAcceptsB_forget
#print axioms sup_sum_cast
#print axioms finalOfPK_succ
#print axioms okAcc_iff
#print axioms rap_paired_sound_perfect
#print axioms rapEps_eq_sErrors
#print axioms rap_hclear
#print axioms deep_inputs
#print axioms rap_paired_sound_deep
#print axioms rap_hclear_deep
#print axioms NonVacuous.toy_cert
#print axioms NonVacuous.nonvac_rap_hclear
