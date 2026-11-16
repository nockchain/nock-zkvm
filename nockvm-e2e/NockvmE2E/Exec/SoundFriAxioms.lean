import NockvmE2E.Exec.SoundFri

/-!  FRI axiom check: every line must print `[propext, Classical.choice, Quot.sound]` (or fewer). -/
open NockvmE2E.Exec.SF

#print axioms fold2
#print axioms checkRound_of_ptFold
#print axioms verifyQueries_ne_none_of_pointwise
#print axioms level_fold
#print axioms flat_of_walk
#print axioms ptFold_of_flat
#print axioms verifyQueries_of_flat
#print axioms queryBad_of_flat
#print axioms friAccepts_of_flat
#print axioms foldK3_hom
#print axioms yAt_hom
#print axioms hornerK_hom
#print axioms walkKGo_sound
#print axioms walkK_sound
#print axioms deepWordS_hom
#print axioms combined_deep_eq
#print axioms input_word_eq
#print axioms nonvac_hγ
#print axioms nonvac_flat
