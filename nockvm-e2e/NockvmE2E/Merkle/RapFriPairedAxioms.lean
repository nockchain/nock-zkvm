/-
Axiom guard for `Merkle/MaskAppend.lean` and `Merkle/RapFriPaired.lean`.
-/
import NockvmE2E.Merkle.MaskAppend
import NockvmE2E.Merkle.RapFriPaired

open NockvmE2E.Merkle.MA NockvmE2E.Merkle.RapFri

#print axioms baseRounds_append
#print axioms pairedRoundsK_append
#print axioms merkleSkels_append
#print axioms merkleCount_append
#print axioms fstB
#print axioms sndB
#print axioms fstP
#print axioms sndP
#print axioms fstK
#print axioms sndK
#print axioms preRoots
#print axioms pathRootsK_append
#print axioms pathRootsK_append_fst
#print axioms pathRootsK_append_snd
#print axioms fstOpen
#print axioms sndOpen
#print axioms joinOpen
#print axioms fstOpen_join
#print axioms sndOpen_join
#print axioms join_fst_snd
#print axioms AgreesPre
#print axioms Agrees_append
#print axioms fstB_forgetPath
#print axioms sndB_forgetPath
#print axioms castPath_paired_append
#print axioms castPath_base_append
#print axioms sufExtP
#print axioms cExtP
#print axioms sufExtP_preserving
#print axioms sufExtP_bounded
#print axioms cExtP_terminal
#print axioms QOk_iff
#print axioms sufExtP_ks
#print axioms cExtP_ks
#print axioms sum_e2P
#print axioms sup_e2P_le
#print axioms rap_fri_paired_sound
#print axioms rap_fri_paired_sound_deep
#print axioms rhs_check
