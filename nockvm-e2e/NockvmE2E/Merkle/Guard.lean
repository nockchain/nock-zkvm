/-
Axiom guard for the Merkle/BCS definitions (expected: propext, Classical.choice, Quot.sound
or fewer). No soundness theorem is delivered.
-/
import NockvmE2E.Merkle.Compiled
import NockvmE2E.Merkle.Opening
import NockvmE2E.Merkle.Rename

#print axioms NockvmE2E.Merkle.compiledRounds_length
#print axioms NockvmE2E.Merkle.pathRoots_length
#print axioms NockvmE2E.Merkle.untranslate_translate
#print axioms NockvmE2E.Merkle.translate_injective
#print axioms NockvmE2E.Merkle.succinctAcceptedExecution

-- (masked rounds, QD-shaped experiment, openings)
#print axioms NockvmE2E.Merkle.merkle_nonempty
#print axioms NockvmE2E.Merkle.compiledRoundsK_length
#print axioms NockvmE2E.Merkle.untranslate_translateK
#print axioms NockvmE2E.Merkle.translate_injectiveK
#print axioms NockvmE2E.Merkle.untranslate_challengeK
#print axioms NockvmE2E.Merkle.pairGuards
#print axioms NockvmE2E.Merkle.pairAccepts
#print axioms NockvmE2E.Merkle.forgetPath
#print axioms NockvmE2E.Merkle.pathRootsK
#print axioms NockvmE2E.Merkle.pathRootsK_length
#print axioms NockvmE2E.Merkle.succinctVerifyK
#print axioms NockvmE2E.Merkle.succinctAcceptedExecutionK
#print axioms NockvmE2E.Merkle.instFiniteBatchOpening
#print axioms NockvmE2E.Merkle.instDecEqBatchOpening
#print axioms NockvmE2E.Merkle.instFiniteOpenAll
#print axioms NockvmE2E.Merkle.instDecEqOpenAll
#print axioms NockvmE2E.Merkle.codecDec
#print axioms NockvmE2E.Merkle.codecDec_enc
#print axioms NockvmE2E.Merkle.merkleSkels_length
#print axioms NockvmE2E.Merkle.mkClaims
#print axioms NockvmE2E.Merkle.merkleCheck
#print axioms NockvmE2E.Merkle.bits_verifyOpeningClaims_relog
#print axioms NockvmE2E.Merkle.bits_mkClaims_root_only
#print axioms NockvmE2E.Merkle.merkleCheck_of_length
#print axioms NockvmE2E.Merkle.merkleCheck_of_length_ne
#print axioms NockvmE2E.Merkle.Agrees
#print axioms NockvmE2E.Merkle.QueryOnly
#print axioms NockvmE2E.Merkle.QueryOnly.accepts_of_agrees

-- (adaptive FS renaming)
#print axioms NockvmE2E.Merkle.Rename.bImpl
#print axioms NockvmE2E.Merkle.Rename.realImpl
#print axioms NockvmE2E.Merkle.Rename.impl₁
#print axioms NockvmE2E.Merkle.Rename.sim_impl₁
#print axioms NockvmE2E.Merkle.Rename.preserves
#print axioms NockvmE2E.Merkle.Rename.intertwines
#print axioms NockvmE2E.Merkle.Rename.step_inl
#print axioms NockvmE2E.Merkle.Rename.step_hash
#print axioms NockvmE2E.Merkle.Rename.step_fs
#print axioms NockvmE2E.Merkle.Rename.merge_cacheQuery_inl
#print axioms NockvmE2E.Merkle.Rename.merge_cacheQuery_inr
#print axioms NockvmE2E.Merkle.Rename.evalDist_adaptiveRename
#print axioms NockvmE2E.Merkle.Rename.sample_untranslateK
#print axioms NockvmE2E.Merkle.Rename.evalDist_adaptiveRenameK
