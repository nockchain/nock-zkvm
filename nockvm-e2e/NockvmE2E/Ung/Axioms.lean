/-
Axiom guard (expected: propext, Classical.choice, Quot.sound or fewer).
-/
import NockvmE2E.Ung.Defs
import NockvmE2E.Ung.MerkleNegative
import NockvmE2E.Ung.AirDet
import NockvmE2E.Ung.Positive
import NockvmE2E.Ung.MerkleCompose
import NockvmE2E.Ung.Staged

#print axioms NockvmE2E.Ung.Ungrindable.mono
#print axioms NockvmE2E.Ung.iopUnique
#print axioms NockvmE2E.Ung.twoAcceptExecution
#print axioms NockvmE2E.Ung.opening_complete
#print axioms NockvmE2E.Ung.root_inj
#print axioms NockvmE2E.Ung.accHonest_iff
#print axioms NockvmE2E.Ung.flip_root_ne
#print axioms NockvmE2E.Ung.flip_values
#print axioms NockvmE2E.Ung.flip_accepts_iff
#print axioms NockvmE2E.Ung.merkle_not_unique
#print axioms NockvmE2E.Ung.prob_mem_le
#print axioms NockvmE2E.Ung.merkle_flip_prob
#print axioms NockvmE2E.Ung.merkle_ungrind_negative
#print axioms NockvmE2E.Ung.inj_free
#print axioms NockvmE2E.Ung.merkle_not_unique_example

-- part B
#print axioms NockvmE2E.Ung.AirDet.pair
#print axioms NockvmE2E.Ung.toyRap_airDet
#print axioms NockvmE2E.Ung.pr_accept_split_ev
#print axioms NockvmE2E.Ung.finalOf_nd
#print axioms NockvmE2E.Ung.rapAccepts_nd_iff
#print axioms NockvmE2E.Ung.roundBound_nd
#print axioms NockvmE2E.Ung.certificate_nd
#print axioms NockvmE2E.Ung.rap_succinct_noncanon
#print axioms NockvmE2E.Ung.ro_pure
#print axioms NockvmE2E.Ung.swapAdv
#print axioms NockvmE2E.Ung.wql_fst
#print axioms NockvmE2E.Ung.wql_bind_fst
#print axioms NockvmE2E.Ung.swap_eq
#print axioms NockvmE2E.Ung.stage2
#print axioms NockvmE2E.Ung.two_eq_bind
#print axioms NockvmE2E.Ung.pr_two_first_le
#print axioms NockvmE2E.Ung.pr_two_second_le
#print axioms NockvmE2E.Ung.uniqFail_of_canon
#print axioms NockvmE2E.Ung.rap_succinct_unique
#print axioms NockvmE2E.Ung.rap_succinct_unique_iop
#print axioms NockvmE2E.Ung.no_unique_of_wordCommit
#print axioms NockvmE2E.Ung.collide_nonempty_of_wordCommit
#print axioms NockvmE2E.Ung.wordOf_root
#print axioms NockvmE2E.Ung.merkleCS
#print axioms NockvmE2E.Ung.merkle_no_unique
#print axioms NockvmE2E.Ung.merkle_compose
#print axioms NockvmE2E.Ung.toyData
#print axioms NockvmE2E.Ung.toy_no_unique
#print axioms NockvmE2E.Ung.ro_query_log
#print axioms NockvmE2E.Ung.ro_log_len
#print axioms NockvmE2E.Ung.isTotalQueryBound_pure'
#print axioms NockvmE2E.Ung.mapped_bound
#print axioms NockvmE2E.Ung.verify_bound
#print axioms NockvmE2E.Ung.swap_keys_le
#print axioms NockvmE2E.Ung.sRounds_length
#print axioms NockvmE2E.Ung.rap_succinct_unique_Q
#print axioms NockvmE2E.Ung.rap_succinct_unique_iop_Q

-- part C
#print axioms NockvmE2E.Ung.AirDet.staged
#print axioms NockvmE2E.Ung.toy2Rap_airDetStaged
#print axioms NockvmE2E.Ung.toy2Rap_not_airDet
#print axioms NockvmE2E.Ung.ro_hash_support
#print axioms NockvmE2E.Ung.ro_le
#print axioms NockvmE2E.Ung.PathCached.mono
#print axioms NockvmE2E.Ung.mapped_cached
#print axioms NockvmE2E.Ung.pEq_zero
#print axioms NockvmE2E.Ung.pEq_succ
#print axioms NockvmE2E.Ung.pc_tail
#print axioms NockvmE2E.Ung.pc_head
#print axioms NockvmE2E.Ung.chal_at
#print axioms NockvmE2E.Ung.single_cached
#print axioms NockvmE2E.Ung.two_cached
#print axioms NockvmE2E.Ung.rap_succinct_badpath
#print axioms NockvmE2E.Ung.canTr_congr
#print axioms NockvmE2E.Ung.badC_sound
#print axioms NockvmE2E.Ung.finalOf_out
#print axioms NockvmE2E.Ung.finalOf_agree
#print axioms NockvmE2E.Ung.finalOf_msg
#print axioms NockvmE2E.Ung.proj_eq_of_good
#print axioms NockvmE2E.Ung.rap_succinct_unique_staged
#print axioms NockvmE2E.Ung.rap_succinct_unique_staged_Q
#print axioms NockvmE2E.Ung.rap_succinct_unique_staged_iop
