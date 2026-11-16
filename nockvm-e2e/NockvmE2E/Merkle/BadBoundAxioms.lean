/-
Axiom guard for `Merkle/BadBound.lean`. Expected: propext, Classical.choice, Quot.sound or fewer.
-/
import NockvmE2E.Merkle.BadBound

open NockvmE2E.Merkle.BadBound
#print axioms isHashQuery
#print axioms FsBound
#print axioms Obs.fresh_seen
#print axioms Obs.fresh_len
#print axioms bs_hashBound
#print axioms bs_ckptBound
#print axioms finalNE_len
#print axioms hH_of_hashBound
#print axioms hbud_of_fsBound
#print axioms hashImpl
#print axioms liftV
#print axioms seeded_liftV
#print axioms seeded_bind_liftV
#print axioms realWorld
#print axioms bad_real_le
#print axioms bad_real_le_of_bounds
