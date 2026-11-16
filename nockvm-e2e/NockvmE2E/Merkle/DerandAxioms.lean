/-
Axiom guard for `Merkle/Derand.lean` (S0-S3 derandomisation). Expected: propext, Classical.choice,
Quot.sound or fewer.
-/
import NockvmE2E.Merkle.Derand

#print axioms NockvmE2E.Merkle.Derand.evalDist_sampler
#print axioms NockvmE2E.Merkle.Derand.s1_real_eq
#print axioms NockvmE2E.Merkle.Derand.seeded_eq
#print axioms NockvmE2E.Merkle.Derand.exists_perIndexBound
#print axioms NockvmE2E.Merkle.Derand.realObs_evalDistEq
#print axioms NockvmE2E.Merkle.Derand.eager_run'_eq
#print axioms NockvmE2E.Merkle.Derand.derand
#print axioms NockvmE2E.Merkle.Derand.observer_run'
#print axioms NockvmE2E.Merkle.Derand.evalDist_randomOracle_run_eq_cachingOracle_run
#print axioms NockvmE2E.Merkle.Derand.evalDist_randomOracle_run'_eq_withCacheOverlay
#print axioms NockvmE2E.Merkle.Derand.derand_prEvent_le
