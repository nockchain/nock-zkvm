import NockvmE2E.Exec.Field
import NockvmE2E.Exec.Tip5

/-! / axiom check: every line must print `[propext, Classical.choice, Quot.sound]` (or fewer). -/
open NockvmE2E.Exec

#print axioms goldilocks_prime
#print axioms Gold.toZ_add
#print axioms Gold.toZ_sub
#print axioms Gold.toZ_neg
#print axioms Gold.toZ_mul
#print axioms Gold.toZ_inv
#print axioms Gold.toZ_pow
#print axioms K3.toK_add
#print axioms K3.toK_sub
#print axioms K3.toK_mul
#print axioms K3.toK_inv
#print axioms K3.toK_injective
#print axioms K3.toK_surjective
#print axioms KC_card
#print axioms smoothDomain
#print axioms orderOf_zeta
#print axioms ntt_root_spec
#print axioms NTT.ntt_check8
#print axioms NTT.ntt_check16
#print axioms Tip5.P_eq
#print axioms Tip5.tv1_varlen
#print axioms Tip5.tv9_varlen
#print axioms Tip5.tv14_hash10
#print axioms Tip5.tv_perm0
#print axioms Tip5.tv_permI
#print axioms Tip5.tip5Oracle
#print axioms Tip5.fsChallenge
