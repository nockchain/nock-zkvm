/-
Axiom guard for `Merkle/Reduction.lean` and `Merkle/VerifyTransport.lean`.
-/
import NockvmE2E.Merkle.Reduction
import NockvmE2E.Merkle.VerifyTransport

open NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.VerifyTransport

#print axioms NockvmE2E.Merkle.Reduction.memoAdd_extends
#print axioms NockvmE2E.Merkle.Reduction.addEntries_extends
#print axioms NockvmE2E.Merkle.Reduction.addEntries_defined
#print axioms NockvmE2E.Merkle.Reduction.obsStep
#print axioms NockvmE2E.Merkle.Reduction.obsStep_extends
#print axioms NockvmE2E.Merkle.Reduction.obsStep_defined
#print axioms NockvmE2E.Merkle.Reduction.memoWords_congr
#print axioms NockvmE2E.Merkle.Reduction.translateK_stable
#print axioms NockvmE2E.Merkle.Reduction.pairMsgs
#print axioms NockvmE2E.Merkle.Reduction.bImplK
#print axioms NockvmE2E.Merkle.Reduction.reductionB
#print axioms NockvmE2E.Merkle.Reduction.reduction_rename
#print axioms NockvmE2E.Merkle.VerifyTransport.finishK
#print axioms NockvmE2E.Merkle.VerifyTransport.compiled_eq_paired_then_finish
#print axioms NockvmE2E.Merkle.VerifyTransport.publicStoppedVerify_compiled_eq
#print axioms NockvmE2E.Merkle.VerifyTransport.input_untranslateK
#print axioms NockvmE2E.Merkle.VerifyTransport.translateK_untranslateK
