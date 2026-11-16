/-
 conjunct 5, step "merkle_embed_side": the audited `merkleCheck` over the merkle part `skM` of the side oracle, read through the
tag-shifted model `shiftModel`, accepts under a hash table `h : NQuery sk → DgJ8` as soon as every tree `4+w` of `sk` reconstructs its root
(the output of `tree_embed_side`).  `rootUnder_shift` is the transport lemma (shiftModel at `⟨w,a⟩` = idModel at `⟨4+w, trI a⟩`).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue8` is complete.
-/
import NockvmE2E.Exec.SideGlue7

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue8
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.SM NockvmE2E.Exec.Cover NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Exec.Emb

/-- generic transport: along `e : s = t` two keyed models reconstruct the same root of the same flat tree if their hashed queries agree -/
theorem rootUnder_congr_skel {Q1 Q2 A1 A2 : Type} (h1 : Q1 → DgJ8) (h2 : Q2 → DgJ8)
    (m1 : MerkleTreeExtractability.NodeQueryModel Q1 A1 DgJ8) (m2 : MerkleTreeExtractability.NodeQueryModel Q2 A2 DgJ8)
    (T : FTree DgJ8) {s t : Skeleton} (e : s = t) (key1 : SkeletonInternalIndex s → A1) (key2 : SkeletonInternalIndex t → A2)
    (hq : ∀ a l r, h1 (m1.mkQuery (key1 a) (l, r)) = h2 (m2.mkQuery (key2 (trI e a)) (l, r))) :
    rootUnder h1 m1 key1 (mkOpeningD T s) = rootUnder h2 m2 key2 (mkOpeningD T t) := by
  subst e
  unfold rootUnder
  congr 1
  funext a l r
  exact hq a l r

theorem rootUnder_shift (sk skM : List Skeleton) (hlen : 4 + skM.length ≤ sk.length)
    (hget : ∀ w (hw : w < skM.length) (hj : 4 + w < sk.length), sk.get ⟨4 + w, hj⟩ = skM.get ⟨w, hw⟩)
    (dflt : MAddress skM) (h : NQuery sk → DgJ8) (w : Fin skM.length) (hj : 4 + w.1 < sk.length) (T : FTree DgJ8) :
    rootUnder h (shiftModel sk skM hlen hget dflt) (fun a => (⟨w, a⟩ : MAddress skM)) (mkOpeningD T (skM.get w)) =
      rootUnder (Query := NQuery sk) h (idModel sk) (fun a => (⟨⟨4 + w.1, hj⟩, a⟩ : MAddress sk))
        (mkOpeningD T (sk.get ⟨4 + w.1, hj⟩)) := by
  apply rootUnder_congr_skel h h _ _ T (hget w.1 w.2 hj).symm
  intro a l r
  rfl

/-- **`merkle_embed_side`**: if every tree `4+w` of `sk` reconstructs `roots[w]` from the flat tree `ts[4+w]`, the shifted-model `merkleCheck`
of the opening `openAllOf skM (ts.drop 4)` accepts. -/
theorem merkle_embed_side (sk skM : List Skeleton) (hlen : 4 + skM.length ≤ sk.length)
    (hget : ∀ w (hw : w < skM.length) (hj : 4 + w < sk.length), sk.get ⟨4 + w, hj⟩ = skM.get ⟨w, hw⟩)
    (dflt : MAddress skM) (h : NQuery sk → DgJ8) (ts : List (FTree DgJ8)) (roots : List DgJ8)
    (hr : roots.length = skM.length)
    (htree : ∀ (w : Fin skM.length) (hj : 4 + w.1 < sk.length),
      rootUnder (Query := NQuery sk) h (idModel sk) (fun a => (⟨⟨4 + w.1, hj⟩, a⟩ : MAddress sk))
        (mkOpeningD (ts.getD (4 + w.1) ⟨fun _ => false, fun _ => default, [], default⟩) (sk.get ⟨4 + w.1, hj⟩)) =
        roots.get (w.cast hr.symm)) :
    tabEval (spec := NQuery sk →ₒ DgJ8) (fun q => some (h q))
      (merkleCheck skM (shiftModel sk skM hlen hget dflt) id roots (openAllOf skM (ts.drop 4))) = some true := by
  rw [tabEval_merkleCheck h skM (shiftModel sk skM hlen hget dflt) id _ _ hr]
  congr 1
  simp only [List.all_eq_true, List.mem_ofFn, id]
  rintro _ ⟨w, rfl⟩
  have hj : 4 + w.1 < sk.length := by have := w.2; omega
  rw [get_openAllOf, rootUnder_shift sk skM hlen hget dflt h w hj]
  have e : (ts.drop 4).getD w.1 ⟨fun _ => false, fun _ => default, [], default⟩ =
      ts.getD (4 + w.1) ⟨fun _ => false, fun _ => default, [], default⟩ := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]
  rw [e, htree w hj]
  simp

end NockvmE2E.Exec.SideGlue8

#print axioms NockvmE2E.Exec.SideGlue8.rootUnder_shift
#print axioms NockvmE2E.Exec.SideGlue8.merkle_embed_side
