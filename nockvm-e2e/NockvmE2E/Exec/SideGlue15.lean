/-
 conjunct 5, FS agreement for the FRI-mask part of the compiled side path (`hch` of `friLocal_side`): the encoded challenge `t` of
the friMask path `p.2.2` is the side FS function at the flat prefix `z :: ctx :: fm.take (t+2)`.

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue15` is complete.
-/
import NockvmE2E.Exec.SideGlue12

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue15
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx NockvmE2E.Exec.E2EFri
  NockvmE2E.Exec.SideGlue9 NockvmE2E.FriPort NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Merkle.RapFriQ NockvmE2E.Exec.E2EResid NockvmE2E.Exec.Inst NockvmE2E.Exec.Emb

section Side
variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC} (s : Fin (k + 1) → ℕ+) (l : ℕ) (L : Fri.FriLeaves (ω := ω) s)
  [SampleableType KC] [Inhabited KC] [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
variable (XI : ExecInst) {Statement Salt : Type} (decZ : List ℕ → Statement × Salt) (encZ : Statement × Salt → List ℕ)

/-- **the FS agreement on the FRI-mask part**: the encoded challenge `t` of the friMask path (`p.2.2`) is the side FS function at the flat prefix
`z :: ctx :: fm.take (t + 2)` -/
theorem chal_side (hz : ∀ x, decZ (encZ x) = x) {Op : Type} [Finite Op] [DecidableEq Op] (ω0 ω' : Op)
    (gk : (kk : Key (SStmt XI × (Statement × Salt)) PUnit (compiledRoundsK DgJ8 Op (SMSg s l L))) → kk.Challenge)
    (z0 : Statement × Salt) (ctx : List ℕ) (fm : List (List ℕ)) (hfm : fm.length ≤ k + 3) (t : ℕ) (ht : t + 2 ≤ fm.length) (nn : ℕ) :
    (encPathD (compiledRoundsK DgJ8 Op (friMask s 1 l L DgJ8 E2EResid.encK))
      (mDecs dgOf (friMask s 1 l L DgJ8 E2EResid.encK) (dsmC s 1 l L E2EResid.encK) ω0)
      (pathOf (stF XI ctx (fm.headD []), z0) _ gk
        (decMsgs _ (mDecs dgOf (SMSg s l L) (dsS s l L) ω') fm)).2.2).getD t [] =
    frOfX s l L XI ω0 (fkOfX s l L XI decZ ω0 (encZ z0 :: ctx :: fm.take (t + 2))) (gk _) nn := by
  have h := SideGlue.fs_side s l L XI decZ encZ hz ω0 ω' gk z0 ctx fm hfm (t + 2) (by omega) ht nn
  rw [h]
  rfl

/-- the merkle messages of the FRI merkle mask: the first `c` flat messages, as digests -/
theorem merkleMsgs_fmm (dY : List ℕ → DgJ8) : (c i : ℕ) → (h : i + c = k) → (fm : List (List ℕ)) → c ≤ fm.length →
    merkleMsgs dY (friMerkleMask s 1 l L DgJ8 E2EResid.encK i c h) fm = (fm.take c).map dY
  | 0, i, h, fm, _ => rfl
  | c + 1, i, h, fm, hc => by
      cases fm with
      | nil => simp at hc
      | cons m t =>
        show dY ((m :: t).headD []) :: merkleMsgs dY (friMerkleMask s 1 l L DgJ8 E2EResid.encK i.succ c (by omega)) t = _
        rw [merkleMsgs_fmm dY c i.succ (by omega) t (by simpa using hc)]
        simp

/-- the merkle messages of the side mask: the roots (messages `2 .. k+1` of the side transcript), as digests -/
theorem merkleMsgs_SMSg (dY : List ℕ → DgJ8) (fm : List (List ℕ)) (hfm : k + 2 ≤ fm.length) :
    merkleMsgs dY (SMSg s l L) fm = ((fm.drop 2).take k).map dY := by
  show merkleMsgs dY (friMerkleMask s 1 l L DgJ8 E2EResid.encK 0 k (by omega)) fm.tail.tail = _
  have e : fm.tail.tail = fm.drop 2 := by rcases fm with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp
  rw [e, merkleMsgs_fmm s l L dY k 0 (by omega) _ (by simp; omega)]

end Side

end NockvmE2E.Exec.SideGlue15

#print axioms NockvmE2E.Exec.SideGlue15.merkleMsgs_fmm
#print axioms NockvmE2E.Exec.SideGlue15.merkleMsgs_SMSg

#print axioms NockvmE2E.Exec.SideGlue15.chal_side
