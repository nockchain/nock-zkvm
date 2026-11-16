/-
 conjuncts 1-4 of `hglue_J8` assembled at `sideOfX` / `decSX` (`conj1234_sideOfX`).  Conjunct 5 and `hglue_J8` are NOT written.

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue3` is complete.
-/
import NockvmE2E.Exec.SideGlue2

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue
open NockvmE2E.Exec NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Exec.V NockvmE2E.Merkle NockvmE2E.Exec.SideInst NockvmE2E.Exec.SideOnlineR
  NockvmE2E.Exec.VL NockvmE2E.Exec.Inst

section Side
variable {n k : ℕ} {ω : SmoothCosetFftDomain n KC} (s : Fin (k + 1) → ℕ+) (l : ℕ) (L : Fri.FriLeaves (ω := ω) s)
  [SampleableType KC] [Inhabited KC] [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]

/-- the side statement of `sideOfX` is `stF` of the true context and the flat `vF` -/
theorem sideOfX_fst {Statement Salt W : Type} (XI : ExecInst) (FS : FSFn) (encZ : Statement × Salt → List ℕ)
    (o : Statement × Salt × FlatProof × FixProof × W) :
    (sideOfX s l L XI FS encZ o).1 =
      stF XI (fixCtx o.2.2.1 (zetaOf XI FS (encZ (o.1, o.2.1)) o.2.2.1))
        (o.2.2.2.1.vF.toList.flatMap (fun a => a.toList.flatMap VF.K3.limbs)) := by
  unfold sideOfX
  simp only
  rw [fixMsgs_headD]

/-- conjuncts 1-4 of `hglue_J8` at `sideOfX` and `decS := decSX XI` -/
theorem conj1234_sideOfX {Statement Salt W : Type} (XI : ExecInst) (hg : setupGates XI = true) (hn : XI.nD ≤ 32) (L' : DomLink XI hn)
    (FS : FSFn) (encZ : Statement × Salt → List ℕ) (o : Statement × Salt × FlatProof × FixProof × W)
    (vk : VK) (Hf : HFn) (FSf : FSFn) (hc : vk.cols = fixCols XI) (hX : vk.X = eraseX XI)
    (h : FixFailR XI vk Hf FS FSf (encZ (o.1, o.2.1)) o.2.2.1 o.2.2.2.1) :
    decSX XI (sideOfX s l L XI FS encZ o).1 =
        ⟨[], fixCtx o.2.2.1 (zetaOf XI FS (encZ (o.1, o.2.1)) o.2.2.1), o.2.2.2.1.vF⟩ ∧
      (∀ j, canon3 (ptKX XI (decSX XI (sideOfX s l L XI FS encZ o).1).ctx j)) ∧
      (∀ j i, smoothDomain XI.nD hn i ≠ toKV (ptKX XI (decSX XI (sideOfX s l L XI FS encZ o).1).ctx j)) ∧
      (∀ j o', j < (fixCols XI).size → o' < fixLen XI (fixCols XI)[j]! →
        canon3 (o.2.2.2.1.vF[j]!)[o']! ∧
          canon3 (fixTrue XI (fixCols XI)[j]! ((openPts XI (zetaOf XI FS (encZ (o.1, o.2.1)) o.2.2.1))[o']!))) := by
  have h1 : decSX XI (sideOfX s l L XI FS encZ o).1 =
      ⟨[], fixCtx o.2.2.1 (zetaOf XI FS (encZ (o.1, o.2.1)) o.2.2.1), o.2.2.2.1.vF⟩ := by
    rw [sideOfX_fst]
    exact conj1_of_FixFailR XI vk Hf FS FSf _ _ _ hc (fun c => by rw [hX]; rfl) h
  obtain ⟨h2, h3, h4⟩ := conj234_of_FixFailR XI hg hn L' vk Hf FS FSf _ _ _ hc hX h
  refine ⟨h1, ?_, ?_, h4⟩
  · rw [h1]; exact h2
  · rw [h1]; exact h3

end Side
end NockvmE2E.Exec.SideGlue

#print axioms NockvmE2E.Exec.SideGlue.sideOfX_fst
#print axioms NockvmE2E.Exec.SideGlue.conj1234_sideOfX
