/-
 conjunct 5 assembled (`conj5_side`).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue20` is complete.
-/
import NockvmE2E.Exec.SideGlue17
import NockvmE2E.Exec.SideGlue19

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue20
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx NockvmE2E.Exec.E2EFri
  NockvmE2E.Exec.SideGlue9 NockvmE2E.FriPort NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Merkle.RapFriQ NockvmE2E.Exec.SideGlue13
  NockvmE2E.Exec.E2EResid NockvmE2E.Exec.Inst NockvmE2E.Exec.Emb NockvmE2E.Exec.SideGlue NockvmE2E.Exec.SideGlue11 NockvmE2E.Exec.SideGlue12 NockvmE2E.Exec.SideGlue14 NockvmE2E.Exec.SideGlue18 NockvmE2E.Exec.SideGlue7 NockvmE2E.Exec.SideGlue10 NockvmE2E.FriPort.Batched NockvmE2E.Exec.SideGlue19 NockvmE2E.Exec.SideGlue16 NockvmE2E.Exec.SideOnlineR NockvmE2E.Exec.E2EOnlineP NockvmE2E.Exec.E2EJ8V NockvmE2E.Merkle.SideMerkle NockvmE2E.Exec.SideGlue17


/-- the challenge samplers of `pSpec` at `eraseX XI` are those at `XI` (`eraseX` only erases `pre`) -/
instance instSampEraseX [SampleableType KC] [Inhabited KC] (XI : ExecInst) {n : ℕ} {ω : SmoothCosetFftDomain n KC}
    (s : Fin (XI.k + 1) → ℕ+)
    [inst : ∀ j, SampleableType ((pSpec XI.k (ω := ω) s XI.l).Challenge j)] :
    ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := ω) s (eraseX XI).l).Challenge j) :=
  inst
instance instSampEraseX2 [SampleableType KC] [Inhabited KC] (XI : ExecInst) (hn : XI.nD ≤ 32) (s : Fin (XI.k + 1) → ℕ+)
    [inst : ∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) s XI.l).Challenge j)] :
    ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := smoothDomain (eraseX XI).nD hn) s (eraseX XI).l).Challenge j) :=
  inst


theorem fixMsgs_last (k : ℕ) (ctx : List ℕ) (vF : Array (Array VF.K3)) (roots : Array Dg5) (pfinal : Array VF.K3) (hr : roots.size = k) :
    (((fixMsgs k ctx vF roots pfinal).toList.drop 1).tail).getD (k + 1) [] = pfinal.toList.flatMap VF.K3.limbs := by
  have : roots.extract 0 k = roots := by rw [Array.extract_eq_self_iff]; omega
  simp [fixMsgs, this, hr, List.getD_eq_getElem?_getD, List.drop_append]

section Dflt
variable [SampleableType KC] [Inhabited KC]
/-- the fallback address of `modelSS`, transported along `hSM` -/
noncomputable def dfltS (XI : ExecInst) (hg : setupGates XI = true) (hk : 1 ≤ XI.k) (hn : XI.nD ≤ 32)
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)] :
    MAddress (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn))) :=
  cast (congrArg MAddress (SideGlue13.hSM XI hn XI.l).symm) (dfltX XI hg hk)
end Dflt

section C5
variable [SampleableType KC] [Inhabited KC]

/-- **conjunct 5 of `hglue_J8`** at `sideOfX`, `modelSS`, `bLocal`, `trueGuards` (generic in the side table `gF`) -/
theorem conj5_side {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    (XI : ExecInst) (hg : setupGates XI = true) (hn : XI.nD ≤ 32) (L' : DomLink XI hn)
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)]
    (hshift : XI.dShift = 7) (hgen : psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC)) (hd1 : XI.d = 1) (hl0 : 0 < XI.l)
    (hdom : 2 ^ (∑ j, (((fun _ : Fin (XI.k + 1) => (1 : ℕ+)) j : ℕ+) : ℕ)) * (1 : ℕ+).val ≤ 2 ^ XI.nD)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (FS : FSFn) (o : Statement × Salt × FlatProof × FixProof × W)
    (dflt : MAddress (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn))))
    (gF : ∀ d', succinctRange DgJ8 (OpenAll DgJ8 (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn))))
      (NQuery (skelsSide XI)) (SStmt XI) (Statement × Salt) (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn)) d')
    (vk : VK) (hc : vk.cols = fixCols XI) (hX : vk.X = eraseX XI)
    (hFF : FixFailR XI vk (HfOf (skelsSide XI) (fun k => Key.Challenge k) gF) FS
      (FSfOf (skelsSide XI) (fun k => Key.Challenge k)
        (fkOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI decZ (ω0S (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn)))
        (frOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI (ω0S (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn))) gF)
      (encZ (o.1, o.2.1)) o.2.2.1 o.2.2.2.1)
    (hnc : ¬ VKcoll XI vk (HfOf (skelsSide XI) (fun k => Key.Challenge k) gF) o.2.2.2.1) :
    ∃ p, tabEval (tabK gF) (succinctVerifyK (trueGuards _)
      (merkleCheck (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn)))
        (modelSS XI hn XI.l dflt) id)
      (bLocal (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 XI.l (mSX XI) (GX XI) (LX XI hn) DgJ8 E2EResid.encK
        (OpenAll DgJ8 (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn)))) hdom
        (fun st => stmtOf (SideCfg.mk (m := mSX XI) XI (opIdxX XI) (ptKX XI)) hn (decSX XI st)) id)
      ((sideOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI FS encZ o).1,
        (sideOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI FS encZ o).2.1)
      (sideOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI FS encZ o).2.2) = some (some p) := by
  classical
  letI : ∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain (eraseX XI).nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain (eraseX XI).nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) (eraseX XI).l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := smoothDomain (eraseX XI).nD hn) (fun _ : Fin ((eraseX XI).k + 1) => (1 : ℕ+)) XI.l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := smoothDomain (eraseX XI).nD hn) (fun _ : Fin ((eraseX XI).k + 1) => (1 : ℕ+)) (eraseX XI).l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) (eraseX XI).l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := smoothDomain XI.nD hn) (fun _ : Fin ((eraseX XI).k + 1) => (1 : ℕ+)) XI.l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  letI : ∀ j, SampleableType ((pSpec (eraseX XI).k (ω := smoothDomain XI.nD hn) (fun _ : Fin ((eraseX XI).k + 1) => (1 : ℕ+)) (eraseX XI).l).Challenge j) :=
    ‹∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)›
  have hFFv := hFF.1.1
  obtain ⟨h1, _⟩ := SideGlue.conj1234_sideOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI hg hn L' FS encZ o vk _ _ hc hX hFF
  obtain ⟨hsz_pf, hsz_pos, hsz_roots, hpfc⟩ := verifyFix'_sizes vk _ _ _ _ _ _ hFFv
  have hk : vk.X.k = XI.k := by rw [hX]; rfl
  have hl : vk.X.l = XI.l := by rw [hX]; rfl
  have hr : o.2.2.2.1.roots.size = XI.k := by rw [hsz_roots, hk]
  let gk := fun k => gF (Sum.inr k)
  let ω0 := ω0S (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn)
  have hFSf : ∀ x nn, FSfOf (skelsSide XI) (fun k => Key.Challenge k)
        (fkOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI decZ ω0)
        (frOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI ω0) gF x nn =
      frOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI ω0
        (fkOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI decZ ω0 x) (gk _) nn := fun _ _ => rfl
  have hcs := cs_fix (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI decZ encZ hz ω0
    (openAllS (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI o.2.2.2.1) gk vk hk hl hl0 _ hFSf (o.1, o.2.1)
    (fixCtx o.2.2.1 (zetaOf XI FS (encZ (o.1, o.2.1)) o.2.2.1)) o.2.2.2.1 (by omega)
  let ctx := fixCtx o.2.2.1 (zetaOf XI FS (encZ (o.1, o.2.1)) o.2.2.1)
  let fm := (fixMsgs XI.k ctx o.2.2.2.1.vF o.2.2.2.1.roots o.2.2.2.1.pfinal).toList.drop 1
  let ω' := openAllS (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI o.2.2.2.1
  let z' : SStmt XI × (Statement × Salt) := (stF XI ctx (fm.headD []), (o.1, o.2.1))
  let msgs' := decMsgs _ (mDecs dgOf (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn)) (dsS (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn)) ω') fm
  have hrootsP := pathRoots_side (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI rfl ω' gk (o.1, o.2.1) ctx o.2.2.2.1 hr
  have hp : pathOfG (fun key => gF (Sum.inr key)) (compiledRoundsK DgJ8 (OpenAll DgJ8 (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn)))) (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn))) z' msgs' id (fun _ => rfl) =
      pathOf z' (compiledRoundsK DgJ8 (OpenAll DgJ8 (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn)))) (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn))) gk msgs' :=
    pathOfG_eq_pathOf gk _ _ _ id (fun _ => rfl)
  have hz' : ((sideOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI FS encZ o).1,
      (sideOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI FS encZ o).2.1) = z' := rfl
  have hmsg' : (sideOfX (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI FS encZ o).2.2 = msgs' := rfl
  rw [hz', hmsg']
  refine ⟨_, NockvmE2E.Exec.E2EMain.tabEval_succinctVerifyK gF _ _ z' msgs' _ hp ?_ ?_⟩
  · rw [hrootsP]
    exact merkle_side_accepts (eraseX XI) hn XI.l dflt vk hX (fun q => gF (Sum.inl q)) _ _ _ _ _ hFFv
  · have h1' : decSX XI (stF XI ctx (fm.headD [])) = ⟨[], ctx, o.2.2.2.1.vF⟩ := h1
    unfold bLocal
    simp only []
    rw [h1']
    refine local_side XI hg hn L' hshift hgen hd1 hdom vk (fun q => gF (Sum.inl q)) _ _ ctx
      (zetaOf XI FS (encZ (o.1, o.2.1)) o.2.2.1) o.2.2.1 o.2.2.2.1 hc hX rfl hFFv hnc
      (OpenAll DgJ8 (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn))))
      ω0 (openAllS (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI o.2.2.2.1) _ id (GX XI) _ ?_ (o.1, o.2.1) ?_ fm.tail ?_ ?_ ?_
    · intro i
      show _ ^ (i : ℕ) = _ ^ (i : ℕ)
      exact congrArg (· ^ (i : ℕ)) hcs.symm
    · intro t ht
      exact (chal_fix (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI decZ encZ hz ω0
        (openAllS (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI o.2.2.2.1) gk vk hk hl hl0 _ hFSf (o.1, o.2.1) ctx o.2.2.2.1 (by omega) t ht).symm
    · exact congrArg Prod.snd (pathMsgs_pathOf _ _ gk _)
    · exact fixMsgs_last XI.k ctx _ _ _ hr
    · exact (congrArg Prod.snd hrootsP).trans (openAllS_eq (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l (LX XI hn) XI vk hk o.2.2.2.1 (by omega))

end C5

end NockvmE2E.Exec.SideGlue20
