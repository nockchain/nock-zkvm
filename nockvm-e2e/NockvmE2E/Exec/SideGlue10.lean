/-
 conjunct 5, FRI link, step 2: `coversF_side` (the selectors cover the read set) and `friLocal_side` (the FRI local check
`friLocal` accepts a compiled FRI-mask path from the explicit flat data: coverage + `friLinkAt_side` + the flat walk).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue10` is complete.
-/
import NockvmE2E.Exec.SideGlue9

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue10
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx NockvmE2E.Exec.E2EFri
  NockvmE2E.Exec.SideGlue9 NockvmE2E.FriPort NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Merkle.RapFriQ

/-- **`coversF_side`**: the FRI selectors of `os` cover the read set of the query vector `xs`, from the selector link `SelF (QS sels)` and the facts that
`sels[4+i] = treeSel XI 0 (4+i) pos` and `xs` is the verifier's position vector. -/
theorem coversF_side (XI : ExecInst) (hn32 : XI.nD ≤ 32) [SampleableType KC] [Inhabited KC]
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)]
    (d : ℕ+) (hdom : 2 ^ (∑ j, (((fun _ : Fin (XI.k + 1) => (1 : ℕ+)) j : ℕ+) : ℕ)) * d.val ≤ 2 ^ XI.nD)
    (L : Fri.FriLeaves (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)))
    (hL : L = LX XI hn32) (enc : KC ↪ DgJ8)
    (os : OpenAll DgJ8 (merkleSkels (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc)))
    (xs : Fin XI.l → ((smoothDomain XI.nD hn32).subdomain 0).toFinset)
    (pos : Array ℕ) (sels : Array (Array ℕ))
    (hshift : XI.dShift = 7) (hgen : psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC)) (hk1 : XI.k + 1 ≤ XI.nD) (hsz : pos.size = XI.l)
    (hsels : ∀ i, i < XI.k → sels[4 + i]! = treeSel XI 0 (4 + i) pos)
    (hxs : ∀ j, (xs j).val = homV.ψ XI.dShift * homV.ψ XI.dGen ^ pos[j.1]!)
    (hselF : SelF (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc (QS sels) 0 XI.k (by omega) os) :
    Covers (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc (round_bound hdom) xs 0 XI.k (by omega) os := by
  have hs := round_bound hdom
  have hx' : ∀ j, (xs j).val = algebraMap (ZMod NockvmE2E.Exec.p) KC 7 * ((zeta XI.nD : KCˣ) : KC) ^ (fun j : Fin XI.l => pos[j.1]!) j := by
    intro j
    rw [hxs j]
    show psiV XI.dShift * psiV XI.dGen ^ _ = _
    rw [psiV_shift XI hshift, hgen]
  have hmem : ∀ j : Fin XI.l, pos[j.1]! ∈ pos.toList := by
    intro j
    have : j.1 < pos.size := by rw [hsz]; exact j.2
    rw [getElem!_pos pos j.1 this]; simp
  subst hL
  refine covers_of _ _ _ _ _ _ hs xs _ ?_ XI.k 0 _ _ hselF
  intro i hi y hy
  have hi2 : i + 2 ≤ XI.nD := by omega
  obtain ⟨j, hj⟩ := DomIdx.readPts_idx (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l hn32 rfl (fun _ => rfl) hs xs
    (fun j => pos[j.1]!) hx' i hi2 hi y hy
  show _ ∈ (sels[4 + i]!).toList
  rw [LX_leafNum XI hn32 i hi hi2, hsels i hi]
  have e1 : XI.nD - (4 + i - 3) - 1 = XI.nD - i - 2 := by omega
  have hu := ((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i + 1), ((1 : ℕ+) : ℕ))).equivToFinset.symm y |>.isLt
  have hm : (∑ j ∈ finRangeTo (XI.k + 1) (i + 1), ((1 : ℕ+) : ℕ)) = i + 1 := msum1 XI.k i hi
  have hu2 : (((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i + 1), ((1 : ℕ+) : ℕ))).equivToFinset.symm y).val
      < 2 ^ (XI.nD - (i + 1)) := lt_of_lt_of_eq hu (by rw [hm])
  have hx2 : (((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i + 1), ((1 : ℕ+) : ℕ))).equivToFinset.symm y).val
      / 2 ^ (XI.nD - i - 2) < 2 := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_succ]
    have : XI.nD - i - 2 + 1 = XI.nD - (i + 1) := by omega
    rwa [this]
  have := mem_treeSel_fri XI (4 + i) pos (by omega) (pos[j.1]!) (hmem j) _ hx2
  rw [e1, ← hj] at this
  exact this

/-- **`friLocal_side`**: the FRI local check accepts the compiled FRI-mask path `pm` from the explicit flat data (the flat walk of every query
`hwalk` plus canonicity, the FRI link `friLinkAt_side`, and coverage `coversF_side`). -/
theorem friLocal_side (XI : ExecInst) (hn32 : XI.nD ≤ 32) [SampleableType KC] [Inhabited KC]
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)]
    (d : ℕ+) (hdom : 2 ^ (∑ j, (((fun _ : Fin (XI.k + 1) => (1 : ℕ+)) j : ℕ+) : ℕ)) * d.val ≤ 2 ^ XI.nD)
    (L : Fri.FriLeaves (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)))
    (hL : L = LX XI hn32) (enc : KC ↪ DgJ8) (Op : Type) [Finite Op] [DecidableEq Op]
    (decode : Op → OpenAll DgJ8 (merkleSkels (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc)))
    (pm : (protocol (compiledRoundsK DgJ8 Op (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc))).tree.ExecutionPath)
    {Salt : Type} (zS : FriStmt (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) × Salt)
    (pos : Array ℕ) (vals sels : Array (Array ℕ)) (word0 : ℕ → VF.K3) (alphas pfinal : Array VF.K3) (ch : ℕ → List ℕ)
    (hshift : XI.dShift = 7) (hgen : psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC)) (hk1 : XI.k + 1 ≤ XI.nD) (hsz : pos.size = XI.l)
    (hsels : ∀ i, i < XI.k → sels[4 + i]! = treeSel XI 0 (4 + i) pos)
    (hvals : ∀ a ∈ vals, ∀ x ∈ a, x < NockvmE2E.Exec.p) (hpf : ∀ x ∈ pfinal, canon3 x) (hw0 : ∀ i, canon3 (word0 i))
    (hwalk : ∀ q ∈ pos.toList, walkK XI word0 (faV vals sels) (fbV vals sels) alphas pfinal q = true)
    (hxs : ∀ j, (XsOf (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc Op 0 XI.k (by omega) pm.2.2 j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^ pos[j.1]!)
    (hselF : SelF (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc (QS sels) 0 XI.k (by omega)
      (decode (pathRootsK DgJ8 Op (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc) pm).2))
    (hvalF : ValF (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc (lvS vals sels) 0 XI.k (by omega)
      (decode (pathRootsK DgJ8 Op (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc) pm).2))
    (dY' : List ℕ → DgJ8) (ω0 : Op) (dsm : MDec (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc))
    (hch : ∀ t, t < XI.k + 2 → (encPathD (compiledRoundsK DgJ8 Op (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc))
      (mDecs dY' (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc) dsm ω0) pm).getD t [] = ch (7 + t))
    (hcod0 : ∀ x, cast (foldChallenge_type (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l ⟨0, by omega⟩)
      (xp (a := ⟨0, by have := friLength (k := XI.k); omega⟩)
        (b := (foldChallenge (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l ⟨0, by omega⟩).val)
        (Fin.ext (by simp only [foldChallenge_val])) (dsm.1.decC x)) = toKV (VF.K3.ofLimbs x))
    (hcod : CodOK (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc (fun x => toKV (VF.K3.ofLimbs x)) 0 XI.k (by omega) dsm.2)
    (hPdec : ∀ y, (finPolyOf (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc Op 0 XI.k (by omega) pm.2.2).eval y =
      hornerF (fun j => homV.φ pfinal[j]!) pfinal.size y)
    (hα : ∀ i : Fin (XI.k + 1), toKV (VF.K3.ofLimbs (ch (7 + i.val))) = homV.φ alphas[i.val]!)
    (hW0 : ∀ (j : Fin XI.l) g, Rd XI.nD (pos[j.1]!) 0 g →
      ∃ y : ((smoothDomain XI.nD hn32).subdomain 0).toFinset, y.val = Yp (homV.ψ XI.dShift) (homV.ψ XI.dGen) 0 g ∧
        initialOracle (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) zS.1 y =
          homV.φ (Wf XI word0 (faV vals sels) (fbV vals sels) 0 g)) :
    friLocal (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc Op hdom decode zS pm = true := by
  classical
  have hF := friLinkAt_side XI hn32 d L hL enc Op _ pm zS pos vals sels word0 alphas pfinal ch hshift hgen hk1 hsz hsels hxs hselF hvalF dY' ω0 dsm
    hch hcod0 hcod hPdec hα hW0
  unfold friLocal
  simp only [decide_eq_true_eq]
  refine ⟨coversF_side XI hn32 d hdom L hL enc _ _ pos sels hshift hgen hk1 hsz hsels hxs hselF, _, agree_q0 _ _ _, ?_⟩
  unfold friAccepts'
  refine friAccepts_of_flat (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l hdom (fun _ => rfl) zS _ hF.link hF.hdeg ?_
  intro j
  refine flat_of_walk hk1 _ _ _ _ ?_
  have hj : j.1 < pos.size := by rw [hsz]; exact j.2
  have hmem : pos[j.1]! ∈ pos.toList := by
    rw [getElem!_pos pos j.1 hj]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem hj)
  exact walkK_sound_V XI word0 vals sels alphas pfinal _ hvals hpf hw0 (hwalk _ hmem)

end NockvmE2E.Exec.SideGlue10

#print axioms NockvmE2E.Exec.SideGlue10.coversF_side
#print axioms NockvmE2E.Exec.SideGlue10.friLocal_side
