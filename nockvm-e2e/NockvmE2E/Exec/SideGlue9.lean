/-
 conjunct 5, FRI link, step 1: `hW_inst_side`, the FRI words `w >= 1` read link of `E2ELinksFri.hW_inst`, with the flat
proof replaced by explicit data (`pos`, `vals`, `sels`) and the `FlatOk`-derived facts replaced by hypotheses.

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue9` is complete.
-/
import NockvmE2E.Exec.SideGlue8
import NockvmE2E.Exec.E2ELinksFri

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue9
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx NockvmE2E.Exec.E2EFri

/-- FRI word `i`'s leaf `t` is in the selection `sels[4+i]` -/
def QS (sels : Array (Array ℕ)) (i t : ℕ) : Prop := t ∈ (sels[4 + i]!).toList

/-- the flat value (in `KC`) of leaf `t` of FRI tree `4 + i` -/
noncomputable def lvS (vals sels : Array (Array ℕ)) (i t : ℕ) : KC :=
  homV.φ (friAtV vals (4 + i) (lb sels[4 + i]! t))

theorem hW_inst_side (XI : ExecInst) (hn32 : XI.nD ≤ 32) (pos : Array ℕ) (vals sels : Array (Array ℕ)) (word0 : ℕ → VF.K3)
    (hshift : XI.dShift = 7) (hgen : psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC)) (hk1 : XI.k + 1 ≤ XI.nD) (hsz : pos.size = XI.l)
    (hsels : ∀ i, i < XI.k → sels[4 + i]! = treeSel XI 0 (4 + i) pos)
    (j : Fin XI.l) (i : Fin XI.k) (g : ℕ) (hg : Rd XI.nD (pos[j.1]!) (i.val + 1) g) :
    ∃ y : wordDom (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) i.val,
      y.val = Yp (psiV XI.dShift) (psiV XI.dGen) (i.val + 1) g ∧
      QS sels i.val (leafNum (((LX XI hn32).idx i).symm y)) ∧
      lvS vals sels i.val (leafNum (((LX XI hn32).idx i).symm y)) =
        homV.φ (Wf XI word0 (faV vals sels) (fbV vals sels) (i.val + 1) g) := by
  have hm := msum1 XI.k i.val i.2
  have hi2 : i.val + 2 ≤ XI.nD := by omega
  obtain ⟨hg1, hg2⟩ := hg
  let u : Fin (2 ^ (XI.nD - ∑ j ∈ finRangeTo (XI.k + 1) (i.val + 1), (((fun _ : Fin (XI.k + 1) => (1 : ℕ+)) j : ℕ+) : ℕ))) :=
    ⟨g, by rw [hm]; exact hg1⟩
  refine ⟨((smoothDomain XI.nD hn32).subdomain _).equivToFinset u, ?_, ?_⟩
  · show _ = Yp (psiV XI.dShift) (psiV XI.dGen) _ _
    rw [psiV_shift XI hshift, hgen]
    exact pt_val XI.nD hn32 _ _ (by omega) hm u
  · have hleaf := LX_leafNum XI hn32 i.val i.2 hi2 (((smoothDomain XI.nD hn32).subdomain _).equivToFinset u)
    have hu := congrArg Fin.val (Equiv.symm_apply_apply (((smoothDomain XI.nD hn32).subdomain _).equivToFinset) u)
    have hB : (((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i.val + 1), (1 : ℕ))).equivToFinset.symm
      (((smoothDomain XI.nD hn32).subdomain _).equivToFinset u)).val = g := hu
    have hC : (((smoothDomain XI.nD hn32).subdomain (∑ j ∈ finRangeTo (XI.k + 1) (i.val + 1), ((1 : ℕ+) : ℕ))).equivToFinset.symm
      (((smoothDomain XI.nD hn32).subdomain _).equivToFinset u)).val = g := hu
    have hleaf2 : leafNum (((LX XI hn32).idx i).symm (((smoothDomain XI.nD hn32).subdomain _).equivToFinset u)) =
        2 * (g % 2 ^ (XI.nD - i.val - 2)) + g / 2 ^ (XI.nD - i.val - 2) :=
      hleaf.trans (congrArg₂ (fun a b : ℕ => 2 * (a % 2 ^ (XI.nD - i.val - 2)) + b / 2 ^ (XI.nD - i.val - 2)) hB hC)
    clear hleaf hu hB hC
    have hpos : 0 < 2 ^ (XI.nD - i.val - 2) := Nat.two_pow_pos _
    have hdiv : g / 2 ^ (XI.nD - i.val - 2) < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [← pow_succ, show XI.nD - i.val - 2 + 1 = XI.nD - (i.val + 1) by omega]
      exact hg1
    have hg2' : g % 2 ^ (XI.nD - i.val - 2) = pos[j.1]! % 2 ^ (XI.nD - i.val - 2) := by
      rw [show XI.nD - i.val - 2 = XI.nD - (i.val + 1) - 1 by omega]; exact hg2
    have hmem : pos[j.1]! ∈ pos.toList := by
      have : j.1 < pos.size := by rw [hsz]; exact j.2
      rw [getElem!_pos pos j.1 this]; simp
    refine ⟨?_, ?_⟩
    · show _ ∈ (sels[4 + i.val]!).toList
      rw [hleaf2, hsels i.val i.2]
      have := mem_treeSel_fri XI (4 + i.val) pos (by omega) (pos[j.1]!) hmem _ hdiv
      rw [show XI.nD - (4 + i.val - 3) - 1 = XI.nD - i.val - 2 by omega, ← hg2'] at this
      exact this
    · unfold lvS
      rw [hleaf2]
      unfold Wf
      simp only [Nat.add_one_ne_zero, ite_false]
      have h34 : 3 + (i.val + 1) = 4 + i.val := by omega
      by_cases hlt : g < 2 ^ (XI.nD - i.val - 2)
      · rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, show XI.nD - (i.val + 1) - 1 = XI.nD - i.val - 2 by omega, ]
        simp only [hlt, ite_true, faV, h34, Nat.add_zero]
      · have hd1 : g / 2 ^ (XI.nD - i.val - 2) = 1 := Nat.div_eq_of_lt_le (by omega) (by
          have e2 : 2 ^ (XI.nD - (i.val + 1)) = 2 * 2 ^ (XI.nD - i.val - 2) := by
            rw [← pow_succ']; congr 1; omega
          omega)
        have hm1 : g % 2 ^ (XI.nD - i.val - 2) = g - 2 ^ (XI.nD - i.val - 2) := by
          have := Nat.mod_add_div g (2 ^ (XI.nD - i.val - 2)); rw [hd1] at this; omega
        rw [hd1, hm1, show XI.nD - (i.val + 1) - 1 = XI.nD - i.val - 2 by omega, ]
        simp only [hlt, ite_false, fbV, h34]

section LinkSide
open NockvmE2E.FriPort NockvmE2E.Merkle.Fri NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Merkle.RapFriQ

/-- **`friLinkAt_side`**: `FriLinkAt` for the base path `q0Of (friMask ..) os pm` of a compiled FRI-mask path `pm`, from the explicit flat data.
This is `E2ELinksFri.friLinkAt_of_flat` with `FlatOk` replaced by the hypotheses `hshift hgen hk1 hsz hsels hwalk` and the data
`pos vals sels word0 alphas pfinal ch` explicit.  The words `w >= 1` read link is `hW_inst_side`; word 0 is `hW0`. -/
theorem friLinkAt_side (XI : ExecInst) (hn32 : XI.nD ≤ 32) [SampleableType KC] [Inhabited KC]
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) XI.l).Challenge j)]
    (d : ℕ+) (L : Fri.FriLeaves (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)))
    (hL : L = LX XI hn32) (enc : KC ↪ DgJ8) (Op : Type) [Finite Op] [DecidableEq Op]
    (os : OpenAll DgJ8 (merkleSkels (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc)))
    (pm : (protocol (compiledRoundsK DgJ8 Op (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc))).tree.ExecutionPath)
    {Salt : Type} (zS : FriStmt (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) × Salt)
    (pos : Array ℕ) (vals sels : Array (Array ℕ)) (word0 : ℕ → VF.K3) (alphas pfinal : Array VF.K3) (ch : ℕ → List ℕ)
    (hshift : XI.dShift = 7) (hgen : psiV XI.dGen = ((zeta XI.nD : KCˣ) : KC)) (hk1 : XI.k + 1 ≤ XI.nD) (hsz : pos.size = XI.l)
    (hsels : ∀ i, i < XI.k → sels[4 + i]! = treeSel XI 0 (4 + i) pos)
    (hxs : ∀ j, (XsOf (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc Op 0 XI.k (by omega) pm.2.2 j).val =
      homV.ψ XI.dShift * homV.ψ XI.dGen ^ pos[j.1]!)
    (hselF : SelF (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc (QS sels) 0 XI.k (by omega) os)
    (hvalF : ValF (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc (lvS vals sels) 0 XI.k (by omega) os)
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
    FriLinkAt (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l zS
      (toFriPath (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc
        (q0Of (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc) os pm))
      (homV.ψ XI.dShift) (homV.ψ XI.dGen) (fun j => pos[j.1]!)
      (fun w i => homV.φ (SF.Wf XI word0 (faV vals sels) (fbV vals sels) w i))
      (SF.hornerF (fun j => homV.φ pfinal[j]!) pfinal.size) (fun i => homV.φ alphas[i]!) := by
  have hQT := fri_QT (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc Op dY' ω0 ch (fun x => toKV (VF.K3.ofLimbs x))
    (lvS vals sels) (QS sels) dsm os pm (q0Of (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc) os pm)
    (agree_q0 (friMask (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc) os pm)
    hselF hvalF hcod0 hcod hch
  have hγ : homV.ψ XI.dGen ^ 2 ^ (XI.nD - 1) = -1 := by
    show psiV XI.dGen ^ _ = _
    rw [hgen]
    exact neg_one_of_order _ _ (by omega) (orderOf_zeta hn32)
  refine friLinkAt_of_QT (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l _ _ _ _ _ _ _ hQT _ _ _ _ _ _ hγ hxs ?_ hPdec
    (finPoly_deg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) d XI.l L DgJ8 enc Op XI.k 0 (by omega) _) ?_ hW0
  · intro i
    exact hα i
  · intro j i g hg
    subst hL
    exact hW_inst_side XI hn32 pos vals sels word0 hshift hgen hk1 hsz hsels j i g hg

end LinkSide

end NockvmE2E.Exec.SideGlue9

#print axioms NockvmE2E.Exec.SideGlue9.hW_inst_side
#print axioms NockvmE2E.Exec.SideGlue9.friLinkAt_side
