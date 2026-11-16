/-
 conjunct 5, step "per-tree Merkle, j >= 4".
`tree_embed_side`: port of `E2EEmbed.tree_embed` for a tree `j >= 4` of a flat proof `πa` (the `fixAdapt` layout), with the acceptance
fact stated as `treeCheck .. = .ok ` with arbitrary `W half0 sels` (so it applies to the `verifyFix'` check) and the skeleton fact
only for `j >= 4`.  `blockLayout_size`, `selsOf_ge4`.  `hglue_J8` is NOT written.

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue7` is complete.
-/
import NockvmE2E.Exec.SideGlue6

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.Exec.SideGlue7
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.SM NockvmE2E.Exec.Cover NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Exec.Emb

/-- the block layout has four blocks -/
theorem blockLayout_size (XI : ExecInst) : (blockLayout XI).1.size = 4 := by
  unfold blockLayout
  have : ∀ (l : List ℕ) (st : Array ℕ × Array ℕ), st.1.size = 4 →
      (l.foldl (fun (st : Array ℕ × Array ℕ) c =>
        let b := XI.blockOf[c]!
        if b < 4 then (st.1.modify b (· + 1), st.2.set! c st.1[b]!) else st) st).1.size = 4 := by
    intro l
    induction l with
    | nil => intro st h; exact h
    | cons c l ih =>
      intro st h
      apply ih
      simp only []
      split <;> simp [h]
  exact this _ _ (by simp)

/-- for a tree `j >= 4` the selection is read with a zero block width -/
theorem selsOf_ge4 (XI : ExecInst) (π : FlatProof) (j : ℕ) (hj : j < 4 + XI.k) (h4 : 4 ≤ j) :
    (selsOf XI π)[j]! = treeSel XI 0 j π.pos := by
  unfold selsOf
  rw [getElem!_pos _ j (by simpa using hj)]
  simp only [Array.getElem_map, Array.getElem_range]
  have : (blockLayout XI).1.getD j 0 = 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [blockLayout_size]; exact h4)]
    rfl
  rw [this]

/-- **`tree_embed_side`**: port of `tree_embed` for a tree `j >= 4`: if the verifier's `treeCheck` of tree `j` passed (with the given
width/half/selection arrays, the selection of tree `j` being the one `ftree` reads), then the embedded opening reconstructs `dgOf roots[j]`
under the node hash. -/
theorem tree_embed_side (XI : ExecInst) (πa : FlatProof) (skels : List Skeleton)
    (h : NQuery skels → DgJ8) (W : Array ℕ) (half0 : ℕ) (sels : Array (Array ℕ))
    (hlen : skels.length = 4 + XI.k)
    (j : Fin skels.length) (hj4 : 4 ≤ j.1)
    (hsk : skels.get j = skelFlat XI j.1)
    (htc : treeCheck XI (Hof skels h) πa W half0 sels j.1 = .ok ())
    (hsel : sels[j.1]! = (selsOf XI πa)[j.1]!)
    (hlim : ∀ v ∈ πa.vals, ∀ x ∈ v, x < NockvmE2E.Exec.p)
    (hsb : ∀ d ∈ (πa.sibs[j.1]!).toList, dgOk d = true) :
    rootUnder (Query := NQuery skels) h (idModel skels) (fun a => (⟨j, a⟩ : MAddress skels))
        (OpenAll.get skels (openAllOf skels (flatTrees XI πa)) j) = dgOf πa.roots[j.1]! ∧
      (OpenAll.get skels (openAllOf skels (flatTrees XI πa)) j).selector =
          selOf (ftree XI πa j.1).isSel (skels.get j) 0 := by
  have hjk : j.1 < 4 + XI.k := hlen ▸ j.2
  rw [get_openAllOf, ftree_getD XI πa j.1 hjk]
  have hne : ¬ (j.1 < 4 ∧ W[j.1]! = 0) := by omega
  obtain ⟨_, hgo⟩ := treeCheck_root XI (Hof skels h) πa W half0 sels j.1 htc hne
  rw [hsel] at hgo
  have hsp : WfSpec (friSpec (2 ^ (XI.nD - (j.1 - 3)))) ∧ 1 ≤ (friSpec (2 ^ (XI.nD - (j.1 - 3)))).total :=
    ⟨wf_friSpec _, by simp only [friSpec]; exact Nat.two_pow_pos _⟩
  have hn4 : ¬ j.1 < 4 := by omega
  have hcl : ∀ r, dgOk [(πa.vals[j.1]!)[3 * r]!, (πa.vals[j.1]!)[3 * r + 1]!, (πa.vals[j.1]!)[3 * r + 2]!, 0, 0] = true := by
    intro r
    have hz : NockvmE2E.Exec.VF.based 0 = true := by
      simp [NockvmE2E.Exec.VF.based, PN_eq]; exact (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
    simp [dgOk, NockvmE2E.Exec.VF.based, PN_eq, arr_get_lt (a := πa.vals) hlim, hz]
    exact (Fact.out : Nat.Prime NockvmE2E.Exec.p).pos
  have hsk' : skels.get j = skelOf (friSpec (2 ^ (XI.nD - (j.1 - 3)))) (friSpec (2 ^ (XI.nD - (j.1 - 3)))).total
      (friSpec (2 ^ (XI.nD - (j.1 - 3)))).total := by
    rw [hsk]; unfold skelFlat; simp [hn4]
  have hpw : ((selsOf XI πa)[j.1]!).toList.Pairwise (· < ·) := selsOf_pw XI πa j.1 hjk
  have hcl' : ∀ r, dgOk (if j.1 < 4 then [(πa.vals[j.1]!)[r]!, 0, 0, 0, 0]
      else [(πa.vals[j.1]!)[3 * r]!, (πa.vals[j.1]!)[3 * r + 1]!, (πa.vals[j.1]!)[3 * r + 2]!, 0, 0]) = true := by
    intro r; simp only [hn4, ite_false]; exact hcl r
  obtain ⟨h1, h2⟩ := embed_tree skels h j _ hsp.1 hsk' hsp.2 _ hpw _ _ _ hcl' hsb
    (by simpa [hn4] using hgo)
  exact ⟨h2, h1⟩

end NockvmE2E.Exec.SideGlue7

#print axioms NockvmE2E.Exec.SideGlue7.blockLayout_size
#print axioms NockvmE2E.Exec.SideGlue7.selsOf_ge4
#print axioms NockvmE2E.Exec.SideGlue7.tree_embed_side
