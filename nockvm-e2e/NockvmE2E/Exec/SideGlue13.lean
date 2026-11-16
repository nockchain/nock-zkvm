/-
 conjunct 5, supplying `friLocal_side` hypotheses from an accepting `verifyFix'`: the flat FRI walk of every query (`hwalk`).

LABELS.  Internal.  Kernel-checked only once the build of `NockvmE2E.Exec.SideGlue13` is complete.
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

namespace NockvmE2E.Exec.SideGlue13
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle NockvmE2E.Exec.SideInst
  NockvmE2E.Merkle.Fri NockvmE2E.Exec.SF NockvmE2E.Exec.Cover NockvmE2E.Exec.Layout NockvmE2E.Exec.DomIdx NockvmE2E.Exec.E2EFri
  NockvmE2E.Exec.SideGlue9 NockvmE2E.FriPort NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Merkle.RapFriQ NockvmE2E.Exec.SideGlue7 NockvmE2E.Exec.SideGlue8 NockvmE2E.Exec.Emb

/-- the side verifier's challenge array -/
def fixChals (vk : VK) (FSf : FSFn) (z ctx : List Nat) (πF : FixProof) : Array (List Nat) :=
  let XX := vk.X
  let kk := XX.k
  let msgs := fixMsgs kk ctx πF.vF πF.roots πF.pfinal
  (Array.range msgs.size).map fun i =>
    if fixNl kk XX.l i == 0 then [] else FSf (z :: (msgs.extract 0 (i + 1)).toList) (fixNl kk XX.l i)

def fixCs (vk : VK) (FSf : FSFn) (z ctx : List Nat) (πF : FixProof) : VF.K3 := VF.K3.ofLimbs (fixChals vk FSf z ctx πF)[1]!

def fixAlphas (vk : VK) (FSf : FSFn) (z ctx : List Nat) (πF : FixProof) : Array VF.K3 :=
  (Array.range (vk.X.k + 1)).map fun w => VF.K3.ofLimbs (fixChals vk FSf z ctx πF)[2 + w]!

def fixSels (vk : VK) (πF : FixProof) : Array (Array Nat) :=
  (Array.range (4 + vk.X.k)).map fun j =>
    if j == 0 then treeSel vk.X vk.cols.size 0 πF.pos else if j < 4 then #[] else treeSel vk.X 0 j πF.pos

def fixPa (vk : VK) (πF : FixProof) : FlatProof :=
  let z5 : Dg5 := [0, 0, 0, 0, 0]
  { roots := #[vk.root, z5, z5, z5] ++ πF.roots, vT := #[], vQ := #[], pfinal := πF.pfinal, pos := πF.pos,
    vals := #[πF.vals[0]!, #[], #[], #[]] ++ πF.vals.extract 1 (1 + vk.X.k),
    sibs := #[πF.sibs[0]!, #[], #[], #[]] ++ πF.sibs.extract 1 (1 + vk.X.k) }

def fixBaseAt (vk : VK) (πF : FixProof) (c idx : Nat) : VF.G :=
  UInt64.ofNat (((fixPa vk πF).vals[0]!)[lb ((fixSels vk πF)[0]!)
    ((idx % 2 ^ (vk.X.nD - 1)) * 2 * vk.cols.size + (idx / 2 ^ (vk.X.nD - 1)) * vk.cols.size + c)]!)

def fixWord0 (vk : VK) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof) : Nat → VF.K3 :=
  deepWord vk.X (openPts vk.X zeta) (fixOps vk.X vk.cols (fixCs vk FSf z ctx πF) πF.vF) (fixBaseAt vk πF)

/-- **the flat FRI walk of every query of an accepting `verifyFix'`** -/
theorem verifyFix'_walk (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof)
    (h : verifyFix' vk Hf FSf z ctx zeta πF = .ok ()) :
    ∀ q ∈ πF.pos.toList, SF.walkK vk.X (fixWord0 vk FSf z ctx zeta πF) (faV (fixPa vk πF).vals (fixSels vk πF))
      (fbV (fixPa vk πF).vals (fixSels vk πF)) (fixAlphas vk FSf z ctx πF) πF.pfinal q = true := by
  unfold verifyFix' at h
  simp only [bind_unit_ok, forM_ok, ckE_ok, List.mem_range] at h
  obtain ⟨_, _, _, _, _, _, _, hw⟩ := h
  intro q hq
  have h1 := hw q hq
  refine (fri_query_iff_walkK vk.X (fixPa vk πF).vals (fixSels vk πF) (fixAlphas vk FSf z ctx πF) πF.pfinal q
    (fixWord0 vk FSf z ctx zeta πF)).mp ?_
  simp only [bind, Except.bind] at h1
  split at h1
  · cases h1
  · rename_i res hs
    refine ⟨res, hs, ?_⟩
    simp only [ckE_ok] at h1
    exact h1

/-- reading the FRI part of an adapted array: `(pre ++ e.extract 1 (1+k))[4+w]! = e[1+w]!` -/
theorem adapt_getElem {α : Type} [Inhabited α] (pre e : Array α) (k w : ℕ) (hpre : pre.size = 4) (hw : w < k) (he : 1 + k ≤ e.size) :
    (pre ++ e.extract 1 (1 + k))[4 + w]! = e[1 + w]! := by
  have h1 : 4 + w < (pre ++ e.extract 1 (1 + k)).size := by simp [hpre]; omega
  rw [getElem!_pos (pre ++ e.extract 1 (1 + k)) (4 + w) h1, getElem!_pos e (1 + w) (by omega)]
  simp [Array.getElem_append, hpre, Array.getElem_extract]

theorem append_getElem {α : Type} [Inhabited α] (pre e : Array α) (w : ℕ) (hpre : pre.size = 4) (hw : w < e.size) :
    (pre ++ e)[4 + w]! = e[w]! := by
  have h1 : 4 + w < (pre ++ e).size := by simp [hpre]; omega
  rw [getElem!_pos (pre ++ e) (4 + w) h1, getElem!_pos e w hw]
  simp [Array.getElem_append, hpre]

/-- every tree check of an accepting `verifyFix'` -/
theorem verifyFix'_trees (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof)
    (h : verifyFix' vk Hf FSf z ctx zeta πF = .ok ()) :
    ∀ j < 4 + vk.X.k, treeCheck vk.X Hf (fixPa vk πF) #[vk.cols.size, 0, 0, 0] (2 ^ (vk.X.nD - 1)) (fixSels vk πF) j = .ok () := by
  unfold verifyFix' at h
  simp only [bind_unit_ok, forM_ok, ckE_ok, List.mem_range] at h
  obtain ⟨_, _, _, _, _, ht, _⟩ := h
  exact ht

/-- the limbs of the adapted values are canonical, the adapted siblings are digests, and the sizes match -/
theorem verifyFix'_limits (vk : VK) (Hf : HFn) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof)
    (h : verifyFix' vk Hf FSf z ctx zeta πF = .ok ()) :
    πF.vals.size = 1 + vk.X.k ∧ πF.sibs.size = 1 + vk.X.k ∧ πF.roots.size = vk.X.k ∧
    (∀ v ∈ πF.vals, ∀ x ∈ v, x < NockvmE2E.Exec.p) ∧ (∀ v ∈ πF.sibs, ∀ d ∈ v, dgOk d = true) ∧ (∀ d ∈ πF.roots, dgOk d = true) := by
  unfold verifyFix' at h
  simp only [bind_unit_ok, ckE_ok] at h
  obtain ⟨h1, h2, _⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Array.all_eq_true_iff_forall_mem] at h1 h2
  refine ⟨h1.1.2, h1.2, h1.1.1.2, fun v hv x hx => ?_, h2.1.1.2, h2.1.1.1.1.2⟩
  have := h2.1.1.1.2 v hv x hx
  simpa [VF.based, PN_eq_p] using this

/-! ### the Merkle part -/

theorem ftree_congr (XI : ExecInst) (π π' : FlatProof) (j : ℕ) (hp : π.pos = π'.pos) (hv : π.vals = π'.vals) (hs : π.sibs = π'.sibs)
    (hr : π.roots[j]! = π'.roots[j]!) : ftree XI π j = ftree XI π' j := by
  unfold ftree selsOf
  rw [hp, hv, hs, hr]

theorem mem_adapt {α : Type} (pre e : Array α) (i j : ℕ) (v : α) (h : v ∈ pre ++ e.extract i j) : v ∈ pre ∨ v ∈ e := by
  rcases Array.mem_append.mp h with h | h
  · exact Or.inl h
  · obtain ⟨k, hk, hkv⟩ := Array.mem_extract_iff_getElem.mp h
    exact Or.inr (hkv ▸ Array.getElem_mem _)

theorem fixPa_vals_mem (vk : VK) (πF : FixProof) (hv : ∀ v ∈ πF.vals, ∀ x ∈ v, x < NockvmE2E.Exec.p) :
    ∀ v ∈ (fixPa vk πF).vals, ∀ x ∈ v, x < NockvmE2E.Exec.p := by
  intro v hv' x hx
  unfold fixPa at hv'
  rcases mem_adapt _ _ _ _ _ hv' with h | h
  · have : v = πF.vals[0]! ∨ v = #[] := by simpa using h
    rcases this with rfl | rfl
    · rcases Nat.lt_or_ge 0 πF.vals.size with h0 | h0
      · exact hv _ (by rw [getElem!_pos πF.vals 0 h0]; exact Array.getElem_mem h0) x hx
      · have h0' : ¬ 0 < πF.vals.size := by omega
        rw [getElem!_neg πF.vals 0 h0'] at hx
        have e : (default : Array ℕ) = #[] := rfl
        rw [e] at hx
        simp at hx
    · simp at hx
  · exact hv v h x hx

section ModelSS
variable [SampleableType KC] [Inhabited KC]


theorem hSM (XI : ExecInst) (hn32 : XI.nD ≤ 32) (l : ℕ)
    [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) l).Challenge j)] :
    merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) l (LX XI hn32)) = (List.finRange XI.k).map (friSkel XI) := by
  unfold SMSg
  rw [NockvmE2E.Merkle.SideMerkle.merkleSkels_bMask_eq]
  rfl

variable (XI : ExecInst) (hn32 : XI.nD ≤ 32) (l : ℕ)
  [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD hn32) (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) l).Challenge j)]

theorem hlenS : 4 + (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) l (LX XI hn32))).length ≤ (skelsSide XI).length := by
  rw [hSM XI hn32 l, skelsSide_length]; simp

theorem hgetS : ∀ w (hw : w < (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) l (LX XI hn32))).length) (hj : 4 + w < (skelsSide XI).length),
    (skelsSide XI).get ⟨4 + w, hj⟩ = (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) l (LX XI hn32))).get ⟨w, hw⟩ := by
  intro w hw hj
  have hw' : w < XI.k := by have := hw; rw [hSM XI hn32 l] at this; simpa using this
  rw [skelsSide_get_fri XI w hw' hj, List.get_of_eq (hSM XI hn32 l) ⟨w, hw⟩]

/-- the tag-shifted node-query model at the side mask `SMSg` itself (not through the `finRange` transport) -/
noncomputable def modelSS (dflt : MAddress (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) l (LX XI hn32)))) :
    MerkleTreeExtractability.NodeQueryModel (NQuery (skelsSide XI)) (MAddress (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) l (LX XI hn32)))) DgJ8 :=
  shiftModel (skelsSide XI) _ (hlenS XI hn32 l) (hgetS XI hn32 l) dflt

/-- **the Merkle part of conjunct 5**: an accepting `verifyFix'` on the table's hash view makes the compiled `merkleCheck` (shifted model, the
FRI-layer opening of the side proof) accept under the table -/
theorem merkle_side_accepts (dflt : MAddress (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) l (LX XI hn32))))
    (vk : VK) (hX : vk.X = XI) (h : NQuery (skelsSide XI) → DgJ8) (FSf : FSFn) (z ctx : List Nat) (zeta : VF.K3) (πF : FixProof)
    (hv : verifyFix' vk (Hof (skelsSide XI) h) FSf z ctx zeta πF = .ok ()) :
    tabEval (spec := NQuery (skelsSide XI) →ₒ DgJ8) (fun q => some (h q))
      (merkleCheck (merkleSkels (SMSg (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) l (LX XI hn32))) (modelSS XI hn32 l dflt) id
        (πF.roots.toList.map dgOf) (openAllS (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) l (LX XI hn32) XI πF)) = some true := by
  subst hX
  obtain ⟨hvs, hss, hrs, hlim, hsb, hrdg⟩ := verifyFix'_limits vk _ FSf z ctx zeta πF hv
  have htrees := verifyFix'_trees vk _ FSf z ctx zeta πF hv
  unfold openAllS modelSS
  refine merkle_embed_side (skelsSide vk.X) _ (hlenS vk.X hn32 l) (hgetS vk.X hn32 l) dflt h (flatTrees vk.X (fixAdaptD vk.X πF))
    (πF.roots.toList.map dgOf) (by simp [hSM vk.X hn32 l, hrs]) ?_
  intro w hj
  have hl : (merkleSkels (SMSg (fun _ : Fin (vk.X.k + 1) => (1 : ℕ+)) l (LX vk.X hn32))).length = vk.X.k := by
    rw [hSM vk.X hn32 l]; simp
  have hwk : w.1 < vk.X.k := by have := w.2; omega
  have hj4 : 4 + w.1 < 4 + vk.X.k := by omega
  rw [ftree_getD vk.X (fixAdaptD vk.X πF) (4 + w.1) hj4]
  have e1 : ftree vk.X (fixAdaptD vk.X πF) (4 + w.1) = ftree vk.X (fixPa vk πF) (4 + w.1) := by
    refine ftree_congr _ _ _ _ rfl rfl rfl ?_
    show (#[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]] ++ πF.roots)[4 + w.1]! =
      (#[vk.root, [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]] ++ πF.roots)[4 + w.1]!
    rw [append_getElem _ _ _ rfl (by omega), append_getElem _ _ _ rfl (by omega)]
  rw [e1]
  have hsel : (fixSels vk πF)[4 + w.1]! = (selsOf vk.X (fixPa vk πF))[4 + w.1]! := by
    rw [selsOf_ge4 vk.X (fixPa vk πF) (4 + w.1) hj4 (by omega)]
    unfold fixSels
    rw [getElem!_pos _ (4 + w.1) (by simp; omega)]
    simp only [Array.getElem_map, Array.getElem_range]
    have h1 : ¬ (4 + w.1 == 0) = true := by simp
    have h2 : ¬ (4 + w.1 < 4) := by omega
    simp only [h1, h2, if_false]
    rfl
  have hsk : (skelsSide vk.X).get ⟨4 + w.1, hj⟩ = skelFlat vk.X (4 + w.1) := by
    rw [skelsSide_get_fri vk.X w.1 hwk hj]
    simpa using friSkel_eq_skelFlat vk.X ⟨w.1, hwk⟩
  have hsibs : ∀ d ∈ (((fixPa vk πF).sibs)[4 + w.1]!).toList, dgOk d = true := by
    have e : ((fixPa vk πF).sibs)[4 + w.1]! = πF.sibs[1 + w.1]! :=
      adapt_getElem _ _ vk.X.k w.1 rfl hwk (by omega)
    rw [e]
    intro d hd
    refine hsb _ ?_ d (Array.mem_toList_iff.mp hd)
    rw [getElem!_pos πF.sibs (1 + w.1) (by omega)]
    exact Array.getElem_mem _
  obtain ⟨T1, _⟩ := tree_embed_side vk.X (fixPa vk πF) (skelsSide vk.X) h #[vk.cols.size, 0, 0, 0] (2 ^ (vk.X.nD - 1)) (fixSels vk πF)
    (skelsSide_length vk.X) ⟨4 + w.1, hj⟩ (by simp) hsk (htrees (4 + w.1) hj4) hsel (fixPa_vals_mem vk πF hlim) hsibs
  rw [get_openAllOf, ftree_getD vk.X (fixPa vk πF) (4 + w.1) hj4] at T1
  refine T1.trans ?_
  show dgOf ((#[vk.root, [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]] ++ πF.roots)[4 + w.1]!) = _
  rw [append_getElem _ _ _ rfl (by omega), getElem!_pos πF.roots w.1 (by omega)]
  simp [List.get_eq_getElem]

end ModelSS

end NockvmE2E.Exec.SideGlue13

#print axioms NockvmE2E.Exec.SideGlue13.verifyFix'_walk
#print axioms NockvmE2E.Exec.SideGlue13.verifyFix'_trees
#print axioms NockvmE2E.Exec.SideGlue13.verifyFix'_limits
#print axioms NockvmE2E.Exec.SideGlue13.hSM
#print axioms NockvmE2E.Exec.SideGlue13.merkle_side_accepts
