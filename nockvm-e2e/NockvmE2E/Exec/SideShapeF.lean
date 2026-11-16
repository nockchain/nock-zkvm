/-
  NockvmE2E/Exec/SideShapeF.lean

  Additive family-generic copies of the side-chain shape lemmas: the binder `hsh : J8Shape.j8ShapeOk X = true` becomes
  `{F : Fam} (hsh : shapeOkF F X = true)`.  Proof bodies are those of the J-8 originals; only the shape reads change
  (`J8Shape.paramsOk_of_shape` -> `paramsOk_of_shapeF`, `hN_of_shape` -> `hN_of_shapeF`, `hpd_of_shape` -> `hpd_of_shapeF`).
    * `natDegree_fj_le_F`         (VKSpec.natDegree_fj_le_J8)
    * `vF_correct_of_languageF`   (SideStmt.vF_correct_of_language)
    * `fix_not_languageF`         (HFixFri.fix_not_language)
    * `hFix_fri'R_F`              (SideOnlineRFri.hFix_fri'R)
    * `vk_total_le_F`             (VKBindBridge.vk_total_le)
  Probe: `hFix_fri'R_F (F := famJ8)` takes `hsh : j8ShapeOk` through `j8ShapeOk_eq`.
-/
import NockvmE2E.Exec.SideOnlineRFri
import NockvmE2E.Exec.ShapeF

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NockvmE2E.Exec.V
open NockvmE2E.Exec NockvmE2E.Exec.VF NockvmE2E.Exec.VL NockvmE2E.Exec.VKBindBridge NockvmE2E.Exec.SideOnlineR
open NockvmE2E.Exec.ShapeF

/-- degree bound over any family shape -/
theorem natDegree_fj_le_F {F : Fam} {XI : ExecInst} (hsh : shapeOkF F XI = true) :
    ∀ col ∈ fixCols XI, (fj XI col).natDegree ≤ 2 ^ (XI.k + 1) := by
  intro col hcol
  rw [← hN_of_shapeF hsh]
  exact natDegree_fj_le XI (hpd_of_shapeF hsh) col (fixCols_pre_lt XI col hcol)

section Assembly
open OracleComp OracleSpec ProtocolSpec ENNReal
open BinaryTree
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain NockvmE2E.FriPort NockvmE2E.FriPort.Batched NockvmE2E.Merkle.Fri
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open NockvmE2E.Merkle NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good NockvmE2E.Merkle.SoundnessWorld
  NockvmE2E.Merkle.SoundnessCoupling NockvmE2E.Merkle.BadBound
open MerkleTreeMultiExtractability
open NockvmE2E.Exec.Emb NockvmE2E.Exec.E2E NockvmE2E.Exec.E2EOnlineP NockvmE2E.Merkle.SideMerkle NockvmE2E.Deep NockvmE2E.Exec.Inst
open Polynomial
open scoped NNReal ENNReal

section Correct
variable {k : ℕ}

theorem vF_correct_of_languageF {m : ℕ} (C : SideCfg m) (hg : setupGates C.XI = true) {F : Fam}
    (hsh : shapeOkF F C.XI = true)
    (hn : C.XI.nD ≤ 32) {s : Fin (k + 1) → ℕ+} {d : ℕ+} {δ : ℝ≥0}
    (hfb : 2 ^ (C.XI.k + 1) ≤ friBound s d) (hN : friBound s d + 1 ≤ 2 ^ C.XI.nD)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb (smoothDomain C.XI.nD hn)) (friBound s d + 1) : Set (Fin (2 ^ C.XI.nD) → KC)))
    (hcol : ∀ j, (C.opIdx j).1 < (fixCols C.XI).size)
    (st : SideStmt) (hcanon : ∀ j, canon3 (C.ptK st.ctx j))
    (hz : ∀ j i, smoothDomain C.XI.nD hn i ≠ C.pt st j)
    (hmem : stmtOf C hn st ∈ (BatchedFri.Spec.BatchingRound.inputRelation (ω := smoothDomain C.XI.nD hn) s d m δ).language) :
    ∀ j, C.val st j = toKV (fixTrue C.XI (C.col j) (C.ptK st.ctx j)) := by
  obtain ⟨sw, hsw, hsw1⟩ := hmem
  have L : DomLink C.XI hn := J8Shape.domLink_of_paramsOk C.XI (paramsOk_of_shapeF hsh) hn
  obtain ⟨hS, hpre⟩ := canon_of_gates hg
  have hwords : ∀ j i, sw.1.2 j ((smoothDomain C.XI.nD hn).equivToFinset i) =
      NockvmE2E.Deep.deepWord (⇑(smoothDomain C.XI.nD hn)) (honestWord C.XI (C.col j)) (C.pt st j) (C.val st j) i := by
    intro j i
    rw [hsw1]; exact stmtOf_words C hn st j i
  obtain ⟨P, ⟨S, hS', hA⟩, hdeg, hop, huniq⟩ := deep_of_inputRelation (m := m) (s := s) (d := d)
    (ω := smoothDomain C.XI.nD hn) (id : Fin (m + 1) → Fin (m + 1)) (C.pt st) (C.val st)
    (fun j => honestWord C.XI (C.col j)) Function.surjective_id hz hN hδ sw hsw hwords
  intro j
  have hmemc : C.col j ∈ fixCols C.XI := by
    unfold SideCfg.col
    rw [getElem!_pos (fixCols C.XI) (C.opIdx j).1 (hcol j)]
    exact Array.getElem_mem _
  have hdegf : ((fj C.XI (C.col j)).map (algebraMap (ZMod NockvmE2E.Exec.p) KC)).natDegree < friBound s d + 1 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap (ZMod NockvmE2E.Exec.p) KC).injective]
    exact Nat.lt_succ_of_le ((natDegree_fj_le_F hsh _ hmemc).trans hfb)
  have hPe := huniq j _ Finset.univ hdegf (dense_univ δ)
    (fun i _ => honestWord_eval C.XI hg hn L (C.col j) i)
  rw [show P j = P (id j) from rfl] at hPe; rw [← hop j, ← hPe, fixTrue_eq_fj C.XI hS hpre (C.col j) _ (hcanon j)]
  rfl

end Correct

section Main
variable {m : ℕ} {k : ℕ} {D : Type} {R : D → Type} [DecidableEq D] [instR : SampleableType (∀ d, R d)] {O : Type}

theorem fix_not_languageF (C : SideCfg m) (hn : C.XI.nD ≤ 32)
    (hg : setupGates C.XI = true) {F : Fam} (hsh : shapeOkF F C.XI = true)
    {s : Fin (k + 1) → ℕ+} {dd : ℕ+} {δ : ℝ≥0}
    (hfb : 2 ^ (C.XI.k + 1) ≤ friBound s dd) (hN : friBound s dd + 1 ≤ 2 ^ C.XI.nD)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb (smoothDomain C.XI.nD hn)) (friBound s dd + 1) : Set (Fin (2 ^ C.XI.nD) → NockvmE2E.Exec.KC)))
    (hcol : ∀ j, (C.opIdx j).1 < (fixCols C.XI).size)
    (hC1 : ∀ j o, j < (fixCols C.XI).size → o < fixLen C.XI (fixCols C.XI)[j]! → ∃ i, C.opIdx i = (j, o))
    (hC2 : ∀ π ζ i, C.ptK (fixCtx π ζ) i = (openPts C.XI ζ)[(C.opIdx i).2]!)
    (π : FlatProof) (ζ : VF.K3) (πF : FixProof) (st : SideStmt) (hst : st = ⟨[], fixCtx π ζ, πF.vF⟩)
    (hcanon : ∀ j, canon3 (C.ptK st.ctx j))
    (hz : ∀ j i, smoothDomain C.XI.nD hn i ≠ C.pt st j)
    (hcanV : ∀ j o', j < (fixCols C.XI).size → o' < fixLen C.XI (fixCols C.XI)[j]! →
      canon3 ((πF.vF[j]!)[o']!) ∧ canon3 (fixTrue C.XI (fixCols C.XI)[j]! ((openPts C.XI ζ)[o']!)))
    (j0 o0 : ℕ) (hj0 : j0 < (fixCols C.XI).size) (ho0 : o0 < fixLen C.XI (fixCols C.XI)[j0]!)
    (hne : (πF.vF[j0]!)[o0]! ≠ fixTrue C.XI (fixCols C.XI)[j0]! ((openPts C.XI ζ)[o0]!)) :
    stmtOf C hn st ∉ (inputRelation (ω := smoothDomain C.XI.nD hn) s dd m δ).language := by
  intro hmem
  have hv := vF_correct_of_languageF C hg hsh hn hfb hN hδ hcol st hcanon hz hmem
  obtain ⟨i, hi⟩ := hC1 j0 o0 hj0 ho0
  have h1 := hv i
  have e1 : C.val st i = toKV ((πF.vF[j0]!)[o0]!) := by
    unfold SideCfg.val; rw [hi, hst]
  have e2 : C.col i = (fixCols C.XI)[j0]! := by unfold SideCfg.col; rw [hi]
  have e3 : C.ptK st.ctx i = (openPts C.XI ζ)[o0]! := by rw [hst, hC2, hi]
  rw [e1, e2, e3] at h1
  obtain ⟨c1, c2⟩ := hcanV j0 o0 hj0 ho0
  exact hne (toKV_inj _ _ c1 c2 h1)

local notation "KCf" => NockvmE2E.Exec.KC

set_option maxHeartbeats 4000000 in
/-- **`hFix_fri'R_F`**: `hFix_fri'R` over any chip family shape (`shapeOkF F`); statement otherwise unchanged. -/
theorem hFix_fri'R_F (C : SideCfg m) (hn : C.XI.nD ≤ 32)
    (hg : setupGates C.XI = true) {F : Fam} (hsh : shapeOkF F C.XI = true)
    (s : Fin (k + 1) → ℕ+) (dd : ℕ+) (l : ℕ)
    [∀ j, SampleableType ((pSpec k (ω := smoothDomain C.XI.nD hn) s l).Challenge j)]
    {S : Type} [Fintype S] [Nonempty S] [SampleableType S] [SampleableType KCf]
    (G : CoreDefinitions.Generator S (Fin (m + 1)) KCf)
    (L : FriLeaves (ω := smoothDomain C.XI.nD hn) s) (Dg : Type) [Finite Dg] [DecidableEq Dg] [SampleableType Dg] [Inhabited Dg]
    (enc : KCf ↪ Dg) (hk : 1 ≤ k)
    (hdom : 2 ^ (∑ j, (s j).val) * dd.val ≤ 2 ^ C.XI.nD) (θ : ℝ) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code ((smoothDomain C.XI.nD hn : SmoothCosetFftDomain C.XI.nD KCf) : Fin (2 ^ C.XI.nD) ↪ KCf)
        (2 ^ (∑ i, (s i).1) * dd)).carrier δ δ ≤ ε)
    (hfb : 2 ^ (C.XI.k + 1) ≤ friBound s dd) (hN : friBound s dd + 1 ≤ 2 ^ C.XI.nD)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb (smoothDomain C.XI.nD hn)) (friBound s dd + 1) : Set (Fin (2 ^ C.XI.nD) → KCf)))
    (hcol : ∀ j, (C.opIdx j).1 < (fixCols C.XI).size)
    {Op : Type} [Finite Op] [DecidableEq Op] {Query : Type} [DecidableEq Query] [Finite Query]
    {Stmt Salt : Type} [DecidableEq Stmt] [DecidableEq Salt] [Finite Stmt] [Finite Salt]
    [instRF : SampleableType (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d')]
    (decS : Stmt → SideStmt)
    (decode : Op → OpenAll Dg (merkleSkels (bMask (S := S) s dd l L Dg enc)))
    (model : MerkleTreeExtractability.NodeQueryModel Query (MAddress (merkleSkels (bMask (S := S) s dd l L Dg enc))) Dg)
    (guards : GuardSchedule (Stmt × Salt) PUnit (compiledRoundsK Dg Op (bMask (S := S) s dd l L Dg enc)))
    (localAccepts : Stmt × Salt →
      (protocol (compiledRoundsK Dg Op (bMask (S := S) s dd l L Dg enc))).tree.ExecutionPath → Bool)
    (hlocal : QueryOnly (bMask (S := S) s dd l L Dg enc) decode
      (bAccepts s dd l m G L Dg enc hdom (fun st => stmtOf C hn (decS st)) (Salt := Salt)) localAccepts)
    (HfOf : (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') → HFn)
    (FSOf : (∀ d, R d) → FSFn)
    (FSfOf : (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') → FSFn)
    (vkOf : (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') → VK)
    (hvk : ∀ gF, vkOf gF = vkSpec C.XI (HfOf gF))
    (zO : O → List Nat) (πO : O → FlatProof) (πFO : O → FixProof)
    (sideOf : (∀ d, R d) → O → Stmt × Salt × PublicMessages (compiledRoundsK Dg Op (bMask (S := S) s dd l L Dg enc)))
    (Aon : OracleComp ((unifSpec + OracleSpec.ofFn R) +
      OracleSpec.ofFn (succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc))) (Option O))
    (Q_FS Q_H V P T : ℕ)
    (hFS : ∀ g, FsBound (Q := Query)
      (∅ : (ofFn (SoundnessWorld.KC Dg Op Stmt Salt (bMask (S := S) s dd l L Dg enc))).QueryCache) Q_FS
      (verifiedFS guards (sideAdv sideOf Aon g)))
    (hH : ∀ g, IsQueryBoundP (sideAdv sideOf Aon g)
      (@isHashQuery Query Dg _ (SoundnessWorld.KC Dg Op Stmt Salt (bMask (S := S) s dd l L Dg enc))) Q_H)
    (hterm : ∀ (roots : List Dg) (h : roots.length = (merkleSkels (bMask (S := S) s dd l L Dg enc)).length) (op : Op)
      (logs : Fin (merkleSkels (bMask (S := S) s dd l L Dg enc)).length → MerkleTreeExtractor.QueryLog Query Dg),
      claimsQueryCount (mkClaims (merkleSkels (bMask (S := S) s dd l L Dg enc)) roots h (decode op) logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (bMask (S := S) s dd l L Dg enc))).nodeBudget tag ≤ P)
    (hC1 : ∀ j o, j < (fixCols C.XI).size → o < fixLen C.XI (fixCols C.XI)[j]! → ∃ i, C.opIdx i = (j, o))
    (hC2 : ∀ π ζ i, C.ptK (fixCtx π ζ) i = (openPts C.XI ζ)[(C.opIdx i).2]!)
    (hglue : ∀ g gF o,
      FixFailR C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) →
        decS (sideOf g o).1 = ⟨[], fixCtx (πO o) (zetaOf C.XI (FSOf g) (zO o) (πO o)), (πFO o).vF⟩ ∧
        (∀ j, canon3 (C.ptK (decS (sideOf g o).1).ctx j)) ∧
        (∀ j i, smoothDomain C.XI.nD hn i ≠ C.pt (decS (sideOf g o).1) j) ∧
        (∀ j o', j < (fixCols C.XI).size → o' < fixLen C.XI (fixCols C.XI)[j]! →
          canon3 ((πFO o).vF[j]!)[o']! ∧
          canon3 (fixTrue C.XI (fixCols C.XI)[j]! ((openPts C.XI (zetaOf C.XI (FSOf g) (zO o) (πO o)))[o']!))) ∧
        (¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o) →
          ∃ p, tabEval (tabK gF) (succinctVerifyK guards
            (merkleCheck (merkleSkels (bMask (S := S) s dd l L Dg enc)) model decode) localAccepts
            ((sideOf g o).1, (sideOf g o).2.1) (sideOf g o).2.2) = some (some p)))
    (hcoll : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
        match o with
        | none => False
        | some o => VKcollC C.XI (vkOf gF) (HfOf gF) (πFO o)] ≤ ((Q_H + V + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card Dg : ℝ≥0∞))) :
    Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some o => FixFailR C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] ≤
    bfriErr (ω := smoothDomain C.XI.nD hn) s dd l θ δ ε Q_FS +
      (multiCheckpointROMErrorNumerator ((k * (Q_FS + 1)) * P) (k * (Q_FS + 1)) V Q_H : ℝ≥0∞) * (Nat.card Dg : ℝ≥0∞)⁻¹ +
      ((Q_H + V + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card Dg : ℝ≥0∞)) := by
  classical
  have hX : ∀ gF, (vkOf gF).cols = fixCols C.XI := fun gF => by rw [hvk]; rfl
  let stm : Stmt → BStmt (smoothDomain C.XI.nD hn) m := fun st => stmtOf C hn (decS st)
  have hpt : ∀ g gF o,
      (FixFailR C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)) →
      (∃ p, tabEval (tabK gF) (succinctVerifyK guards
            (merkleCheck (merkleSkels (bMask (S := S) s dd l L Dg enc)) model decode) localAccepts
            ((sideOf g o).1, (sideOf g o).2.1) (sideOf g o).2.2) = some (some p)) ∧
      (sideOf g o).1 ∉ {st | stm st ∈ (inputRelation (ω := smoothDomain C.XI.nD hn) s dd m δ).language} := by
    intro g gF o ⟨hFR, hnc⟩
    obtain ⟨hstm, hcan, hz, hcanV, hacc⟩ := hglue g gF o hFR
    refine ⟨hacc hnc, ?_⟩
    obtain ⟨_, j0, o0, hj0, ho0, hne⟩ := hFR.1
    have hc := (hX gF)
    rw [hc] at hj0 ho0 hne
    exact fix_not_languageF C hn hg hsh hfb hN hδ hcol hC1 hC2 (πO o) (zetaOf C.XI (FSOf g) (zO o) (πO o)) (πFO o)
      (decS (sideOf g o).1) hstm hcan hz hcanV j0 o0 hj0 ho0 hne
  have hper : ∀ g : (∀ d, R d),
      Pr{let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
        match o with
        | none => False
        | some o => FixFailR C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)] ≤
      bfriErr (ω := smoothDomain C.XI.nD hn) s dd l θ δ ε Q_FS +
        (multiCheckpointROMErrorNumerator ((k * (Q_FS + 1)) * P) (k * (Q_FS + 1)) V Q_H : ℝ≥0∞) * (Nat.card Dg : ℝ≥0∞)⁻¹ := by
    intro g
    have hre : ∀ gF, simulateQ (withTable2 g gF) Aon = simulateQ (withTable gF) (simulateQ (mainImpl g) Aon) :=
      fun gF => (sim_main g gF Aon).symm
    simp only [hre]
    let cont : Option O → OracleComp (SuccinctSpecK Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc))
        (Option ((Stmt × Salt) × (protocol (compiledRoundsK Dg Op (bMask (S := S) s dd l L Dg enc))).tree.ExecutionPath × PUnit)) :=
      fun o => match o with
        | none => pure none
        | some o => do
            let path ← succinctVerifyK guards (merkleCheck (merkleSkels (bMask (S := S) s dd l L Dg enc)) model decode) localAccepts
              ((sideOf g o).1, (sideOf g o).2.1) (sideOf g o).2.2
            pure (path.map fun p => (((sideOf g o).1, (sideOf g o).2.1), p, PUnit.unit))
    have hshape : succinctAcceptedExecutionK guards (merkleCheck (merkleSkels (bMask (S := S) s dd l L Dg enc)) model decode) localAccepts
        (sideAdv sideOf Aon g) = simulateQ (mainImpl g) Aon >>= cont := by
      simp only [succinctAcceptedExecutionK, sideAdv, map_eq_bind_pure_comp, bind_assoc, bind_pure_comp]
      refine bind_congr fun o => ?_
      cases o <;> rfl
    refine le_trans (pr_flat_le_audited (simulateQ (mainImpl g) Aon) cont
      (fun gF o => match o with
        | none => False
        | some o => FixFailR C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o))
      (fun c => match c with
        | none => False
        | some (z, _, _) => z.1 ∉ {st | stm st ∈ (inputRelation (ω := smoothDomain C.XI.nD hn) s dd m δ).language}) ?_) ?_
    · intro gF o hE
      rcases o with _ | o
      · exact hE.elim
      · obtain ⟨⟨p, hp⟩, hnot⟩ := hpt g gF o hE
        refine ⟨some (((sideOf g o).1, (sideOf g o).2.1), p, PUnit.unit), ?_, hnot⟩
        simp only [cont, simulateQ_bind, simulate_of_tabEval gF _ _ hp, pure_bind, simulateQ_pure]
        rfl
    · rw [← hshape]
      have h := side_merkle_singleSalt_soundness s dd l m G L Dg enc hk hdom θ δ ε hε stm decode model guards localAccepts hlocal
        (sideAdv sideOf Aon g) Q_FS Q_H V P (hFS g) (hH g) hterm hconfig
      refine le_trans (prEvent_mono _ _ _ ?_) h
      rintro ⟨⟨_ | ⟨z, path, w⟩, _⟩, _⟩ hb
      · exact hb
      · exact hb
  let M : ProbComp ((∀ d, R d) × (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') × Option O) :=
    do let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon; pure (g, gF, o)
  let Pfx : ((∀ d, R d) × (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') × Option O) → Prop := fun x => match x.2.2 with
    | none => False
    | some o => FixFailR C.XI (vkOf x.2.1) (HfOf x.2.1) (FSOf x.1) (FSfOf x.2.1) (zO o) (πO o) (πFO o)
  let Pnc : ((∀ d, R d) × (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') × Option O) → Prop := fun x => match x.2.2 with
    | none => False
    | some o => FixFailR C.XI (vkOf x.2.1) (HfOf x.2.1) (FSOf x.1) (FSfOf x.2.1) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf x.2.1) (HfOf x.2.1) (πFO o)
  let Pcl : ((∀ d, R d) × (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d') × Option O) → Prop := fun x => match x.2.2 with
    | none => False
    | some o => VKcollC C.XI (vkOf x.2.1) (HfOf x.2.1) (πFO o)
  have e1 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some o => FixFailR C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o)] = Pr{let x ← M}[Pfx x] :=
    NockvmE2E.Exec.E2EOnline.pr_triple _ _ _ (fun g gF (o : Option O) => match o with
      | none => False
      | some o => FixFailR C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o))
  have e2 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some o => FixFailR C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)] = Pr{let x ← M}[Pnc x] :=
    NockvmE2E.Exec.E2EOnline.pr_triple _ _ _ (fun g gF (o : Option O) => match o with
      | none => False
      | some o => FixFailR C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o))
  have e3 : Pr{let g ← $ᵗ (∀ d, R d); let gF ← $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'); let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some o => VKcollC C.XI (vkOf gF) (HfOf gF) (πFO o)] = Pr{let x ← M}[Pcl x] :=
    NockvmE2E.Exec.E2EOnline.pr_triple _ _ _ (fun g gF (o : Option O) => match o with
      | none => False
      | some o => VKcollC C.XI (vkOf gF) (HfOf gF) (πFO o))
  have hnc := triple_le ($ᵗ (∀ d, R d)) (fun _ => $ᵗ (∀ d', succinctRange Dg Op Query Stmt Salt (bMask (S := S) s dd l L Dg enc) d'))
    (fun g gF => simulateQ (withTable2 g gF) Aon) (fun g gF (o : Option O) => match o with
      | none => False
      | some o => FixFailR C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) ∧ ¬ VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)) _ hper
  rw [e2] at hnc
  rw [e3] at hcoll
  have hmono : Pr{let x ← M}[Pfx x] ≤ Pr{let x ← M}[Pnc x ∨ Pcl x] := by
    refine prEvent_mono_of_support M Pfx _ ?_
    rintro ⟨g, gF, o⟩ _ h
    rcases o with _ | o
    · exact absurd h id
    · by_cases hc : VKcoll C.XI (vkOf gF) (HfOf gF) (πFO o)
      · obtain ⟨c1, c2⟩ := fixFail'_canon C.XI (vkOf gF) (HfOf gF) (FSOf g) (FSfOf gF) (zO o) (πO o) (πFO o) h.1
        exact Or.inr ⟨hc, c1, c2⟩
      · exact Or.inl ⟨h, hc⟩
  rw [e1]
  exact hmono.trans ((prEvent_or_le M Pnc Pcl).trans (add_le_add hnc hcoll))

end Main

end Assembly

/-- the VK tree has `F * 2^nD` leaves, at most `F * 2^32` under any family shape (cf. `VKBindBridge.vk_total_le`) -/
theorem vk_total_le_F {F : Fam} {XI : ExecInst} (h : shapeOkF F XI = true) :
    (VKBind.vkSp XI).total ≤ (fixCols XI).size * 2 ^ 32 := by
  have h32 := hn32_of_shapeF h
  have h1 := hn1_of_shapeF h
  rw [VKBind.vkSp_total]
  have : 2 * 2 ^ (XI.nD - 1) ≤ 2 ^ 32 := by
    have : 2 * 2 ^ (XI.nD - 1) = 2 ^ XI.nD := by
      rw [← pow_succ']; congr 1; omega
    rw [this]; exact Nat.pow_le_pow_right (by norm_num) h32
  calc 2 * (fixCols XI).size * 2 ^ (XI.nD - 1) = (fixCols XI).size * (2 * 2 ^ (XI.nD - 1)) := by ring
    _ ≤ (fixCols XI).size * 2 ^ 32 := Nat.mul_le_mul_left _ this

/-! ### probe: the J-8 shape binder is accepted by the F-generic statements at `famJ8` -/

example {Xi : ExecInst} (h : J8Shape.j8ShapeOk Xi = true) : shapeOkF famJ8 Xi = true := by
  rw [← j8ShapeOk_eq]; exact h
/-- `j8ShapeOk` plugs into the F-generic lemmas at `famJ8` (defeq, no rewrite) -/
example {Xi : ExecInst} (h : J8Shape.j8ShapeOk Xi = true) := natDegree_fj_le_F (F := famJ8) h
example {Xi : ExecInst} (h : J8Shape.j8ShapeOk Xi = true) := vk_total_le_F (F := famJ8) h

/-- probe: `hFix_fri'R_F (F := famJ8)` elaborates with `hsh : j8ShapeOk` (the type is checked by unification up to `rfl`) -/
example {m k : ℕ} (C : SideCfg m) (hn : C.XI.nD ≤ 32) (hg : setupGates C.XI = true)
    (h : J8Shape.j8ShapeOk C.XI = true) :=
  @hFix_fri'R_F m k Unit (fun _ => Unit) _ _ Unit C hn hg famJ8 h

end NockvmE2E.Exec.V

#print axioms NockvmE2E.Exec.V.natDegree_fj_le_F
#print axioms NockvmE2E.Exec.V.vF_correct_of_languageF
#print axioms NockvmE2E.Exec.V.fix_not_languageF
#print axioms NockvmE2E.Exec.V.hFix_fri'R_F
#print axioms NockvmE2E.Exec.V.vk_total_le_F
