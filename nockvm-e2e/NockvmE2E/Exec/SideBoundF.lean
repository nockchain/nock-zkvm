/-
the family-generic side bound.
  * `SideNums`     : bundle of the side numerics (rule 5), XI-only.
  * `hglue_F`      : `hglue_J8` (HFixJ8V5) over `shapeOkF F XI`, the main FS view abstract (`FSOf : GM -> FSFn`).
  * `hFix_side_F`  : Pr[FixFailR ...] <= bfriErr + mcROM + (Q_Hf+Vf+T)^2/(2|Dg|), from `hglue_F` + `hcoll_J8` + `hFix_fri'R_F`;
                     `hspec` comes from `hspec_of_shapeF`.
No main-instance notation is used: the main table is `{DM} {RM : DM -> Type}`.
(The instance is named `XI`, not `X`: `open Polynomial` makes `X` the polynomial variable.)
-/
import NockvmE2E.Exec.SideOnlineRFri
import NockvmE2E.Exec.SideShapeF
import NockvmE2E.Exec.HCollJ8
import NockvmE2E.Exec.E2EOnlineP
import NockvmE2E.Exec.SideGlue20
import NockvmE2E.Exec.HSpecGen

open BinaryTree InductiveMerkleTree OracleComp OracleSpec ProtocolSpec Polynomial
open Interaction.Oracle Interaction.Oracle.Security Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir
open Fri.Spec Domain
open BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 2000

namespace NockvmE2E.Exec.SideBoundF
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Exec.SM NockvmE2E.Exec.E2E NockvmE2E.Merkle
  NockvmE2E.Exec.SideInst NockvmE2E.Exec.ShapeF NockvmE2E.Exec.SideOnlineR NockvmE2E.Exec.E2EOnlineP NockvmE2E.Exec.Cover
open NockvmE2E.Exec.E2EResid (encK)
open NockvmE2E.Exec.E2EJ8V NockvmE2E.Deep NockvmE2E.FriPort
open NockvmE2E.Exec.Emb NockvmE2E.Merkle.SoundnessWorld NockvmE2E.Merkle.SideMerkle NockvmE2E.Exec.Inst
open NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good NockvmE2E.Merkle.SoundnessCoupling NockvmE2E.Merkle.BadBound
open MerkleTreeMultiExtractability

variable [SampleableType KC]

/-- the side numerics of `exec_e2e_J8V5`, bundled (rule 5); XI-only. -/
structure SideNums (XI : ExecInst) (hn : XI.nD ≤ 32) (θ : ℝ) (δ ε : ℝ≥0) : Prop where
  hk : 1 ≤ XI.k
  hdomS : 2 ^ (∑ j, ((fun _ : Fin (XI.k + 1) => (1 : ℕ+)) j).val) * (1 : ℕ+).val ≤ 2 ^ XI.nD
  hε : ProximityGap.caError (GX XI)
    (ReedSolomon.code ((smoothDomain XI.nD hn : SmoothCosetFftDomain XI.nD KC) : Fin (2 ^ XI.nD) ↪ KC)
      (2 ^ (∑ i, ((fun _ : Fin (XI.k + 1) => (1 : ℕ+)) i).1) * (1 : ℕ+))).carrier δ δ ≤ ε
  hfb : 2 ^ (XI.k + 1) ≤ friBound (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1
  hN : friBound (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 + 1 ≤ 2 ^ XI.nD
  hδ : δ ≤ Code.relativeUniqueDecodingRadius
    (ReedSolomon.code (domEmb (smoothDomain XI.nD hn)) (friBound (fun _ : Fin (XI.k + 1) => (1 : ℕ+)) 1 + 1) :
      Set (Fin (2 ^ XI.nD) → KC))

variable {F : Fam} (XI : ExecInst) (hsh : shapeOkF F XI = true) (hgates : setupGates XI = true) (hk : 1 ≤ XI.k)

set_option hygiene false in
local notation "s1" => (fun _ : Fin (XI.k + 1) => (1 : ℕ+))
set_option hygiene false in
local notation "LV" => LX XI (hn32_of_shapeF hsh)
set_option hygiene false in
local notation "CS" => (SideCfg.mk XI (opIdxX XI) (ptKX XI))
set_option hygiene false in
local notation "SMS" => NockvmE2E.Merkle.SideMerkle.bMask (S := KC) s1 1 XI.l LV DgJ8 encK
set_option hygiene false in
local notation "ZStmt'" => SStmt XI
set_option hygiene false in
local notation "ZSalt'" => (Statement × Salt)
set_option hygiene false in
local notation "ZOp" => OpenAll DgJ8 (merkleSkels (SMS))
set_option hygiene false in
local notation "Zskels" => skelsSide XI
set_option hygiene false in
local notation "ZmS" => mSX XI
set_option hygiene false in
local notation "ZG" => GX XI
set_option hygiene false in
local notation "ZdecS" => decSX XI
set_option hygiene false in
local notation "Zdecode" => (id : OpenAll DgJ8 (merkleSkels (SMS)) → OpenAll DgJ8 (merkleSkels (SMS)))
set_option hygiene false in
local notation "Zmodel" => SideGlue13.modelSS XI (hn32_of_shapeF hsh) XI.l (SideGlue20.dfltS XI hgates hk (hn32_of_shapeF hsh))
set_option hygiene false in
local notation "Zguards" => (trueGuards _)
set_option hygiene false in
local notation "ZlocalAccepts" => (bLocal s1 1 XI.l ZmS ZG LV DgJ8 encK ZOp hdomS (fun st => stmtOf CS (hn32_of_shapeF hsh) (ZdecS st)) id)
set_option hygiene false in
local notation "ZfkOf" => (fkOfX s1 XI.l LV XI decZ (ω0S s1 XI.l LV))
set_option hygiene false in
local notation "ZfrOf" => (frOfX s1 XI.l LV XI (ω0S s1 XI.l LV))
set_option hygiene false in
local notation "ZChal" => (fun k : Key (ZStmt' × ZSalt') PUnit (compiledRoundsK DgJ8 ZOp (SMS)) => Key.Challenge k)

variable [∀ j, SampleableType ((pSpec XI.k (ω := smoothDomain XI.nD (hn32_of_shapeF hsh)) s1 XI.l).Challenge j)]

set_option maxHeartbeats 4000000 in
/-- **`hglue_F`**: `hglue_J8` over any family shape (`shapeOkF F XI`), the main FS view abstract (`FSOf : GM → FSFn`). -/
theorem hglue_F {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    {GM : Type} (FSOf : GM → FSFn)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (hdomS : 2 ^ (∑ j, (s1 j).val) * (1 : ℕ+).val ≤ 2 ^ XI.nD) :
    ∀ (g : GM) (gF : ∀ d', succinctRange DgJ8 ZOp (NQuery Zskels) ZStmt' ZSalt' (SMS) d')
      (o : Statement × Salt × FlatProof × FixProof × W),
      FixFailR XI (vkSide XI Zskels ZChal gF) (HfOf Zskels ZChal gF) (FSOf g)
        (FSfOf Zskels ZChal ZfkOf ZfrOf gF) (encZ (o.1, o.2.1)) o.2.2.1 o.2.2.2.1 →
        ZdecS (sideOfX s1 XI.l LV XI (FSOf g) encZ o).1 = ⟨[], fixCtx o.2.2.1 (zetaOf XI (FSOf g) (encZ (o.1, o.2.1)) o.2.2.1), o.2.2.2.1.vF⟩ ∧
        (∀ j, canon3 (ptKX XI (ZdecS (sideOfX s1 XI.l LV XI (FSOf g) encZ o).1).ctx j)) ∧
        (∀ j i, smoothDomain XI.nD (hn32_of_shapeF hsh) i ≠ SideCfg.pt CS (ZdecS (sideOfX s1 XI.l LV XI (FSOf g) encZ o).1) j) ∧
        (∀ j o', j < (fixCols XI).size → o' < fixLen XI (fixCols XI)[j]! →
          canon3 (o.2.2.2.1.vF[j]!)[o']! ∧
          canon3 (fixTrue XI (fixCols XI)[j]! ((openPts XI (zetaOf XI (FSOf g) (encZ (o.1, o.2.1)) o.2.2.1))[o']!))) ∧
        (¬ VKcoll XI (vkSide XI Zskels ZChal gF) (HfOf Zskels ZChal gF) o.2.2.2.1 →
          ∃ p, tabEval (tabK gF) (succinctVerifyK Zguards (merkleCheck (merkleSkels (SMS)) Zmodel Zdecode) ZlocalAccepts
            ((sideOfX s1 XI.l LV XI (FSOf g) encZ o).1, (sideOfX s1 XI.l LV XI (FSOf g) encZ o).2.1)
            (sideOfX s1 XI.l LV XI (FSOf g) encZ o).2.2) = some (some p)) := by
  intro g gF o hFF
  have hn := hn32_of_shapeF hsh
  have hsetup := setup'_of_gates hgates (HfOf Zskels ZChal gF)
  obtain ⟨_, hX, hc⟩ := setup'_some hsetup
  have hp := paramsOk_of_shapeF hsh
  have L' := J8Shape.domLink_of_paramsOk XI hp hn
  obtain ⟨h1, h2, h3, h4⟩ := SideGlue.conj1234_sideOfX s1 XI.l LV XI hgates hn L' (FSOf g) encZ o _ _ _ hc hX hFF
  exact ⟨h1, h2, h3, h4, fun hnc => SideGlue20.conj5_side XI hgates hn L' (J8Shape.dShift_of_paramsOk _ hp)
    (J8Shape.dGen_of_paramsOk _ hp) (d_of_shapeF hsh) (by rw [hl_of_shapeF hsh]; norm_num) hdomS encZ decZ hz (FSOf g) o
    (SideGlue20.dfltS XI hgates hk hn) gF _ hc hX hFF hnc⟩

include hgates in
set_option maxHeartbeats 4000000 in
/-- **`hFix_side_F`**: `Pr[FixFailR] ≤ bfriErr + mcROM + (Q_Hf+Vf+T)²/(2|Dg|)` for the side protocol at any family shape
(`shapeOkF F XI`); the main table `RM` and its FS view `FSOf` are abstract.  `hglue_F` + `hcoll_J8` + `hFix_fri'R_F`; `hspec` is
`hspec_of_shapeF`. -/
theorem hFix_side_F {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    {θ : ℝ} {δ ε : ℝ≥0} (hnum : SideNums XI (hn32_of_shapeF hsh) θ δ ε)
    {DM : Type} {RM : DM → Type} [DecidableEq DM] [instTab : SampleableType (∀ d, RM d)]
    [Finite (NQuery Zskels)]
    [instTabF : SampleableType (∀ d', succinctRange DgJ8 ZOp (NQuery Zskels) ZStmt' ZSalt' (SMS) d')]
    (FSOf : (∀ d, RM d) → FSFn)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (Aon : OracleComp ((unifSpec + OracleSpec.ofFn RM) +
        OracleSpec.ofFn (succinctRange DgJ8 ZOp (NQuery Zskels) ZStmt' ZSalt' (SMS)))
      (Option (Statement × Salt × FlatProof × FixProof × W)))
    (Q_FSf Q_Hf Vf Pf T : ℕ)
    (hFSf : ∀ g : (∀ d, RM d), FsBound (Q := NQuery Zskels)
      (∅ : (ofFn (SoundnessWorld.KC DgJ8 ZOp ZStmt' ZSalt' (SMS))).QueryCache) Q_FSf (verifiedFS Zguards (sideAdv
        (fun g o => sideOfX s1 XI.l LV XI (FSOf g) encZ o) Aon g)))
    (hHf : ∀ g : (∀ d, RM d), IsQueryBoundP (sideAdv (fun g o => sideOfX s1 XI.l LV XI (FSOf g) encZ o) Aon g)
      (@isHashQuery (NQuery Zskels) DgJ8 _ (SoundnessWorld.KC DgJ8 ZOp ZStmt' ZSalt' (SMS))) Q_Hf)
    (htermf : ∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (SMS)).length) (op : ZOp)
      (logs : Fin (merkleSkels (SMS)).length → MerkleTreeExtractor.QueryLog (NQuery Zskels) DgJ8),
      claimsQueryCount (mkClaims (merkleSkels (SMS)) roots h (Zdecode op) logs) ≤ Vf)
    (hconfigf : ∀ tag, (mconfig (merkleSkels (SMS))).nodeBudget tag ≤ Pf)
    (hTb : 2 * ((NockvmE2E.Exec.VKBind.vkSp XI).total - 1) ≤ T) :
    Pr{let g ← $ᵗ (∀ d, RM d); let gF ← $ᵗ (∀ d', succinctRange DgJ8 ZOp (NQuery Zskels) ZStmt' ZSalt' (SMS) d');
        let o ← simulateQ (withTable2 g gF) Aon}[
      match o with
      | none => False
      | some o => FixFailR XI (vkSide XI Zskels ZChal gF) (HfOf Zskels ZChal gF) (FSOf g)
          (FSfOf Zskels ZChal ZfkOf ZfrOf gF) (encZ (o.1, o.2.1)) o.2.2.1 o.2.2.2.1] ≤
      bfriErr (ω := smoothDomain XI.nD (hn32_of_shapeF hsh)) s1 1 XI.l θ δ ε Q_FSf +
        (multiCheckpointROMErrorNumerator ((XI.k * (Q_FSf + 1)) * Pf) (XI.k * (Q_FSf + 1)) Vf Q_Hf : ℝ≥0∞) *
          (Nat.card DgJ8 : ℝ≥0∞)⁻¹ +
        ((Q_Hf + Vf + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card DgJ8 : ℝ≥0∞)) := by
  have hn := hn32_of_shapeF hsh
  have hk := hnum.hk
  have hdomS := hnum.hdomS
  have hspec : HSpec XI := hspec_of_shapeF hgates hsh
  have hr2 := r_ge_two_of_gates hgates
  have hFc := SideGlue18.fixCols_size_pos XI
  have hcol := fun j => SideGlue.hcolX XI hFc j
  have hC1 := SideGlue.hC1X XI 0 hFc (SideGlue18.fixLen_pos _ _ (by omega))
  have hC2 := fun π ζ i => hC2X XI π ζ i
  have hlocal := NockvmE2E.Merkle.SideMerkle.bMask_queryOnly s1 1 XI.l (mSX XI) (GX XI) LV DgJ8 encK hdomS ZOp
    (Stmt := ZStmt') (Salt := ZSalt') (fun st => stmtOf CS hn (ZdecS st)) Zdecode
  have hsk : Zskels[0]? = some (NockvmE2E.Exec.VKTrace.skelVK XI) := rfl
  have hcollP := NockvmE2E.Exec.HCollJ8.hcoll_J8 (R := RM) (instR := instTab) (instRF := instTabF) XI hgates hspec hsk
    (fun g o => sideOfX s1 XI.l LV XI (FSOf g) encZ o) Aon (fun o => o.2.2.2.1) Q_Hf Vf T hHf hTb
  have hF := hFix_fri'R_F (C := CS) (hn := hn) (hg := hgates) (hsh := hsh) (s := s1) (dd := 1)
    (l := XI.l) (G := ZG) (L := LV) (Dg := DgJ8) (enc := encK) (hk := hk) (hdom := hdomS) (θ := θ) (δ := δ) (ε := ε)
    (hε := hnum.hε) (hfb := hnum.hfb) (hN := hnum.hN) (hδ := hnum.hδ) (hcol := hcol) (decS := ZdecS) (decode := Zdecode)
    (model := Zmodel) (guards := Zguards) (localAccepts := ZlocalAccepts) (hlocal := hlocal)
    (HfOf := HfOf Zskels ZChal) (FSOf := FSOf) (FSfOf := FSfOf Zskels ZChal ZfkOf ZfrOf)
    (vkOf := vkSide XI Zskels ZChal) (hvk := fun gF => mkVKData'_vk_eq_vkSpec hspec hgates _)
    (zO := fun o => encZ (o.1, o.2.1)) (πO := fun o => o.2.2.1) (πFO := fun o => o.2.2.2.1)
    (sideOf := fun g o => sideOfX s1 XI.l LV XI (FSOf g) encZ o) (Aon := Aon)
    (instR := instTab) (instRF := instTabF) (Q_FS := Q_FSf) (Q_H := Q_Hf) (V := Vf) (P := Pf) (T := T)
    (hFS := hFSf) (hH := hHf) (hterm := htermf) (hconfig := hconfigf) (hC1 := hC1) (hC2 := hC2)
    (hglue := hglue_F (hsh := hsh) (hgates := hgates) (hk := hk) (FSOf := FSOf) (encZ := encZ) (decZ := decZ) (hz := hz)
      (hdomS := hdomS))
    (hcoll := by
      refine le_trans (le_of_eq (NockvmE2E.Exec.E2EOnline.pr_triple_congr _ _ _ _ _ ?_)) hcollP
      intro g gF o; rcases o with _ | o <;> exact Iff.rfl)
  refine le_trans (le_of_eq (NockvmE2E.Exec.E2EOnline.pr_triple_congr _ _ _ _ _ ?_)) hF
  intro g gF o
  rcases o with _ | o <;> exact Iff.rfl

end NockvmE2E.Exec.SideBoundF

#print axioms NockvmE2E.Exec.SideBoundF.hglue_F
#print axioms NockvmE2E.Exec.SideBoundF.hFix_side_F
