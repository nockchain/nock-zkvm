/-
 follow-up 2: `exec_e2e_J8V'''` = `exec_e2e_J8V''` with `hcoll` restated over `VKcollC` (canonical tree-0 limbs), via `hFix_fri'` (HFixFriC.lean).
-/
import NockvmE2E.Exec.HFixFriC
import NockvmE2E.Exec.E2EOnlineP

/-! # Part 2: `exec_e2e_J8V'''` -- `exec_e2e_J8V'` with `hFix'` discharged by `hFix_fri` -/

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

namespace NockvmE2E.Exec.E2EJ8V
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit NockvmE2E.J8 NockvmE2E.J8.TieJ8G
open NockvmE2E.J8.InstJ8W (sigmaX tabIdx)
open NockvmE2E.J8.TieJ8 (HopZero)
open NockvmE2E.Exec.E2EJ8P2 NockvmE2E.Exec.E2EJ8P
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.InstGen NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Rap
open NockvmE2E.J8.InstJ8 (Φ0)

/-! ## 1. hop 0 from the exe's chip check: `HopsOK`, `NumOK`, the constraint-count cap -/

open NockvmE2E.Exec.E2EJ8F
open NockvmE2E.Exec.V NockvmE2E.Exec.VL NockvmE2E.Merkle NockvmE2E.Exec.E2E NockvmE2E.Exec.Emb NockvmE2E.FriPort
  NockvmE2E.Exec.E2EFri NockvmE2E.Exec.E2EMain NockvmE2E.Exec.E2EResid NockvmE2E.Exec.E2EW0 NockvmE2E.Exec.E2EFinal
open NockvmE2E.Succ NockvmE2E.Deep NockvmE2E.Succ.FriC NockvmE2E.FriPort NockvmE2E.FriPort.Batched
  NockvmE2E.Succ.FriDeep NockvmE2E.Succ.App NockvmE2E.Lift NockvmE2E.Lift.Alternating
  NockvmE2E.Exec.Inst NockvmE2E.Rap NockvmE2E.Merkle.RapFriQ NockvmE2E.Merkle.MA NockvmE2E.Exec.SL NockvmE2E.Exec.Cover
  NockvmE2E.Exec.SF NockvmE2E.Merkle.Fri NockvmE2E.Exec.Layout NockvmE2E.Exec.SM
open NockvmE2E.Exec.E2EJ8 NockvmE2E.Exec.E2EJ8.J8X
open NockvmE2E.J8.InstJ8 (Datum DatumOK J8 PbOfX PosX posX_of_shape hNof ω0 StmtP PubP)
open NockvmE2E.J8.TieJ8G (Inst HopsOK NumOK RdSpec Gflat hsz_of_hops gbJ hdagU_J8 hoff_J8 hdom_J8 colJ pubJ chalK)
open NockvmE2E.J8.InstJ8W (sigmaX RJ8 hfree_J8)
open NockvmE2E.Exec.MaskOk (maskOk)

variable (XI0 : ExecInst) (hsh : J8Shape.j8ShapeOk (XI170 XI0) = true) (hshX : J8Shape.j8ShapeXOk (XI170 XI0) = true)

set_option hygiene false in
local notation "ωS" => smoothDomain (XI170 XI0).nD (J8Shape.hn32_of_shape hsh)
set_option hygiene false in
local notation "s1" => (fun _ : Fin ((XI170 XI0).k + 1) => (1 : ℕ+))

variable [SampleableType KC]
variable (D : DatX (XI170 XI0) hsh) (hdk : DatumOK D.d)
variable (R : TabRestr (J8 D.d hdk)) (hT : R.T' = (XI170 XI0).tabs.size)
  (hσ : ∀ t : Fin R.T', R.σ t = sigmaX (XI170 XI0) (Fin.cast hT t)) (hfree : (J8 D.d hdk).AccOn R.q)

set_option hygiene false in
local notation "IX" => (⟨XI170 XI0, hsh, posX_of_shape hsh, D.kroots, D.krootsV, D.Rt, D.regs, D.ids, D.idx, D.rk, D.lay, D.d, D.hd,
  hdk, D.hdN, D.hdω, R, hT, hσ, hfree⟩ : Inst)

set_option hygiene false in
local notation "npubV" => (XI170 XI0).pubOf.size
set_option hygiene false in
local notation "hcapV" => hcap_of_shapeX IX (XI170 XI0).pubOf.size rfl hshX

variable (tp : Fin (IX).Jm.T)

set_option hygiene false in
local notation "JXn" => (IX).JJ (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "prV" => prX IX (XI170 XI0).pubOf.size tp hcapV

/- the executed chip check and the datum numerals (labels in the ledger at the end) -/
variable (hchips : chipsOk (XI170 XI0) = true)
  (hnum0 : ∀ t : Fin (XI170 XI0).tabs.size,
    (chipNumeral (XI170 XI0).tabs[t].chip).getD 0 = numOf D.d (sigmaX (XI170 XI0) t))

set_option hygiene false in
local notation "hd1" => ((J8Shape.d_of_shape hsh).symm : (1 : ℕ+).val = (XI170 XI0).d)
set_option hygiene false in
local notation "hNHV" => hNH_X IX (XI170 XI0).pubOf.size tp hcapV 1 hd1
set_option hygiene false in
local notation "hpdV" => hpd_X IX (XI170 XI0).pubOf.size tp hcapV
set_option hygiene false in
local notation "hopsV" => (hops_of_chips IX hchips litTies hnum0).1
set_option hygiene false in
local notation "hnumV" => (hops_of_chips IX hchips litTies hnum0).2.1
set_option hygiene false in
local notation "GX" => Gflat IX (hsz_of_hops IX jDers jMeta hnumV hopsV)
set_option hygiene false in
local notation "PJ" => (deepParamsJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV).regroup GX gbJ
set_option hygiene false in
local notation "AJ" => (airJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV).regroup GX gbJ
set_option hygiene false in
local notation "R0P" => R0J JXn prV ωS (31 / 64) (friBound s1 1)
set_option hygiene false in
local notation "RestP" => RestJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV
set_option hygiene false in
local notation "RestVP" => RestVJ JXn prV ωS (31 / 64) (friBound s1 1) hNHV hpdV
set_option hygiene false in
local notation "cIV" => cIX IX (XI170 XI0).pubOf.size tp hcapV rfl
set_option hygiene false in
local notation "mV" => (XI170 XI0).nc * (JXn).r + (PJ).nq - 1

set_option hygiene false in
local notation "EJ" => eOf (XI170 XI0) cIV (JXn).r (NockvmE2E.Exec.E2EJ8F.F.hmV_X XI0 hsh hshX D hdk R hT hσ hfree tp hchips hnum0)

variable [DecidableEq ((PJ).statement (R0P) (RestP)).M0] [Finite ((PJ).statement (R0P) (RestP)).M0]
  [DecidableEq (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  [Finite (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin]
  (I0 : OracleInterface ((PJ).statement (R0P) (RestP)).M0)
  (I : (r : ℕ) → OracleInterface (Cols (PJ).colRoundX (Fin (2 ^ (XI170 XI0).nD) → ZMod NockvmE2E.Exec.p) r))
  (Ifin : OracleInterface (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin)
variable [∀ j, SampleableType ((pSpec (XI170 XI0).k (ω := ωS) s1 (XI170 XI0).l).Challenge j)]
variable (m0 : ((PJ).statement (R0P) (RestP)).M0) (mf : (R0P).Mfin)

set_option hygiene false in
local notation "HNQ" => ((nq_of_shapeX hshX).trans rfl : (XI170 XI0).nq = (PJ).nq)
set_option hygiene false in
local notation "HBLK" => hblk_of_shapeX IX (XI170 XI0).pubOf.size tp hcapV rfl hshX
set_option hygiene false in
local notation "HBLKQ" => hblkq_X IX (PJ).nq (HNQ).ge
set_option hygiene false in
local notation "MDV" => mdX (XI170 XI0) (J8Shape.hn1_of_shape hsh) (PJ).colRoundX
  (rkP (XI170 XI0) (PJ) rfl HNQ cIV HBLK HBLKQ) toyEncB
set_option hygiene false in
local notation "LV" => LX (XI170 XI0) (J8Shape.hn32_of_shape hsh)

set_option hygiene false in
local notation "MC" => msC (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 4 s1 1 (XI170 XI0).l DgJ8 encK MDV LV (S := KC)
set_option hygiene false in
local notation "RM" => RapP.rapMask (extFrame (JXn).Φ0 2) KC (MDV).toRapMaskData ((PJ).statement (R0P) (RestP)).M0
  (friPlan (ω := ωS) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ)).Mfin I0 I Ifin 4
set_option hygiene false in
local notation "BM" => bmask (S := KC) s1 1 (XI170 XI0).l DgJ8 encK LV
set_option hygiene false in
local notation "OPN" => OpenAll DgJ8 (merkleSkels (MC))
set_option hygiene false in
local notation "DA" => daOf (XI170 XI0) (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin DgJ8 MDV cIV sl0X sl1X
  (PJ).ha (PJ).hz
  (single_az (XI170 XI0) JXn prV (ω := ωS) (31 / 64) (friBound s1 1) hNHV hpdV).1
  (single_az (XI170 XI0) JXn prV (ω := ωS) (31 / 64) (friBound s1 1) hNHV hpdV).2 m0 mf
set_option hygiene false in
local notation "EMBF" => fun (π : FlatProof) =>
  embedMsgs dgOf (MC) (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK))
    (openAllOf (merkleSkels (MC)) (flatTrees (XI170 XI0) π)) (msgsOf (XI170 XI0) π).toList

/-! ## side-protocol notations -/

variable {mS : ℕ} (opIdx : Fin (mS + 1) → ℕ × ℕ) (ptK : List Nat → Fin (mS + 1) → VF.K3) {SS : Type}

set_option hygiene false in
local notation "CS" => (SideCfg.mk (XI170 XI0) opIdx ptK)
set_option hygiene false in
local notation "SMS" => NockvmE2E.Merkle.SideMerkle.bMask (S := SS) s1 1 (XI170 XI0).l LV DgJ8 encK
set_option hygiene false in
local notation "TabM[" St "," Sa "]" => (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) St Sa (MC) dd)
set_option hygiene false in
local notation "FSM" => FST XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV
set_option hygiene false in
local notation "HTM" => HT XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV
set_option hygiene false in
local notation "ROM" => (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK))

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability NockvmE2E.Merkle.SideMerkle in
set_option maxHeartbeats 4000000 in
/-- **VACUOUS-AS-STATED: `hglue` is unsatisfiable (see `SideOnlineRUnsat.old_hglue_bounds_roots`: kernel reduction, the premise `FixFail'` leaves
the roots unbounded -- argued; superseded by the `FixFailR` restatement `SideOnlineRJ8.exec_e2e_J8V'R` / `SideOnlineRFri.hFix_fri'R`).**
**`exec_e2e_J8V'''`**: `exec_e2e_J8V''` with `hcoll` restated over `VKcollC` (canonical tree-0 limbs; `hFix_fri'`).  Conclusion `≤ 2^-82 + εfix` with
`εfix = bfriErr + (multiCheckpointROMErrorNumerator ..)/|Dg| + (Q_Hf+Vf+T)^2/(2|Dg|)` (numbers: `epsfix_numbers`).
Remaining hypotheses (besides the budgets and the instance checks of `exec_e2e_J8V'`): `hspec`, `hglue` (7-5), `hcoll` (7-4),
the config facts `hC1 hC2` and the FRI parameter facts `hfb hN hδ hε`.  The side oracle is `succinctRange` of the compiled side protocol
`bMask` over node queries `NQuery skelsF` (side tags: `skelsF` = VK rag tree then the `k` FRI trees). -/
theorem exec_e2e_J8V''' {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt]
    [Finite (NQuery (merkleSkels (MC)))]
    [instTab : SampleableType (TabM[Statement, Salt])]
    {skelsF : List Skeleton} [Finite (NQuery skelsF)] {Stmt' Salt' : Type} [DecidableEq Stmt'] [DecidableEq Salt'] [Finite Stmt'] [Finite Salt']
    {Op : Type} [Finite Op] [DecidableEq Op]
    [Fintype SS] [Nonempty SS] [SampleableType SS]
    [instTabF : SampleableType (∀ d', succinctRange DgJ8 Op (NQuery skelsF) Stmt' Salt' (SMS) d')]
    (hl : XI0.l = 170)
    (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x)
    (hS : StmtP D.d) (hlink : NockvmE2E.J8.RVUJ8.InpLink D.d (XI170 XI0).pubIn)
    (hids : ∀ id ∈ D.d.Pb.regs, id < NockvmE2E.J8.InstJ8.P)
    (hmask : maskOk (XI170 XI0) = true) (hnumeralOk : NockvmE2E.Exec.MaskOk.numeralOk (XI170 XI0) = true)
    (hjet : ∀ t : Fin (XI170 XI0).tabs.size, (XI170 XI0).tabs[t].chip.id = "jetChipJ8" →
      ∀ c, c < (XI170 XI0).tabs[t].nc - (XI170 XI0).tabs[t].npub → (XI170 XI0).colKind[(XI170 XI0).tabs[t].col0 + c]! = 1 →
        NockvmE2E.Exec.MaskBridge.LagrAt IX (XI170 XI0).pubOf.size tp hcapV t c)
    (hgates : setupGates (XI170 XI0) = true) (hspec : HSpec (XI170 XI0))
    -- side protocol parameters
    (G : CoreDefinitions.Generator SS (Fin (mS + 1)) KC) (hk : 1 ≤ (XI170 XI0).k)
    (hdomS : 2 ^ (∑ j, (s1 j).val) * (1 : ℕ+).val ≤ 2 ^ (XI170 XI0).nD) (θ : ℝ) (δ ε : ℝ≥0)
    (hε : ProximityGap.caError G
      (ReedSolomon.code ((smoothDomain (XI170 XI0).nD (J8Shape.hn32_of_shape hsh) : SmoothCosetFftDomain (XI170 XI0).nD KC) :
        Fin (2 ^ (XI170 XI0).nD) ↪ KC) (2 ^ (∑ i, (s1 i).1) * (1 : ℕ+))).carrier δ δ ≤ ε)
    (hfb : 2 ^ ((XI170 XI0).k + 1) ≤ friBound s1 1) (hN : friBound s1 1 + 1 ≤ 2 ^ (XI170 XI0).nD)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code (domEmb (smoothDomain (XI170 XI0).nD (J8Shape.hn32_of_shape hsh))) (friBound s1 1 + 1) :
        Set (Fin (2 ^ (XI170 XI0).nD) → KC)))
    (hcol : ∀ j, (opIdx j).1 < (fixCols (XI170 XI0)).size)
    (decS : Stmt' → SideStmt)
    (decode : Op → OpenAll DgJ8 (merkleSkels (SMS)))
    (model : MerkleTreeExtractability.NodeQueryModel (NQuery skelsF) (MAddress (merkleSkels (SMS))) DgJ8)
    (guards : GuardSchedule (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)))
    (localAccepts : Stmt' × Salt' → (protocol (compiledRoundsK DgJ8 Op (SMS))).tree.ExecutionPath → Bool)
    (hlocal : QueryOnly (SMS) decode (bAccepts s1 1 (XI170 XI0).l mS G LV DgJ8 encK hdomS (fun st => stmtOf CS (J8Shape.hn32_of_shape hsh) (decS st)) (Salt := Salt')) localAccepts)
    (fkOf : List (List ℕ) → Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)))
    (frOf : ∀ k, Key.Challenge k → ℕ → List ℕ)
    (sideOf : TabM[Statement, Salt] → (Statement × Salt × FlatProof × FixProof × W) →
      Stmt' × Salt' × PublicMessages (compiledRoundsK DgJ8 Op (SMS)))
    (Aon : OracleComp (SuccinctSpecK DgJ8 (OPN) (NQuery (merkleSkels (MC))) Statement Salt (MC) +
        OracleSpec.ofFn (succinctRange DgJ8 Op (NQuery skelsF) Stmt' Salt' (SMS)))
      (Option (Statement × Salt × FlatProof × FixProof × W)))
    (Q_FS Q_H V Pn : ℕ) (hQFS : Q_FS ≤ 2 ^ 64) (hQH : Q_H ≤ 2 ^ 64) (hV : V ≤ 2 ^ 32)
    (hFS : FsBound (Q := NQuery (merkleSkels (MC))) (∅ : (ofFn (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))).QueryCache)
      Q_FS (verifiedFS (trueGuards _) (embedAdv DgJ8 EMBF
        (E2EOnlineP.repackP (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2))) Aon))))
    (hHq : IsQueryBoundP (embedAdv DgJ8 EMBF
        (E2EOnlineP.repackP (fun o : Statement × Salt × FlatProof × FixProof × W => (o.1, o.2.1, o.2.2.1, (o.2.2.2.1, o.2.2.2.2))) Aon))
      (@isHashQuery (NQuery (merkleSkels (MC))) DgJ8 _ (SoundnessWorld.KC DgJ8 (OPN) Statement Salt (MC))) Q_H)
    (hterm : ∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (MC)).length) (op : OPN)
      (logs : Fin (merkleSkels (MC)).length → MerkleTreeExtractor.QueryLog (NQuery (merkleSkels (MC))) DgJ8),
      claimsQueryCount (mkClaims (merkleSkels (MC)) roots h op logs) ≤ V)
    (hconfig : ∀ tag, (mconfig (merkleSkels (MC))).nodeBudget tag ≤ Pn)
    (Q_FSf Q_Hf Vf Pf T : ℕ)
    (hFSf : ∀ g : TabM[Statement, Salt], FsBound (Q := NQuery skelsF)
      (∅ : (ofFn (SoundnessWorld.KC DgJ8 Op Stmt' Salt' (SMS))).QueryCache) Q_FSf (verifiedFS guards (sideAdv sideOf Aon g)))
    (hHf : ∀ g : TabM[Statement, Salt], IsQueryBoundP (sideAdv sideOf Aon g)
      (@isHashQuery (NQuery skelsF) DgJ8 _ (SoundnessWorld.KC DgJ8 Op Stmt' Salt' (SMS))) Q_Hf)
    (htermf : ∀ (roots : List DgJ8) (h : roots.length = (merkleSkels (SMS)).length) (op : Op)
      (logs : Fin (merkleSkels (SMS)).length → MerkleTreeExtractor.QueryLog (NQuery skelsF) DgJ8),
      claimsQueryCount (mkClaims (merkleSkels (SMS)) roots h (decode op) logs) ≤ Vf)
    (hconfigf : ∀ tag, (mconfig (merkleSkels (SMS))).nodeBudget tag ≤ Pf)
    (hC1 : ∀ j o, j < (fixCols (XI170 XI0)).size → o < fixLen (XI170 XI0) (fixCols (XI170 XI0))[j]! → ∃ i, opIdx i = (j, o))
    (hC2 : ∀ π ζ i, ptK (fixCtx π ζ) i = (openPts (XI170 XI0) ζ)[(opIdx i).2]!)
    (hglue : ∀ (g : TabM[Statement, Salt]) (gF : ∀ d', succinctRange DgJ8 Op (NQuery skelsF) Stmt' Salt' (SMS) d') (o : Statement × Salt × FlatProof × FixProof × W),
      FixFail' (XI170 XI0) (vkSide (XI170 XI0) skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k) gF)
        (HfOf skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k) gF) (FSM decZ ROM g) (FSfOf skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k) fkOf frOf gF) (encZ (o.1, o.2.1)) o.2.2.1 o.2.2.2.1 →
        decS (sideOf g o).1 = ⟨[], fixCtx o.2.2.1 (zetaOf (XI170 XI0) (FSM decZ ROM g) (encZ (o.1, o.2.1)) o.2.2.1), o.2.2.2.1.vF⟩ ∧
        (∀ j, canon3 (ptK (decS (sideOf g o).1).ctx j)) ∧
        (∀ j i, smoothDomain (XI170 XI0).nD (J8Shape.hn32_of_shape hsh) i ≠ SideCfg.pt CS (decS (sideOf g o).1) j) ∧
        (∀ j o', j < (fixCols (XI170 XI0)).size → o' < fixLen (XI170 XI0) (fixCols (XI170 XI0))[j]! →
          canon3 (o.2.2.2.1.vF[j]!)[o']! ∧
          canon3 (fixTrue (XI170 XI0) (fixCols (XI170 XI0))[j]!
            ((openPts (XI170 XI0) (zetaOf (XI170 XI0) (FSM decZ ROM g) (encZ (o.1, o.2.1)) o.2.2.1))[o']!))) ∧
        (¬ VKcoll (XI170 XI0) (vkSide (XI170 XI0) skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k) gF)
            (HfOf skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k) gF) o.2.2.2.1 →
          ∃ p, tabEval (tabK gF) (succinctVerifyK guards (merkleCheck (merkleSkels (SMS)) model decode) localAccepts
            ((sideOf g o).1, (sideOf g o).2.1) (sideOf g o).2.2) = some (some p)))
    (hcoll : Pr{let g ← $ᵗ TabM[Statement, Salt]; let gF ← $ᵗ (∀ d', succinctRange DgJ8 Op (NQuery skelsF) Stmt' Salt' (SMS) d'); let o ← simulateQ (E2EOnlineP.withTable2 g gF) Aon}[
        match o with
        | none => False
        | some o => NockvmE2E.Exec.VKBindBridge.VKcollC (XI170 XI0) (vkSide (XI170 XI0) skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k) gF)
            (HfOf skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k) gF) o.2.2.2.1] ≤ ((Q_Hf + Vf + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card DgJ8 : ℝ≥0∞))) :
    Pr{let g ← $ᵗ TabM[Statement, Salt]; let gF ← $ᵗ (∀ d', succinctRange DgJ8 Op (NQuery skelsF) Stmt' Salt' (SMS) d'); let o ← simulateQ (E2EOnlineP.withTable2 g gF) Aon}[
      match o with
      | none => False
      | some (z, salt, π, πF, _) =>
        verifyOnline' (vkSide (XI170 XI0) skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k) gF)
          (HTM g) (HfOf skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k) gF)
          (FSM decZ ROM g) (FSfOf skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k) fkOf frOf gF) (encZ (z, salt)) π πF = true ∧ ¬ Nock.Jet.HoldsN D.d.c] ≤
      (2 ^ 82 : ℝ≥0∞)⁻¹ +
        (bfriErr (ω := smoothDomain (XI170 XI0).nD (J8Shape.hn32_of_shape hsh)) s1 1 (XI170 XI0).l θ δ ε Q_FSf +
          (multiCheckpointROMErrorNumerator (((XI170 XI0).k * (Q_FSf + 1)) * Pf) ((XI170 XI0).k * (Q_FSf + 1)) Vf Q_Hf : ℝ≥0∞) *
            (Nat.card DgJ8 : ℝ≥0∞)⁻¹ +
          ((Q_Hf + Vf + T) ^ 2 : ℝ≥0∞) / (2 * (Nat.card DgJ8 : ℝ≥0∞))) := by
  have hFx := hFix_fri' (C := CS) (hn := J8Shape.hn32_of_shape hsh) (hg := hgates) (hsh := hsh) (s := s1) (dd := 1)
    (l := (XI170 XI0).l) (G := G) (L := LV) (Dg := DgJ8) (enc := encK) (hk := hk) (hdom := hdomS) (θ := θ) (δ := δ) (ε := ε)
    (hε := hε) (hfb := hfb) (hN := hN) (hδ := hδ) (hcol := hcol) (decS := decS) (decode := decode) (model := model)
    (guards := guards) (localAccepts := localAccepts) (hlocal := hlocal)
    (HfOf := HfOf skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k))
    (FSOf := FSM decZ ROM)
    (FSfOf := FSfOf skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k) fkOf frOf)
    (vkOf := vkSide (XI170 XI0) skelsF (fun k : Key (Stmt' × Salt') PUnit (compiledRoundsK DgJ8 Op (SMS)) => Key.Challenge k))
    (hvk := fun gF => mkVKData'_vk_eq_vkSpec hspec hgates _)
    (zO := fun o => encZ (o.1, o.2.1)) (πO := fun o => o.2.2.1) (πFO := fun o => o.2.2.2.1) (sideOf := sideOf) (Aon := Aon)
    (instR := instTab) (instRF := instTabF) (Q_FS := Q_FSf) (Q_H := Q_Hf) (V := Vf) (P := Pf) (T := T) hFSf hHf htermf hconfigf hC1 hC2 hglue (by refine le_trans (le_of_eq (NockvmE2E.Exec.E2EOnline.pr_triple_congr _ _ _ _ _ ?_)) hcoll; intro g gF o; rcases o with _ | o <;> exact Iff.rfl)
  refine exec_e2e_J8V' XI0 hsh hshX D hdk R hT hσ hfree tp hchips hnum0 I0 I Ifin m0 mf fkOf frOf hl encZ decZ hz hS hlink hids
    hmask hnumeralOk hjet hgates Aon Q_FS Q_H V Pn hQFS hQH hV hFS hHq hterm hconfig _ ?_
  refine le_trans (le_of_eq (NockvmE2E.Exec.E2EOnline.pr_triple_congr _ _ _ _ _ ?_)) hFx
  intro g gF o
  rcases o with _ | ⟨z, salt, π, πF, w⟩ <;> exact Iff.rfl


end NockvmE2E.Exec.E2EJ8V

#print axioms NockvmE2E.Exec.E2EJ8V.exec_e2e_J8V'''
