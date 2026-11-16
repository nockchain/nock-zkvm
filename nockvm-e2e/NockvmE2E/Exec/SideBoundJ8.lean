/-
J-8 recovery.  `hglue_J8'` has the statement of `hglue_J8` (HFixJ8V5) verbatim (same notation block) and is proved by the
single application `hglue_F (F := famJ8)` (SideBoundF): the generic statement specialises to the statement
(`j8ShapeOk = shapeOkF famJ8` is `rfl`; `FSOf := FSM decZ ROM`).
-/
import NockvmE2E.Exec.SideOnlineRFri
import NockvmE2E.Exec.SideOnlineRJ8
import NockvmE2E.Exec.HCollJ8
import NockvmE2E.Exec.E2EOnlineP
import NockvmE2E.Exec.SideGlue20
import NockvmE2E.Exec.SideBoundF

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

namespace NockvmE2E.Exec.E2EJ8V
open NockvmE2E.Exec NockvmE2E.Exec.Tr NockvmE2E.Exec.J8Chips NockvmE2E.Exec.J8ChipsK NockvmE2E.Emit Nock.Emit NockvmE2E.J8 NockvmE2E.J8.TieJ8G
open NockvmE2E.J8.InstJ8W (sigmaX tabIdx)
open NockvmE2E.J8.TieJ8 (HopZero)
open NockvmE2E.Exec.E2EJ8P2 NockvmE2E.Exec.E2EJ8P
open NockvmE2E.Exec.E2ELR NockvmE2E.Exec.InstGen NockvmE2E.Lift NockvmE2E.Lift.Alternating NockvmE2E.Rap
open NockvmE2E.J8.InstJ8 (Φ0)

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
local notation "CS" => (SideCfg.mk (XI170 XI0) (NockvmE2E.Exec.SideInst.opIdxX (XI170 XI0)) (NockvmE2E.Exec.SideInst.ptKX (XI170 XI0)))
set_option hygiene false in
local notation "SMS" => NockvmE2E.Merkle.SideMerkle.bMask (S := KC) s1 1 (XI170 XI0).l LV DgJ8 encK
set_option hygiene false in
local notation "TabM[" St "," Sa "]" => (∀ dd, succinctRange DgJ8 (OPN) (NQuery (merkleSkels (MC))) St Sa (MC) dd)
set_option hygiene false in
local notation "FSM" => FST XI0 (J8Shape.hn32_of_shape hsh) (PJ) (AJ) (R0P) (RestP) (RestVP) (EJ) I0 I Ifin 1 encK MDV LV
set_option hygiene false in
local notation "ROM" => (mdAppend (RM) (BM) (DA) (dsbC, dsmC s1 1 (XI170 XI0).l LV encK))

set_option hygiene false in
local notation "ZStmt'" => NockvmE2E.Exec.SideInst.SStmt (XI170 XI0)
set_option hygiene false in
local notation "ZSalt'" => (Statement × Salt)
set_option hygiene false in
local notation "ZOp" => OpenAll DgJ8 (merkleSkels (SMS))
set_option hygiene false in
local notation "Zskels" => NockvmE2E.Exec.SideInst.skelsSide (XI170 XI0)
set_option hygiene false in
local notation "ZmS" => NockvmE2E.Exec.SideInst.mSX (XI170 XI0)
set_option hygiene false in
local notation "ZptK" => NockvmE2E.Exec.SideInst.ptKX (XI170 XI0)
set_option hygiene false in
local notation "ZG" => NockvmE2E.Exec.SideInst.GX (XI170 XI0)
set_option hygiene false in
local notation "ZdecS" => NockvmE2E.Exec.SideInst.decSX (XI170 XI0)
set_option hygiene false in
local notation "Zdecode" => (id : OpenAll DgJ8 (merkleSkels (SMS)) → OpenAll DgJ8 (merkleSkels (SMS)))
set_option hygiene false in
local notation "Zmodel" => NockvmE2E.Exec.SideGlue13.modelSS (XI170 XI0) (J8Shape.hn32_of_shape hsh) (XI170 XI0).l (NockvmE2E.Exec.SideGlue20.dfltS (XI170 XI0) hgates hk (J8Shape.hn32_of_shape hsh))
set_option hygiene false in
local notation "Zguards" => (trueGuards _)
set_option hygiene false in
local notation "ZlocalAccepts" => (bLocal s1 1 (XI170 XI0).l ZmS ZG LV DgJ8 encK ZOp hdomS (fun st => stmtOf CS (J8Shape.hn32_of_shape hsh) (ZdecS st)) id)
set_option hygiene false in
local notation "ZfkOf" => (NockvmE2E.Exec.SideInst.fkOfX s1 (XI170 XI0).l LV (XI170 XI0) decZ (NockvmE2E.Exec.SideInst.ω0S s1 (XI170 XI0).l LV))
set_option hygiene false in
local notation "ZfrOf" => (NockvmE2E.Exec.SideInst.frOfX s1 (XI170 XI0).l LV (XI170 XI0) (NockvmE2E.Exec.SideInst.ω0S s1 (XI170 XI0).l LV))
set_option hygiene false in
local notation "ZsideOf" => (fun g o => NockvmE2E.Exec.SideInst.sideOfX s1 (XI170 XI0).l LV (XI170 XI0) (FSM decZ ROM g) encZ o)

open ProximityGap CoreDefinitions NockvmE2E.Succ.Numbers NockvmE2E.Merkle.Reduction NockvmE2E.Merkle.Good SoundnessWorld
  SoundnessCoupling BadBound MerkleTreeMultiExtractability NockvmE2E.Merkle.SideMerkle in
set_option maxHeartbeats 4000000 in
/-- **`hglue_J8'`**: the statement of `hglue_J8` (HFixJ8V5), proved by `hglue_F (F := famJ8)` (generic `SideBoundF.hglue_F`). -/
theorem hglue_J8' {Statement Salt W : Type} [DecidableEq Statement] [DecidableEq Salt] [Finite Statement] [Finite Salt] (hl : XI0.l = 170) (encZ : Statement × Salt → List ℕ) (decZ : List ℕ → Statement × Salt) (hz : ∀ x, decZ (encZ x) = x) (hgates : setupGates (XI170 XI0) = true) (hk : 1 ≤ (XI170 XI0).k) (hdomS : 2 ^ (∑ j, (s1 j).val) * (1 : ℕ+).val ≤ 2 ^ (XI170 XI0).nD) :
    ∀ (g : TabM[Statement, Salt]) (gF : ∀ d', succinctRange DgJ8 ZOp (NQuery Zskels) ZStmt' ZSalt' (SMS) d') (o : Statement × Salt × FlatProof × FixProof × W),
      NockvmE2E.Exec.SideOnlineR.FixFailR (XI170 XI0) (vkSide (XI170 XI0) Zskels (fun k : Key (ZStmt' × ZSalt') PUnit (compiledRoundsK DgJ8 ZOp (SMS)) => Key.Challenge k) gF)
        (HfOf Zskels (fun k : Key (ZStmt' × ZSalt') PUnit (compiledRoundsK DgJ8 ZOp (SMS)) => Key.Challenge k) gF) (FSM decZ ROM g) (FSfOf Zskels (fun k : Key (ZStmt' × ZSalt') PUnit (compiledRoundsK DgJ8 ZOp (SMS)) => Key.Challenge k) ZfkOf ZfrOf gF) (encZ (o.1, o.2.1)) o.2.2.1 o.2.2.2.1 →
        ZdecS (ZsideOf g o).1 = ⟨[], fixCtx o.2.2.1 (zetaOf (XI170 XI0) (FSM decZ ROM g) (encZ (o.1, o.2.1)) o.2.2.1), o.2.2.2.1.vF⟩ ∧
        (∀ j, canon3 (ZptK (ZdecS (ZsideOf g o).1).ctx j)) ∧
        (∀ j i, smoothDomain (XI170 XI0).nD (J8Shape.hn32_of_shape hsh) i ≠ SideCfg.pt CS (ZdecS (ZsideOf g o).1) j) ∧
        (∀ j o', j < (fixCols (XI170 XI0)).size → o' < fixLen (XI170 XI0) (fixCols (XI170 XI0))[j]! →
          canon3 (o.2.2.2.1.vF[j]!)[o']! ∧
          canon3 (fixTrue (XI170 XI0) (fixCols (XI170 XI0))[j]!
            ((openPts (XI170 XI0) (zetaOf (XI170 XI0) (FSM decZ ROM g) (encZ (o.1, o.2.1)) o.2.2.1))[o']!))) ∧
        (¬ VKcoll (XI170 XI0) (vkSide (XI170 XI0) Zskels (fun k : Key (ZStmt' × ZSalt') PUnit (compiledRoundsK DgJ8 ZOp (SMS)) => Key.Challenge k) gF)
            (HfOf Zskels (fun k : Key (ZStmt' × ZSalt') PUnit (compiledRoundsK DgJ8 ZOp (SMS)) => Key.Challenge k) gF) o.2.2.2.1 →
          ∃ p, tabEval (tabK gF) (succinctVerifyK Zguards (merkleCheck (merkleSkels (SMS)) Zmodel Zdecode) ZlocalAccepts
            ((ZsideOf g o).1, (ZsideOf g o).2.1) (ZsideOf g o).2.2) = some (some p)) :=
  NockvmE2E.Exec.SideBoundF.hglue_F (F := NockvmE2E.Exec.ShapeF.famJ8) (XI := XI170 XI0) (hsh := hsh) (hgates := hgates) (hk := hk)
    (FSOf := fun g => FSM decZ ROM g) (encZ := encZ) (decZ := decZ) (hz := hz) (hdomS := hdomS)

end NockvmE2E.Exec.E2EJ8V

#print axioms NockvmE2E.Exec.E2EJ8V.hglue_J8'
