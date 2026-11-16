/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/HokJ9AG9.lean

* `V := valId nA rA sv`, `D := denJ9A tC p rA V`, `hD := denOK9_valId` (`hsv0`, `hsvn`, `64·(nA+nS) ≤ p`).
  * `hW`, `hS` are stated for EVERY `D`, `Rg` (`provP_walkV9` / `provP_split` are `D`-free).
  * Shares (each presence case is one share, cased on chip satisfaction at S9, R8): `svcAx_present` (axis chip satisfied,
    `provP_service9`), `svcAx_absent` (`pX = []`), `walkShareV9` (atom walk satisfied, `provP_walkV9`), `provP_nil`
    (walk / split absent), the split present share is `splitSV_ne0` / `splitSV_lt` / `provP_split` / `split_entry7`.
  * Corollaries: `_present` (all three present: the HokJ9AX9 statement re-derived through the generic), `_axAbsent`,
    `_spAbsent`, `_wAbsent`. -/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HokJ9AX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.HokJ9AG9

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8 (frameJ8 toVSQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 pad8_entry7 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX9 (DenOKX9)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkX9
open Nock.NockVMROM.Thm54.VclL.Handle.TeleX9
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeX9
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeX9
open Nock.J9A.NounAx (valId)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX9 (RecOK9 RecOK9I)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB provK Accepted)
open Nock.Jet.RapJetJ8 (jRd jProv jCons rowsJ)
open Nock.Jet.PinJ8 (pinKey pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.Atoms (val B)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB hDenB_extB)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (hReg_of_pinR denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKIJ8 (hDenB'_extB)
open Nock.NockVMROM.Thm54.VclL.Handle.ChainUJ8 (hchain_of_servedU agree_atomU)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ atomChipHQL_sat atomChipHQL_bind)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomServedQ (consumeServedQ_of_balance)
open Nock.NockVMROM.Thm54.VclL.Handle.HokLJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenJ9A (denJ9A denJ9A_ne3 denOK9_split)
open Nock.NockVMROM.Thm54.VclL.Handle.ProvNewX9 (splitSV provP_split provP_walkV9)
open Nock.NockVMROM.Thm54.VclL.Handle.ProvKindsX9 (denK_three agree_some provP9I_off incProv9)
open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ9AX9 (split_entry7)

open Nock.NockVMROM.Thm54.VclL.Handle.SubJ9A (NotJ7 notJ7_of_tag notJ7_of_zero)
open Nock.NockVMROM.Thm54.VclL.Handle.DenJ9A (denOK9_valId splitSV_ne0 splitSV_lt)
open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ9AX9 (axTag_entry7)
open Nock.NockVMROM.Thm54.VclL.Handle.AxisCoreX9 (recOK9I_p)

noncomputable section

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **S8 outer, generic in the axis, atom-walk and split shares** (see the module header). -/
theorem acceptsJ9A_holdsN_finalLGG [CharP K p] [CharP 𝕂′ p]
    (χ : Coins frameJ8 K) (pv : ℕ → ZMod p)
    -- the compute trace (the J-9 A twin chip)
    {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
    {P : Fin (computeChipVCLHX9 hn nodes b δ (chalVJ8 b χ) pv orbit).rap.w → (ZMod p)[X]}
    {α γ seed : K}
    (C : XCtx hn nodes b δ (chalVJ8 b χ) pv orbit P α γ seed) (hpG : p = Nock.Atoms.p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pv) provs ext)
    -- the cell table
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    -- the J-8 walk
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    -- the J chip and its public registry
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JGenJ8.JChipOK δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ} {rk : ℕ → ℕ × ℕ}
    -- the atom table
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (QL : Fin (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hQA : QA = toHQ δ b hnA nodesA orbitA chalsA pubsA QL)
    (hsatL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QL)
    (hbindL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QL)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    -- the compute IO events and counts
    (hout : ∀ bl, bl ≠ .s → ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext bl).length < p)
    -- the cell validity balance (two providers) and the encoder
    (hnpC : nC < ringChar (ZMod p)) (hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3) ≠ 0)
    (γV ρV : 𝕂′) (hokC : ChalsOK δ chalsC γV ρV 11)
    (reqsC : List (Fin 5 → 𝕂′)) (xsC : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsumC : (reqsC.map fun r => (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ r)⁻¹).sum =
      Quad.mk _ (pubsC 0) (pubsC 1) + (xsC.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1)⁻¹).sum)
    (houtC : (γV, ρV) ∉ FiniteIO.IOFailureEventW
      (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (SVFrame.liftWts (cellVRecords δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) ++ xsC))
    (hxneC : ∀ x ∈ xsC, FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1 ≠ 0)
    (hcountC : (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).length < p)
    (vp : List (VKey 𝕂′))
    (hxC : ∀ x ∈ xsC, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p))
    (E : Noun → FP 𝕂′)
    (hconsE : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) (E a) (E b))
    (hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) E)
    {rA : ℕ → ARow} (hvp : AtomLeaves E vp (extB p rA))
    (hEinj : WalkKJ8.EncInj2 E (cellTableOf δ b nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) (extB p rA))
    -- the J-8 walk's provider premises (`provOK_p`, `provAx_p`)
    (hkW : 1 ≤ kroots) (hknW : kroots ≤ nW) (hkpW : kroots + nW < ringChar (ZMod p))
    (hXW : KeysExported (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))).X)
    (hHXW : ∀ j < nW, ∃ c ∈ (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)),
      (natOf ((walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j).trace WChip.idx),
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) false,
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) true) = exportRecK c.b0)
    (houtW : (chalsW 0, chalsW 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))))
    -- the J chip's public checks and the registry pin
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hnd : regs.Nodup) (hidx : ∀ id ∈ regs, idx id < p) (hrk : ∀ id ∈ regs, rk id ≠ (0, 0))
    (hlt : ∀ id ∈ regs, (rk id).1 < ringChar (ZMod p) ∧ (rk id).2 < ringChar (ZMod p) ∧ idx id < ringChar (ZMod p))
    (hpinC : ∀ id ∈ regs, ClaimVS.claimVec δ (E (Nock.Jet.Autogen.compile p (Rt id))) (idx id : ZMod p)
      ((rk id).1 : ZMod p) ((rk id).2 : ZMod p) ∈ reqsC)
    (hinjE : ∀ id ∈ regs, ∀ d ∈ decodedNouns2 ((cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) (extB p rA),
      E (Nock.Jet.Autogen.compile p (Rt id)) = E d → Nock.Jet.Autogen.compile p (Rt id) = d)
    -- the atom table's inc heads (A-2) and its export balance
    (hRA : ∀ k : Fin nA, Reads (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, SmallU (rA k)) (hidxA : ∀ k : Fin nA, (rA k).idx = k)
    (hrn : ∀ k, nA ≤ k → (rA k).inc = 0) (hB : AtomChipHQ.LimbsBounded rA) (hwRA : ∀ j, (rA j).wR ≤ 1)
    (wreqs : List (Fin 5 → K))
    (hbalA : Quad.mk _ (pubsA CellHQ.pubHQ) (pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk _ (pubsA AtomChipHQ.pubC) (pubsA (AtomChipHQ.pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r => (compress (AtomServedQ.acoins δ chalsA) r)⁻¹).sum)
    (houtA : ((AtomServedQ.acoins δ chalsA).gamma, (AtomServedQ.acoins δ chalsA).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).map
        (liftRec (K := K) (L := 𝕂′))) (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b nodesA orbitA chalsA pubsA QA)))
    (hcountA : (AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).length < p)
    (hnpA : nA < p) (hzA : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    -- J-9 A: `hden2`, `TopNZ`, the id window
    (hden2 : ∀ j l, Denotes rA j l → p ≤ val l → j < nA) (hTout : ∀ j, nA ≤ j → (rA j).wR = 0 → (rA j).aR ≠ 0)
    -- the generic shares: split values `sv`, atom walk `pW`, axis `pX`, split `pS`
    (sv : ℕ → Option ℕ) {nS : ℕ}
    (hsv0 : ∀ s v, sv s = some v → v ≠ 0) (hsvn : ∀ s v, sv s = some v → s < nS)
    (hnAS : 64 * (nA + nS) ≤ p)
    {pW pX pS : List ((Fin 8 → K) × K)}
    (h7W : ∀ q ∈ pW, q.1 ⟨7, by norm_num⟩ = 0) (h7X : ∀ q ∈ pX, NotJ7 (p := p) q.1)
    (h7S : ∀ q ∈ pS, q.1 ⟨7, by norm_num⟩ = 0)
    (hW : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry),
      ProvP (p := p) (K := K) (RecOK9 D (valId nA rA sv) Rg combN) .s pW)
    (hS : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry),
      ProvP (p := p) (K := K) (RecOK9 D (valId nA rA sv) Rg combN) .s pS)
    (hsvc : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), DenOKX9 p D (valId nA rA sv) →
      ProvP (p := p) (K := K) (RecOK9I D (valId nA rA sv) Rg combN) .p (provs .p) →
      ProvP (p := p) (K := K) (RecOK9I D (valId nA rA sv) Rg combN) .s
        (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA)) →
      ∀ pJ : List ((Fin 8 → K) × K), ProvP (p := p) (K := K) (RecOK9I D (valId nA rA sv) Rg combN) .s pJ →
      (∀ c ∈ ext .s, c ∈ (pJ ++ pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++ pW ++ pX ++ pS).map Prod.fst) →
      (∀ c ∈ ext .p, c ∈ (provs .p).map Prod.fst) →
      ProvP (p := p) (K := K) (RecOK9I D (valId nA rA sv) Rg combN) .s
        (pJ ++ pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++ pW ++ pX ++ pS))
    -- the wiring
    {eA : List (Fin 8 → K)}
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hprovS : provs .s = jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++
      (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++ pW ++ pX ++ pS))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ eA ++ jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    -- the compute walk, its events and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0)
      (stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0))).trip) * α)
    (hα : α ∉ tileSet (foOf9 (rowsWX9 (fun r => CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)
      (fun r => stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)))) n)
    (hw : (α, γ) ∉ cwEvent9 (K := K) (rowsWX9 (fun r => CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)
      (fun r => stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r))) n)
    (hreal : (stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0)).sem.isChain = false)
    (x : P8PublicClaim)
    (hs : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xS) = some x.subject)
    (hf : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xF) = some x.formula)
    (he : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xE) = some x.result) :
    Nock.Jet.HoldsN x := by
  have hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA := by
    rw [hQA]; exact atomChipHQL_sat δ b hnA nodesA orbitA chalsA pubsA QL hsatL
  have hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA := by
    rw [hQA]; exact atomChipHQL_bind δ b hnA nodesA orbitA chalsA pubsA QL hbindL
  have hp63 : 2 ^ 63 + 1 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hok : ∀ j, (rA j).inc = 1 → AtomChipHQ.ChainOK rA j := by
    have hcs := consumeServedQ_of_balance δ b hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA wreqs
      hbalA houtA hcountA
    subst hQA
    exact hok_of_gatesL (by omega) hsatL hbindL hinjA hadjA hRA hsA hidxA hrn hB hwRA hcs
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hq : 2 ^ 63 < p := by omega
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; exact hq
  have hp2 : 2 < p := by omega
  have hp5 : 5 < p := by omega
  have hp32 : 2 ^ 32 < p := by omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  set tC := (cellTableOf δ b nodesC orbitC chalsC pubsC
    (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0) with htC
  -- the J-9 A denotation
  set V := valId nA rA sv with hV
  set D := denJ9A tC p rA V with hDdef
  have hD3 : ∀ v, denK tC (extB p rA) (3, v) = none := denK_three tC (extB p rA)
  have hag : ∀ k : HX, k.1 ≠ 3 → D k = denK tC (extB p rA) k := fun k hk => denJ9A_ne3 tC p rA V hk
  have hT : TopNZ rA := AtomLeavesBJ8.topNZ_of_gates hsatA hRA hTout
  have hD : DenOKX9 p D V := denOK9_valId tC p nS hden2 hT hsv0 hsvn hnAS
  -- the cell table: two-provider acceptance, `x` / `p` providers
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b hnC nodesC orbitC chalsC pubsC QC hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b hnC nodesC orbitC chalsC pubsC QC hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b hnC nodesC orbitC chalsC pubsC _ hF' hq' hzC hsatC0 hbindC0
    hinjC hadjC hnpC γV ρV hokC reqsC xsC hsumC houtC hxneC hcountC vp hxC hvp0
  have htbC : (cellTableOf δ b nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).length ≤ ringChar (ZMod p) := by
    simp only [cellTableOf, List.length_ofFn]; exact hnpC.le
  have hXo := ProvXJ8.provOK_x δ b hnC nodesC orbitC chalsC pubsC hp2 hq' hzC QC hsatC hbindC hinjC hadjC hnpC γV ρV hokC
    reqsC xsC hsumC houtC hxneC hcountC vp hxC hvp0 E hconsE hE (extB p rA) hvp Rg (fun _ _ => (0, 0))
  have hPo := WalkKJ8.provOK_p δ kroots b hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hinjW hadjW hkW hknW hkpW hq'
    hconsE hE htabC hvp hEinj htbC hXW hHXW houtW Rg (fun _ _ => (0, 0))
  have hXp : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .x (provs .x) := by
    rw [hprovX]; exact provP9I_off hD3 hag (by decide) hXo
  have hPp : ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .p (provs .p) := by
    rw [hprovP]; exact provP9I_off hD3 hag (by decide) hPo
  have hPax : ProvP (p := p) (K := K) AxOK .p (provs .p) := by
    rw [hprovP]
    exact WalkKJ8.provAx_p δ kroots b hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hinjW hadjW hkW hknW
      hkpW hq' houtW
  -- the registry: `hclaim` from the cell side, `hReg` from the pin, transferred to `D`
  have hvpr : ∀ k ∈ vp, k.2.1 < ringChar (ZMod p) ∧ k.2.2.1 < ringChar (ZMod p) ∧ k.2.2.2 < ringChar (ZMod p) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hvp0 k hk
    exact ⟨by omega, by omega, h3⟩
  have hclaim := Nock.Jet.PinJ8.regClaims_provided δ b hnC nodesC orbitC chalsC pubsC
    (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC) hF' hsatC0 hbindC0 hinjC hadjC γV ρV hokC
    reqsC xsC hsumC houtC hxneC hcountC vp hxC hvpr (Ef := fun id => E (Nock.Jet.Autogen.compile p (Rt id)))
    hpinC hlt
  have hRegP := fun (hAcc : Accepted Rt regs ids (rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)) hpin =>
    ProvKindsX9.hReg_transfer3 hD3 hag _ _ _ _ (hReg_of_pinR hrc hq hconsE hE htabC hvp hAcc hnd hidx hpin hclaim
      hrk hinjE)
  -- the atom table: the inc heads at `D`
  have hwL : ∀ k : Fin nA, (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k).trace Cell.wL = 0 :=
    fun k => (atom_g23 hsatA k).1
  have hchain := hchain_of_servedU δ b hnA nodesA orbitA chalsA pubsA hq' QA hsatA hbindA hinjA hadjA wreqs hbalA
    houtA hcountA hRA hsA hidxA hwL hrn hB hwRA hok
  have hI := incProv9 (V := V) (Rg := Rg) (comb := combN) hp5 hq hsatA hRA hsA hidxA (D := D)
    (fun v => by rw [hag _ (by simp)]; rfl)
    (fun j l hd hl => by rw [hag _ (by simp)]; exact hDenB_extB tC p rA j l hd hl)
    (fun j X hX => by rw [hag _ (by simp)] at hX; exact hDenB'_extB tC p rA j X hX) hchain hpG
  -- the claim handles at `D`
  have hs' := agree_some hD3 hag hs
  have hf' := agree_some hD3 hag hf
  have he' := agree_some hD3 hag he
  have hcJ : Nock.Jet.RapJetJ8.coinsJ δ (chalsJJ8 χ) = coinsCV b δ (chalVJ8 b χ) :=
    (coinsJ_J8 δ χ).trans (coinsCV_J8 δ b χ).symm
  exact FinalJ9AX9.acceptsJ9A_holdsN_EIG9 C hpG hbal nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ hJk hcJ
    (pad8_entry7 _) h7W h7S h7X hprovS hextS hextX hout houtS hcount hRg hD hXp hPp hPax hI (hW D Rg) (hS D Rg)
    (hsvc D Rg hD hPp hI) hlay hsmall huniq hTpl hRegP hseed hα hw hreal x hs' hf' he'


/-! ## The shares (one per presence case; S9 cases on chip satisfaction, R8) -/

theorem provP_nil {Φ : List ℕ × Bal → Prop} {bl : Bal} :
    ProvP (p := p) (K := K) Φ bl ([] : List ((Fin (mOf bl) → K) × K)) :=
  fun q hq => by cases hq

/-- **Axis share, chip PRESENT**: the service step `hsvc` from `AxisSoundX9.provP_service9`. -/
theorem svcAx_present (hpG : p = Nock.Atoms.p)
    {hX nX : ℕ} (hnX : 0 < nX) (nodesX : Fin nX → ZMod p) (orbitX : StrictOrbitDomain (ZMod p) 3 hX)
    (chalsX pubsX : ℕ → K)
    (QX : Fin (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.w → (ZMod p)[X])
    (hsatX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.Satisfies QX)
    (hbindX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).BindsPreprocessing QX)
    (hinjX : Function.Injective nodesX)
    (hadjX : ∀ (i : Fin nX) (hi : (i : ℕ) + 1 < nX), nodesX ⟨(i : ℕ) + 1, hi⟩ = nodesX i * orbitX.ω)
    {V : ℕ → Option ℕ} {pI pW pS : List ((Fin 8 → K) × K)} {extS : List (Fin 8 → K)}
    {pP : List ((Fin (mOf .p) → K) × K)} {extP : List (Fin (mOf .p) → K)}
    (hW : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pW)
    (hS : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pS)
    (hsubS : ∀ i : Fin nX,
      AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ extS)
    (hsubP : ∀ i : Fin nX, (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i).trace AxisChipJ9.z1a = 0 →
      AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ extP) :
    ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), DenOKX9 p D V →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .p pP →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pI →
      ∀ pJ : List ((Fin 8 → K) × K), ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pJ →
      (∀ c ∈ extS, c ∈ (pJ ++ pI ++ pW ++ AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX ++ pS).map Prod.fst) →
      (∀ c ∈ extP, c ∈ pP.map Prod.fst) →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s
        (pJ ++ pI ++ pW ++ AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX ++ pS) :=
  fun D Rg hD hPp hI pJ hJp hsvS hsvP =>
    AxisSoundX9.provP_service9 δ b hnX nodesX orbitX chalsX pubsX QX hpG hsatX hbindX hinjX hadjX Rg hD
      hJp hI (hW D Rg) (hS D Rg) hsvS hsubS (fun a b' c d hr => recOK9I_p a b' c d hr) hsvP hsubP hPp

/-- **Axis share, chip ABSENT** (`pX = []`): the plain append. -/
theorem svcAx_absent {V : ℕ → Option ℕ} {pI pW pS : List ((Fin 8 → K) × K)} {extS : List (Fin 8 → K)}
    {pP : List ((Fin (mOf .p) → K) × K)} {extP : List (Fin (mOf .p) → K)}
    (hW : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pW)
    (hS : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D V Rg combN) .s pS) :
    ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), DenOKX9 p D V →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .p pP →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pI →
      ∀ pJ : List ((Fin 8 → K) × K), ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s pJ →
      (∀ c ∈ extS, c ∈ (pJ ++ pI ++ pW ++ [] ++ pS).map Prod.fst) →
      (∀ c ∈ extP, c ∈ pP.map Prod.fst) →
      ProvP (p := p) (K := K) (RecOK9I D V Rg combN) .s (pJ ++ pI ++ pW ++ [] ++ pS) :=
  fun D Rg _ _ hI pJ hJp _ _ =>
    ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr ⟨ServiceJ8.provP_append.mpr ⟨hJp, hI⟩,
      ProvNewX9.provP_I (hW D Rg)⟩, fun q hq => by cases hq⟩, ProvNewX9.provP_I (hS D Rg)⟩

/-- **Atom-walk share, chip PRESENT**: `provP_walkV9` for every `sv`, `D`, `Rg`, from the atom table's acceptance. -/
theorem walkShareV9 [CharP K p] [CharP 𝕂′ p] (hpG : p = Nock.Atoms.p)
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    {rA : ℕ → ARow}
    (hRA : ∀ k : Fin nA, Reads (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, SmallU (rA k)) (hidxA : ∀ k : Fin nA, (rA k).idx = k)
    (hrn : ∀ k, nA ≤ k → (rA k).inc = 0) (hB : AtomChipHQ.LimbsBounded rA) (hwRA : ∀ j, (rA j).wR ≤ 1)
    (hnpA : nA < p) (hzA : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    (krootsV : ℕ) {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → ZMod p)
    (orbitV : StrictOrbitDomain (ZMod p) 3 hV) (chalsV pubsV : ℕ → K)
    (QV : Fin (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.w → (ZMod p)[X])
    (hsatV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.Satisfies QV)
    (hbindV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).BindsPreprocessing QV)
    (hinjV : Function.Injective nodesV)
    (hadjV : ∀ (i : Fin nV) (hi : (i : ℕ) + 1 < nV), nodesV ⟨(i : ℕ) + 1, hi⟩ = nodesV i * orbitV.ω)
    (hyV : chalsV 2 = chalsA 2 ∧ chalsV 3 = chalsA 3)
    (hkV : 1 ≤ krootsV) (hknV : krootsV ≤ nV) (hkpV : krootsV + nV < ringChar (ZMod p))
    (hseedsV : AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsV 2) (chalsV 3)) (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    (hXV : KeysExported (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV)).X)
    (hHXV : ∀ j < nV, ∃ c ∈ (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)),
      (natOf ((walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j).trace WChip.idx), childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) false, childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) true) = exportRec c.b0)
    (houtV : (chalsV 0, chalsV 1) ∉ walkEvent (algebraMap (ZMod p) K δ) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV))) :
    ∀ (sv : ℕ → Option ℕ) (D : HX → Option Noun) (Rg : Nock.Jet.Registry),
      ProvP (p := p) (K := K) (RecOK9 D (valId nA rA sv) Rg combN) .s
        (pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV)) := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp63 : 2 ^ 63 + 1 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq : 2 ^ 63 < p := by omega
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; exact hq
  have hF' := GeneratedField.primeFieldElems_zmod p
  have hTA := AtomChipHQ.atomTable_accepts δ b hnA nodesA orbitA chalsA pubsA hF' hq' hzA QA hsatA hbindA hinjA
    hadjA (by rw [hrc]; exact hnpA) hservedA []
  have htab : TableAccepts (Quad.mk (algebraMap (ZMod p) K δ) (chalsV 2) (chalsV 3)) (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)) [] := by rw [hyV.1, hyV.2]; exact hTA
  have hzV : Quad.mk (algebraMap (ZMod p) K δ) (chalsV 2) (chalsV 3) ≠ 0 := by rw [hyV.1, hyV.2]; exact hzA
  have hser := cellTable_serial δ b hnA nodesA orbitA chalsA pubsA _
    (AtomChipHQ.atomChipHQ_restrict_cell_sat δ b hnA nodesA orbitA chalsA pubsA QA hsatA) hF'
    (AtomChipHQ.atomChipHQ_restrict_bind δ b hnA nodesA orbitA chalsA pubsA QA hbindA) hinjA hadjA
    (by rw [hrc]; exact hnpA)
  have htb : (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)).length ≤ ringChar (ZMod p) := by
    simp only [cellTableOf, List.length_ofFn]; rw [hrc]; exact hnpA.le
  have htl : (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)).length = nA := by
    simp only [cellTableOf, List.length_ofFn]
  have hagA : ∀ c ∈ (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)).map (·.b0), AgreeRow c (rA c.idx) :=
    fun c hc => (agree_atomU hq hsatA hRA hsA hidxA hB (fun k => hwRA k) c hc).2
  intro sv D Rg
  exact provP_walkV9 δ krootsV b hnV nodesV orbitV chalsV pubsV QV hsatV hbindV hinjV hadjV hkV hknV
    hkpV hq' hzV htab hseedsV hXV hHXV houtV hser htb hagA htl sv D Rg

/-- **All three shares PRESENT**: the `HokJ9AX9.acceptsJ9A_holdsN_finalLG` statement, through the generic. -/
theorem acceptsJ9A_holdsN_present [CharP K p] [CharP 𝕂′ p]
    (χ : Coins frameJ8 K) (pv : ℕ → ZMod p)
    -- the compute trace (the J-9 A twin chip)
    {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
    {P : Fin (computeChipVCLHX9 hn nodes b δ (chalVJ8 b χ) pv orbit).rap.w → (ZMod p)[X]}
    {α γ seed : K}
    (C : XCtx hn nodes b δ (chalVJ8 b χ) pv orbit P α γ seed) (hpG : p = Nock.Atoms.p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pv) provs ext)
    -- the cell table
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    -- the J-8 walk
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    -- the J chip and its public registry
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JGenJ8.JChipOK δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ} {rk : ℕ → ℕ × ℕ}
    -- the atom table
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (QL : Fin (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hQA : QA = toHQ δ b hnA nodesA orbitA chalsA pubsA QL)
    (hsatL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QL)
    (hbindL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QL)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    -- the atom walk
    (krootsV : ℕ) {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → ZMod p)
    (orbitV : StrictOrbitDomain (ZMod p) 3 hV) (chalsV pubsV : ℕ → K)
    (QV : Fin (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.w → (ZMod p)[X])
    (hsatV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.Satisfies QV)
    (hbindV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).BindsPreprocessing QV)
    (hinjV : Function.Injective nodesV)
    (hadjV : ∀ (i : Fin nV) (hi : (i : ℕ) + 1 < nV), nodesV ⟨(i : ℕ) + 1, hi⟩ = nodesV i * orbitV.ω)
    -- the axis chip (present)
    {hX nX : ℕ} (hnX : 0 < nX) (nodesX : Fin nX → ZMod p) (orbitX : StrictOrbitDomain (ZMod p) 3 hX)
    (chalsX pubsX : ℕ → K)
    (QX : Fin (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.w → (ZMod p)[X])
    (hsatX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.Satisfies QX)
    (hbindX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).BindsPreprocessing QX)
    (hinjX : Function.Injective nodesX)
    (hadjX : ∀ (i : Fin nX) (hi : (i : ℕ) + 1 < nX), nodesX ⟨(i : ℕ) + 1, hi⟩ = nodesX i * orbitX.ω)
    -- the split chip (present)
    {hS nS : ℕ} (hnS : 0 < nS) (nodesS : Fin nS → ZMod p) (orbitS : StrictOrbitDomain (ZMod p) 3 hS)
    (chalsS pubsS : ℕ → K)
    (QS : Fin (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).rap.w → (ZMod p)[X])
    (hsatS : (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).rap.Satisfies QS)
    (hbindS : (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).BindsPreprocessing QS)
    (hinjS : Function.Injective nodesS)
    (hadjS : ∀ (i : Fin nS) (hi : (i : ℕ) + 1 < nS), nodesS ⟨(i : ℕ) + 1, hi⟩ = nodesS i * orbitS.ω)
    -- the wiring
    {eA : List (Fin 8 → K)}
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hprovS : provs .s = jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++
      (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++ pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV) ++
        AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX ++ SplitChipJ9.splitProvs b nodesS orbitS chalsS pubsS QS))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ eA ++ jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hsubS : ∀ i : Fin nX,
      AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ eA)
    (hsubP : ∀ i : Fin nX, (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i).trace AxisChipJ9.z1a = 0 →
      AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ ext .p)
    -- the compute IO events and counts
    (hout : ∀ bl, bl ≠ .s → ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext bl).length < p)
    -- the cell validity balance (two providers) and the encoder
    (hnpC : nC < ringChar (ZMod p)) (hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3) ≠ 0)
    (γV ρV : 𝕂′) (hokC : ChalsOK δ chalsC γV ρV 11)
    (reqsC : List (Fin 5 → 𝕂′)) (xsC : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsumC : (reqsC.map fun r => (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ r)⁻¹).sum =
      Quad.mk _ (pubsC 0) (pubsC 1) + (xsC.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1)⁻¹).sum)
    (houtC : (γV, ρV) ∉ FiniteIO.IOFailureEventW
      (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (SVFrame.liftWts (cellVRecords δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) ++ xsC))
    (hxneC : ∀ x ∈ xsC, FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1 ≠ 0)
    (hcountC : (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).length < p)
    (vp : List (VKey 𝕂′))
    (hxC : ∀ x ∈ xsC, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p))
    (E : Noun → FP 𝕂′)
    (hconsE : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) (E a) (E b))
    (hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) E)
    {rA : ℕ → ARow} (hvp : AtomLeaves E vp (extB p rA))
    (hEinj : WalkKJ8.EncInj2 E (cellTableOf δ b nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) (extB p rA))
    -- the J-8 walk's provider premises (`provOK_p`, `provAx_p`)
    (hkW : 1 ≤ kroots) (hknW : kroots ≤ nW) (hkpW : kroots + nW < ringChar (ZMod p))
    (hXW : KeysExported (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))).X)
    (hHXW : ∀ j < nW, ∃ c ∈ (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)),
      (natOf ((walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j).trace WChip.idx),
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) false,
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) true) = exportRecK c.b0)
    (houtW : (chalsW 0, chalsW 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))))
    -- the J chip's public checks and the registry pin
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hnd : regs.Nodup) (hidx : ∀ id ∈ regs, idx id < p) (hrk : ∀ id ∈ regs, rk id ≠ (0, 0))
    (hlt : ∀ id ∈ regs, (rk id).1 < ringChar (ZMod p) ∧ (rk id).2 < ringChar (ZMod p) ∧ idx id < ringChar (ZMod p))
    (hpinC : ∀ id ∈ regs, ClaimVS.claimVec δ (E (Nock.Jet.Autogen.compile p (Rt id))) (idx id : ZMod p)
      ((rk id).1 : ZMod p) ((rk id).2 : ZMod p) ∈ reqsC)
    (hinjE : ∀ id ∈ regs, ∀ d ∈ decodedNouns2 ((cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) (extB p rA),
      E (Nock.Jet.Autogen.compile p (Rt id)) = E d → Nock.Jet.Autogen.compile p (Rt id) = d)
    -- the atom table's inc heads (A-2) and its export balance
    (hRA : ∀ k : Fin nA, Reads (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, SmallU (rA k)) (hidxA : ∀ k : Fin nA, (rA k).idx = k)
    (hrn : ∀ k, nA ≤ k → (rA k).inc = 0) (hB : AtomChipHQ.LimbsBounded rA) (hwRA : ∀ j, (rA j).wR ≤ 1)
    (wreqs : List (Fin 5 → K))
    (hbalA : Quad.mk _ (pubsA CellHQ.pubHQ) (pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk _ (pubsA AtomChipHQ.pubC) (pubsA (AtomChipHQ.pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r => (compress (AtomServedQ.acoins δ chalsA) r)⁻¹).sum)
    (houtA : ((AtomServedQ.acoins δ chalsA).gamma, (AtomServedQ.acoins δ chalsA).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).map
        (liftRec (K := K) (L := 𝕂′))) (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b nodesA orbitA chalsA pubsA QA)))
    (hcountA : (AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).length < p)
    (hnpA : nA < p) (hzA : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    -- the atom walk
    (hyV : chalsV 2 = chalsA 2 ∧ chalsV 3 = chalsA 3)
    (hkV : 1 ≤ krootsV) (hknV : krootsV ≤ nV) (hkpV : krootsV + nV < ringChar (ZMod p))
    (hseedsV : AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsV 2) (chalsV 3)) (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    (hXV : KeysExported (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV)).X)
    (hHXV : ∀ j < nV, ∃ c ∈ (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)),
      (natOf ((walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j).trace WChip.idx), childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) false, childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) true) = exportRec c.b0)
    (houtV : (chalsV 0, chalsV 1) ∉ walkEvent (algebraMap (ZMod p) K δ) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV)))
    -- J-9 A: `hden2`, `TopNZ`, the id window
    (hden2 : ∀ j l, Denotes rA j l → p ≤ val l → j < nA) (hTout : ∀ j, nA ≤ j → (rA j).wR = 0 → (rA j).aR ≠ 0)
    (hnAS : 64 * (nA + nS) ≤ p)
    -- the compute walk, its events and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0)
      (stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0))).trip) * α)
    (hα : α ∉ tileSet (foOf9 (rowsWX9 (fun r => CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)
      (fun r => stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)))) n)
    (hw : (α, γ) ∉ cwEvent9 (K := K) (rowsWX9 (fun r => CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)
      (fun r => stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r))) n)
    (hreal : (stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0)).sem.isChain = false)
    (x : P8PublicClaim)
    (hs : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xS) = some x.subject)
    (hf : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xF) = some x.formula)
    (he : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xE) = some x.result) :
    Nock.Jet.HoldsN x := by
  have hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA := by
    rw [hQA]; exact atomChipHQL_sat δ b hnA nodesA orbitA chalsA pubsA QL hsatL
  have hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA := by
    rw [hQA]; exact atomChipHQL_bind δ b hnA nodesA orbitA chalsA pubsA QL hbindL
  have hp63 : 2 ^ 63 + 1 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp5 : 5 < p := by omega
  have hp32 : 2 ^ 32 < p := by omega
  have hW' := walkShareV9 hpG hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA hRA hsA hidxA hrn hB hwRA hnpA hzA hservedA krootsV hnV nodesV orbitV chalsV pubsV QV hsatV hbindV hinjV hadjV hyV hkV hknV hkpV hseedsV hXV hHXV houtV
  have hW0 := hW' (splitSV δ nA b hnS nodesS orbitS chalsS pubsS QS)
  have hS' : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D (valId nA rA (splitSV δ nA b hnS nodesS orbitS chalsS pubsS QS)) Rg combN) .s
      (SplitChipJ9.splitProvs b nodesS orbitS chalsS pubsS QS) :=
    fun D Rg => provP_split δ nA b hnS nodesS orbitS chalsS pubsS QS D Rg rA hp32 hsatS hbindS hinjS hadjS (by omega)
  have hsubS' : ∀ i : Fin nX, AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ ext .s :=
    fun i => by rw [hextS]; exact List.mem_append_left _ (List.mem_append_right _ (hsubS i))
  exact acceptsJ9A_holdsN_finalLGG (pX := AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX) χ pv C hpG
    hbal hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC kroots hnW nodesW orbitW chalsW pubsW QW
    hsatW hbindW hinjW hadjW nodesJ orbitJ pubsJ lay PJ hJk hnA nodesA orbitA chalsA pubsA QA QL hQA hsatL
    hbindL hinjA hadjA hout houtS hcount hnpC hzC γV ρV hokC reqsC xsC hsumC houtC hxneC hcountC vp hxC hvp0 E
    hconsE hE hvp hEinj hkW hknW hkpW hXW hHXW houtW hRg hlay hsmall huniq hTpl hnd hidx hrk hlt hpinC hinjE
    hRA hsA hidxA hrn hB hwRA wreqs hbalA houtA hcountA hnpA hzA hservedA hden2 hTout (splitSV δ nA b hnS
    nodesS orbitS chalsS pubsS QS) (splitSV_ne0 δ nA b hnS nodesS orbitS chalsS pubsS QS hp32 hsatS)
    (splitSV_lt δ nA b hnS nodesS orbitS chalsS pubsS QS) hnAS (pad8_entry7 _) (fun q hq => notJ7_of_tag (t :=
    5) hp5 (by norm_num) (by norm_num) (by omega) (axTag_entry7 b nodesX orbitX chalsX pubsX QX q hq))
    (split_entry7 b nodesS orbitS chalsS pubsS QS) hW0 hS' (svcAx_present hpG hnX nodesX orbitX chalsX pubsX QX
    hsatX hbindX hinjX hadjX hW0 hS' hsubS' hsubP) hprovX hextX hprovP hprovS hextS hseed hα hw hreal x hs hf
    he

/-- **Axis chip ABSENT** (`pX = []`; no axis chip, no `hsubS`/`hsubP`); split and atom walk present. -/
theorem acceptsJ9A_holdsN_axAbsent [CharP K p] [CharP 𝕂′ p]
    (χ : Coins frameJ8 K) (pv : ℕ → ZMod p)
    -- the compute trace (the J-9 A twin chip)
    {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
    {P : Fin (computeChipVCLHX9 hn nodes b δ (chalVJ8 b χ) pv orbit).rap.w → (ZMod p)[X]}
    {α γ seed : K}
    (C : XCtx hn nodes b δ (chalVJ8 b χ) pv orbit P α γ seed) (hpG : p = Nock.Atoms.p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pv) provs ext)
    -- the cell table
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    -- the J-8 walk
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    -- the J chip and its public registry
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JGenJ8.JChipOK δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ} {rk : ℕ → ℕ × ℕ}
    -- the atom table
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (QL : Fin (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hQA : QA = toHQ δ b hnA nodesA orbitA chalsA pubsA QL)
    (hsatL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QL)
    (hbindL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QL)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    -- the atom walk
    (krootsV : ℕ) {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → ZMod p)
    (orbitV : StrictOrbitDomain (ZMod p) 3 hV) (chalsV pubsV : ℕ → K)
    (QV : Fin (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.w → (ZMod p)[X])
    (hsatV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.Satisfies QV)
    (hbindV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).BindsPreprocessing QV)
    (hinjV : Function.Injective nodesV)
    (hadjV : ∀ (i : Fin nV) (hi : (i : ℕ) + 1 < nV), nodesV ⟨(i : ℕ) + 1, hi⟩ = nodesV i * orbitV.ω)
    -- the split chip (present)
    {hS nS : ℕ} (hnS : 0 < nS) (nodesS : Fin nS → ZMod p) (orbitS : StrictOrbitDomain (ZMod p) 3 hS)
    (chalsS pubsS : ℕ → K)
    (QS : Fin (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).rap.w → (ZMod p)[X])
    (hsatS : (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).rap.Satisfies QS)
    (hbindS : (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).BindsPreprocessing QS)
    (hinjS : Function.Injective nodesS)
    (hadjS : ∀ (i : Fin nS) (hi : (i : ℕ) + 1 < nS), nodesS ⟨(i : ℕ) + 1, hi⟩ = nodesS i * orbitS.ω)
    -- the wiring
    {eA : List (Fin 8 → K)}
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hprovS : provs .s = jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++
      (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++ pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV) ++
        [] ++ SplitChipJ9.splitProvs b nodesS orbitS chalsS pubsS QS))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ eA ++ jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    -- the compute IO events and counts
    (hout : ∀ bl, bl ≠ .s → ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext bl).length < p)
    -- the cell validity balance (two providers) and the encoder
    (hnpC : nC < ringChar (ZMod p)) (hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3) ≠ 0)
    (γV ρV : 𝕂′) (hokC : ChalsOK δ chalsC γV ρV 11)
    (reqsC : List (Fin 5 → 𝕂′)) (xsC : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsumC : (reqsC.map fun r => (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ r)⁻¹).sum =
      Quad.mk _ (pubsC 0) (pubsC 1) + (xsC.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1)⁻¹).sum)
    (houtC : (γV, ρV) ∉ FiniteIO.IOFailureEventW
      (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (SVFrame.liftWts (cellVRecords δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) ++ xsC))
    (hxneC : ∀ x ∈ xsC, FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1 ≠ 0)
    (hcountC : (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).length < p)
    (vp : List (VKey 𝕂′))
    (hxC : ∀ x ∈ xsC, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p))
    (E : Noun → FP 𝕂′)
    (hconsE : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) (E a) (E b))
    (hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) E)
    {rA : ℕ → ARow} (hvp : AtomLeaves E vp (extB p rA))
    (hEinj : WalkKJ8.EncInj2 E (cellTableOf δ b nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) (extB p rA))
    -- the J-8 walk's provider premises (`provOK_p`, `provAx_p`)
    (hkW : 1 ≤ kroots) (hknW : kroots ≤ nW) (hkpW : kroots + nW < ringChar (ZMod p))
    (hXW : KeysExported (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))).X)
    (hHXW : ∀ j < nW, ∃ c ∈ (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)),
      (natOf ((walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j).trace WChip.idx),
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) false,
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) true) = exportRecK c.b0)
    (houtW : (chalsW 0, chalsW 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))))
    -- the J chip's public checks and the registry pin
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hnd : regs.Nodup) (hidx : ∀ id ∈ regs, idx id < p) (hrk : ∀ id ∈ regs, rk id ≠ (0, 0))
    (hlt : ∀ id ∈ regs, (rk id).1 < ringChar (ZMod p) ∧ (rk id).2 < ringChar (ZMod p) ∧ idx id < ringChar (ZMod p))
    (hpinC : ∀ id ∈ regs, ClaimVS.claimVec δ (E (Nock.Jet.Autogen.compile p (Rt id))) (idx id : ZMod p)
      ((rk id).1 : ZMod p) ((rk id).2 : ZMod p) ∈ reqsC)
    (hinjE : ∀ id ∈ regs, ∀ d ∈ decodedNouns2 ((cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) (extB p rA),
      E (Nock.Jet.Autogen.compile p (Rt id)) = E d → Nock.Jet.Autogen.compile p (Rt id) = d)
    -- the atom table's inc heads (A-2) and its export balance
    (hRA : ∀ k : Fin nA, Reads (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, SmallU (rA k)) (hidxA : ∀ k : Fin nA, (rA k).idx = k)
    (hrn : ∀ k, nA ≤ k → (rA k).inc = 0) (hB : AtomChipHQ.LimbsBounded rA) (hwRA : ∀ j, (rA j).wR ≤ 1)
    (wreqs : List (Fin 5 → K))
    (hbalA : Quad.mk _ (pubsA CellHQ.pubHQ) (pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk _ (pubsA AtomChipHQ.pubC) (pubsA (AtomChipHQ.pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r => (compress (AtomServedQ.acoins δ chalsA) r)⁻¹).sum)
    (houtA : ((AtomServedQ.acoins δ chalsA).gamma, (AtomServedQ.acoins δ chalsA).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).map
        (liftRec (K := K) (L := 𝕂′))) (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b nodesA orbitA chalsA pubsA QA)))
    (hcountA : (AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).length < p)
    (hnpA : nA < p) (hzA : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    -- the atom walk
    (hyV : chalsV 2 = chalsA 2 ∧ chalsV 3 = chalsA 3)
    (hkV : 1 ≤ krootsV) (hknV : krootsV ≤ nV) (hkpV : krootsV + nV < ringChar (ZMod p))
    (hseedsV : AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsV 2) (chalsV 3)) (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    (hXV : KeysExported (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV)).X)
    (hHXV : ∀ j < nV, ∃ c ∈ (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)),
      (natOf ((walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j).trace WChip.idx), childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) false, childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) true) = exportRec c.b0)
    (houtV : (chalsV 0, chalsV 1) ∉ walkEvent (algebraMap (ZMod p) K δ) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV)))
    -- J-9 A: `hden2`, `TopNZ`, the id window
    (hden2 : ∀ j l, Denotes rA j l → p ≤ val l → j < nA) (hTout : ∀ j, nA ≤ j → (rA j).wR = 0 → (rA j).aR ≠ 0)
    (hnAS : 64 * (nA + nS) ≤ p)
    -- the compute walk, its events and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0)
      (stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0))).trip) * α)
    (hα : α ∉ tileSet (foOf9 (rowsWX9 (fun r => CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)
      (fun r => stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)))) n)
    (hw : (α, γ) ∉ cwEvent9 (K := K) (rowsWX9 (fun r => CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)
      (fun r => stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r))) n)
    (hreal : (stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0)).sem.isChain = false)
    (x : P8PublicClaim)
    (hs : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xS) = some x.subject)
    (hf : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xF) = some x.formula)
    (he : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xE) = some x.result) :
    Nock.Jet.HoldsN x := by
  have hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA := by
    rw [hQA]; exact atomChipHQL_sat δ b hnA nodesA orbitA chalsA pubsA QL hsatL
  have hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA := by
    rw [hQA]; exact atomChipHQL_bind δ b hnA nodesA orbitA chalsA pubsA QL hbindL
  have hp63 : 2 ^ 63 + 1 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp5 : 5 < p := by omega
  have hp32 : 2 ^ 32 < p := by omega
  have hW' := walkShareV9 hpG hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA hRA hsA hidxA hrn hB hwRA hnpA hzA hservedA krootsV hnV nodesV orbitV chalsV pubsV QV hsatV hbindV hinjV hadjV hyV hkV hknV hkpV hseedsV hXV hHXV houtV
  have hW0 := hW' (splitSV δ nA b hnS nodesS orbitS chalsS pubsS QS)
  have hS' : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D (valId nA rA (splitSV δ nA b hnS nodesS orbitS chalsS pubsS QS)) Rg combN) .s
      (SplitChipJ9.splitProvs b nodesS orbitS chalsS pubsS QS) :=
    fun D Rg => provP_split δ nA b hnS nodesS orbitS chalsS pubsS QS D Rg rA hp32 hsatS hbindS hinjS hadjS (by omega)
  exact acceptsJ9A_holdsN_finalLGG (pX := []) χ pv C hpG hbal hnC nodesC orbitC chalsC pubsC QC hsatC hbindC
    hinjC hadjC kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hinjW hadjW nodesJ orbitJ pubsJ lay PJ
    hJk hnA nodesA orbitA chalsA pubsA QA QL hQA hsatL hbindL hinjA hadjA hout houtS hcount hnpC hzC γV ρV hokC
    reqsC xsC hsumC houtC hxneC hcountC vp hxC hvp0 E hconsE hE hvp hEinj hkW hknW hkpW hXW hHXW houtW hRg hlay
    hsmall huniq hTpl hnd hidx hrk hlt hpinC hinjE hRA hsA hidxA hrn hB hwRA wreqs hbalA houtA hcountA hnpA hzA
    hservedA hden2 hTout (splitSV δ nA b hnS nodesS orbitS chalsS pubsS QS) (splitSV_ne0 δ nA b hnS nodesS
    orbitS chalsS pubsS QS hp32 hsatS) (splitSV_lt δ nA b hnS nodesS orbitS chalsS pubsS QS) hnAS (pad8_entry7
    _) (fun q hq => by cases hq) (split_entry7 b nodesS orbitS chalsS pubsS QS) hW0 hS' (svcAx_absent hW0 hS')
    hprovX hextX hprovP hprovS hextS hseed hα hw hreal x hs hf he

/-- **Split chip ABSENT** (`sv = fun _ => none`, `nS = 0`, `pS = []`; `hnAS : 64·nA ≤ p`); axis and atom walk present. -/
theorem acceptsJ9A_holdsN_spAbsent [CharP K p] [CharP 𝕂′ p]
    (χ : Coins frameJ8 K) (pv : ℕ → ZMod p)
    -- the compute trace (the J-9 A twin chip)
    {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
    {P : Fin (computeChipVCLHX9 hn nodes b δ (chalVJ8 b χ) pv orbit).rap.w → (ZMod p)[X]}
    {α γ seed : K}
    (C : XCtx hn nodes b δ (chalVJ8 b χ) pv orbit P α γ seed) (hpG : p = Nock.Atoms.p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pv) provs ext)
    -- the cell table
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    -- the J-8 walk
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    -- the J chip and its public registry
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JGenJ8.JChipOK δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ} {rk : ℕ → ℕ × ℕ}
    -- the atom table
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (QL : Fin (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hQA : QA = toHQ δ b hnA nodesA orbitA chalsA pubsA QL)
    (hsatL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QL)
    (hbindL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QL)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    -- the atom walk
    (krootsV : ℕ) {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → ZMod p)
    (orbitV : StrictOrbitDomain (ZMod p) 3 hV) (chalsV pubsV : ℕ → K)
    (QV : Fin (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.w → (ZMod p)[X])
    (hsatV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.Satisfies QV)
    (hbindV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).BindsPreprocessing QV)
    (hinjV : Function.Injective nodesV)
    (hadjV : ∀ (i : Fin nV) (hi : (i : ℕ) + 1 < nV), nodesV ⟨(i : ℕ) + 1, hi⟩ = nodesV i * orbitV.ω)
    -- the axis chip (present)
    {hX nX : ℕ} (hnX : 0 < nX) (nodesX : Fin nX → ZMod p) (orbitX : StrictOrbitDomain (ZMod p) 3 hX)
    (chalsX pubsX : ℕ → K)
    (QX : Fin (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.w → (ZMod p)[X])
    (hsatX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.Satisfies QX)
    (hbindX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).BindsPreprocessing QX)
    (hinjX : Function.Injective nodesX)
    (hadjX : ∀ (i : Fin nX) (hi : (i : ℕ) + 1 < nX), nodesX ⟨(i : ℕ) + 1, hi⟩ = nodesX i * orbitX.ω)
    -- the wiring
    {eA : List (Fin 8 → K)}
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hprovS : provs .s = jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++
      (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++ pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV) ++
        AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX ++ []))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ eA ++ jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hsubS : ∀ i : Fin nX,
      AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ eA)
    (hsubP : ∀ i : Fin nX, (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i).trace AxisChipJ9.z1a = 0 →
      AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ ext .p)
    -- the compute IO events and counts
    (hout : ∀ bl, bl ≠ .s → ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext bl).length < p)
    -- the cell validity balance (two providers) and the encoder
    (hnpC : nC < ringChar (ZMod p)) (hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3) ≠ 0)
    (γV ρV : 𝕂′) (hokC : ChalsOK δ chalsC γV ρV 11)
    (reqsC : List (Fin 5 → 𝕂′)) (xsC : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsumC : (reqsC.map fun r => (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ r)⁻¹).sum =
      Quad.mk _ (pubsC 0) (pubsC 1) + (xsC.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1)⁻¹).sum)
    (houtC : (γV, ρV) ∉ FiniteIO.IOFailureEventW
      (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (SVFrame.liftWts (cellVRecords δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) ++ xsC))
    (hxneC : ∀ x ∈ xsC, FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1 ≠ 0)
    (hcountC : (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).length < p)
    (vp : List (VKey 𝕂′))
    (hxC : ∀ x ∈ xsC, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p))
    (E : Noun → FP 𝕂′)
    (hconsE : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) (E a) (E b))
    (hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) E)
    {rA : ℕ → ARow} (hvp : AtomLeaves E vp (extB p rA))
    (hEinj : WalkKJ8.EncInj2 E (cellTableOf δ b nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) (extB p rA))
    -- the J-8 walk's provider premises (`provOK_p`, `provAx_p`)
    (hkW : 1 ≤ kroots) (hknW : kroots ≤ nW) (hkpW : kroots + nW < ringChar (ZMod p))
    (hXW : KeysExported (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))).X)
    (hHXW : ∀ j < nW, ∃ c ∈ (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)),
      (natOf ((walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j).trace WChip.idx),
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) false,
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) true) = exportRecK c.b0)
    (houtW : (chalsW 0, chalsW 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))))
    -- the J chip's public checks and the registry pin
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hnd : regs.Nodup) (hidx : ∀ id ∈ regs, idx id < p) (hrk : ∀ id ∈ regs, rk id ≠ (0, 0))
    (hlt : ∀ id ∈ regs, (rk id).1 < ringChar (ZMod p) ∧ (rk id).2 < ringChar (ZMod p) ∧ idx id < ringChar (ZMod p))
    (hpinC : ∀ id ∈ regs, ClaimVS.claimVec δ (E (Nock.Jet.Autogen.compile p (Rt id))) (idx id : ZMod p)
      ((rk id).1 : ZMod p) ((rk id).2 : ZMod p) ∈ reqsC)
    (hinjE : ∀ id ∈ regs, ∀ d ∈ decodedNouns2 ((cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) (extB p rA),
      E (Nock.Jet.Autogen.compile p (Rt id)) = E d → Nock.Jet.Autogen.compile p (Rt id) = d)
    -- the atom table's inc heads (A-2) and its export balance
    (hRA : ∀ k : Fin nA, Reads (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, SmallU (rA k)) (hidxA : ∀ k : Fin nA, (rA k).idx = k)
    (hrn : ∀ k, nA ≤ k → (rA k).inc = 0) (hB : AtomChipHQ.LimbsBounded rA) (hwRA : ∀ j, (rA j).wR ≤ 1)
    (wreqs : List (Fin 5 → K))
    (hbalA : Quad.mk _ (pubsA CellHQ.pubHQ) (pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk _ (pubsA AtomChipHQ.pubC) (pubsA (AtomChipHQ.pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r => (compress (AtomServedQ.acoins δ chalsA) r)⁻¹).sum)
    (houtA : ((AtomServedQ.acoins δ chalsA).gamma, (AtomServedQ.acoins δ chalsA).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).map
        (liftRec (K := K) (L := 𝕂′))) (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b nodesA orbitA chalsA pubsA QA)))
    (hcountA : (AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).length < p)
    (hnpA : nA < p) (hzA : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    -- the atom walk
    (hyV : chalsV 2 = chalsA 2 ∧ chalsV 3 = chalsA 3)
    (hkV : 1 ≤ krootsV) (hknV : krootsV ≤ nV) (hkpV : krootsV + nV < ringChar (ZMod p))
    (hseedsV : AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsV 2) (chalsV 3)) (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    (hXV : KeysExported (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV)).X)
    (hHXV : ∀ j < nV, ∃ c ∈ (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)),
      (natOf ((walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j).trace WChip.idx), childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) false, childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) true) = exportRec c.b0)
    (houtV : (chalsV 0, chalsV 1) ∉ walkEvent (algebraMap (ZMod p) K δ) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV)))
    -- J-9 A: `hden2`, `TopNZ`, the id window
    (hden2 : ∀ j l, Denotes rA j l → p ≤ val l → j < nA) (hTout : ∀ j, nA ≤ j → (rA j).wR = 0 → (rA j).aR ≠ 0)
    (hnAS : 64 * nA ≤ p)
    -- the compute walk, its events and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0)
      (stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0))).trip) * α)
    (hα : α ∉ tileSet (foOf9 (rowsWX9 (fun r => CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)
      (fun r => stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)))) n)
    (hw : (α, γ) ∉ cwEvent9 (K := K) (rowsWX9 (fun r => CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)
      (fun r => stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r))) n)
    (hreal : (stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0)).sem.isChain = false)
    (x : P8PublicClaim)
    (hs : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xS) = some x.subject)
    (hf : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xF) = some x.formula)
    (he : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xE) = some x.result) :
    Nock.Jet.HoldsN x := by
  have hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA := by
    rw [hQA]; exact atomChipHQL_sat δ b hnA nodesA orbitA chalsA pubsA QL hsatL
  have hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA := by
    rw [hQA]; exact atomChipHQL_bind δ b hnA nodesA orbitA chalsA pubsA QL hbindL
  have hp63 : 2 ^ 63 + 1 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp5 : 5 < p := by omega
  have hp32 : 2 ^ 32 < p := by omega
  have hW' := walkShareV9 hpG hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA hRA hsA hidxA hrn hB hwRA hnpA hzA hservedA krootsV hnV nodesV orbitV chalsV pubsV QV hsatV hbindV hinjV hadjV hyV hkV hknV hkpV hseedsV hXV hHXV houtV
  have hW0 := hW' (fun _ => none)
  have hS' : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D (valId nA rA (fun _ => none)) Rg combN) .s
      ([] : List ((Fin 8 → K) × K)) := fun D Rg => provP_nil
  have hsubS' : ∀ i : Fin nX, AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ ext .s :=
    fun i => by rw [hextS]; exact List.mem_append_left _ (List.mem_append_right _ (hsubS i))
  exact acceptsJ9A_holdsN_finalLGG (nS := 0) (pS := []) (pX := AxisChipJ9.axTagProvs b nodesX orbitX chalsX
    pubsX QX) χ pv C hpG hbal hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC kroots hnW nodesW
    orbitW chalsW pubsW QW hsatW hbindW hinjW hadjW nodesJ orbitJ pubsJ lay PJ hJk hnA nodesA orbitA chalsA
    pubsA QA QL hQA hsatL hbindL hinjA hadjA hout houtS hcount hnpC hzC γV ρV hokC reqsC xsC hsumC houtC hxneC
    hcountC vp hxC hvp0 E hconsE hE hvp hEinj hkW hknW hkpW hXW hHXW houtW hRg hlay hsmall huniq hTpl hnd hidx
    hrk hlt hpinC hinjE hRA hsA hidxA hrn hB hwRA wreqs hbalA houtA hcountA hnpA hzA hservedA hden2 hTout (fun
    _ => none) (fun _ _ h => by cases h) (fun _ _ h => by cases h) (show 64 * (nA + 0) ≤ p by simpa using hnAS)
    (pad8_entry7 _) (fun q hq => notJ7_of_tag (t := 5) hp5 (by norm_num) (by norm_num) (by omega) (axTag_entry7
    b nodesX orbitX chalsX pubsX QX q hq)) (fun q hq => by cases hq) hW0 hS' (svcAx_present hpG hnX nodesX
    orbitX chalsX pubsX QX hsatX hbindX hinjX hadjX hW0 hS' hsubS' hsubP) hprovX hextX hprovP hprovS hextS
    hseed hα hw hreal x hs hf he

/-- **Atom walk ABSENT** (`pW = []`; no atom-walk chip or premises); axis and split present. -/
theorem acceptsJ9A_holdsN_wAbsent [CharP K p] [CharP 𝕂′ p]
    (χ : Coins frameJ8 K) (pv : ℕ → ZMod p)
    -- the compute trace (the J-9 A twin chip)
    {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
    {P : Fin (computeChipVCLHX9 hn nodes b δ (chalVJ8 b χ) pv orbit).rap.w → (ZMod p)[X]}
    {α γ seed : K}
    (C : XCtx hn nodes b δ (chalVJ8 b χ) pv orbit P α γ seed) (hpG : p = Nock.Atoms.p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalVJ8 b χ) (pubVal := pv) provs ext)
    -- the cell table
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    -- the J-8 walk
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    -- the J chip and its public registry
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hJk : JGenJ8.JChipOK δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} {idx : ℕ → ℕ} {rk : ℕ → ℕ × ℕ}
    -- the atom table
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (QL : Fin (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hQA : QA = toHQ δ b hnA nodesA orbitA chalsA pubsA QL)
    (hsatL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QL)
    (hbindL : (atomChipHQL δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QL)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    -- the axis chip (present)
    {hX nX : ℕ} (hnX : 0 < nX) (nodesX : Fin nX → ZMod p) (orbitX : StrictOrbitDomain (ZMod p) 3 hX)
    (chalsX pubsX : ℕ → K)
    (QX : Fin (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.w → (ZMod p)[X])
    (hsatX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).rap.Satisfies QX)
    (hbindX : (AxisChipJ9.axisChipJ9 δ b hnX nodesX orbitX chalsX pubsX).BindsPreprocessing QX)
    (hinjX : Function.Injective nodesX)
    (hadjX : ∀ (i : Fin nX) (hi : (i : ℕ) + 1 < nX), nodesX ⟨(i : ℕ) + 1, hi⟩ = nodesX i * orbitX.ω)
    -- the split chip (present)
    {hS nS : ℕ} (hnS : 0 < nS) (nodesS : Fin nS → ZMod p) (orbitS : StrictOrbitDomain (ZMod p) 3 hS)
    (chalsS pubsS : ℕ → K)
    (QS : Fin (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).rap.w → (ZMod p)[X])
    (hsatS : (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).rap.Satisfies QS)
    (hbindS : (SplitChipJ9.splitChipJ9 δ nA b hnS nodesS orbitS chalsS pubsS).BindsPreprocessing QS)
    (hinjS : Function.Injective nodesS)
    (hadjS : ∀ (i : Fin nS) (hi : (i : ℕ) + 1 < nS), nodesS ⟨(i : ℕ) + 1, hi⟩ = nodesS i * orbitS.ω)
    -- the wiring
    {eA : List (Fin 8 → K)}
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hprovS : provs .s = jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++
      (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++ [] ++
        AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX ++ SplitChipJ9.splitProvs b nodesS orbitS chalsS pubsS QS))
    (hextS : ext .s = pinCons (p := p) (K := K) regs idx ++ eA ++ jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hsubS : ∀ i : Fin nX,
      AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ eA)
    (hsubP : ∀ i : Fin nX, (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i).trace AxisChipJ9.z1a = 0 →
      AxisChipJ9.keyVecL 5 AxisChipJ9.pathKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ ext .p)
    -- the compute IO events and counts
    (hout : ∀ bl, bl ≠ .s → ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (houtS : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext .s) (effP (liftP (provs .s))))
    (hcount : ∀ bl, (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pv) (orbit := orbit) (P := P) ext bl).length < p)
    -- the cell validity balance (two providers) and the encoder
    (hnpC : nC < ringChar (ZMod p)) (hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3) ≠ 0)
    (γV ρV : 𝕂′) (hokC : ChalsOK δ chalsC γV ρV 11)
    (reqsC : List (Fin 5 → 𝕂′)) (xsC : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsumC : (reqsC.map fun r => (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ r)⁻¹).sum =
      Quad.mk _ (pubsC 0) (pubsC 1) + (xsC.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1)⁻¹).sum)
    (houtC : (γV, ρV) ∉ FiniteIO.IOFailureEventW
      (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (SVFrame.liftWts (cellVRecords δ b hnC nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) ++ xsC))
    (hxneC : ∀ x ∈ xsC, FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1 ≠ 0)
    (hcountC : (reqsC ++ cellVInternal δ b hnC nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).length < p)
    (vp : List (VKey 𝕂′))
    (hxC : ∀ x ∈ xsC, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p))
    (E : Noun → FP 𝕂′)
    (hconsE : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) (E a) (E b))
    (hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (chalsC 2) (chalsC 3)) E)
    {rA : ℕ → ARow} (hvp : AtomLeaves E vp (extB p rA))
    (hEinj : WalkKJ8.EncInj2 E (cellTableOf δ b nodesC orbitC chalsC pubsC
      (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)) (extB p rA))
    -- the J-8 walk's provider premises (`provOK_p`, `provAx_p`)
    (hkW : 1 ≤ kroots) (hknW : kroots ≤ nW) (hkpW : kroots + nW < ringChar (ZMod p))
    (hXW : KeysExported (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC))
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))).X)
    (hHXW : ∀ j < nW, ∃ c ∈ (cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)),
      (natOf ((walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j).trace WChip.idx),
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) false,
        WalkKJ8.childHOfK (walkEnvFA δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW) j) true) = exportRecK c.b0)
    (houtW : (chalsW 0, chalsW 1) ∉ walkEvent (algebraMap (ZMod p) K δ)
      (walkDataOf δ kroots b hnW nodesW orbitW chalsW pubsW
        (restrictWalkK δ kroots b hnW nodesW orbitW chalsW pubsW
          (WalkJ8.bitFix δ kroots b hnW nodesW orbitW chalsW pubsW QW))))
    -- the J chip's public checks and the registry pin
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hnd : regs.Nodup) (hidx : ∀ id ∈ regs, idx id < p) (hrk : ∀ id ∈ regs, rk id ≠ (0, 0))
    (hlt : ∀ id ∈ regs, (rk id).1 < ringChar (ZMod p) ∧ (rk id).2 < ringChar (ZMod p) ∧ idx id < ringChar (ZMod p))
    (hpinC : ∀ id ∈ regs, ClaimVS.claimVec δ (E (Nock.Jet.Autogen.compile p (Rt id))) (idx id : ZMod p)
      ((rk id).1 : ZMod p) ((rk id).2 : ZMod p) ∈ reqsC)
    (hinjE : ∀ id ∈ regs, ∀ d ∈ decodedNouns2 ((cellTableOf δ b nodesC orbitC chalsC pubsC
        (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) (extB p rA),
      E (Nock.Jet.Autogen.compile p (Rt id)) = E d → Nock.Jet.Autogen.compile p (Rt id) = d)
    -- the atom table's inc heads (A-2) and its export balance
    (hRA : ∀ k : Fin nA, Reads (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, SmallU (rA k)) (hidxA : ∀ k : Fin nA, (rA k).idx = k)
    (hrn : ∀ k, nA ≤ k → (rA k).inc = 0) (hB : AtomChipHQ.LimbsBounded rA) (hwRA : ∀ j, (rA j).wR ≤ 1)
    (wreqs : List (Fin 5 → K))
    (hbalA : Quad.mk _ (pubsA CellHQ.pubHQ) (pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk _ (pubsA AtomChipHQ.pubC) (pubsA (AtomChipHQ.pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r => (compress (AtomServedQ.acoins δ chalsA) r)⁻¹).sum)
    (houtA : ((AtomServedQ.acoins δ chalsA).gamma, (AtomServedQ.acoins δ chalsA).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).map
        (liftRec (K := K) (L := 𝕂′))) (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b nodesA orbitA chalsA pubsA QA)))
    (hcountA : (AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).length < p)
    (hnpA : nA < p) (hzA : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA
      (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    -- J-9 A: `hden2`, `TopNZ`, the id window
    (hden2 : ∀ j l, Denotes rA j l → p ≤ val l → j < nA) (hTout : ∀ j, nA ≤ j → (rA j).wR = 0 → (rA j).aR ≠ 0)
    (hnAS : 64 * (nA + nS) ≤ p)
    -- the compute walk, its events and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K) (rowW9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0)
      (stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0))).trip) * α)
    (hα : α ∉ tileSet (foOf9 (rowsWX9 (fun r => CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)
      (fun r => stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)))) n)
    (hw : (α, γ) ∉ cwEvent9 (K := K) (rowsWX9 (fun r => CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r)
      (fun r => stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P r))) n)
    (hreal : (stX9 (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0)).sem.isChain = false)
    (x : P8PublicClaim)
    (hs : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xS) = some x.subject)
    (hf : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xF) = some x.formula)
    (he : denJ8 δ b hnC nodesC orbitC chalsC pubsC QC rA
      (hdV (CompReqsX9.envsN9 hn nodes orbit (chalVJ8 b χ) pv P 0) xE) = some x.result) :
    Nock.Jet.HoldsN x := by
  have hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA := by
    rw [hQA]; exact atomChipHQL_sat δ b hnA nodesA orbitA chalsA pubsA QL hsatL
  have hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA := by
    rw [hQA]; exact atomChipHQL_bind δ b hnA nodesA orbitA chalsA pubsA QL hbindL
  have hp63 : 2 ^ 63 + 1 < p := by subst hpG; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hp5 : 5 < p := by omega
  have hp32 : 2 ^ 32 < p := by omega
  have hW0 : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D (valId nA rA (splitSV δ nA b hnS nodesS orbitS chalsS pubsS QS)) Rg combN) .s
      ([] : List ((Fin 8 → K) × K)) := fun D Rg => provP_nil
  have hS' : ∀ (D : HX → Option Noun) (Rg : Nock.Jet.Registry), ProvP (p := p) (K := K) (RecOK9 D (valId nA rA (splitSV δ nA b hnS nodesS orbitS chalsS pubsS QS)) Rg combN) .s
      (SplitChipJ9.splitProvs b nodesS orbitS chalsS pubsS QS) :=
    fun D Rg => provP_split δ nA b hnS nodesS orbitS chalsS pubsS QS D Rg rA hp32 hsatS hbindS hinjS hadjS (by omega)
  have hsubS' : ∀ i : Fin nX, AxisChipJ9.keyVecL 8 AxisChipJ9.limbKey (AxisChipJ9.axEF b nodesX orbitX chalsX pubsX QX i) ∈ ext .s :=
    fun i => by rw [hextS]; exact List.mem_append_left _ (List.mem_append_right _ (hsubS i))
  exact acceptsJ9A_holdsN_finalLGG (pW := []) (pX := AxisChipJ9.axTagProvs b nodesX orbitX chalsX pubsX QX) χ
    pv C hpG hbal hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC kroots hnW nodesW orbitW chalsW
    pubsW QW hsatW hbindW hinjW hadjW nodesJ orbitJ pubsJ lay PJ hJk hnA nodesA orbitA chalsA pubsA QA QL hQA
    hsatL hbindL hinjA hadjA hout houtS hcount hnpC hzC γV ρV hokC reqsC xsC hsumC houtC hxneC hcountC vp hxC
    hvp0 E hconsE hE hvp hEinj hkW hknW hkpW hXW hHXW houtW hRg hlay hsmall huniq hTpl hnd hidx hrk hlt hpinC
    hinjE hRA hsA hidxA hrn hB hwRA wreqs hbalA houtA hcountA hnpA hzA hservedA hden2 hTout (splitSV δ nA b hnS
    nodesS orbitS chalsS pubsS QS) (splitSV_ne0 δ nA b hnS nodesS orbitS chalsS pubsS QS hp32 hsatS)
    (splitSV_lt δ nA b hnS nodesS orbitS chalsS pubsS QS) hnAS (fun q hq => by cases hq) (fun q hq =>
    notJ7_of_tag (t := 5) hp5 (by norm_num) (by norm_num) (by omega) (axTag_entry7 b nodesX orbitX chalsX pubsX
    QX q hq)) (split_entry7 b nodesS orbitS chalsS pubsS QS) hW0 hS' (svcAx_present hpG hnX nodesX orbitX
    chalsX pubsX QX hsatX hbindX hinjX hadjX hW0 hS' hsubS' hsubP) hprovX hextX hprovP hprovS hextS hseed hα hw
    hreal x hs hf he

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.HokJ9AG9

open Nock.NockVMROM.Thm54.VclL.Handle.HokJ9AG9 in
#print axioms acceptsJ9A_holdsN_finalLGG
open Nock.NockVMROM.Thm54.VclL.Handle.HokJ9AG9 in
#print axioms svcAx_present
open Nock.NockVMROM.Thm54.VclL.Handle.HokJ9AG9 in
#print axioms svcAx_absent
open Nock.NockVMROM.Thm54.VclL.Handle.HokJ9AG9 in
#print axioms walkShareV9
open Nock.NockVMROM.Thm54.VclL.Handle.HokJ9AG9 in
#print axioms acceptsJ9A_holdsN_present
open Nock.NockVMROM.Thm54.VclL.Handle.HokJ9AG9 in
#print axioms acceptsJ9A_holdsN_axAbsent
open Nock.NockVMROM.Thm54.VclL.Handle.HokJ9AG9 in
#print axioms acceptsJ9A_holdsN_spAbsent
open Nock.NockVMROM.Thm54.VclL.Handle.HokJ9AG9 in
#print axioms acceptsJ9A_holdsN_wAbsent
