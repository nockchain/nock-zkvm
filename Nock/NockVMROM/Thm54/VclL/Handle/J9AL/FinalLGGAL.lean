/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/FinalLGGAL.lean

  **The `finalLGG` twin with the ALU export reads on `.x`.**
  `HokJ9AG9.acceptsJ9A_holdsN_finalLGG` verbatim, except that its `hextX` fixes
  `ext .x = walkXReqs ++ jRd`; here the walk part is a generic `wX` (`FinalJ9AX9.acceptsJ9A_holdsN_EIG9` is generic
  in `wX`), so the J-9 AL core instantiates `wX := walkXReqs ++ aluX`.  `hextX` is used only in the final call.
  Second change: `hsvc` is stated at the J-9 A denotation `denJ9A tC p rA (valId nA rA sv)` itself (not for every
  `D`; the ALU's per-call semantics `CtxAL.hsem_of_ctx` is a fact about that denotation), and it receives the `.x`
  block served (`ext_served9_one`, the one-block form of `AxisCoreX9.ext_served9`) and the `.x` providers'
  `RecOK9I`, from which the core reads the ALU export `Cell3`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HokJ9AG9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FinalLGGAL

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

section Served
open Nock.NockVMROM.Thm54.VclL.Handle.CompReqsX9 (compReqsX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8 (liftP den_prov_ne_of_out)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec_inj)
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  [FiniteDimensional (ZMod p) K] [Fintype K] [DecidableEq K]
  {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {b : Basis (Fin 3) (ZMod p) K} {δ : ZMod p}
  [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] [DecidableEq (Quad (algebraMap (ZMod p) K δ))]
  {chalV pubVal : ℕ → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
  {P : Fin (computeChipVCLHX9 hn nodes b δ chalV pubVal orbit).rap.w → (ZMod p)[X]}

/-- **`AxisCoreX9.ext_served9` at ONE block** (its proof uses `hout`, `hcount` at that block only, and the compute denominators `hne` of every block):
here at `.x`, where the `.s` event of `finalLGG` is the effective one. -/
theorem ext_served9_one [CharP (Quad (algebraMap (ZMod p) K δ)) p] (C : BCtx9 hn nodes b δ chalV pubVal orbit P)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    (hbal : BalJ8 (b := b) (δ := δ) (chalV := chalV) (pubVal := pubVal) provs ext)
    (hne : ∀ bl, ∀ r ∈ compReqsX9 (K := K) hn nodes orbit chalV pubVal P bl,
      compress (coinsCV b δ chalV) (liftRec (L := Quad (algebraMap (ZMod p) K δ)) r) ≠ 0) (bl : Bal)
    (hout : ((coinsCV b δ chalV).gamma, (coinsCV b δ chalV).pole) ∉
      IOFailureEventW (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : (reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
        (pubVal := pubVal) (orbit := orbit) (P := P) ext bl).length < p) :
    ∀ c ∈ ext bl, c ∈ (provs bl).map Prod.fst := by
  have hd : ∀ r ∈ reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
      (pubVal := pubVal) (orbit := orbit) (P := P) ext bl, compress ⟨(coinsCV b δ chalV).gamma,
        (coinsCV b δ chalV).pole⟩ r ≠ 0 :=
    TeleC.den_ne_of_out _ _ _ _ hout
  have hserved : ∀ r ∈ reqsJ9 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalV)
      (pubVal := pubVal) (orbit := orbit) (P := P) ext bl, r ∈ (liftP (provs bl)).map Prod.fst := by
    refine ServeH.served_of_balance (p := p) _ _ _ _ hd
      (den_prov_ne_of_out _ _ _ _ hout) ?_ hcount hout
    have h1 := compReqsX9_sum C hne bl
    have h2 := hbal bl
    unfold reqsJ9 liftP
    rw [List.map_map, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def] at h1 ⊢
    rw [h1]
    exact h2
  intro c hc
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp
    (hserved _ (List.mem_map_of_mem (List.mem_append_right _ hc)))
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨q0, hq0, liftRec_inj hqe⟩

end Served

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **S8 outer, generic in the axis, atom-walk and split shares, and in the `.x` walk reads `wX`** (see the module header). -/
theorem acceptsJ9AL_holdsN_finalLGG [CharP K p] [CharP 𝕂′ p]
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
    -- CHANGED (AL): the service step at the J-9 A denotation itself (the ALU's per-call semantics is a fact about
    -- it), with the `.x` block served and its providers' `RecOK9I` as extra inputs (the ALU export reads)
    (hsvc : DenOKX9 p (denJ9A ((cellTableOf δ b nodesC orbitC chalsC pubsC (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) p rA (valId nA rA sv)) (valId nA rA sv) →
      (∀ c ∈ ext .x, c ∈ (provs .x).map Prod.fst) →
      ProvP (p := p) (K := K) (RecOK9I (denJ9A ((cellTableOf δ b nodesC orbitC chalsC pubsC (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) p rA (valId nA rA sv)) (valId nA rA sv) Rg combN) .x (provs .x) →
      ProvP (p := p) (K := K) (RecOK9I (denJ9A ((cellTableOf δ b nodesC orbitC chalsC pubsC (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) p rA (valId nA rA sv)) (valId nA rA sv) Rg combN) .p (provs .p) →
      ProvP (p := p) (K := K) (RecOK9I (denJ9A ((cellTableOf δ b nodesC orbitC chalsC pubsC (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) p rA (valId nA rA sv)) (valId nA rA sv) Rg combN) .s
        (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA)) →
      ∀ pJ : List ((Fin 8 → K) × K), ProvP (p := p) (K := K) (RecOK9I (denJ9A ((cellTableOf δ b nodesC orbitC chalsC pubsC (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) p rA (valId nA rA sv)) (valId nA rA sv) Rg combN) .s pJ →
      (∀ c ∈ ext .s, c ∈ (pJ ++ pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++ pW ++ pX ++ pS).map Prod.fst) →
      (∀ c ∈ ext .p, c ∈ (provs .p).map Prod.fst) →
      ProvP (p := p) (K := K) (RecOK9I (denJ9A ((cellTableOf δ b nodesC orbitC chalsC pubsC (CellTwinKW.restrictHQKWCell δ b hnC nodesC orbitC chalsC pubsC QC)).map (·.b0)) p rA (valId nA rA sv)) (valId nA rA sv) Rg combN) .s
        (pJ ++ pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++ pW ++ pX ++ pS))
    -- the wiring
    {eA : List (Fin 8 → K)}
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    {wX : List (Fin 5 → K)} (hextX : ext .x = wX ++ jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
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
  have hneAll : ∀ bl, ∀ r ∈ CompReqsX9.compReqsX9 (K := K) hn nodes orbit (chalVJ8 b χ) pv P bl,
      compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r) ≠ 0 := by
    intro bl r hr
    cases bl with
    | s => exact TeleC.den_ne_of_out _ _ _ _ houtS _ (List.mem_map_of_mem (List.mem_append_left _ hr))
    | x =>
      exact TeleC.den_ne_of_out _ _ _ _ (hout .x (by intro h; cases h)) _
        (List.mem_map_of_mem (List.mem_append_left _ hr))
    | p =>
      exact TeleC.den_ne_of_out _ _ _ _ (hout .p (by intro h; cases h)) _
        (List.mem_map_of_mem (List.mem_append_left _ hr))
  have hsvX : ∀ c ∈ ext .x, c ∈ (provs .x).map Prod.fst :=
    ext_served9_one (HoldsX9.bctx9_of_xctx C) hbal hneAll .x (hout .x (by decide)) (hcount .x)
  exact FinalJ9AX9.acceptsJ9A_holdsN_EIG9 C hpG hbal nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ hJk hcJ
    (pad8_entry7 _) h7W h7S h7X hprovS hextS hextX hout houtS hcount hRg hD hXp hPp hPax hI (hW D Rg) (hS D Rg)
    (hsvc hD hsvX hXp hPp hI) hlay hsmall huniq hTpl hRegP hseed hα hw hreal x hs' hf' he'

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.FinalLGGAL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.FinalLGGAL
#print axioms acceptsJ9AL_holdsN_finalLGG
end Axioms
