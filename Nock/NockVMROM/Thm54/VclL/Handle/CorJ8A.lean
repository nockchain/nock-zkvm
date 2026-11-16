/-
  Nock/NockVMROM/Thm54/VclL/Handle/CorJ8A.lean

  **The corollary of `acceptsJ8_holdsN'` at
  `D := denK tC (extA rA)` with the atom-side dischargers substituted** (`acceptsJ8_holdsN_atom`).  New module,
  additive.

  Substituted: `hD0`, `hDen`, `hchain`, `hold`, `hAW` (see the theorem's docstring).  Still named: the `x` / `p`
  provider obligations (with their dischargers), the J chip's `hReg` / `hSub`, the compute's walk / IO /
  root-binding hypotheses, `hD : DenOKX p D`.

  A non-exported 2-limb row of value `< p` makes
  `DenOKX.big` false at `extA`.  Repair options: restrict `extA` to `mb`-exported rows (and `hDen` to them), or
  read `DenOKX.big` only on handles a consumed record names.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8A
import Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.CorJ8A

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
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 pad8_entry7 atomIncProvs provP_append)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Denotes Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.RowSemChipX (RecOK)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalVSX (HX DenOKX)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons rowsJ)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.Atoms (val)

open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8 (axOK_x axOK_s)
open Nock.NockVMROM.Thm54.VclL.Handle.RecOKAJ8

open Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8A (acceptsJ8_holdsN')
open Nock.NockVMROM.Thm54.VclL.Handle.AtomCombJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (hAW_of_atomWalk' AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomDenJ8 (extA hDen_extA hD0_denK hchain_of_served)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)

noncomputable section

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`acceptsJ8_holdsN'` with the atom side discharged.**  `hX` / `hP` / `hPax` stay named (dischargers `provPA_of_provOK ∘ ProvXJ8.provOK_x`,
`provPA_of_provOK ∘ WalkKJ8.provOK_p`, `WalkKJ8.provAx_p`); `hD` stays named (see the module docstring). -/
theorem acceptsJ8_holdsN_atom [CharP K p] [CharP 𝕂′ p]
    (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → 𝕂′) (ρS : 𝕂′)
    -- the compute trace
    {h n : ℕ} {hn : 0 < n} {nodes : Fin n → ZMod p} {orbit : StrictOrbitDomain (ZMod p) 3 h}
    {P : Fin (computeChipVCLHX hn nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit).rap.w → (ZMod p)[X]}
    {α γ seed : K}
    (C : XCtx hn nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P α γ seed) (hp : 2 ^ 63 + 1 < p)
    {provs : (bl : Bal) → List ((Fin (mOf bl) → K) × K)} {ext : (bl : Bal) → List (Fin (mOf bl) → K)}
    -- the cell table
    {hC nC : ℕ} (hnC : 0 < nC) (nodesC : Fin nC → ZMod p)
    (orbitC : StrictOrbitDomain (ZMod p) 3 hC) (chalsC pubsC : ℕ → K)
    (QC : Fin (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.w → (ZMod p)[X])
    (hsatC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).rap.Satisfies QC)
    (hbindC : (cellChipHQKW δ b hnC nodesC orbitC chalsC pubsC).BindsPreprocessing QC)
    (hinjC : Function.Injective nodesC)
    (hadjC : ∀ (i : Fin nC) (hi : (i : ℕ) + 1 < nC), nodesC ⟨(i : ℕ) + 1, hi⟩ = nodesC i * orbitC.ω)
    (hchC : ∀ j, 33 ≤ j → j ≤ 36 → chalsC j = chalsMJ8 δ χ j)
    -- the J-8 walk
    (kroots : ℕ) {hW nW : ℕ} (hnW : 0 < nW) (nodesW : Fin nW → ZMod p)
    (orbitW : StrictOrbitDomain (ZMod p) 3 hW) (chalsW pubsW : ℕ → K)
    (QW : Fin (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.w → (ZMod p)[X])
    (hsatW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).rap.Satisfies QW)
    (hbindW : (walkChipJ8 δ kroots b hnW nodesW orbitW chalsW pubsW).BindsPreprocessing QW)
    (hF : GeneratedField.PrimeFieldElems (ZMod p)) (hp64 : 64 ≤ ringChar (ZMod p))
    (hinjW : Function.Injective nodesW)
    (hadjW : ∀ (i : Fin nW) (hi : (i : ℕ) + 1 < nW), nodesW ⟨(i : ℕ) + 1, hi⟩ = nodesW i * orbitW.ω)
    (hchW : ∀ j, 33 ≤ j → j ≤ 36 → chalsW j = chalsMJ8 δ χ j)
    -- the J chip
    {hJ nJ : ℕ} (nodesJ : Fin nJ → ZMod p) (orbitJ : StrictOrbitDomain (ZMod p) 3 hJ) (pubsJ : ℕ → K)
    (lay : Fin nJ → PRow)
    (PJ : Fin (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.w → (ZMod p)[X])
    (hsatJ : (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).rap.Satisfies PJ)
    (hbindJ : (jetChipJ8 δ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay).BindsPreprocessing PJ)
    (hinjJ : Function.Injective nodesJ) (hnJ : 0 < nJ)
    (hadjJ : ∀ (i : Fin nJ) (hi : (i : ℕ) + 1 < nJ), nodesJ ⟨(i : ℕ) + 1, hi⟩ = nodesJ i * orbitJ.ω)
    -- the atom table
    {hA nA : ℕ} (hnA : 0 < nA) (nodesA : Fin nA → ZMod p) (orbitA : StrictOrbitDomain (ZMod p) 3 hA)
    (chalsA pubsA : ℕ → K)
    (QA : Fin (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.w → (ZMod p)[X])
    (hsatA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).rap.Satisfies QA)
    (hbindA : (AtomChipHQ.atomChipHQ δ b hnA nodesA orbitA chalsA pubsA).BindsPreprocessing QA)
    (hinjA : Function.Injective nodesA)
    (hadjA : ∀ (i : Fin nA) (hi : (i : ℕ) + 1 < nA), nodesA ⟨(i : ℕ) + 1, hi⟩ = nodesA i * orbitA.ω)
    (hchA : ∀ j, 33 ≤ j → j ≤ 36 → chalsA j = chalsMJ8 δ χ j)
    -- the atom walk
    (krootsV : ℕ) {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → ZMod p)
    (orbitV : StrictOrbitDomain (ZMod p) 3 hV) (chalsV pubsV : ℕ → K)
    (QV : Fin (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.w → (ZMod p)[X])
    (hsatV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.Satisfies QV)
    (hbindV : (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).BindsPreprocessing QV)
    (hinjV : Function.Injective nodesV)
    (hadjV : ∀ (i : Fin nV) (hi : (i : ℕ) + 1 < nV), nodesV ⟨(i : ℕ) + 1, hi⟩ = nodesV i * orbitV.ω)
    (hchV : ∀ j, 33 ≤ j → j ≤ 36 → chalsV j = chalsMJ8 δ χ j)
    -- the wiring
    (hprovX : provs .x = cellProvsW b nodesC orbitC chalsC pubsC QC)
    (hextX : ext .x = ServeH.walkXReqs b nodesW orbitW chalsW pubsW QW ++
      jRd b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    (hprovP : provs .p = ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW)
    (hextP : ext .p = [])
    (hprovS : provs .s = jProv b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ ++
      (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++
        pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV)))
    (hextS : ext .s = jCons b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ)
    -- the verifier's public equations
    (hGx : ρ 3 + (Quad.mk _ (pubsW WalkHQ.pubXQ) (pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (pubsJ 2) (pubsJ 3)) =
      Quad.mk _ (pubsC CellHQ.pubHQ) (pubsC (CellHQ.pubHQ + 1)))
    (hGp : ρ 4 = Quad.mk _ (pubsW WalkHQ.pubPQ) (pubsW (WalkHQ.pubPQ + 1)))
    (hGS : ρS + Quad.mk _ (pubsJ 0) (pubsJ 1) =
      Quad.mk _ (pubsA AtomChipHQ.pubMI) (pubsA (AtomChipHQ.pubMI + 1)) +
        Quad.mk _ (pubsV WalkHQ.pubPQ) (pubsV (WalkHQ.pubPQ + 1)))
    -- the IO events and counts at the compute coins
    (hout : ∀ bl, ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl) (liftP (provs bl)))
    (hcount : ∀ bl, (reqsJ8 (hn := hn) (nodes := nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
        (pubVal := pubVJ8 δ b c m ρ ρS χ) (orbit := orbit) (P := P) ext bl).length < p)
    -- the denotation
    {Rg : Nock.Jet.Registry} {q' : ℕ} (tC : List (CellRowB0 q')) {D : HX → Option Noun}
    (hRg : Rg.Faithful) (hD : DenOKX p D)
    -- the x and p provider obligations (`provOK_x`, `provOK_p`, `provAx_p`)
    (hX : ProvP (p := p) (K := K) (RecOKA D Rg combN) .x (cellProvsW b nodesC orbitC chalsC pubsC QC))
    (hP : ProvP (p := p) (K := K) (RecOKA D Rg combN) .p (ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW))
    (hPax : ProvP (p := p) (K := K) AxOK .p (ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW))
    -- the J chip's checks and registry
    {Rt : ℕ → Nock.Jet.Autogen.Tpl} {regs ids : List ℕ} (hlay : List.ofFn lay = layoutJ8 Rt regs ids)
    (hsmall : ∀ q ∈ layoutJ8 Rt regs ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p)
    (huniq : ((layoutJ8 Rt regs ids).filterMap tvKey).Nodup)
    (hTpl : ∀ i ∈ regs, Rg i = some ⟨(Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Rt i)⟩ ∧
      axPosB (Rt i) = true ∧ (Rt i).WellTyped p)
    (hReg : ∀ r ∈ rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ, r.pre.kd = .reg →
      D (r.w.kN.val, r.w.vN.val) = some (Nock.Jet.Autogen.compile p (Rt r.pre.id)))
    (hSub : ∀ r ∈ rowsJ b nodesJ orbitJ (chalsJJ8 χ) pubsJ lay PJ, r.pre.kd = .call →
      ∃ S, D (r.w.kL.val, r.w.vL.val) = some S)
    -- the atom table's inc heads (A-2)
    {rA : ℕ → ARow} (hRA : ∀ k : Fin nA, Reads (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k) (rA k))
    (hsA : ∀ k : Fin nA, (rA k).Small) (hidxA : ∀ k : Fin nA, (rA k).idx = k)




    (hpG : p = Nock.Atoms.p)
    -- the denotation: `D = denK tC (extA rA)`
    (hDdef : D = denK tC (extA rA))
    -- A-2's ℕ premises (`hchain_of_served`) and the atom export balance (summand #4)
    (hrn : ∀ k, nA ≤ k → (rA k).inc = 0) (hB : AtomChipHQ.LimbsBounded rA) (hwRA : ∀ j, (rA j).wR ≤ 1)
    (hok : ∀ j, (rA j).inc = 1 → AtomChipHQ.ChainOK rA j)
    (wreqs : List (Fin 5 → K))
    (hbalA : Quad.mk _ (pubsA CellHQ.pubHQ) (pubsA (CellHQ.pubHQ + 1)) =
      Quad.mk _ (pubsA AtomChipHQ.pubC) (pubsA (AtomChipHQ.pubC + 1)) +
        ((wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r => (compress (AtomServedQ.acoins δ chalsA) r)⁻¹).sum)
    (houtA : ((AtomServedQ.acoins δ chalsA).gamma, (AtomServedQ.acoins δ chalsA).pole) ∉
      IOFailureEventW ((AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).map
        (liftRec (K := K) (L := 𝕂′))) (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b nodesA orbitA chalsA pubsA QA)))
    (hcountA : (AtomServedQ.atomCReqs b nodesA orbitA chalsA pubsA QA ++ wreqs).length < p)
    -- the atom table's validity (T1 at its limb coin)
    (hnpA : nA < p) (hzA : Quad.mk (algebraMap (ZMod p) K δ) (chalsA 2) (chalsA 3) ≠ 0)
    (hservedA : ValidityServed (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    (hyV : chalsV 2 = chalsA 2 ∧ chalsV 3 = chalsA 3)
    (hkV : 1 ≤ krootsV) (hknV : krootsV ≤ nV) (hkpV : krootsV + nV < ringChar (ZMod p))
    (hseedsV : AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsV 2) (chalsV 3)) (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)))
    (hXV : KeysExported (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV)).X)
    (hHXV : ∀ j < nV, ∃ c ∈ (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)),
      (natOf ((walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j).trace WChip.idx), childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) false, childHOf (walkEnvFA δ krootsV b hnV nodesV orbitV chalsV pubsV QV j) true) = exportRec c.b0)
    (houtV : (chalsV 0, chalsV 1) ∉ walkEvent (algebraMap (ZMod p) K δ) (walkDataOf δ krootsV b hnV nodesV orbitV chalsV pubsV (restrictWalkK δ krootsV b hnV nodesV orbitV chalsV pubsV QV)))

    -- the compute walk, its events and the root binding
    (hseed : seed = Walk.rlc γ (encT (K := K)
      (rowW (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0)
        (stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0))).trip) * α)
    (hα : α ∉ tileSet (foOf (rowsWX (fun r => envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)
      (fun r => stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)))) n)
    (hw : (α, γ) ∉ cwEvent (K := K)
      (rowsWX (fun r => envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r)
        (fun r => stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P r))) n)
    (hreal : (stX (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0)).isChain = false)
    (x : P8PublicClaim)
    (hs : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xS) = some x.subject)
    (hf : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xF) = some x.formula)
    (he : D (hdV (envsN hn nodes (chalVJ8 b χ) (pubVJ8 δ b c m ρ ρS χ) orbit P 0) xE) = some x.result) :
    Nock.Jet.HoldsN x := by
  subst hDdef
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hq : 2 ^ 63 < p := by omega
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; exact hq
  have hF' := GeneratedField.primeFieldElems_zmod p
  have hD0 := hD0_denK tC (extA rA)
  have hDen := hDen_extA tC rA
  have hwL : ∀ k : Fin nA, (AtomServedQ.aEF b nodesA orbitA chalsA pubsA QA k).trace Cell.wL = 0 :=
    fun k => (atom_g23 hsatA k).1
  have hchain := hchain_of_served δ b hnA nodesA orbitA chalsA pubsA hq' QA hsatA hbindA hinjA hadjA wreqs hbalA
    houtA hcountA hRA hsA hidxA hwL hrn hB hwRA hok
  have hcs := AtomServedQ.consumeServedQ_of_balance δ b hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA
    hadjA wreqs hbalA houtA hcountA
  have hold := hold_of_served hq hsatA hbindA hinjA hadjA hnpA hzA hservedA hRA hsA hidxA hB (fun k => hwRA k) hcs
  -- the atom table, seen by the atom walk
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
  have hag : ∀ c ∈ (cellTableOf δ b nodesA orbitA chalsA pubsA (AtomChipHQ.restrictAtomCell δ b hnA nodesA orbitA chalsA pubsA QA)).map (·.b0), AgreeRow c (rA c.idx) :=
    fun c hc => (agree_atom hq hsatA hRA hsA hidxA hB (fun k => hwRA k) c hc).2
  have hAW := hAW_of_atomWalk' δ krootsV b hnV nodesV orbitV chalsV pubsV QV hsatV hbindV hinjV hadjV hkV hknV
    hkpV hq' hzV htab hseedsV hXV hHXV houtV hser htb hag tC Rg
  exact acceptsJ8_holdsN' (comb := combN) (hD0 := hD0) (hDen := hDen) (hold := hold) (hchain := hchain) (hAW :=
    hAW) χ c m ρ ρS C hp hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC hchC kroots hnW nodesW orbitW
    chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW hchW nodesJ orbitJ pubsJ lay PJ hsatJ hbindJ hinjJ hnJ hadjJ
    hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA hchA krootsV hnV nodesV orbitV chalsV pubsV QV
    hsatV hbindV hinjV hadjV hchV hprovX hextX hprovP hextP hprovS hextS hGx hGp hGS hout hcount hRg hD hX hP hPax
    hlay hsmall huniq hTpl hReg hSub hRA hsA hidxA hpG hseed hα hw hreal x hs hf he

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.CorJ8A
