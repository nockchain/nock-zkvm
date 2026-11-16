/-
  Nock/NockVMROM/Thm54/VclL/Handle/FinalJ8.lean

  **`acceptsJ8_holdsN` — the J-8 assembly at
  `frameJ8`'s verifier data.**  New module, additive.

  An accepted J-8 compute trace (`RapWalkJ8.XCtx` at `chalVJ8 b χ` / `pubVJ8 … χ`) together with the five accepted
  memory-side traces (cell `cellChipHQKW`, walk `walkChipJ8`, J `jetChipJ8` at `chalsJJ8 χ`, atom table `atomChipHQ`,
  atom walk `walkChipHQK`), the verifier's public equations (`hGx`, `hGp`, `hGS`), outside the compute walk events
  and each balance's weighted IO failure event, proves `HoldsN` of the claim.

  Composition:
  * the balance `BalJ8` is `BalSJ8.balJ8_frameJ8S` (all three balances from the public equations; no named
    telescope left);
  * the `s` providers: the J half by `ServiceJ8.jetProvOK_of_balJ8` with JB's `hRd` DISCHARGED by
    `BalXJ8.hRd_of_balX` (from the `x` provider obligation), the coin premise by `coinsJ_J8`, `hO7` by
    `pad8_entry7`; the atom table's inc heads by `IncHeadJ8.atomInc_provOK`; the atom walk's half named (`hAW`);
    assembled by `ServiceJ8.provOK_s`;
  * `AxOK` holds vacuously at `.x` / `.s` (`axOK_x`, `axOK_s`); at `.p` it is the walk's `provAx_p` (named `hPax`);
  * then `AcceptJ8.acceptsJ8_holdsN_compute`.

  **Named hypotheses on the final theorem** (each with its kernel discharger where one exists):
  * `hX : ProvOK.x (cellProvsW …)` — discharged by `ProvXJ8.provOK_x` under its hypotheses;
  * `hP : ProvOK.p (walkPProvs …)`, `hPax : ProvP AxOK.p (walkPProvs …)` — `WalkKJ8.provOK_p` / `provAx_p`;
  * atom table: the ℕ reading `rA` (`hRA / hsA / hidxA`), `hD0`, `hDen` (the definition of `ext`), `hold`,
    `hchain` (A-2), `hpG`;
  * atom walk: `hAW : ProvP RecOK.s (pad8 (walkPProvs …))` (step 1: `limbA`, the limb comb);
  * compute: `hseed`, `hα / hw` (walk events), `hout / hcount` (IO events), `hreal`, `hs / hf / he` (root binding),
    `hR`, `hD`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.BalSJ8
import Nock.NockVMROM.Thm54.VclL.Handle.IncHeadJ8
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8

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

noncomputable section

/-! ## 1. `AxOK` is vacuous off the path balance -/

theorem axOK_x (l : List ℕ) : AxOK (l, .x) := by
  rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> trivial

theorem axOK_s (l : List ℕ) : AxOK (l, .s) := by
  rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> trivial

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] {δ : ZMod p} [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  [DecidableEq (Quad (algebraMap (ZMod p) K δ))] {b : Basis (Fin 3) (ZMod p) K}
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`acceptsJ8_holdsN`.**  At `frameJ8`'s verifier data (`chalVJ8 b χ`, `pubVJ8 δ b c m ρ ρS χ`),
an accepted J-8 compute trace and the five accepted memory-side traces, under the verifier's public equations
`hGx / hGp / hGS`, outside the compute walk events (`hα`, `hw`) and each balance's weighted IO failure event (`hout`),
prove `HoldsN` of the claim.  The named hypotheses are listed in the module docstring. -/
theorem acceptsJ8_holdsN [CharP K p] [CharP 𝕂′ p]
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
    {D : HX → Option Noun} {Rg : Nock.Jet.Registry} {limbA : ℕ → ℕ → HX}
    (hRg : Rg.Faithful) (hD : DenOKX p D)
    -- the x and p provider obligations (`provOK_x`, `provOK_p`, `provAx_p`)
    (hX : ProvOK (p := p) (K := K) D Rg limbA .x (cellProvsW b nodesC orbitC chalsC pubsC QC))
    (hP : ProvOK (p := p) (K := K) D Rg limbA .p (ServeH.walkPProvs b nodesW orbitW chalsW pubsW QW))
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
    (hD0 : ∀ v, D (0, v) = some (.atom v))
    (hDen : ∀ j l, Denotes rA j l → D (2, j) = some (.atom (val l)))
    (hold : ∀ k : Fin nA, (rA k).inc = 1 → ∃ l, Denotes rA (rA k).idxO l)
    (hchain : ∀ k : Fin nA, (rA k).inc = 1 → ∀ lold, Denotes rA (rA k).idxO lold →
      ∃ lnew, Denotes rA k lnew ∧ val lnew = val lold + 1)
    (hpG : p = Nock.Atoms.p)
    -- the atom walk's providers (step 1)
    (hAW : ProvP (p := p) (K := K) (RecOK D Rg limbA) .s
      (pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV)))
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
  have hbal := BalSJ8.balJ8_frameJ8S χ c m ρ ρS (provs := provs) (ext := ext)
    hnC nodesC orbitC chalsC pubsC QC hsatC hbindC hinjC hadjC hchC
    kroots hnW nodesW orbitW chalsW pubsW QW hsatW hbindW hF hp64 hinjW hadjW hchW
    nodesJ orbitJ pubsJ lay PJ hsatJ hbindJ hinjJ hnJ hadjJ
    hnA nodesA orbitA chalsA pubsA QA hsatA hbindA hinjA hadjA hchA
    krootsV hnV nodesV orbitV chalsV pubsV QV hsatV hbindV hinjV hadjV hchV
    hprovX hextX hprovP hextP hprovS hextS hGx hGp hGS
  have B := AcceptJ8.bctx_of_xctx C
  have hp3 : 3 < p := by omega
  have hq : 2 ^ 63 < p := by omega
  -- the `x` obligation at `provs.x`
  have hXp : ProvOK (p := p) (K := K) D Rg limbA .x (provs .x) := by rw [hprovX]; exact hX
  -- JB's `hRd` from the `x` balance
  have hRd := BalXJ8.hRd_of_balX B hbal hout hcount _ hextX hXp
  -- the other service providers' `hO7`
  have hO7 : ∀ q ∈ (pad8 (atomIncProvs b nodesA orbitA chalsA pubsA QA) ++
      pad8 (ServeH.walkPProvs b nodesV orbitV chalsV pubsV QV)), q.1 ⟨7, by norm_num⟩ = 0 := by
    intro q hq'
    rcases List.mem_append.mp hq' with hq' | hq'
    · exact pad8_entry7 _ q hq'
    · exact pad8_entry7 _ q hq'
  have hJ := ServiceJ8.jetProvOK_of_balJ8 hp3 B hbal hout (hcount .s) _ hprovS hextS hO7
    ((coinsJ_J8 δ χ).trans (coinsCV_J8 δ b χ).symm) hsatJ hbindJ hinjJ hnJ hadjJ hlay hsmall huniq hD hTpl hRd
    hReg hSub
  have hI := IncHeadJ8.atomInc_provOK (Rg := Rg) (limbA := limbA) hq hsatA hRA hsA hidxA hD0 hDen hold hchain hpG
  have hS := ServiceJ8.provOK_s _ hprovS hJ (provP_append.mpr ⟨hI, hAW⟩)
  have hprov : ∀ bl, ProvOK (p := p) (K := K) D Rg limbA bl (provs bl) := by
    intro bl
    cases bl with
    | x => exact hXp
    | p => rw [hprovP]; exact hP
    | s => exact hS
  have haxP : ∀ bl, ProvP (p := p) (K := K) AxOK bl (provs bl) := by
    intro bl
    cases bl with
    | x => intro q _ l _ _ _; exact axOK_x l
    | p => rw [hprovP]; exact hPax
    | s => intro q _ l _ _ _; exact axOK_s l
  exact AcceptJ8.acceptsJ8_holdsN_compute C hp hRg hD hseed hα hw hbal hout hcount hprov haxP hreal x hs hf he

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.FinalJ8
