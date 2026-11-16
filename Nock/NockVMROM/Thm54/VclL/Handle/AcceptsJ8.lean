/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8.lean

  **Card J-8a part 13, FINAL : `AcceptsJ8`, `hsoundJ8` and the figure.**

  * §1 **`PubJ8`** (the verifier's fixed public parameters: the six chips' row layouts, orbits, walk roots, the J
    layout and the registry), **`MsgJ8`** (the prover's public messages: claim message, `ρ`, `ρ_s`, the chips'
    publics, the cell validity external lists and the atom export's external requests), the six chip views of a
    `TrJ8` trace.
  * §2 **`AcceptsJ8 Pb Rg c χ M tr`**: THE verifier's checks and nothing else — every chip `Satisfies` (with
    preprocessing binding) at the `frameJ8` vectors (`chalVJ8` / `pubVJ8`, `chalsMJ8`, `chalsJJ8`, `chalsAJ8`), the
    public layout checks (injective `ω`-adjacent nodes, row counts `< p`, walk roots), the public equations
    (`hGx hGp hGS`, the cell validity terminal `hsumC`, the atom export terminal `hbalA`), the public LogUp
    denominators (`hxneC`), the J public checks (`hlay hsmall huniq hTpl`), the registry pin's public checks
    (`hnd hidx hrk hlt hpinC`) and the cell validity's external keys (`hxC hvp0`).
  * §3 **`LinkJ8`**: every hypothesis of `CorJ8I.acceptsJ8_holdsN_final'` that is NOT a verifier check, NOT an
    exclusion ingredient (`OutJ8`), NOT derived here and NOT a statement binder.
  * §4 **`hsoundJ8`**: `AcceptsJ8 → (∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ) → LinkJ8 → HoldsN c`, through
    `BundleJ8.outJ8_of_outside` (and `EncInjJ8.encInj2_of_outside`, `Lift40J8.wchain_out`) and
    `CorJ8I.acceptsJ8_holdsN_final'`, at the statement binders `hpG : p = Atoms.p`, `hRg : Rg.Faithful`,
    `hqM`, `hk`.  Discharged inside (class (c)): the coin agreements `hch*`, `hyV`, `hF`, `hp64`, `hp`, the compute
    context `XCtx` (α, γ, `pubIC`, `pubSeed`, `pubOut` from `pubVJ8`), `γV ρV hokC` (`chalsOK_J8`), the encoder
    `E := encZY z y` with `hconsE` / `hE`, the wiring `hprovX … hextS` (by definition), the J-8 walk event's
    coins (`coinW_J8`) and the atom walk's data readout (`wdV_view`: `TraceJ8.withWalkV`'s `wdVJ8` is the walk
    data at the atom-walk view; `hsoundJ8` takes it as `hWV`, `probJ8_final` discharges it).
  * §5 **`probJ8_final`**: for every staged `Q` (`StJ8`), `Pr[(∃ M, AcceptsJ8 … (Q χ)) ∧ ¬ HoldsN c] < 2^-155`
    at the census corner, at `R := withLiftC (withWalkV R0 …) L`, conditional on `LinkJ8` at every accepted coin.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CorJ8I
import Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8
import Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8

open Nock Nock.Reified Nock.Framework Nock.Walk Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVSQ Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHQ
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ServedJ8
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (mOf)
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW cellProvsW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ServiceJ8 (pad8 atomIncProvs)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQ (ARow Reads)
open Nock.NockVMROM.Thm54.VclL.Handle.LocalOKX (hdV)
open Nock.NockVMROM.Thm54.VclL.Handle.RowDecodeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkLblVSX
open Nock.NockVMROM.Thm54.VclL.Handle.WalkTreeVSX
open Nock.NockVMROM.Thm54.VclL.Handle.RapWalkJ8
open Nock.NockVMROM.Thm54.VclL.Handle.TeleC (envsN)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.RapJetJ8 (jRd jProv jCons)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkBridgeJ8
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkAW (walkEnvFA restrictWalkK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomWalkProvJ8 (AWSeedsOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomBigJ8 (extB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.Jet.FibreJ8 (effP)
open Nock.NockVMROM.Thm54.VclL.Handle.DenXJ8 (compReqsX)
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.Atoms (lenL)

noncomputable section

/-! ## 1. Public parameters, messages, chip views -/

/-- **The verifier's fixed public parameters**: every chip's row layout (heights, rows, nodes, orbit), the walk
roots, the J layout and the registry (template ids, registered ids, rank map). -/
structure PubJ8 (p : ℕ) [Fact p.Prime] where
  h : ℕ
  n : ℕ
  hn : 0 < n
  nodes : Fin n → ZMod p
  orbit : StrictOrbitDomain (ZMod p) 3 h
  hC : ℕ
  nC : ℕ
  hnC : 0 < nC
  nodesC : Fin nC → ZMod p
  orbitC : StrictOrbitDomain (ZMod p) 3 hC
  kroots : ℕ
  hW : ℕ
  nW : ℕ
  hnW : 0 < nW
  nodesW : Fin nW → ZMod p
  orbitW : StrictOrbitDomain (ZMod p) 3 hW
  hJ : ℕ
  nJ : ℕ
  nodesJ : Fin nJ → ZMod p
  orbitJ : StrictOrbitDomain (ZMod p) 3 hJ
  lay : Fin nJ → PRow
  hA : ℕ
  nA : ℕ
  hnA : 0 < nA
  nodesA : Fin nA → ZMod p
  orbitA : StrictOrbitDomain (ZMod p) 3 hA
  krootsV : ℕ
  hV : ℕ
  nV : ℕ
  hnV : 0 < nV
  nodesV : Fin nV → ZMod p
  orbitV : StrictOrbitDomain (ZMod p) 3 hV
  Rt : ℕ → Nock.Jet.Autogen.Tpl
  regs : List ℕ
  ids : List ℕ
  idx : ℕ → ℕ
  rk : ℕ → ℕ × ℕ

/-- **The prover's public messages**: the claim message, the balance publics `ρ`, `ρ_s`, each chip's publics,
the cell validity's external requests / provides and keys, the atom export's external requests. -/
structure MsgJ8 (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] (δ : ZMod p) where
  m : ClaimMsgVS
  ρ : Fin 5 → Quad (algebraMap (ZMod p) K δ)
  ρS : Quad (algebraMap (ZMod p) K δ)
  pubsC : ℕ → K
  pubsW : ℕ → K
  pubsJ : ℕ → K
  pubsA : ℕ → K
  pubsV : ℕ → K
  reqsC : List (Fin 5 → Quad (algebraMap (ZMod p) K δ))
  xsC : List ((Fin 5 → Quad (algebraMap (ZMod p) K δ)) × Quad (algebraMap (ZMod p) K δ))
  vp : List (VKey (Quad (algebraMap (ZMod p) K δ)))
  wreqs : List (Fin 5 → K)

/-- The three handle balances' provider / external lists, by balance. -/
def byBal {β : Bal → Type} (x : β .x) (pp : β .p) (s : β .s) : (bl : Bal) → β bl
  | .x => x
  | .p => pp
  | .s => s

section Views
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δ : ZMod p) (b : Basis (Fin 3) (ZMod p) K) (Pb : PubJ8 p) (tr : TrJ8 (ZMod p))

/-- The compute view (width `123`, `TraceJ8.widthC_eq`). -/
def qX (chalV pubVal : ℕ → ZMod p) :
    Fin (computeChipVCLHX Pb.hn Pb.nodes b δ chalV pubVal Pb.orbit).rap.w → (ZMod p)[X] := tr.C

/-- The cell table view (width `242`). -/
def qM (chals pubs : ℕ → K) : Fin (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC chals pubs).rap.w → (ZMod p)[X] :=
  tr.M

/-- The J-8 walk view (width `166`). -/
def qW (chals pubs : ℕ → K) :
    Fin (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals pubs).rap.w → (ZMod p)[X] :=
  fun j => tr.W (Fin.cast (WalkJ8.walkChipJ8_width δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW chals pubs) j)

/-- The J chip view (width `71`). -/
def qJ (chals pubs : ℕ → K) :
    Fin (jetChipJ8 δ b Pb.nodesJ Pb.orbitJ chals pubs Pb.lay).rap.w → (ZMod p)[X] :=
  fun j => tr.J (Fin.cast (Nock.Jet.ChipJ8.jetChipJ8_width δ b Pb.nodesJ Pb.orbitJ chals pubs Pb.lay) j)

/-- The atom table view (width `349`). -/
def qA (chals pubs : ℕ → K) :
    Fin (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA chals pubs).rap.w → (ZMod p)[X] :=
  fun j => tr.A (Fin.cast (AtomChipHQ.atomChipHQ_width δ b Pb.hnA Pb.nodesA Pb.orbitA chals pubs) j)

/-- The atom walk view (width `166`). -/
def qV (chals pubs : ℕ → K) :
    Fin (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV chals pubs).rap.w → (ZMod p)[X] :=
  fun j => tr.V (Fin.cast (CellTwinK.walkChipHQK_width δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV chals pubs) j)

end Views

/-! ## 2. `AcceptsJ8`: the verifier's checks -/

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`AcceptsJ8`: THE verifier's checks** at the coins `χ`, the claim `c`, the messages `M`, the trace `tr`.
Chips at the `frameJ8` vectors: compute `chalVJ8 b χ` / `pubVJ8 … χ`; cell table and J-8 walk `chalsMJ8 δ χ`;
J chip `chalsJJ8 χ`; atom table and atom walk `chalsAJ8 δ χ`. -/
structure AcceptsJ8 (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) : Prop where
  -- compute
  hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ (chalVJ8 b χ)
    (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
  hinjX : Function.Injective Pb.nodes
  hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  -- the cell table
  hsatC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.Satisfies
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hbindC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).BindsPreprocessing
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hinjC : Function.Injective Pb.nodesC
  hadjC : ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω
  hnpC : Pb.nC < ringChar (ZMod p)
  -- the J-8 walk
  hsatW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).rap.Satisfies
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hbindW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).BindsPreprocessing
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hinjW : Function.Injective Pb.nodesW
  hadjW : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω
  hkW : 1 ≤ Pb.kroots
  hknW : Pb.kroots ≤ Pb.nW
  hkpW : Pb.kroots + Pb.nW < ringChar (ZMod p)
  -- the J chip
  hsatJ : (jetChipJ8 δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay).rap.Satisfies
    (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
  hbindJ : (jetChipJ8 δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay).BindsPreprocessing
    (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
  hinjJ : Function.Injective Pb.nodesJ
  hnJ : 0 < Pb.nJ
  hadjJ : ∀ (i : Fin Pb.nJ) (hi : (i : ℕ) + 1 < Pb.nJ), Pb.nodesJ ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesJ i * Pb.orbitJ.ω
  -- the atom table
  hsatA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA).rap.Satisfies
    (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)
  hbindA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA).BindsPreprocessing
    (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < p
  -- the atom walk
  hsatV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV).rap.Satisfies
    (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV)
  hbindV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV).BindsPreprocessing
    (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV)
  hinjV : Function.Injective Pb.nodesV
  hadjV : ∀ (i : Fin Pb.nV) (hi : (i : ℕ) + 1 < Pb.nV), Pb.nodesV ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesV i * Pb.orbitV.ω
  hkV : 1 ≤ Pb.krootsV
  hknV : Pb.krootsV ≤ Pb.nV
  hkpV : Pb.krootsV + Pb.nV < ringChar (ZMod p)
  -- the public balance equations
  hGx : M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))
  hGp : M.ρ 4 = Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))
  hGS : M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1))
  hsumC : (M.reqsC.map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk _ (M.pubsC 0) (M.pubsC 1) + (M.xsC.map fun x => x.2 * (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1)⁻¹).sum
  hxneC : ∀ x ∈ M.xsC, FiniteIO.compress (m := 5) ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ x.1 ≠ 0
  hbalA : Quad.mk _ (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      ((M.wreqs.map (liftRec (K := K) (L := 𝕂′))).map fun r =>
        (compress (AtomServedQ.acoins δ (chalsAJ8 δ χ)) r)⁻¹).sum
  -- the cell validity's external keys
  hxC : ∀ x ∈ M.xsC, ∃ k ∈ M.vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p)
  hvp0 : ∀ k ∈ M.vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p)
  -- the J chip's public checks and the registry pin
  hlay : List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids
  hsmall : ∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p
  huniq : ((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup
  hTpl : ∀ i ∈ Pb.regs, Rg i = some ⟨(Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Pb.Rt i)⟩ ∧
    axPosB (Pb.Rt i) = true ∧ (Pb.Rt i).WellTyped p
  hnd : Pb.regs.Nodup
  hidx : ∀ id ∈ Pb.regs, Pb.idx id < p
  hrk : ∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0)
  hlt : ∀ id ∈ Pb.regs, (Pb.rk id).1 < ringChar (ZMod p) ∧ (Pb.rk id).2 < ringChar (ZMod p) ∧
    Pb.idx id < ringChar (ZMod p)
  hpinC : ∀ id ∈ Pb.regs, ClaimVS.claimVec δ
    (encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))
      (Nock.Jet.Autogen.compile p (Pb.Rt id))) (Pb.idx id : ZMod p)
    ((Pb.rk id).1 : ZMod p) ((Pb.rk id).2 : ZMod p) ∈ M.reqsC

end Accept

/-! ## 3. The compute publics at `frameJ8` (class (c): `XCtx`'s `hIC` / `hOut`) -/

section Pubs
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

theorem limbVal_pubVHQ_low (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → Quad (algebraMap (ZMod p) K δ))
    (ψ : Coins frameVSQ K) (k : ℕ) (hk : k + 3 ≤ 21) :
    limbVal b (pubVHQ δ b c m ρ ψ) k = limbVal b (pubVH δ b c m ρ (toVS ψ)) k := by
  unfold limbVal
  refine Finset.sum_congr rfl fun i _ => ?_
  have : k + (i : ℕ) < 21 := by have := i.isLt; omega
  simp only [pubVHQ, if_pos this]

/-- `XCtx.hIC` at `frameJ8`: the initial-count public is the walk coin `α`. -/
theorem pubVJ8_IC (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → Quad (algebraMap (ZMod p) K δ))
    (ρS : Quad (algebraMap (ZMod p) K δ)) (χ : Coins frameJ8 K) :
    limbVal b (pubVJ8 δ b c m ρ ρS χ) pubIC = limbVal b (chalVJ8 b χ) chalAlphaW := by
  rw [Lift40J8.limb_alphaW_J8, limbVal_pubVJ8_low δ b c m ρ ρS χ _ (by simp [pubIC]),
    limbVal_pubVHQ_low δ b c m ρ _ _ (by simp [pubIC]), FrameVS.limb_pubVH_IC]
  rfl

/-- `XCtx.hOut` at `frameJ8`. -/
theorem pubVJ8_out (c : P8PublicClaim) (m : ClaimMsgVS) (ρ : Fin 5 → Quad (algebraMap (ZMod p) K δ))
    (ρS : Quad (algebraMap (ZMod p) K δ)) (χ : Coins frameJ8 K) :
    limbVal b (pubVJ8 δ b c m ρ ρS χ) pubOut = 0 := by
  rw [limbVal_pubVJ8_low δ b c m ρ ρS χ _ (by simp [pubOut]),
    limbVal_pubVHQ_low δ b c m ρ _ _ (by simp [pubOut]), FrameVS.limb_pubVH_out]

end Pubs

/-! ## 3b. Two readout identifications (class (c)) -/

section Ident
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)

/-- The J-8 walk's event coins: leaves `0, 1` of `chalsMJ8` are the `frameVSQ` coins `0, 1`. -/
theorem coinW_J8 (χ : Coins frameJ8 K) : chalsMJ8 δ χ 0 = toVSQ χ v0 ∧ chalsMJ8 δ χ 1 = toVSQ χ v1 := by
  rw [ProbJ8.chalsMJ8_lo δ χ 0 (by norm_num), ProbJ8.chalsMJ8_lo δ χ 1 (by norm_num)]
  constructor
  · simp [FrameVS.chalsVS, Chips.ChipRAP.chalsVCL, CellH.hGam, CellH.hRho, FrameVS.toVCL, toVS, toVSQ, v0]
  · simp [FrameVS.chalsVS, Chips.ChipRAP.chalsVCL, CellH.hGam, CellH.hRho, FrameVS.toVCL, toVS, toVSQ, v1]

/-- **#9's readout is the atom walk's data**: `TraceJ8.wdVJ8` (the readout of `withWalkV`) is the walk data
`acceptsJ8_holdsN_final'` reads at the atom-walk view, at any coins and publics. -/
theorem wdV_view (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) (chals pubs : ℕ → K) :
    TraceJ8.wdVJ8 δ b Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV tr =
      walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV chals pubs
        (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV chals pubs (qV δ b Pb tr chals pubs)) :=
  walkDataOf_congr δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV _ _ (by norm_num)
    (by norm_num) (fun j hj => rfl) _ _ _ _

end Ident

/-! ## 4. `LinkJ8`: the hypotheses that are none of (a)–(d) at this commit -/

section Link
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- The external lists of the three handle balances (`.x`: the J-8 walk's and the J chip's reads; `.p`: none;
`.s`: the registry pins and the J chip's consumes). -/
def extJ8 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    (bl : Bal) → List (Fin (mOf bl) → K) :=
  byBal (β := fun bl => List (Fin (mOf bl) → K))
    (ServeH.walkXReqs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) ++
      jRd b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ))
    []
    (pinCons (p := p) (K := K) Pb.regs Pb.idx ++
      jCons b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ))

/-- The providers of the three handle balances (`.x`: the cell table's exports; `.p`: the J-8 walk's records;
`.s`: the J chip's provides, the atom table's inc heads, the atom walk's records). -/
def provsJ8 (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :
    (bl : Bal) → List ((Fin (mOf bl) → K) × K) :=
  byBal (β := fun bl => List ((Fin (mOf bl) → K) × K))
    (cellProvsW b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))
    (ServeH.walkPProvs b Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW))
    (jProv b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) ++
      (pad8 (atomIncProvs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)) ++
        pad8 (ServeH.walkPProvs b Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV))))

/-- The compute requests of balance `bl` with the externals, lifted (`ServedJ8.reqsJ8`). -/
abbrev reqsOf (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (bl : Bal) : List (Fin (mOf bl) → 𝕂′) :=
  reqsJ8 (hn := Pb.hn) (nodes := Pb.nodes) (b := b) (δ := δ) (chalV := chalVJ8 b χ)
    (pubVal := pubVJ8 δ b c M.m M.ρ M.ρS χ) (orbit := Pb.orbit)
    (P := qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) (extJ8 δ b Pb c χ M tr) bl

/-- The compute environments of the trace at the `frameJ8` coins. -/
abbrev envX (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (i : ℕ) : Env (ZMod p) :=
  envsN Pb.hn Pb.nodes (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
    (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ)) i

/-- The cell table of the trace (restricted to the original cell chip). -/
abbrev cellT (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :=
  cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))

/-- The atom table as a cell table (restricted). -/
abbrev atomT (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p)) :=
  cellTableOf δ b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
    (AtomChipHQ.restrictAtomCell δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
      (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA))

/-- The encoder `E(z, y)` at the `frameJ8` coins. -/
abbrev encJ8 (χ : Coins frameJ8 K) : Noun → FP 𝕂′ :=
  encZY (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (Quad.mk (algebraMap (ZMod p) K δ) (χ cY1) (χ cY2))

structure LinkJ8 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
    (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (rA : ℕ → ARow) : Prop where
  -- L1: the IO-list readouts of `R` / `L` at the trace, their budgets, the counts
  rdX : R.D.cxReqs tr χ = reqsOf δ b Pb c χ M tr .x ∧ R.D.cxProvs tr χ = liftP (provsJ8 δ b Pb χ M tr .x)
  budX : (R.D.cxReqs tr χ).length ≤ 3 * r.N + r.W + r.rd ∧ (R.D.cxProvs tr χ).length ≤ r.D
  rdP : L.pReqs tr (toVSQ χ) = reqsOf δ b Pb c χ M tr .p ∧
    L.pProvs tr (toVSQ χ) = liftP (provsJ8 δ b Pb χ M tr .p)
  budP : (L.pReqs tr (toVSQ χ)).length ≤ 2 * r.N ∧ (L.pProvs tr (toVSQ χ)).length ≤ 2 * r.W
  rdS : R.D.svReqs tr χ = reqsOf δ b Pb c χ M tr .s ∧
    R.D.svProvs tr χ = effP (liftP (provsJ8 δ b Pb χ M tr .s))
  budS : (R.D.svReqs tr χ).length ≤ r.N + 2 * r.J + g ∧
    (R.D.svProvs tr χ).length ≤ r.calls + r.heads + r.blocks + r.J
  hcount : ∀ bl, (reqsOf δ b Pb c χ M tr bl).length < p
  rdV : R.D.valReqs tr χ = M.reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) ∧
    R.D.valProvs tr χ = SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))) ++ M.xsC
  budV : (R.D.valReqs tr χ).length ≤ 3 + 2 * r.D + g ∧ (R.D.valProvs tr χ).length ≤ r.D + r.mb
  hcountC : (M.reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))).length < p
  -- L2: the three walk-data readouts
  rdWC : L.cRows tr = rowsWX (fun i => envX δ b Pb c χ M tr i) (fun i => stX (envX δ b Pb c χ M tr i)) ∧
    L.cH tr = Pb.n
  rdWW : L.wdW tr (toVSQ χ) = walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
    (restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))
  -- L3: `EncInj2`'s census / atom-leaf premises
  hext : ∀ j m, extB p rA j = some m → ∃ v, m = .atom v ∧ lenL v ≤ r.maxlen
  hprs : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M tr).map (·.b0)) (extB p rA)),
    pr ∈ R.D.prs tr
  hvp : AtomLeaves (encJ8 δ χ) M.vp (extB p rA)
  -- L4: the J-8 walk's export premises
  hXW : KeysExported (cellT δ b Pb χ M tr)
    (walkDataOf δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
      (restrictWalkK δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)))).X
  hHXW : ∀ j < Pb.nW, ∃ c' ∈ cellT δ b Pb χ M tr,
    (natOf ((walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j).trace WChip.idx),
      WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) false,
      WalkKJ8.childHOfK (walkEnvFA δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
        (WalkJ8.bitFix δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW
          (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)) j) true) = exportRecK c'.b0
  -- L5: the atom table's row reader and its facts, its export event
  hRA : ∀ k : Fin Pb.nA, Reads (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
    (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA) k) (rA k)
  hsA : ∀ k : Fin Pb.nA, (rA k).Small
  hidxA : ∀ k : Fin Pb.nA, (rA k).idx = k
  hrn : ∀ k, Pb.nA ≤ k → (rA k).inc = 0
  hB : AtomChipHQ.LimbsBounded rA
  hwRA : ∀ j, (rA j).wR ≤ 1
  hok : ∀ j, (rA j).inc = 1 → AtomChipHQ.ChainOK rA j
  houtA : ((AtomServedQ.acoins δ (chalsAJ8 δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8 δ χ)).pole) ∉
    IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
        (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA) ++ M.wreqs).map (liftRec (K := K) (L := 𝕂′)))
      (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
        (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA)))
  hcountA : (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8 δ χ) M.pubsA
    (qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA) ++ M.wreqs).length < p
  hservedA : ValidityServed (atomT δ b Pb χ M tr)
  -- L6: the atom walk's export premises
  hseedsV : AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8 δ χ 2) (chalsAJ8 δ χ 3)) (atomT δ b Pb χ M tr)
  hXV : KeysExported (atomT δ b Pb χ M tr)
    (walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV))).X
  hHXV : ∀ j < Pb.nV, ∃ c' ∈ atomT δ b Pb χ M tr,
    (natOf ((walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j).trace WChip.idx),
      childHOf (walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j) false,
      childHOf (walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) j) true) = exportRec c'.b0
  -- L7: the registered nouns' injectivity against the decoded nouns
  hinjE : ∀ id ∈ Pb.regs, ∀ d ∈ decodedNouns2 ((cellT δ b Pb χ M tr).map (·.b0)) (extB p rA),
    encJ8 δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id)) = encJ8 δ χ d → Nock.Jet.Autogen.compile p (Pb.Rt id) = d
  -- L8: the compute root binding
  hseed : limbVal b (pubVJ8 δ b c M.m M.ρ M.ρS χ) pubSeed =
    Walk.rlc (limbVal b (chalVJ8 b χ) chalGammaW) (encT (K := K)
      (rowW (envX δ b Pb c χ M tr 0) (stX (envX δ b Pb c χ M tr 0))).trip) * limbVal b (chalVJ8 b χ) chalAlphaW
  hreal : (stX (envX δ b Pb c χ M tr 0)).isChain = false
  hs : denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
    (hdV (envX δ b Pb c χ M tr 0) xS) = some c.subject
  hf : denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
    (hdV (envX δ b Pb c χ M tr 0) xF) = some c.formula
  he : denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
    (hdV (envX δ b Pb c χ M tr 0) xE) = some c.result

end Link

/-! ## 5. `hsoundJ8` -/

section Sound
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {P g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

theorem hsoundJ8 [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hacc : AcceptsJ8 δ b Pb Rg c χ M tr)
    (hout : ∀ s ∈ allJ8C (withLiftC R L), ¬ s.mem tr χ)
    (hWV : R.wdC tr χ = walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8 δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV)))
    {rA : ℕ → ARow} (hl : LinkJ8 δ b Pb c χ M tr R L rA) :
    Nock.Jet.HoldsN c := by
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hp : 2 ^ 63 + 1 < p := by rw [hpG]; norm_num [Nock.Atoms.p, Nock.Field.p]
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; omega
  have hF' := GeneratedField.primeFieldElems_zmod p
  have O := outJ8_of_outside R L b hout
  have hz2 : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) =
      Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3) := by
    rw [(chalsMJ8_z (δ := δ) χ).1, (chalsMJ8_z (δ := δ) χ).2]
  have hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0 := by
    rw [hz2]; exact O.z_ne
  -- (b) the IO events, read at the trace's lists (L1)
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hx : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.cxReqs tr χ) (R.D.cxProvs tr χ) := O.hout_x hl.budX.1 hl.budX.2
  rw [hl.rdX.1, hl.rdX.2] at hx
  have hpp : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (L.pReqs tr (toVSQ χ)) (L.pProvs tr (toVSQ χ)) := O.hout_p hl.budP.1 hl.budP.2
  rw [hl.rdP.1, hl.rdP.2] at hpp
  have hs : ((coinsCV b δ (chalVJ8 b χ)).gamma, (coinsCV b δ (chalVJ8 b χ)).pole) ∉
      IOFailureEventW (R.D.svReqs tr χ) (R.D.svProvs tr χ) := O.hout_s hl.budS.1 hl.budS.2
  rw [hl.rdS.1, hl.rdS.2] at hs
  have hV : (chalsAJ8 δ χ 0, chalsAJ8 δ χ 1) ∉ WalkVCL.walkEvent (algebraMap (ZMod p) K δ) (R.wdC tr χ) :=
    O.houtV
  rw [hWV] at hV
  have hW := wchain_out L (outside40C R L hout)
  rw [hl.rdWW, ← (coinW_J8 δ χ).1, ← (coinW_J8 δ χ).2] at hW
  have hw0 : (limbVal b (chalVJ8 b χ) chalAlphaW, limbVal b (chalVJ8 b χ) chalGammaW) ∉
      cwEvent (K := K) (L.cRows tr) (L.cH tr) := O.hw rfl rfl
  rw [hl.rdWC.1, hl.rdWC.2] at hw0
  have hα0 : limbVal b (chalVJ8 b χ) chalAlphaW ∉ tileSet (K := K) (foOf (L.cRows tr)) (L.cH tr) := O.hα rfl
  rw [hl.rdWC.1, hl.rdWC.2] at hα0
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) M.reqsC M.xsC hacc.hsumC houtC
    hacc.hxneC hl.hcountC M.vp hacc.hxC hacc.hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  have hEinj := EncInjJ8.encInj2_of_outside (withLiftC R L).D
    (outside_sumJ8_D (withLiftC R L) hout .bivariateCensus (by decide) (by decide) (by decide)) hq' O.z_ne hE
    htabC hl.hvp hl.hext hqM hk hl.hprs
  -- (c) the compute context
  have XC : XCtx Pb.hn Pb.nodes b δ (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb.orbit
      (qX δ b Pb tr (chalVJ8 b χ) (pubVJ8 δ b c M.m M.ρ M.ρS χ))
      (limbVal b (chalVJ8 b χ) chalAlphaW) (limbVal b (chalVJ8 b χ) chalGammaW)
      (limbVal b (pubVJ8 δ b c M.m M.ρ M.ρS χ) pubSeed) :=
    ⟨by omega, hacc.hsatX, hacc.hinjX, hacc.hadjX, rfl, rfl, pubVJ8_IC δ b c M.m M.ρ M.ρS χ, rfl,
      pubVJ8_out δ b c M.m M.ρ M.ρS χ⟩
  exact CorJ8I.acceptsJ8_holdsN_final' (χ := χ) (c := c) (m := M.m) (ρ := M.ρ) (ρS := M.ρS) (C := XC) (hp := hp)
    (provs := provsJ8 δ b Pb χ M tr) (ext := extJ8 δ b Pb c χ M tr)
    (hnC := Pb.hnC) (nodesC := Pb.nodesC) (orbitC := Pb.orbitC) (chalsC := chalsMJ8 δ χ) (pubsC := M.pubsC)
    (QC := qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) (hsatC := hacc.hsatC) (hbindC := hacc.hbindC)
    (hinjC := hacc.hinjC) (hadjC := hacc.hadjC) (hchC := fun _ _ _ => rfl)
    (kroots := Pb.kroots) (hnW := Pb.hnW) (nodesW := Pb.nodesW) (orbitW := Pb.orbitW) (chalsW := chalsMJ8 δ χ)
    (pubsW := M.pubsW) (QW := qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) (hsatW := hacc.hsatW) (hbindW := hacc.hbindW)
    (hF := hF') (hp64 := by rw [hrc]; omega) (hinjW := hacc.hinjW) (hadjW := hacc.hadjW)
    (hchW := fun _ _ _ => rfl)
    (nodesJ := Pb.nodesJ) (orbitJ := Pb.orbitJ) (pubsJ := M.pubsJ) (lay := Pb.lay)
    (PJ := qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) (hsatJ := hacc.hsatJ) (hbindJ := hacc.hbindJ)
    (hinjJ := hacc.hinjJ) (hnJ := hacc.hnJ) (hadjJ := hacc.hadjJ)
    (Rt := Pb.Rt) (regs := Pb.regs) (ids := Pb.ids) (idx := Pb.idx) (rk := Pb.rk)
    (hnA := Pb.hnA) (nodesA := Pb.nodesA) (orbitA := Pb.orbitA) (chalsA := chalsAJ8 δ χ) (pubsA := M.pubsA)
    (QA := qA δ b Pb tr (chalsAJ8 δ χ) M.pubsA) (hsatA := hacc.hsatA) (hbindA := hacc.hbindA)
    (hinjA := hacc.hinjA) (hadjA := hacc.hadjA) (hchA := fun j h1 h2 => chalsAJ8_agree (δ := δ) χ j h1 h2)
    (krootsV := Pb.krootsV) (hnV := Pb.hnV) (nodesV := Pb.nodesV) (orbitV := Pb.orbitV) (chalsV := chalsAJ8 δ χ)
    (pubsV := M.pubsV) (QV := qV δ b Pb tr (chalsAJ8 δ χ) M.pubsV) (hsatV := hacc.hsatV) (hbindV := hacc.hbindV)
    (hinjV := hacc.hinjV) (hadjV := hacc.hadjV) (hchV := fun j h1 h2 => chalsAJ8_agree (δ := δ) χ j h1 h2)
    (hprovX := rfl) (hextX := rfl) (hprovP := rfl) (hextP := rfl) (hprovS := rfl) (hextS := rfl)
    (hGx := hacc.hGx) (hGp := hacc.hGp) (hGS := hacc.hGS)
    (hout := fun bl hbl => by cases bl with | x => exact hx | p => exact hpp | s => exact absurd rfl hbl)
    (houtS := hs) (hcount := hl.hcount)
    (hnpC := hacc.hnpC) (hzC := hzC) (γV := _) (ρV := _) (hokC := chalsOK_J8 (δ := δ) χ)
    (reqsC := M.reqsC) (xsC := M.xsC) (hsumC := hacc.hsumC) (houtC := houtC) (hxneC := hacc.hxneC)
    (hcountC := hl.hcountC) (vp := M.vp) (hxC := hacc.hxC) (hvp0 := hacc.hvp0)
    (E := encJ8 δ χ) (hconsE := fun a b' => by rw [hz2]; rfl) (hE := by rw [hz2]; exact hE)
    (rA := rA) (hvp := hl.hvp) (hEinj := hEinj)
    (hkW := hacc.hkW) (hknW := hacc.hknW) (hkpW := hacc.hkpW) (hXW := hl.hXW) (hHXW := hl.hHXW) (houtW := hW)
    (hRg := hRg) (hlay := hacc.hlay) (hsmall := hacc.hsmall) (huniq := hacc.huniq) (hTpl := hacc.hTpl)
    (hnd := hacc.hnd) (hidx := hacc.hidx) (hrk := hacc.hrk) (hlt := hacc.hlt) (hpinC := hacc.hpinC)
    (hinjE := hl.hinjE)
    (hRA := hl.hRA) (hsA := hl.hsA) (hidxA := hl.hidxA) (hpG := hpG) (hrn := hl.hrn) (hB := hl.hB)
    (hwRA := hl.hwRA) (hok := hl.hok) (wreqs := M.wreqs) (hbalA := hacc.hbalA) (houtA := hl.houtA)
    (hcountA := hl.hcountA) (hnpA := hacc.hnpA) (hzA := O.atom_hz) (hservedA := hl.hservedA)
    (hyV := ⟨rfl, rfl⟩) (hkV := hacc.hkV) (hknV := hacc.hknV) (hkpV := hacc.hkpV) (hseedsV := hl.hseedsV)
    (hXV := hl.hXV) (hHXV := hl.hHXV) (houtV := hV)
    (hseed := hl.hseed) (hα := hα0) (hw := hw0) (hreal := hl.hreal) (x := c) (hs := hl.hs) (hf := hl.hf)
    (he := hl.he)

/-! ## 6. The figure -/

open Classical in
/-- **The J-8 figure**: for every staged strategy `Q`, the probability over the `frameJ8` coins that some message
makes the verifier accept while the claim is false is `< 2^-155` (census corner, `P ≤ 2^66`, `g ≤ 2^31`
registered ids), at the statement binders, conditional on `LinkJ8` at every accepted coin. -/
theorem probJ8_final [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim)
    (R0 : WeightsJ8.DataJ8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P)
    (hAW : Pb.nV ≤ r.AW)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    (hcK : Fintype.card K = VclL.Events.cK) (hr : RowsLe r EncInjJ8.cornerC) (hP : P ≤ 2 ^ 66) (hg : g ≤ 2 ^ 31)
    (hlink : ∀ χ (M : MsgJ8 p K δ), AcceptsJ8 δ b Pb Rg c χ M (Q χ) →
      ∃ rA, LinkJ8 δ b Pb c χ M (Q χ)
        (TraceJ8.withWalkV (g := g) δ b R0 Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV hAW) L rA) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8 p K δ, AcceptsJ8 δ b Pb Rg c χ M (Q χ)) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 :=
  BundleJ8.probJ8C_lt_155_census
    (withLiftC (TraceJ8.withWalkV (g := g) δ b R0 Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV hAW) L) Q hQ _ _
    (fun χ hacc hout => by
      obtain ⟨M, hM⟩ := hacc
      obtain ⟨rA, hl⟩ := hlink χ M hM
      exact hsoundJ8 δ b Pb hRg c χ M (Q χ) _ L hpG hqM hk hM hout (wdV_view δ b Pb (Q χ) _ _) hl)
    hcK hr hP hg

end Sound

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
