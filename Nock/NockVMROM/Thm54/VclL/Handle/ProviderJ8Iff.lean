/-
  Nock/NockVMROM/Thm54/VclL/Handle/ProviderJ8Iff.lean

  `J8providers` (the six chips: compute, cell, walk, J, atom, atom walk), `claimJ8`, `budgetJ8`,
  the iff `acceptsGeneric_j8_iff` with `AcceptsJ8V`, and the transfer of the J-8 bound
  (`probGeneric_j8_final`) and of its non-vacuity (`probGeneric_j8_nonvacuous`) from `CleanJ8`.

  The 50 fields of `AcceptsJ8V` land as: `hprov` (compute 3, cell 5, walk 7, J 1 (`JChipOK`, split into its two
  disjuncts), atom 7, atom walk 1 (`AWChipOK`, split)) = 24 fields; `hbal` (eight classes: `hGx hGp hGS hsumC' hbalA'
  hvalA0 hfxC hfxA`, with the verifier terms of `service`/`validity` in `claimJ8`); `hclaim` (`hlay hsmall huniq hTpl
  hnd hidx hrk hlt hclA hclI hclR hcen hcellF` = 13); `hsize` (`hlenC hlenA`); `hbud` (`hnA62 hbud hbudV`).
  24 + 8 + 13 + 2 + 3 = 50.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CleanJ8
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
import Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8

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
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8A Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base

noncomputable section

section Inst
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- The compute provider (mandatory): `hsatX hinjX hadjX`, read at the claim's compute publics. -/
def provX : Provider (K := K) δ where
  chipOK := fun pv Pb M tr χ =>
    RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ (chalVJ8 b χ) pv Pb.orbit)
        (qX δ b Pb tr (chalVJ8 b χ) pv) ∧
      Function.Injective Pb.nodes ∧
      ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  absentOK := fun _ _ => False
  term := fun β _ M => match β with
    | .export => M.ρ 3
    | .path => M.ρ 4
    | .service => M.ρS
    | _ => 0
  size := fun _ _ => 0

/-- The cell table (mandatory): `hsatC hbindC hinjC hadjC hnpC`. -/
def provC : Provider (K := K) δ where
  chipOK := fun _ Pb M tr χ =>
    (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.Satisfies
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) ∧
      (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).BindsPreprocessing
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) ∧
      Function.Injective Pb.nodesC ∧
      (∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω) ∧
      Pb.nC < ringChar (ZMod p)
  absentOK := fun _ _ => False
  term := fun β _ M => match β with
    | .export => -Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))
    | .validity => -Quad.mk _ (M.pubsC 0) (M.pubsC 1)
    | .fxC => Quad.mk _ (M.pubsC 2) (M.pubsC 3)
    | _ => 0
  size := fun s Pb => match s with
    | .rows => 2 * Pb.nC
    | .atoms => 0

/-- The J-8 walk (mandatory): `hsatW hbindW hinjW hadjW hkW hknW hkpW`. -/
def provW : Provider (K := K) δ where
  chipOK := fun _ Pb M tr χ =>
    (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).rap.Satisfies
        (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) ∧
      (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).BindsPreprocessing
        (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW) ∧
      Function.Injective Pb.nodesW ∧
      (∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω) ∧
      1 ≤ Pb.kroots ∧ Pb.kroots ≤ Pb.nW ∧ Pb.kroots + Pb.nW < ringChar (ZMod p)
  absentOK := fun _ _ => False
  term := fun β _ M => match β with
    | .export => Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1))
    | .path => -Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))
    | .fxC => -Quad.mk _ (M.pubsW 0) (M.pubsW 1)
    | _ => 0
  size := fun _ _ => 0

/-- The J chip (optional): PRESENT = the left disjunct of `JChipOK`, ABSENT = its right disjunct. -/
def provJ : Provider (K := K) δ where
  chipOK := fun _ Pb M tr χ =>
    (jetChipJ8 δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay).rap.Satisfies
        (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) ∧
      (jetChipJ8 δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay).BindsPreprocessing
        (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ) ∧
      Function.Injective Pb.nodesJ ∧ 0 < Pb.nJ ∧
      ∀ (i : Fin Pb.nJ) (hi : (i : ℕ) + 1 < Pb.nJ), Pb.nodesJ ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesJ i * Pb.orbitJ.ω
  absentOK := fun Pb M =>
    Pb.nJ = 0 ∧ M.pubsJ 0 = 0 ∧ M.pubsJ 1 = 0 ∧ M.pubsJ 2 = 0 ∧ M.pubsJ 3 = 0
  term := fun β _ M => match β with
    | .export => Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)
    | .service => Quad.mk _ (M.pubsJ 0) (M.pubsJ 1)
    | _ => 0
  size := fun s Pb => match s with
    | .rows => Pb.regs.length
    | .atoms => 0

/-- The atom table (mandatory), both views: `hsatA hbindA hinjA hadjA hnpA hsatL hbindL`. -/
def provA : Provider (K := K) δ where
  chipOK := fun _ Pb M tr χ =>
    (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
        (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) ∧
      (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
        (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) ∧
      Function.Injective Pb.nodesA ∧
      (∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω) ∧
      Pb.nA < p ∧
      (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
        (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) ∧
      (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
        (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  absentOK := fun _ _ => False
  term := fun β _ M => match β with
    | .service => -Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1))
    | .validity => -Quad.mk _ (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1))
    | .atomHandle => Quad.mk _ (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) -
        Quad.mk _ (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1))
    | .atomValidity => Quad.mk _ (M.pubsA 0) (M.pubsA 1)
    | .fxA => Quad.mk _ (M.pubsA 2) (M.pubsA 3)
    | _ => 0
  size := fun s Pb => match s with
    | .rows => 0
    | .atoms => Pb.nA

/-- The atom walk (optional): PRESENT = the left disjunct of `AWChipOK`, ABSENT = its right disjunct. -/
def provV : Provider (K := K) δ where
  chipOK := fun _ Pb M tr χ =>
    (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV).rap.Satisfies
        (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) ∧
      (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV).BindsPreprocessing
        (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) ∧
      Function.Injective Pb.nodesV ∧
      (∀ (i : Fin Pb.nV) (hi : (i : ℕ) + 1 < Pb.nV), Pb.nodesV ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesV i * Pb.orbitV.ω) ∧
      1 ≤ Pb.krootsV ∧ Pb.krootsV ≤ Pb.nV ∧ Pb.krootsV + Pb.nV < ringChar (ZMod p)
  absentOK := fun Pb M =>
    Pb.krootsV = 0 ∧ M.pubsV 0 = 0 ∧ M.pubsV 1 = 0 ∧ M.pubsV WalkHQ.pubXQ = 0 ∧
      M.pubsV (WalkHQ.pubXQ + 1) = 0 ∧ M.pubsV WalkHQ.pubPQ = 0 ∧ M.pubsV (WalkHQ.pubPQ + 1) = 0
  term := fun β _ M => match β with
    | .service => -Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1))
    | .atomHandle => -Quad.mk _ (M.pubsV WalkHQ.pubXQ) (M.pubsV (WalkHQ.pubXQ + 1))
    | .fxA => -Quad.mk _ (M.pubsV 0) (M.pubsV 1)
    | _ => 0
  size := fun s Pb => match s with
    | .rows => 0
    | .atoms => Pb.nV

/-- **The J-8 provider list**: compute, cell, walk, J, atom, atom walk. -/
def J8providers : List (Provider (K := K) δ) :=
  [provX δ b, provC δ b, provW δ b, provJ δ b, provA δ b, provV δ b]

/-- The registry statics (the J chip's public checks and the registry pin: `hlay … hlt`). -/
def staticsJ8 (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) : Prop :=
  List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids ∧
  (∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
  ((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup ∧
  (∀ i ∈ Pb.regs, Rg i = some ⟨(Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Pb.Rt i)⟩ ∧
    axPosB (Pb.Rt i) = true ∧ (Pb.Rt i).WellTyped p) ∧
  Pb.regs.Nodup ∧
  (∀ id ∈ Pb.regs, Pb.idx id < p) ∧
  (∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0)) ∧
  (∀ id ∈ Pb.regs, (Pb.rk id).1 < ringChar (ZMod p) ∧ (Pb.rk id).2 < ringChar (ZMod p) ∧
    Pb.idx id < ringChar (ZMod p))

/-- **The J-8 claim component**: `pubVJ8`; the verifier terms of `service` (pin consumes) and `validity` (claim and pin
records); the statics and claim checks `hclA hclI hclR hcen hcellF`. -/
def claimJ8 : ClaimSpec (K := K) δ where
  pubs := fun c M χ => pubVJ8 δ b c M.m M.ρ M.ρS χ
  verifierTerm := fun β c Pb M χ => match β with
    | .service => ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum
    | .validity => ((claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ).map fun r => (FiniteIO.compress (m := 5)
        ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum
    | _ => 0
  checks := fun Rg c Pb M =>
    staticsJ8 Pb Rg ∧
    (∀ k : Fin 3, ∀ v, claimNoun c k = .atom v → v < p) ∧
    (∀ k : Fin 3, isCellN (claimNoun c k) = true → (M.m k).1 < p) ∧
    (∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p) ∧
    (∀ x ∈ censusG Pb c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, v < p) ∧
    isCellN c.formula = true

/-- **The J-8 budget component**: `hlenC` (`3 + regs + 2·nC < p`), `hlenA` (`nA + nV < p`), `hnA62 hbud hbudV`. -/
def budgetJ8 : Budget (p := p) where
  offset := fun s _ => match s with
    | .rows => 3
    | .atoms => 0
  cap := fun _ => p
  ok := fun Pb r g => Pb.nA ≤ 2 ^ 62 ∧ RealIOJ8.BudJ8 Pb r (g + r.N) ∧
    (Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW)

variable {δ b}

/-- **THE IFF.**  `AcceptsGeneric` at the J-8 providers is `AcceptsJ8V`, at the same binders. -/
theorem acceptsGeneric_j8_iff (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ) :
    AcceptsGeneric δ (J8providers δ b) (claimJ8 δ b) budgetJ8 Pb Rg c χ M tr r g ↔
      AcceptsJ8V δ b Pb Rg c χ M tr r g := by
  constructor
  · intro h
    have hP := h.hprov
    have hX := hP (provX δ b) (by simp [J8providers])
    have hC := hP (provC δ b) (by simp [J8providers])
    have hW := hP (provW δ b) (by simp [J8providers])
    have hJ := hP (provJ δ b) (by simp [J8providers])
    have hA := hP (provA δ b) (by simp [J8providers])
    have hV := hP (provV δ b) (by simp [J8providers])
    have hX' : (provX δ b).chipOK (pubVJ8 δ b c M.m M.ρ M.ρS χ) Pb M tr χ := hX.resolve_right id
    have hC' := hC.resolve_right id
    have hW' := hW.resolve_right id
    have hA' := hA.resolve_right id
    obtain ⟨hsatX, hinjX, hadjX⟩ := hX'
    obtain ⟨hsatC, hbindC, hinjC, hadjC, hnpC⟩ := hC'
    obtain ⟨hsatW, hbindW, hinjW, hadjW, hkW, hknW, hkpW⟩ := hW'
    obtain ⟨hsatA, hbindA, hinjA, hadjA, hnpA, hsatL, hbindL⟩ := hA'
    obtain ⟨hstat, hclA, hclI, hclR, hcen, hcellF⟩ := h.hclaim
    obtain ⟨hlay, hsmall, huniq, hTpl, hnd, hidx, hrk, hlt⟩ := hstat
    obtain ⟨hnA62, hbud, hbudV⟩ := h.hbud
    have hs1 := h.hsize .rows
    have hs2 := h.hsize .atoms
    simp only [J8providers, provX, provC, provW, provJ, provA, provV, budgetJ8, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at hs1 hs2
    have e1 := h.hbal .export
    have e2 := h.hbal .path
    have e3 := h.hbal .service
    have e4 := h.hbal .validity
    have e5 := h.hbal .atomHandle
    have e6 := h.hbal .atomValidity
    have e7 := h.hbal .fxC
    have e8 := h.hbal .fxA
    simp only [J8providers, provX, provC, provW, provJ, provA, provV, claimJ8, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at e1 e2 e3 e4 e5 e6 e7 e8
    refine
      { hsatX := hsatX, hinjX := hinjX, hadjX := hadjX
        hsatC := hsatC, hbindC := hbindC, hinjC := hinjC, hadjC := hadjC, hnpC := hnpC
        hsatW := hsatW, hbindW := hbindW, hinjW := hinjW, hadjW := hadjW, hkW := hkW, hknW := hknW, hkpW := hkpW
        hJk := hJ
        hsatA := hsatA, hbindA := hbindA, hinjA := hinjA, hadjA := hadjA, hnpA := hnpA
        hVk := hV
        hGx := by linear_combination e1
        hGp := by linear_combination e2
        hGS := by linear_combination e3
        hlay := hlay, hsmall := hsmall, huniq := huniq, hTpl := hTpl, hnd := hnd, hidx := hidx, hrk := hrk
        hlt := hlt
        hsumC' := by linear_combination e4
        hbalA' := by linear_combination e5
        hvalA0 := ?_
        hfxC := ?_
        hfxA := ?_
        hclA := hclA, hclI := hclI, hclR := hclR, hcen := hcen
        hlenC := by omega
        hlenA := by omega
        hcellF := hcellF, hnA62 := hnA62, hbud := hbud, hbudV := hbudV
        hsatL := hsatL, hbindL := hbindL }
    · have := (Quad.mk_eq_zero_iff (algebraMap (ZMod p) K δ) _ _).1 (by simpa using e6)
      exact this
    · have h' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 2) (M.pubsC 3) =
          Quad.mk (algebraMap (ZMod p) K δ) (M.pubsW 0) (M.pubsW 1) := by linear_combination e7
      have := Quad.mk_injective (algebraMap (ZMod p) K δ) (a₁ := (M.pubsC 2, M.pubsC 3))
        (a₂ := (M.pubsW 0, M.pubsW 1)) h'
      simpa only [Prod.mk.injEq] using this
    · have h' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA 2) (M.pubsA 3) =
          Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV 0) (M.pubsV 1) := by linear_combination e8
      have := Quad.mk_injective (algebraMap (ZMod p) K δ) (a₁ := (M.pubsA 2, M.pubsA 3))
        (a₂ := (M.pubsV 0, M.pubsV 1)) h'
      simpa only [Prod.mk.injEq] using this
  · intro h
    refine
      { hprov := ?_, hbal := ?_, hclaim := ?_, hsize := ?_, hbud := ?_ }
    · intro P hP
      simp only [J8providers, List.mem_cons, List.mem_nil_iff, or_false] at hP
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨h.hsatX, h.hinjX, h.hadjX⟩
      · exact Or.inl ⟨h.hsatC, h.hbindC, h.hinjC, h.hadjC, h.hnpC⟩
      · exact Or.inl ⟨h.hsatW, h.hbindW, h.hinjW, h.hadjW, h.hkW, h.hknW, h.hkpW⟩
      · exact h.hJk
      · exact Or.inl ⟨h.hsatA, h.hbindA, h.hinjA, h.hadjA, h.hnpA, h.hsatL, h.hbindL⟩
      · exact h.hVk
    · intro β
      cases β <;>
        simp only [J8providers, provX, provC, provW, provJ, provA, provV, claimJ8, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
      · linear_combination h.hGx
      · linear_combination h.hGp
      · linear_combination h.hGS
      · linear_combination h.hsumC'
      · linear_combination h.hbalA'
      · obtain ⟨h0, h1⟩ := h.hvalA0
        have hz := (Quad.mk_eq_zero_iff (algebraMap (ZMod p) K δ) (M.pubsA 0) (M.pubsA 1)).2 ⟨h0, h1⟩
        linear_combination hz
      · obtain ⟨h0, h1⟩ := h.hfxC
        rw [h0, h1]; ring
      · obtain ⟨h0, h1⟩ := h.hfxA
        rw [h0, h1]; ring
    · exact ⟨⟨h.hlay, h.hsmall, h.huniq, h.hTpl, h.hnd, h.hidx, h.hrk, h.hlt⟩, h.hclA, h.hclI, h.hclR, h.hcen,
        h.hcellF⟩
    · intro s
      cases s <;>
        simp only [J8providers, provX, provC, provW, provJ, provA, provV, budgetJ8, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
      · have := h.hlenC; omega
      · have := h.hlenA; omega
    · exact ⟨h.hnA62, h.hbud, h.hbudV⟩

variable (δ b) [DecidableEq K]

open Classical in
/-- **The J-8 bound at `AcceptsGeneric J8providers`**: `probJ8V_final_clean` with the event
rewritten through the iff.  Same binders, same figure `< 2^-155`. -/
theorem probGeneric_j8_final [CharP K p] [CharP (Quad (algebraMap (ZMod p) K δ)) p] (Pb : PubJ8 p)
    {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    {r : RowsJ8} {g : ℕ}
    (hr : RowsLe r EncInjJ8.cornerC) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsGeneric δ (J8providers δ b) (claimJ8 δ b) budgetJ8 Pb Rg c χ M (Q χ) r g) ∧
          ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  have h := CleanJ8.probJ8V_final_clean δ b Pb hRg c Q hQ hpG hcK hr hqM hk hmax hg hLC hLM hLW hLA hLV hnM hreg
  have hset : (Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsGeneric δ (J8providers δ b) (claimJ8 δ b) budgetJ8 Pb Rg c χ M (Q χ) r g) ∧
          ¬ Nock.Jet.HoldsN c) =
      (Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ8V δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c) := by
    refine Finset.filter_congr fun χ _ => ?_
    rw [exists_congr fun M => acceptsGeneric_j8_iff Pb Rg c χ M (Q χ) r g]
  rw [hset]
  exact h

/-- **Non-vacuity at `AcceptsGeneric J8providers`**: `probJ8V_nonvacuous_clean` through the iff (`.2`). -/
theorem probGeneric_j8_nonvacuous (hpG : p = Nock.Atoms.p) (Rt : ℕ → Nock.Jet.Autogen.Tpl) :
    ∃ (Pb : PubJ8 p) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ),
      AcceptsGeneric δ (J8providers δ b) (claimJ8 δ b) budgetJ8 Pb R0 c0 χ M tr r g ∧ Pb.krootsV = 0 ∧
        ¬ 0 < Pb.krootsV ∧ Pb.nJ = 0 ∧ Pb.regs = [] ∧ Nock.Jet.HoldsN c0 := by
  obtain ⟨Pb, χ, M, tr, r, g, h, h1, h2, h3, h4, h5⟩ := CleanJ8.probJ8V_nonvacuous_clean (K := K) δ b hpG Rt
  exact ⟨Pb, χ, M, tr, r, g, (acceptsGeneric_j8_iff Pb R0 c0 χ M tr r g).2 h, h1, h2, h3, h4, h5⟩

end Inst

end

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8
#print axioms acceptsGeneric_j8_iff
#print axioms probGeneric_j8_final
#print axioms probGeneric_j8_nonvacuous
end Axioms

end Nock.NockVMROM.Thm54.VclL.Handle.ProviderJ8
