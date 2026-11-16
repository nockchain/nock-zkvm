/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8PP.lean

  **`AcceptsJ8''`, the verifier predicate with the atom side at the
  rewired vector `chalsAJ8Z` and the R3a / R3b public checks.**

  * **`toMsgJ8Z`**: `toMsgJ8` with `xsC / vp` read from the atom table's `mb` rows AT `chalsAJ8Z` (the g5 key's
    size entry reads `z`, so `hvp` holds for honest atoms, R3b `hvp_of_mb`) and `wreqs` the atom walk's reads.
  * **`AcceptsJ8''`** (parameters: the public row bounds `r` and the registered-id budget `g`) = `AcceptsJ8'` with the
    atom table AND the atom walk at `chalsAJ8Z`, plus `hcellF : isCellN c.formula` (R3b: an atom formula never
    holds, `ReaderR3bJ8.holdsN_formula_cell`, so the check rejects no true claim), `hnA62 : nA ≤ 2^62` (R3b's
    `SmallU`), `hbud : BudJ8 Pb r (g + N)` (the handle budgets, #6 RE-PRICED at `2N + 2J + g`, `RepriceJ8`) and
    `hbudV` (`|regs| ≤ g`, `nA ≤ mb`, `nA ≤ A`, `nV ≤ AW`: the validity / atom budgets).
  * **`acceptsJ8Z_of''`**: `AcceptsJ8''` ⇒ `AcceptsJ8Z` at `toMsgJ8Z` (as `acceptsJ8_of'`, at `chalsAJ8Z_ok`).
  * **`LinkJ8X''`** = `LinkJ8X'` with the atom fields at `chalsAJ8Z` / `atomTZ` and WITHOUT `hrealA` (derived from
    `hcellF`: `AcceptsJ8ZL.hrealJ8Z`); **`hsoundJ8X''`** (as `hsoundJ8X'`, `hXV` from `hfxA` via
    `AcceptsJ8ZX.hXV_withFpxVZ`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZL
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZX
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8ZB

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP

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
open Nock.ComputeTable (FP)
open Nock.NockVMROM.Thm54.VclL.Handle.CorJ8F (denJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ProbJ8 (chalsAJ8 chalsAJ8_agree chalsOK_J8 chalsAJ8_ok)
open Nock.NockVMROM.Thm54.VclL.Handle.EncZYJ8 (encZY encZY_cell inlineAtoms_encZY)
open Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ListJ8C (DataJ8C allJ8C withLiftC outside40C outside_sumJ8_D)
open Nock.NockVMROM.Thm54.VclL.Handle.Lift40J8 (Data40J8 wchain_out v0 v1)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8 StJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.BundleJ8 (OutJ8 outJ8_of_outside chalsMJ8_z)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P

noncomputable section

section Msg
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`toMsgJ8Z`**: the computed message with the atom side read at `chalsAJ8Z`. -/
def toMsgJ8Z (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) :
    MsgJ8 p K δ where
  m := M.m
  ρ := M.ρ
  ρS := M.ρS
  pubsC := M.pubsC
  pubsW := M.pubsW
  pubsJ := M.pubsJ
  pubsA := M.pubsA
  pubsV := M.pubsV
  reqsC := claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ
  xsC := mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  vp := mbVp δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  wreqs := ServeH.walkXReqs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)

end Msg

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **`AcceptsJ8''`: THE verifier's checks** — `AcceptsJ8'` with the atom table and the atom walk at `chalsAJ8Z`,
plus the formula / atom-table-size / budget public checks. -/
structure AcceptsJ8'' (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ) : Prop where
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
  hsatA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hbindA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < p
  -- the atom walk
  hsatV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV).rap.Satisfies
    (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)
  hbindV : (walkChipHQK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV).BindsPreprocessing
    (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)
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
  -- the cell validity: verifier-computed requests against the cell terminal and the atom g5 terminal (Q2 S2)
  hsumC' : ((claimRecsJ8 δ χ c M.m ++ pinRecsJ8 δ Pb χ).map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 0) (M.pubsC 1) + Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1))
  -- the atom export: provides = old-export consumes + the atom walk's handle reads (Q1, `pubsV 4/5`)
  hbalA' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV WalkHQ.pubXQ) (M.pubsV (WalkHQ.pubXQ + 1))
  -- the atom table's validity terminal (Q2 S3)
  hvalA0 : M.pubsA 0 = 0 ∧ M.pubsA 1 = 0
  -- the fingerprint-export links (Q1): cell ↔ J-8 walk, atom table ↔ atom walk
  hfxC : M.pubsC 2 = M.pubsW 0 ∧ M.pubsC 3 = M.pubsW 1
  hfxA : M.pubsA 2 = M.pubsV 0 ∧ M.pubsA 3 = M.pubsV 1
  hclA : ∀ k : Fin 3, ∀ v, claimNoun c k = .atom v → v < p
  hclI : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (M.m k).1 < p
  hclR : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p
  -- the census size check on the registered and claim cell nouns
  hcen : ∀ x ∈ censusG Pb c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, v < p
  -- public lengths
  hlenC : 3 + Pb.regs.length + 2 * Pb.nC < p
  hlenA : Pb.nA + Pb.nV < p
  hcellF : isCellN c.formula = true
  hnA62 : Pb.nA ≤ 2 ^ 62
  hbud : RealIOJ8.BudJ8 Pb r (g + r.N)
  hbudV : Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW

/-- **`AcceptsJ8''` ⇒ `AcceptsJ8Z` at `toMsgJ8Z`.** -/
theorem acceptsJ8Z_of'' {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8'' δ b Pb Rg c χ M tr r g) :
    AcceptsJ8Z δ b Pb Rg c χ (toMsgJ8Z δ b Pb c χ M tr) tr where
  hsatX := h.hsatX
  hinjX := h.hinjX
  hadjX := h.hadjX
  hsatC := h.hsatC
  hbindC := h.hbindC
  hinjC := h.hinjC
  hadjC := h.hadjC
  hnpC := h.hnpC
  hsatW := h.hsatW
  hbindW := h.hbindW
  hinjW := h.hinjW
  hadjW := h.hadjW
  hkW := h.hkW
  hknW := h.hknW
  hkpW := h.hkpW
  hsatJ := h.hsatJ
  hbindJ := h.hbindJ
  hinjJ := h.hinjJ
  hnJ := h.hnJ
  hadjJ := h.hadjJ
  hsatA := h.hsatA
  hbindA := h.hbindA
  hinjA := h.hinjA
  hadjA := h.hadjA
  hnpA := h.hnpA
  hsatV := h.hsatV
  hbindV := h.hbindV
  hinjV := h.hinjV
  hadjV := h.hadjV
  hkV := h.hkV
  hknV := h.hknV
  hkpV := h.hkpV
  hGx := h.hGx
  hGp := h.hGp
  hGS := h.hGS
  hlay := h.hlay
  hsmall := h.hsmall
  huniq := h.huniq
  hTpl := h.hTpl
  hnd := h.hnd
  hidx := h.hidx
  hrk := h.hrk
  hlt := h.hlt
  hsumC := by
    show _ = _ + ((mbXs δ b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _).map _).sum
    rw [mbXs_sum δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ h.hsatA h.hbindA h.hinjA h.hadjA _ _
      (chalsAJ8Z_ok δ χ)]
    exact h.hsumC'
  hxneC := mbXs_den δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ h.hsatA _ _ (chalsAJ8Z_ok δ χ)
  hbalA := by
    show _ = _ + (((ServeH.walkXReqs b Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV _).map _).map _).sum
    rw [List.map_map]
    refine h.hbalA'.trans ?_
    congr 1
    exact (WalkTeleJ8.walkHQK_reqs_sumQ δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV _
      h.hsatV h.hbindV h.hinjV h.hadjV).symm
  hxC := mbXs_claimVec δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _
  hvp0 := fun k hk => by
    obtain ⟨h1, h2, h3⟩ := mbVp_small δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA _ k hk
    exact ⟨h1, h2, by rw [ZMod.ringChar_zmod_n]; exact h3⟩
  hpinC := fun id hid => List.mem_append_right _ (List.mem_map.mpr ⟨id, hid, rfl⟩)

end Accept

section Derived
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **L5 `hcountA` at `chalsAJ8Z`**, from the public length check `nA + nV < p`. -/
theorem hcountA_ofZ'' (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ)
    (tr : TrJ8 (ZMod p)) (hlen : Pb.nA + Pb.nV < p) :
    (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsA
      (qA δ b Pb tr (chalsAJ8Z δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsA) ++ (toMsgJ8Z δ b Pb c χ M tr).wreqs).length < p := by
  have h1 : (AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsA
      (qA δ b Pb tr (chalsAJ8Z δ χ) (toMsgJ8Z δ b Pb c χ M tr).pubsA)).length ≤ Pb.nA := by
    unfold AtomServedQ.atomCReqs
    refine (AcceptsJ8P.length_flatMap_le _ _ 1 fun i => ?_).trans (by simp)
    split_ifs <;> simp
  have h2 : (toMsgJ8Z δ b Pb c χ M tr).wreqs.length = Pb.nV := by simp [toMsgJ8Z, ServeH.walkXReqs]
  rw [List.length_append, h2]
  omega

end Derived

section Sound
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)
variable {r : RowsJ8} {P g : ℕ}

open Nock.NockVMROM.Thm54.VclL.Compute.LogUp (limbVal)

/-- **`LinkJ8X''`: the residue at `AcceptsJ8''`** — `LinkJ8X'` with the atom fields at `chalsAJ8Z` / `atomTZ`, no
`hrealA` (the formula is a cell, `hcellF`). -/
structure LinkJ8X'' (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8 p K δ)
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
  hRA : ∀ k : Fin Pb.nA, Reads (AtomServedQ.aEF b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) k) (rA k)
  hsA : ∀ k : Fin Pb.nA, (rA k).Small
  hidxA : ∀ k : Fin Pb.nA, (rA k).idx = k
  hrn : ∀ k, Pb.nA ≤ k → (rA k).inc = 0
  hB : AtomChipHQ.LimbsBounded rA
  hwRA : ∀ j, (rA j).wR ≤ 1
  hok : ∀ j, (rA j).inc = 1 → AtomChipHQ.ChainOK rA j
  houtA : ((AtomServedQ.acoins δ (chalsAJ8Z δ χ)).gamma, (AtomServedQ.acoins δ (chalsAJ8Z δ χ)).pole) ∉
    IOFailureEventW ((AtomServedQ.atomCReqs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
        (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA) ++ M.wreqs).map (liftRec (K := K) (L := 𝕂′)))
      (AtomServedQ.liftProvs δ (AtomServedQ.atomProvs b Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA
        (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)))
  hservedA : ValidityServed (atomTZ δ b Pb χ M tr)
  -- L6: the atom walk's export premises
  hseedsV : AWSeedsOK δ (Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3)) (atomTZ δ b Pb χ M tr)
  hHXV : ∀ j < Pb.nV, ∃ c' ∈ atomTZ δ b Pb χ M tr,
    (natOf ((walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) j).trace WChip.idx),
      childHOf (walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) j) false,
      childHOf (walkEnvFA δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV) j) true) = exportRec c'.b0
  -- L7: the registered nouns' injectivity against the decoded nouns
  -- L8: the compute root binding
  -- the census readout covers the registered and claim cell nouns too (Q2 `hinjE_of_outside`)
  hprsG : ∀ pr ∈ EncInjJ8.censusPairs (EncInjJ8.censusList2 ((cellT δ b Pb χ M tr).map (·.b0)) (extB p rA) ++
    censusG Pb c), pr ∈ R.D.prs tr

/-- **`hsoundJ8X''`**: accepted by `AcceptsJ8''`, outside `allJ8X (withFpxV … (withLiftC R L) …)`, at the
statement binders and under `LinkJ8X''` at `toMsgJ8Z`, the claim holds (`hXV` from `hfxA`, `hreal` from
`hcellF`, the claim binding and `hinjE` as in `hsoundJ8'`). -/
theorem hsoundJ8X'' [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p))
    (R : DataJ8C (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r P g)
    (L : Data40J8 (q := ringChar (ZMod p)) (algebraMap (ZMod p) K δ) (TrJ8 (ZMod p)) StJ8 r)
    (hpG : p = Nock.Atoms.p) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen) (hk : 2 * fuelChip ≤ r.leaves)
    {r0 : RowsJ8} {g0 : ℕ} (hacc' : AcceptsJ8'' δ b Pb Rg c χ M tr r0 g0)
    (hout : ∀ s ∈ AtomFpxJ8.allJ8X (AtomFpxJ8.withFpxV δ b (withLiftC R L) Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV
      Pb.nodesA Pb.orbitA), ¬ s.mem tr χ)
    (hbV : Pb.nV ≤ r.AW) (hbA : Pb.nA ≤ r.A)
    (hWV : R.wdC tr χ = walkDataOf δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
      (restrictWalkK δ Pb.krootsV b Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
        (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)))
    {rA : ℕ → ARow} (hl : LinkJ8X'' δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr R L rA) :
    Nock.Jet.HoldsN c := by
  have hacc := acceptsJ8Z_of'' δ b hacc'
  have hAV : Quad.mk (algebraMap (ZMod p) K δ) ((toMsgJ8Z δ b Pb c χ M tr).pubsA 2)
      ((toMsgJ8Z δ b Pb c χ M tr).pubsA 3) =
      Quad.mk (algebraMap (ZMod p) K δ) ((toMsgJ8Z δ b Pb c χ M tr).pubsV 0) ((toMsgJ8Z δ b Pb c χ M tr).pubsV 1) := by
    show Quad.mk _ (M.pubsA 2) (M.pubsA 3) = Quad.mk _ (M.pubsV 0) (M.pubsV 1)
    rw [hacc'.hfxA.1, hacc'.hfxA.2]
  have hXV := AcceptsJ8ZX.hXV_withFpxVZ δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr hacc (withLiftC R L) hout hbV hbA hAV
  replace hout := AtomFpxJ8.outsideC_of_outsideX _ hout
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
  have houtC : (Quad.mk (algebraMap (ZMod p) K δ) (χ c4) (χ c6), Quad.mk (algebraMap (ZMod p) K δ) (χ c5) (χ c7)) ∉
      IOFailureEventW (R.D.valReqs tr χ) (R.D.valProvs tr χ) := O.valid hl.budV.1 hl.budV.2
  rw [hl.rdV.1, hl.rdV.2] at houtC
  have hcountC := hcountC_of' δ b Pb c χ M tr hacc'.hlenC
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ hacc.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 hacc.hinjC hacc.hadjC hacc.hnpC _ _ (chalsOK_J8 (δ := δ) χ) _ _ hacc.hsumC houtC
    hacc.hxneC hcountC _ hacc.hxC hacc.hvp0
  rw [hz2] at htabC
  have hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (χ c2) (χ c3)) (encJ8 δ χ) :=
    inlineAtoms_encZY (by rw [hrc]; exact hpG) _ _
  -- the census at the registered and claim cell nouns (Q2)
  have hG := LinkQ2J8.hinjE_of_outside (withLiftC R L) hout hq' O.z_ne hE htabC hl.hvp hl.hext hqM hk
    (G := censusG Pb c)
    (fun x hx => ⟨(hacc'.hcen x hx).1, fun v hv => hqM v (by rw [hrc]; exact (hacc'.hcen x hx).2 v hv)⟩) hl.hprsG
  have hinjE : ∀ id ∈ Pb.regs, ∀ d ∈ decodedNouns2 ((cellT δ b Pb χ (toMsgJ8Z δ b Pb c χ M tr) tr).map (·.b0))
      (extB p rA), encJ8 δ χ (Nock.Jet.Autogen.compile p (Pb.Rt id)) = encJ8 δ χ d →
        Nock.Jet.Autogen.compile p (Pb.Rt id) = d :=
    fun id hid d hd he => hG _ (List.mem_append_left _ (List.mem_map_of_mem hid)) d hd he
  -- the claim's cell records are served
  have hvpr : ∀ k ∈ (toMsgJ8Z δ b Pb c χ M tr).vp,
      k.2.1 < ringChar (ZMod p) ∧ k.2.2.1 < ringChar (ZMod p) ∧ k.2.2.2 < ringChar (ZMod p) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hacc.hvp0 k hk
    exact ⟨by omega, by omega, h3⟩
  have hcell : ∀ k : Fin 3, isCellN (claimNoun c k) = true →
      denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
        (1, (M.m k).1) = some (claimNoun c k) := by
    intro k hkc
    have hprov := Nock.Jet.PinJ8.regClaims_provided δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)) hF' hsatC0 hbindC0 hacc.hinjC hacc.hadjC _ _ (chalsOK_J8 (δ := δ) χ)
      _ _ hacc.hsumC houtC hacc.hxneC hcountC _ hacc.hxC hvpr (regs := [0])
      (Ef := fun _ => encJ8 δ χ (claimNoun c k)) (rk := fun _ => rkC (claimNoun c k)) (idx := fun _ => (M.m k).1)
      (fun _ _ => List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩, rfl⟩))
      (fun _ _ => by
        have h62 : (rkC (claimNoun c k)).2 < 2 ^ 62 := Nat.mod_lt _ (by positivity)
        rw [hrc]
        exact ⟨hacc'.hclR k hkc, by omega, hacc'.hclI k hkc⟩) 0 (List.mem_singleton_self 0)
    rcases hprov with hc | hv
    · exact claimK_genuine_cell hq' (fun a b' => rfl) hE htabC hl.hvp
        (fun d hd he => hG _ (List.mem_append_right _ (List.mem_map_of_mem
          (List.mem_filter.mpr ⟨List.mem_finRange k, hkc⟩))) d hd he) hc
    · exfalso
      obtain ⟨h1, h2, -⟩ := hl.hvp _ hv
      exact rkC_ne hkc (Prod.ext h1 h2)
  have hden : ∀ k : Fin 3, denJ8 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC) rA
      (hdV (envX δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr 0) (![xS, xF, xE] k)) = some (claimNoun c k) := by
    intro k
    rw [AcceptsJ8ZL.row0_hdZ δ b Pb Rg c χ _ tr (by omega) hacc k]
    exact den_claim _ _ c M.m k (hacc'.hclA k) (hacc'.hclI k) (hcell k)
  have hreal : (stX (envX δ b Pb c χ (toMsgJ8Z δ b Pb c χ M tr) tr 0)).isChain = false :=
    AcceptsJ8ZL.hrealJ8Z δ b Pb Rg c χ _ tr (by omega) hacc hacc'.hcellF
  exact hsoundJ8Z δ b Pb hRg c χ (toMsgJ8Z δ b Pb c χ M tr) tr R L hpG hqM hk hacc hout hWV
    { rdX := hl.rdX, budX := hl.budX, rdP := hl.rdP, budP := hl.budP, rdS := hl.rdS, budS := hl.budS, hcount := hl.hcount, rdV := hl.rdV, budV := hl.budV, rdWC := hl.rdWC, rdWW := hl.rdWW, hext := hl.hext, hprs := hl.hprs, hvp := hl.hvp, hXW := hl.hXW, hHXW := hl.hHXW, hRA := hl.hRA, hsA := hl.hsA, hidxA := hl.hidxA, hrn := hl.hrn, hB := hl.hB, hwRA := hl.hwRA, hok := hl.hok, houtA := hl.houtA, hservedA := hl.hservedA, hseedsV := hl.hseedsV, hHXV := hl.hHXV, hXV := hXV,
      hcountC := hcountC, hcountA := hcountA_ofZ'' δ b Pb c χ M tr hacc'.hlenA, hinjE := hinjE,
      hseed := AcceptsJ8ZL.hseedJ8Z δ b Pb Rg c χ _ tr (by omega) hacc, hreal := hreal,
      hs := hden 0, hf := hden 1, he := hden 2 }

end Sound

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
