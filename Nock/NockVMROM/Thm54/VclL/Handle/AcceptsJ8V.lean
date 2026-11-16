/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ8V.lean

  * **`AWChipOK`**: the atom walk's seven conjuncts of `AcceptsJ8''''` (`hsatV hbindV hinjV hadjV hkV hknV hkpV`), or
    ABSENT: `krootsV = 0` and the six atom-walk publics the verifier's equations read are `0` (`pubsV 0, 1` in `hfxA`,
    `pubsV pubXQ, pubXQ+1` in `hbalA'`, `pubsV pubPQ, pubPQ+1` in `hGS`).
    `PubJ8` has
    the FIELD `hnV : 0 < nV` (the walk chip `walkChipHQK` takes it), so `nV = 0` is uninhabited (`nV_pos`) and the
    absent flag is the public `krootsV = 0` instead (disjoint from the present case, which has `hkV : 1 ≤ krootsV`).
  * **`AcceptsJ8V`** = `AcceptsJ8''''` with the seven atom-walk conjuncts replaced by `hVk : AWChipOK …`; every other
    conjunct verbatim.  `toNV_of_pos` / `ofNV` / `iff_NV_of_pos`: at `1 ≤ krootsV` it IS `AcceptsJ8''''`.
  * **`probJ8V_present`**: the J-8 bound over `AcceptsJ8V` at every PRESENT layout (`1 ≤ krootsV`), < 2^-155 at
    `probJ8NV_final`'s binders (events and figure unchanged).
  * The soundness chain needs the #4 and #6
    balances WITHOUT the atom walk's lists; "outside the events WITH them" does not give that.  So the bound at absent
    layouts is NOT derived here: it needs V-free event readouts at absent layouts (same budgets, so the same figure),
    or a `PubJ8` retype admitting `nV = 0` (then the lists are empty, as for J).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.LinkJ8NV
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V

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

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL toHQ)
open Nock.NockVMROM.Thm54.VclL.Handle.ReaderR3bJ8 (SmallU)

noncomputable section

open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G


open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L

section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The atom walk, present or absent.**  Present: the seven atom-walk conjuncts of `AcceptsJ8''''`.  Absent: no
atom-walk root (`krootsV = 0`) and the six atom-walk publics read by the verifier's equations are `0`. -/
def AWChipOK (krootsV : ℕ) {hV nV : ℕ} (hnV : 0 < nV) (nodesV : Fin nV → ZMod p)
    (orbitV : StrictOrbitDomain (ZMod p) 3 hV) (chalsV pubsV : ℕ → K)
    (QV : Fin (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.w → (ZMod p)[X]) : Prop :=
  ((walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.Satisfies QV ∧
      (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).BindsPreprocessing QV ∧
      Function.Injective nodesV ∧
      (∀ (i : Fin nV) (hi : (i : ℕ) + 1 < nV), nodesV ⟨(i : ℕ) + 1, hi⟩ = nodesV i * orbitV.ω) ∧
      1 ≤ krootsV ∧ krootsV ≤ nV ∧ krootsV + nV < ringChar (ZMod p)) ∨
    (krootsV = 0 ∧ pubsV 0 = 0 ∧ pubsV 1 = 0 ∧ pubsV WalkHQ.pubXQ = 0 ∧ pubsV (WalkHQ.pubXQ + 1) = 0 ∧
      pubsV WalkHQ.pubPQ = 0 ∧ pubsV (WalkHQ.pubPQ + 1) = 0)

/-- **`AWChipOK` with a root is the present block.** -/
theorem aw_present_of_pos {krootsV : ℕ} {hV nV : ℕ} {hnV : 0 < nV} {nodesV : Fin nV → ZMod p}
    {orbitV : StrictOrbitDomain (ZMod p) 3 hV} {chalsV pubsV : ℕ → K}
    {QV : Fin (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.w → (ZMod p)[X]}
    (hk : AWChipOK δ b krootsV hnV nodesV orbitV chalsV pubsV QV) (hpos : 1 ≤ krootsV) :
    (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.Satisfies QV ∧
      (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).BindsPreprocessing QV ∧
      Function.Injective nodesV ∧
      (∀ (i : Fin nV) (hi : (i : ℕ) + 1 < nV), nodesV ⟨(i : ℕ) + 1, hi⟩ = nodesV i * orbitV.ω) ∧
      1 ≤ krootsV ∧ krootsV ≤ nV ∧ krootsV + nV < ringChar (ZMod p) := by
  rcases hk with h | h
  · exact h
  · exact absurd h.1 (by omega)

/-- **At `krootsV = 0` the block is exactly the six zero publics** (no chip conjunct remains). -/
theorem aw_absent_iff {krootsV : ℕ} {hV nV : ℕ} {hnV : 0 < nV} {nodesV : Fin nV → ZMod p}
    {orbitV : StrictOrbitDomain (ZMod p) 3 hV} {chalsV pubsV : ℕ → K}
    {QV : Fin (walkChipHQK δ krootsV b hnV nodesV orbitV chalsV pubsV).rap.w → (ZMod p)[X]} (h0 : krootsV = 0) :
    AWChipOK δ b krootsV hnV nodesV orbitV chalsV pubsV QV ↔
      (pubsV 0 = 0 ∧ pubsV 1 = 0 ∧ pubsV WalkHQ.pubXQ = 0 ∧ pubsV (WalkHQ.pubXQ + 1) = 0 ∧
        pubsV WalkHQ.pubPQ = 0 ∧ pubsV (WalkHQ.pubPQ + 1) = 0) := by
  constructor
  · rintro (⟨-, -, -, -, h, -⟩ | ⟨-, h⟩)
    · exact absurd h (by omega)
    · exact h
  · intro h; exact Or.inr ⟨h0, h⟩

/-- **`AcceptsJ8V`: THE verifier's checks, the J chip and the atom walk each present or absent.**  `AcceptsJ8''''`
with the atom walk's seven conjuncts `hsatV hbindV hinjV hadjV hkV hknV hkpV` replaced by `hVk : AWChipOK …`: either
those seven, or `krootsV = 0` and the six atom-walk publics `0` (then `hfxA` gives `pubsA 2 = pubsA 3 = 0`, `hbalA'`
has no walk term, `hGS` no walk provides).  No other conjunct changes. -/
structure AcceptsJ8V (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
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
  hJk : JGenJ8.JChipOK δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
  -- the atom table
  hsatA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hbindA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < p
  -- the atom walk: PRESENT (its seven conjuncts) or ABSENT (`krootsV = 0`, the six atom-walk publics `0`; NV3a)
  hVk : AWChipOK δ b Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)
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
  -- the atom table at the variant chip (`AcceptsJ8'''`)
  hsatL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hbindL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
variable {δ b}

/-- **Present case**: `AcceptsJ8V` with an atom-walk root is `AcceptsJ8''''`. -/
theorem toNV_of_pos {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (hpos : 1 ≤ Pb.krootsV) : AcceptsJ8'''' δ b Pb Rg c χ M tr r g :=
  have hV := aw_present_of_pos δ b h.hVk hpos
  { hsatX := h.hsatX
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
    hJk := h.hJk
    hsatA := h.hsatA
    hbindA := h.hbindA
    hinjA := h.hinjA
    hadjA := h.hadjA
    hnpA := h.hnpA
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
    hsumC' := h.hsumC'
    hbalA' := h.hbalA'
    hvalA0 := h.hvalA0
    hfxC := h.hfxC
    hfxA := h.hfxA
    hclA := h.hclA
    hclI := h.hclI
    hclR := h.hclR
    hcen := h.hcen
    hlenC := h.hlenC
    hlenA := h.hlenA
    hcellF := h.hcellF
    hnA62 := h.hnA62
    hbud := h.hbud
    hbudV := h.hbudV
    hsatL := h.hsatL
    hbindL := h.hbindL
    hsatV := hV.1
    hbindV := hV.2.1
    hinjV := hV.2.2.1
    hadjV := hV.2.2.2.1
    hkV := hV.2.2.2.2.1
    hknV := hV.2.2.2.2.2.1
    hkpV := hV.2.2.2.2.2.2 }

/-- **`AcceptsJ8''''` is the present case of `AcceptsJ8V`.** -/
theorem ofNV {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8'''' δ b Pb Rg c χ M tr r g) :
    AcceptsJ8V δ b Pb Rg c χ M tr r g :=
  { hsatX := h.hsatX
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
    hJk := h.hJk
    hsatA := h.hsatA
    hbindA := h.hbindA
    hinjA := h.hinjA
    hadjA := h.hadjA
    hnpA := h.hnpA
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
    hsumC' := h.hsumC'
    hbalA' := h.hbalA'
    hvalA0 := h.hvalA0
    hfxC := h.hfxC
    hfxA := h.hfxA
    hclA := h.hclA
    hclI := h.hclI
    hclR := h.hclR
    hcen := h.hcen
    hlenC := h.hlenC
    hlenA := h.hlenA
    hcellF := h.hcellF
    hnA62 := h.hnA62
    hbud := h.hbud
    hbudV := h.hbudV
    hsatL := h.hsatL
    hbindL := h.hbindL
    hVk := Or.inl ⟨h.hsatV, h.hbindV, h.hinjV, h.hadjV, h.hkV, h.hknV, h.hkpV⟩ }

/-- **At a present layout the two predicates coincide.** -/
theorem iff_NV_of_pos {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (hpos : 1 ≤ Pb.krootsV) :
    AcceptsJ8V δ b Pb Rg c χ M tr r g ↔ AcceptsJ8'''' δ b Pb Rg c χ M tr r g :=
  ⟨fun h => toNV_of_pos h hpos, ofNV⟩

/-- **Absent case: the atom-table fingerprint export terminal is `0`** (`hfxA` at `pubsV 0 = pubsV 1 = 0`). -/
theorem absent_fxA {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (h0 : Pb.krootsV = 0) : M.pubsA 2 = 0 ∧ M.pubsA 3 = 0 := by
  obtain ⟨h1, h2, -⟩ := (aw_absent_iff δ b h0).1 h.hVk
  exact ⟨h.hfxA.1.trans h1, h.hfxA.2.trans h2⟩

/-- (The J-8 events, by contrast, are read off `tr.V`: `axReqs_reads_V`.) -/
theorem absent_trV_free {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ8' p K δ} {tr : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ} (h : AcceptsJ8V δ b Pb Rg c χ M tr r g)
    (h0 : Pb.krootsV = 0) (V' : Fin 166 → (ZMod p)[X]) :
    AcceptsJ8V δ b Pb Rg c χ M { tr with V := V' } r g :=
  { hsatX := h.hsatX
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
    hJk := h.hJk
    hsatA := h.hsatA
    hbindA := h.hbindA
    hinjA := h.hinjA
    hadjA := h.hadjA
    hnpA := h.hnpA
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
    hsumC' := h.hsumC'
    hbalA' := h.hbalA'
    hvalA0 := h.hvalA0
    hfxC := h.hfxC
    hfxA := h.hfxA
    hclA := h.hclA
    hclI := h.hclI
    hclR := h.hclR
    hcen := h.hcen
    hlenC := h.hlenC
    hlenA := h.hlenA
    hcellF := h.hcellF
    hnA62 := h.hnA62
    hbud := h.hbud
    hbudV := h.hbudV
    hsatL := h.hsatL
    hbindL := h.hbindL
    hVk := Or.inr ⟨h0, (aw_absent_iff δ b h0).1 h.hVk⟩ }

end Accept

section Stop
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))] (b : Basis (Fin 3) (ZMod p) K)

theorem nV_pos (Pb : PubJ8 p) : Pb.nV ≠ 0 := Nat.pos_iff_ne_zero.mp Pb.hnV

theorem axReqs_reads_V (Pb : PubJ8 p) (tr : TrJ8 (ZMod p)) :
    1 ≤ Pb.nV ∧ Pb.nV ≤ (RealAJ8.axReqsJ8 δ b Pb tr).length := by
  refine ⟨Pb.hnV, ?_⟩
  unfold RealAJ8.axReqsJ8
  rw [List.length_map, List.length_append, RealIOJ8.walkXReqs_length]
  omega

end Stop

section Final
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {r : RowsJ8} {g : ℕ}

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

open Classical in
/-- **The J-8 bound over `AcceptsJ8V` at every PRESENT layout** (`1 ≤ krootsV`): `Pr_χ[(∃ M, AcceptsJ8V … (Q χ) r g)
∧ ¬ HoldsN c] < 2^-155` at exactly `LinkJ8NV.probJ8NV_final`'s binders plus `hkV`; the events and the figure are
`probJ8NV_final`'s. -/
theorem probJ8V_present [CharP K p] [CharP 𝕂′ p] (Pb : PubJ8 p) {Rg : Nock.Jet.Registry} (hRg : Rg.Faithful)
    (c : P8PublicClaim) (Q : Coins frameJ8 K → TrJ8 (ZMod p)) (hQ : StJ8 Q)
    (hpG : p = Nock.Atoms.p) (hcK : Fintype.card K = VclL.Events.cK)
    (hr : RowsLe r EncInjJ8.cornerC) (hqM : ∀ x < ringChar (ZMod p), lenL x ≤ r.maxlen)
    (hk : 2 * fuelChip ≤ r.leaves) (hmax : Pb.nA + 2 ≤ r.maxlen) (hg : g ≤ 2 ^ 31)
    (hLC : Pb.n ≤ r.N) (hLM : Pb.nC ≤ r.D) (hLW : Pb.nW ≤ r.W) (hLA : Pb.nA ≤ r.A) (hLV : Pb.nV ≤ r.AW)
    (hnM : Pb.nC ≤ 2 ^ 31) (hreg : (censusG Pb c).length ≤ 2 ^ 31) (hkV : 1 ≤ Pb.krootsV) :
    ((Finset.univ.filter fun χ : Coins frameJ8 K =>
        (∃ M : MsgJ8' p K δ, AcceptsJ8V δ b Pb Rg c χ M (Q χ) r g) ∧ ¬ Nock.Jet.HoldsN c).card : ℚ) /
      Fintype.card (Coins frameJ8 K) < 1 / (2 : ℚ) ^ 155 := by
  refine lt_of_le_of_lt ?_ (LinkJ8NV.probJ8NV_final δ b Pb hRg c Q hQ hpG hcK hr hqM hk hmax hg hLC hLM hLW hLA hLV
    hnM hreg)
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (by
    intro χ hχ
    rw [Finset.mem_filter] at hχ ⊢
    obtain ⟨hu, ⟨M, hM⟩, hn⟩ := hχ
    exact ⟨hu, ⟨M, toNV_of_pos hM hkV⟩, hn⟩)

end Final

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
