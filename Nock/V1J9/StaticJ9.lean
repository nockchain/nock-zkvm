/-
  Nock/V1J9/StaticJ9.lean

  **The executable J-9 checker, first step: the split of `AcceptsJ9V`
  into three blocks, and the executable public-equation check.**

  * **`StaticJ9 Pb c m r g`**: `StaticJ8` with `hclA` dropped, `hclI` extended to the big-atom positions, `hcen` →
    `hcen'` (`censusGJ9`, limb lengths `lenL v ≤ nA + 2`).  **`checkStaticJ9`** / **`checkStaticJ9_iff`**.
  * **`PubEqJ9`**: `PubEqJ8` with `hsumC'` over `claimRecsJ9`; **`ChipsJ9`**: `ChipsJ8` with `hsatX` at `pubVJ9`.
  * **`acceptsJ9V_iff : AcceptsJ9V … ↔ StaticJ9 … ∧ PubEqJ9 … ∧ ChipsJ9 …`** — no conjunct dropped, none added.
  * **`claimBigRecsE`**, **`claimRecsJ9E`** (= `claimRecsJ8E ++ claimBigRecsE`) with `claimRecsJ9E_spec`;
    **`checkPubJ9E`** / **`checkPubJ9E_iff`**; **`acceptsJ9V_iff_exe`**.
-/
import Nock.V1J8.PubExe
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.V1J9

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
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8G
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.Jet.ChipJ8 (entsX ents0T ents1T ents2T ents3)

open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V
open Nock.V1J8

/-! ## 1. The K-free block `StaticJ9` and its checker -/

section Static
variable {p : ℕ} [Fact p.Prime]

/-- **The K-free conjuncts of `AcceptsJ9V`** (`StaticJ8` with `hclA` dropped, `hclI` extended, `hcen'`). -/
structure StaticJ9 (Pb : PubJ8 p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ8) (g : ℕ) : Prop where
  hinjX : Function.Injective Pb.nodes
  hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  hinjC : Function.Injective Pb.nodesC
  hadjC : ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω
  hnpC : Pb.nC < p
  hinjW : Function.Injective Pb.nodesW
  hadjW : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω
  hkW : 1 ≤ Pb.kroots
  hknW : Pb.kroots ≤ Pb.nW
  hkpW : Pb.kroots + Pb.nW < p
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < p
  hlay : List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids
  hsmall : ∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p
  huniq : ((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup
  haxT : ∀ i ∈ Pb.regs, axPosB (Pb.Rt i) = true
  hnd : Pb.regs.Nodup
  hidx : ∀ id ∈ Pb.regs, Pb.idx id < p
  hrk : ∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0)
  hlt : ∀ id ∈ Pb.regs, (Pb.rk id).1 < p ∧ (Pb.rk id).2 < p ∧ Pb.idx id < p
  hclI : ∀ k : Fin 3, (isCellN (claimNoun c k) = true ∨ isBigN p (claimNoun c k) = true) → (m k).1 < p
  hclR : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p
  hcen' : ∀ x ∈ censusGJ9 Pb c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ Pb.nA + 2
  hlenC : 3 + Pb.regs.length + 2 * Pb.nC < p
  hlenA : Pb.nA + Pb.nV < p
  hcellF : isCellN c.formula = true
  hnA62 : Pb.nA ≤ 2 ^ 62
  hbud : RealIOJ8.BudJ8 Pb r (g + r.N)
  hbudV : Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW

/-- **The executable J-9 static check**: one `Bool` per conjunct of `StaticJ9`, in field order. -/
def checkStaticJ9 (Pb : PubJ8 p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ8) (g : ℕ) : Bool :=
  injB Pb.nodes && adjB Pb.nodes Pb.orbit.ω &&
  injB Pb.nodesC && adjB Pb.nodesC Pb.orbitC.ω && decide (Pb.nC < p) &&
  injB Pb.nodesW && adjB Pb.nodesW Pb.orbitW.ω && decide (1 ≤ Pb.kroots) && decide (Pb.kroots ≤ Pb.nW) &&
    decide (Pb.kroots + Pb.nW < p) &&
  injB Pb.nodesA && adjB Pb.nodesA Pb.orbitA.ω && decide (Pb.nA < p) &&
  decide (List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids) &&
  decide (∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) &&
  decide (((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup) &&
  decide (∀ i ∈ Pb.regs, axPosB (Pb.Rt i) = true) &&
  decide Pb.regs.Nodup &&
  decide (∀ id ∈ Pb.regs, Pb.idx id < p) &&
  decide (∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0)) &&
  decide (∀ id ∈ Pb.regs, (Pb.rk id).1 < p ∧ (Pb.rk id).2 < p ∧ Pb.idx id < p) &&
  decide (∀ k : Fin 3, (isCellN (claimNoun c k) = true ∨ isBigN p (claimNoun c k) = true) → (m k).1 < p) &&
  decide (∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p) &&
  decide (∀ x ∈ censusGJ9 Pb c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ Pb.nA + 2) &&
  decide (3 + Pb.regs.length + 2 * Pb.nC < p) &&
  decide (Pb.nA + Pb.nV < p) &&
  isCellN c.formula &&
  decide (Pb.nA ≤ 2 ^ 62) &&
  budB Pb r (g + r.N) &&
  decide (Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW)

/-- **`checkStaticJ9_iff`**: the static check is exactly `StaticJ9`. -/
theorem checkStaticJ9_iff (Pb : PubJ8 p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ8) (g : ℕ) :
    checkStaticJ9 Pb c m r g = true ↔ StaticJ9 Pb c m r g := by
  simp only [checkStaticJ9, Bool.and_eq_true, decide_eq_true_eq, injB_iff, adjB_iff, budB_iff, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩

end Static

/-! ## 2. The public equations `PubEqJ9`, the chip residue `ChipsJ9`, and the split -/

section Split
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The eight public equations of `AcceptsJ9V`** (`PubEqJ8` with `hsumC'` over `claimRecsJ9`). -/
def PubEqJ9 (Pb : PubJ8 p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ8' p K δ) : Prop :=
  (M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))) ∧
  (M.ρ 4 = Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))) ∧
  (M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1))) ∧
  (((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb χ).map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 0) (M.pubsC 1) +
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1))) ∧
  (Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV WalkHQ.pubXQ) (M.pubsV (WalkHQ.pubXQ + 1))) ∧
  (M.pubsA 0 = 0 ∧ M.pubsA 1 = 0) ∧
  (M.pubsC 2 = M.pubsW 0 ∧ M.pubsC 3 = M.pubsW 1) ∧
  (M.pubsA 2 = M.pubsV 0 ∧ M.pubsA 3 = M.pubsV 1)

/-- **The residue**: the per-chip conjuncts of `AcceptsJ9V` (verbatim; `hsatX` at `pubVJ9`), and `hTpl`'s registry
equation with `WellTyped`. -/
structure ChipsJ9 (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) : Prop where
  hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX Pb.hn Pb.nodes b δ (chalVJ8 b χ)
    (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
  hsatC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.Satisfies
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hbindC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).BindsPreprocessing
    (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
  hsatW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).rap.Satisfies
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hbindW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).BindsPreprocessing
    (qW δ b Pb tr (chalsMJ8 δ χ) M.pubsW)
  hJk : JGenJ8.JChipOK δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay (qJ δ b Pb tr (chalsJJ8 χ) M.pubsJ)
  hsatA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hbindA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qA δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hVk : AWChipOK δ b Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV (qV δ b Pb tr (chalsAJ8Z δ χ) M.pubsV)
  hsatL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hbindL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qAL δ b Pb tr (chalsAJ8Z δ χ) M.pubsA)
  hreg : ∀ i ∈ Pb.regs, Rg i = some ⟨(Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Pb.Rt i)⟩ ∧
    (Pb.Rt i).WellTyped p

/-- **The split**: `AcceptsJ9V` is exactly `StaticJ9 ∧ PubEqJ9 ∧ ChipsJ9` (no conjunct dropped or added). -/
theorem acceptsJ9V_iff (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ8' p K δ) (tr : TrJ8 (ZMod p)) (r : RowsJ8) (g : ℕ) :
    AcceptsJ9V δ b Pb Rg c χ M tr r g ↔
      StaticJ9 Pb c M.m r g ∧ PubEqJ9 δ b Pb c χ M ∧ ChipsJ9 δ b Pb Rg c χ M tr := by
  have hr : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  constructor
  · intro h
    refine ⟨⟨h.hinjX, h.hadjX, h.hinjC, h.hadjC, lt_of_lt_of_eq h.hnpC hr, h.hinjW, h.hadjW, h.hkW, h.hknW,
      lt_of_lt_of_eq h.hkpW hr,
      h.hinjA, h.hadjA, h.hnpA, h.hlay, h.hsmall, h.huniq, fun i hi => (h.hTpl i hi).2.1, h.hnd, h.hidx, h.hrk,
      fun id hid => by simpa only [hr] using h.hlt id hid, h.hclI, h.hclR, h.hcen', h.hlenC, h.hlenA, h.hcellF,
      h.hnA62, h.hbud, h.hbudV⟩,
      ⟨h.hGx, h.hGp, h.hGS, h.hsumC', h.hbalA', h.hvalA0, h.hfxC, h.hfxA⟩,
      ⟨h.hsatX, h.hsatC, h.hbindC, h.hsatW, h.hbindW, h.hJk, h.hsatA, h.hbindA, h.hVk, h.hsatL, h.hbindL,
        fun i hi => ⟨(h.hTpl i hi).1, (h.hTpl i hi).2.2⟩⟩⟩
  · rintro ⟨s, ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩, k⟩
    exact
    { hsatX := k.hsatX, hinjX := s.hinjX, hadjX := s.hadjX
      hsatC := k.hsatC, hbindC := k.hbindC, hinjC := s.hinjC, hadjC := s.hadjC, hnpC := lt_of_lt_of_eq s.hnpC hr.symm
      hsatW := k.hsatW, hbindW := k.hbindW, hinjW := s.hinjW, hadjW := s.hadjW, hkW := s.hkW, hknW := s.hknW
      hkpW := lt_of_lt_of_eq s.hkpW hr.symm
      hJk := k.hJk
      hsatA := k.hsatA, hbindA := k.hbindA, hinjA := s.hinjA, hadjA := s.hadjA, hnpA := s.hnpA
      hVk := k.hVk
      hGx := e1, hGp := e2, hGS := e3
      hlay := s.hlay, hsmall := s.hsmall, huniq := s.huniq
      hTpl := fun i hi => ⟨(k.hreg i hi).1, s.haxT i hi, (k.hreg i hi).2⟩
      hnd := s.hnd, hidx := s.hidx, hrk := s.hrk, hlt := fun id hid => by simpa only [hr] using s.hlt id hid
      hsumC' := e4, hbalA' := e5, hvalA0 := e6, hfxC := e7, hfxA := e8
      hclI := s.hclI, hclR := s.hclR, hcen' := s.hcen', hlenC := s.hlenC, hlenA := s.hlenA
      hcellF := s.hcellF, hnA62 := s.hnA62, hbud := s.hbud, hbudV := s.hbudV
      hsatL := k.hsatL, hbindL := k.hbindL }

end Split

/-! ## 3. The executable J-9 claim records and public-equation check -/

namespace Exe9

open Nock.TraceGenExe Nock.Field Nock.V1J8.Exe

/-- **The executable big-leaf claim records** (`claimBigRecs`: `claimVec (E (atom n)) idx 0 0`). -/
def claimBigRecsE (χe : CoinsE) (c : P8PublicClaim) (m : ClaimMsgVS) : List (Fin 5 → K6) :=
  (claimBigs p c).map fun k => claimVecE (encE (zE χe) (yE χe) (claimNoun c k)) (natG (m k).1) (natG 0) (natG 0)

/-- **The executable J-9 claim records** (`claimRecsJ9`). -/
def claimRecsJ9E (χe : CoinsE) (c : P8PublicClaim) (m : ClaimMsgVS) : List (Fin 5 → K6) :=
  claimRecsJ8E χe c m ++ claimBigRecsE χe c m

section Rec
variable [iA : Algebra Nock.Atoms.Fp KQ]

theorem claimBigRecsE_spec (χe : CoinsE) (c : P8PublicClaim) (m : ClaimMsgVS) :
    (claimBigRecsE χe c m).map vQ = claimBigRecs deltaF (toχ χe) c m := by
  unfold claimBigRecsE claimBigRecs
  rw [List.map_map]
  refine List.map_congr_left fun k _ => ?_
  show (fun c => K6.toQ (claimVecE _ _ _ _ c)) = _
  rw [claimVecE_spec, encE_spec, toZ_natG, toZ_natG]
  simp only [Nat.cast_zero]
  rfl

theorem claimRecsJ9E_spec (χe : CoinsE) (c : P8PublicClaim) (m : ClaimMsgVS) :
    (claimRecsJ9E χe c m).map vQ = claimRecsJ9 deltaF (toχ χe) c m := by
  unfold claimRecsJ9E claimRecsJ9
  rw [List.map_append, claimRecsJ8E_spec, claimBigRecsE_spec]

end Rec

/-- **The executable J-9 public-equation check**: the eight conjuncts of `PubEqJ9`, in order. -/
def checkPubJ9E (Pb : PubJ8 p) (c : P8PublicClaim) (χe : CoinsE) (M : MsgE) : Bool :=
  eq6 (M.ρ 3 + (pp M.pubsW WalkHQ.pubXQ + pp M.pubsJ 2)) (pp M.pubsC CellHQ.pubHQ) &&
  eq6 (M.ρ 4) (pp M.pubsW WalkHQ.pubPQ) &&
  eq6 (M.ρS + lsum ((pinConsE Pb.regs Pb.idx).map fun r => (compressE (γHE χe) (ρHE χe) r)⁻¹) + pp M.pubsJ 0)
    (pp M.pubsA AtomChipHQ.pubMI + pp M.pubsV WalkHQ.pubPQ) &&
  eq6 (lsum ((claimRecsJ9E χe c M.m ++ pinRecsJ8E Pb χe).map fun r => (compressE (γVE χe) (ρVE χe) r)⁻¹))
    (pp M.pubsC 0 + pp M.pubsA AtomChipHQ.pubMB) &&
  eq6 (pp M.pubsA CellHQ.pubHQ) (pp M.pubsA AtomChipHQ.pubC + pp M.pubsV WalkHQ.pubXQ) &&
  (eq3 (M.pubsA 0) 0 && eq3 (M.pubsA 1) 0) &&
  (eq3 (M.pubsC 2) (M.pubsW 0) && eq3 (M.pubsC 3) (M.pubsW 1)) &&
  (eq3 (M.pubsA 2) (M.pubsV 0) && eq3 (M.pubsA 3) (M.pubsV 1))

section Iff
variable [iA : Algebra Nock.Atoms.Fp KQ]

/-- **`checkPubJ9E_iff`**: the executable public-equation check is exactly `PubEqJ9` at the concrete field. -/
theorem checkPubJ9E_iff (Pb : PubJ8 p) (c : P8PublicClaim) (χe : CoinsE) (M : MsgE) :
    checkPubJ9E Pb c χe M = true ↔ PubEqJ9 deltaF powerBasis3 Pb c (toχ χe) M.toMsg := by
  have hcv := VerJ8.coinsCV_J8 deltaF powerBasis3 (toχ χe)
  unfold checkPubJ9E PubEqJ9
  simp only [Bool.and_eq_true, eq6_iff, eq3_iff, K6.toQ_add, toQ_pp, toQ_invSum, K3.toK_zero, hcv]
  rw [pinConsE_spec, List.map_append, claimRecsJ9E_spec, pinRecsJ8E_spec]
  simp only [List.map_map, Function.comp_def, and_assoc]
  exact Iff.rfl
  all_goals infer_instance

end Iff

section Split
variable [iA : Algebra Nock.Atoms.Fp KQ] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- **`acceptsJ9V_iff_exe`**: at the concrete field, `AcceptsJ9V` at the coins `toχ χe` and the message `M.toMsg` is
the executable static check, the executable public-equation check, and the chip residue. -/
theorem acceptsJ9V_iff_exe (Pb : PubJ8 p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χe : CoinsE) (M : MsgE)
    (tr : TraceJ8.TrJ8 (ZMod p)) (r : FrameJ8.RowsJ8) (g : ℕ) :
    AcceptsJ9V deltaF powerBasis3 Pb Rg c (toχ χe) M.toMsg tr r g ↔
      checkStaticJ9 Pb c M.m r g = true ∧ checkPubJ9E Pb c χe M = true ∧
        ChipsJ9 deltaF powerBasis3 Pb Rg c (toχ χe) M.toMsg tr := by
  rw [acceptsJ9V_iff, checkStaticJ9_iff, checkPubJ9E_iff]
  exact Iff.rfl

end Split

end Exe9

end Nock.V1J9
