/-
  Nock/V1J9A/CheckJ9AIff.lean

  Pattern: `Nock/V1J9/CheckJ9.lean` `checkJ9_iff`, `StaticJ9.acceptsJ9V_iff`.

  ## CONJUNCT MAP (`AcceptsJ9A` field  ↔  `checkJ9A` conjunct)

  | `AcceptsJ9A` field(s)                                              | executable counterpart                         |
  |--------------------------------------------------------------------|------------------------------------------------|
  | `hsatX` (twin compute RAP `computeChipVCLHX9`, `qX9`)              | `chipsBJ9A`: `compOK I` (= `checkCompX9`)      |
  | `hinjX hadjX`                                                      | `checkStaticJ9A`: `injB/adjB Pb.nodes`         |
  | `hsatC hbindC` / `hinjC hadjC hnpC`                                | `checkCellKW (tabC)` / static                  |
  | `hsatW hbindW` / `hinjW hadjW hkW hknW hkpW`                       | `checkWalkJ8 kroots (tabW)` / static           |
  | `hJk` (J chip present or absent)                                   | `checkJOK (tabJ)`                              |
  | `hsatA hbindA` / `hinjA hadjA hnpA`                                | `checkAtomHQ (tabA)` / static                  |
  | `hVk` (atom walk present or absent)                                | `checkAWOK krootsV (tabV)`                     |
  | `hsatL hbindL`                                                     | `checkAtomHQL (tabA)`                          |
  | `hAXk : AXChipOK` (present = 5 conjuncts, absent = flag + 4 pubs)  | `axOK I` (`checkM axisTemplateJ9`, nodup, adj, `n<p`; or `¬axOn ∧ 4 eq3`) |
  | `hSPk : SPChipOK` (idem, 2 pubs)                                   | `spOK I` (`checkM splitTemplateJ9`, ...)       |
  | `hGx hGp hGS hsumC' hbalA' hvalA0 hfxC hfxA`                       | `checkPubJ9AE` (eight `eq6`/`eq3` conjuncts)   |
  | `hlay hsmall huniq hnd hidx hrk hlt`, `hTpl.2.1` (axPosB)          | `checkStaticJ9A`                               |
  | `hTpl` (registry equation + WellTyped)                             | the premise `RegOK I` (as in `checkJ9_iff`)    |
  | `hclI hclR hcen' hlenC hlenA hcellF`                               | `checkStaticJ9A`                               |
  | `hnAS` / `hbud : BudJ9A` / `hbudV` (+ `nX ≤ AX ∧ nS ≤ SP`) / `hlenX` | `checkStaticJ9A` (`budJ9AB`, ...)            |

  Every `AcceptsJ9A` conjunct has an executable counterpart and vice versa.  Two FINDINGS (see the card report):
  (F1) `PubJ9A` needs `0 < nX`, `0 < nS` and admissible orbits even when the chip is ABSENT, but `checkJ9A` checks
       `0 < AX.n ∧ orbB AX` (resp. SP) only when `axOn` (`spOn`).  So the exact iff is stated with the extra
       Boolean `validAXSPB I` (`ValidJ9A`); `genJ9AX` satisfies it (`chipOf`).
  (F2) `CompX9.checkCompX9` builds the next-row environment with a CYCLIC wrap (`(i+1) % n`), whereas the chip's
       `TableData.env` (as `CompX.TabX.env`, `MemX.TabM.env`) uses the interpolant `∑ cols k · lagW …` at the last row.
       These agree only when the gates are blind to `traceNext` at the last row.  The compute conjunct is therefore
       taken as the HYPOTHESIS `Hc` of `checkJ9A_iff_of_comp` (not proved here).
-/
import Nock.V1J9A.CheckJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
import Nock.V1J9.CheckJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.V1J9A.CheckJ9AIff

open Nock Nock.Reified Nock.Framework Nock.Walk Nock.TraceGenExe Nock.Field Module Polynomial
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
open Nock.NockVMROM.Thm54.VclL.Handle.BalanceQ (liftRec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qX qM qW qJ qA qV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L (qAL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AXChipOK SPChipOK)
open Nock.Atoms (lenL)
open Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.V1J8.MemX (TabM checkM checkCellKW checkWalkJ8 checkJOK checkAtomHQ checkAtomHQL checkAWOK prep2 prep3 prepJ
  checkCellKW_iff checkWalkJ8_iff checkJOK_iff checkAtomHQ_iff checkAtomHQL_iff checkAWOK_iff chipM_iff
  nodupB_iff adj_core)
open Nock.V1J9 Nock.V1J9.Exe9 Nock.V1J9.Check9
open Nock.V1J9A.CheckJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (axisTemplateJ9 pubAXs pubAXp)
open Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9 (splitTemplateJ9 pubSPs)

/-! ## 1. The data built from an input -/

/-- Validity of the J-9 A input: the J-8 validity plus (always) the axis and split chips' admissible shape. -/
structure ValidJ9A (I : InJ9A) : Prop extends ValidJ8 I.toInJ8 where
  nAX : 0 < I.AX.n
  oAX : OrbOK I.AX
  nSP : 0 < I.SP.n
  oSP : OrbOK I.SP

/-- The Boolean validity of the axis and split chips (needed even when absent, because `PubJ9A` has fields for them). -/
-- `validAXSPB` / `validAXSPB_iff` now live in `CheckJ9A` (a conjunct of `checkJ9A`, finding F1).

theorem ValidJ9A.mk' (I : InJ9A) (h8 : ValidJ8 I.toInJ8) (h : 0 < I.AX.n ∧ OrbOK I.AX ∧ 0 < I.SP.n ∧ OrbOK I.SP) :
    ValidJ9A I := { h8 with nAX := h.1, oAX := h.2.1, nSP := h.2.2.1, oSP := h.2.2.2 }

/-- **The verifier's public parameters, built from the input.** -/
def mkPbA (I : InJ9A) (hv : ValidJ9A I) : PubJ9A p :=
  { mkPb I.toInJ8 hv.toValidJ8 with
    hX := I.AX.h, nX := I.AX.n, hnX := hv.nAX, nodesX := nodesOf I.AX, orbitX := mkOrbit I.AX hv.oAX,
    hS := I.SP.h, nS := I.SP.n, hnS := hv.nSP, nodesS := nodesOf I.SP, orbitS := mkOrbit I.SP hv.oSP,
    axOn := I.axOn, spOn := I.spOn }

/-- The message at the concrete field. -/
noncomputable def _root_.Nock.V1J9A.CheckJ9A.InJ9A.toMsg (I : InJ9A) : MsgJ9A' p KC deltaF :=
  { I.M.toMsg with pubsX := fun i => K3.toK (I.pubsX i), pubsS := fun i => K3.toK (I.pubsS i) }

/-- The rows record. -/
def _root_.Nock.V1J9A.CheckJ9A.InJ9A.toRows (I : InJ9A) : RowsJ9A := { toRowsJ8 := I.r, AX := I.rAX, SP := I.rSP }

/-- **The eight traces, built from the input.** -/
noncomputable def _root_.Nock.V1J9A.CheckJ9A.InJ9A.toTr (I : InJ9A) : TrJ9A (ZMod p) where
  C := fun j => interpOf I.X j
  M := fun j => interpOf I.C j
  W := fun j => interpOf I.W j
  J := fun j => interpOf I.J j
  A := fun j => interpOf I.A j
  V := fun j => interpOf I.V j
  X := fun j => interpOf I.AX j
  S := fun j => interpOf I.SP j

/-! ## 2. The static block -/

section Static
variable {p' : ℕ}

theorem budJ9AB_iff (Pb : PubJ9A p) (r : RowsJ9A) (g : ℕ) :
    budJ9AB Pb.toPubJ8 r.toRowsJ8 g Pb.nX Pb.nS r.AX r.SP = true ↔ BudJ9A Pb r (g + r.N) := by
  simp only [budJ9AB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **The K-free conjuncts of `AcceptsJ9A`** (as one conjunction, in `checkStaticJ9A` order). -/
def StaticJ9A (Pb : PubJ9A p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ9A) (g : ℕ) : Prop :=
  Function.Injective Pb.nodes ∧
  (∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω) ∧
  Function.Injective Pb.nodesC ∧
  (∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω) ∧
  Pb.nC < p ∧
  Function.Injective Pb.nodesW ∧
  (∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω) ∧
  1 ≤ Pb.kroots ∧ Pb.kroots ≤ Pb.nW ∧ Pb.kroots + Pb.nW < p ∧
  Function.Injective Pb.nodesA ∧
  (∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω) ∧
  Pb.nA < p ∧
  List.ofFn Pb.lay = layoutJ8 Pb.Rt Pb.regs Pb.ids ∧
  (∀ q ∈ layoutJ8 Pb.Rt Pb.regs Pb.ids, q.id < p ∧ q.cid < p ∧ q.nid < p ∧ q.n1 < p ∧ q.n2 < p) ∧
  ((layoutJ8 Pb.Rt Pb.regs Pb.ids).filterMap tvKey).Nodup ∧
  (∀ i ∈ Pb.regs, axPosB (Pb.Rt i) = true) ∧
  Pb.regs.Nodup ∧
  (∀ id ∈ Pb.regs, Pb.idx id < p) ∧
  (∀ id ∈ Pb.regs, Pb.rk id ≠ (0, 0)) ∧
  (∀ id ∈ Pb.regs, (Pb.rk id).1 < p ∧ (Pb.rk id).2 < p ∧ Pb.idx id < p) ∧
  (∀ k : Fin 3, (isCellN (claimNoun c k) = true ∨ isBigN p (claimNoun c k) = true) → (m k).1 < p) ∧
  (∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p) ∧
  (∀ x ∈ censusGJ9 Pb.toPubJ8 c, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ Pb.nA + 2) ∧
  3 + Pb.regs.length + 2 * Pb.nC < p ∧
  Pb.nA + Pb.nV < p ∧
  isCellN c.formula = true ∧
  Pb.nA + Pb.nS < 2 ^ 57 ∧
  BudJ9A Pb r (g + r.N) ∧
  (Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW ∧ Pb.nX ≤ r.AX ∧ Pb.nS ≤ r.SP) ∧
  (Pb.nX + Pb.n < p ∧ 2 * Pb.nS < p)

/-- **`checkStaticJ9A_iff`**: the static check is exactly `StaticJ9A`. -/
theorem checkStaticJ9A_iff (Pb : PubJ9A p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ9A) (g : ℕ) :
    checkStaticJ9A Pb.toPubJ8 c m r.toRowsJ8 g Pb.nX Pb.nS r.AX r.SP = true ↔ StaticJ9A Pb c m r g := by
  unfold StaticJ9A
  simp only [checkStaticJ9A, Bool.and_eq_true, decide_eq_true_eq, injB_iff, adjB_iff, budJ9AB_iff, and_assoc]

end Static

/-! ## 3. The public equations -/

section PubEq
variable {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The eight public equations of `AcceptsJ9A`**. -/
def PubEqJ9A (Pb : PubJ9A p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ9A' p K δ) : Prop :=
  (M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3)) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))) ∧
  (M.ρ 4 + Quad.mk _ (M.pubsX AxisChipJ9.pubAXp) (M.pubsX (AxisChipJ9.pubAXp + 1)) =
    Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))) ∧
  (M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) +
      Quad.mk _ (M.pubsX AxisChipJ9.pubAXs) (M.pubsX (AxisChipJ9.pubAXs + 1)) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1)) +
      Quad.mk _ (M.pubsS SplitChipJ9.pubSPs) (M.pubsS (SplitChipJ9.pubSPs + 1))) ∧
  (((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ).map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 0) (M.pubsC 1) +
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1))) ∧
  (Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV WalkHQ.pubXQ) (M.pubsV (WalkHQ.pubXQ + 1))) ∧
  (M.pubsA 0 = 0 ∧ M.pubsA 1 = 0) ∧
  (M.pubsC 2 = M.pubsW 0 ∧ M.pubsC 3 = M.pubsW 1) ∧
  (M.pubsA 2 = M.pubsV 0 ∧ M.pubsA 3 = M.pubsV 1)

end PubEq

section PubExe
variable [iA : Algebra Nock.Atoms.Fp KQ]

set_option maxHeartbeats 2000000 in
/-- **`checkPubJ9AE_iff`**: the executable public-equation check is exactly `PubEqJ9A` at the concrete field. -/
theorem checkPubJ9AE_iff(Pb : PubJ9A p) (c : P8PublicClaim) (χe : CoinsE) (M : MsgE) (pubsX pubsS : ℕ → K3) :
    checkPubJ9AE Pb.toPubJ8 c χe M pubsX pubsS = true ↔
      PubEqJ9A deltaF powerBasis3 Pb c (toχ χe)
        { M.toMsg with pubsX := fun i => K3.toK (pubsX i), pubsS := fun i => K3.toK (pubsS i) } := by
  have hcv := VerJ8.coinsCV_J8 deltaF powerBasis3 (toχ χe)
  unfold checkPubJ9AE PubEqJ9A
  simp only [Bool.and_eq_true, eq6_iff, eq3_iff, K6.toQ_add, toQ_pp, toQ_invSum, K3.toK_zero, hcv]
  rw [pinConsE_spec, List.map_append, claimRecsJ9E_spec, pinRecsJ8E_spec]
  simp only [List.map_map, Function.comp_def, and_assoc]
  exact Iff.rfl
  all_goals infer_instance

end PubExe

/-! ## 4. The two new chips: `checkM` at the axis / split templates -/

section NewChips
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (axisChipJ9 axisTemplateJ9_baseCols)
open Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9 (splitChipJ9 splitTemplateJ9_baseCols)

/-- **`checkAxis_iff`: the axis chip (`hsatX`-style: satisfies + binds), finitely.** -/
theorem checkAxis_iff {n h : ℕ} (T : TabM n) (hn : 0 < n) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (P : Fin (axisChipJ9 deltaF powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω) (hprep : T.prep = prep2 n)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (axisChipJ9 deltaF powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))) P ↔ checkM (axisTemplateJ9 deltaF) T = true := by
  refine chipM_iff (axisTemplateJ9 deltaF) T _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · rw [axisTemplateJ9_baseCols]
    exact Nock.V1J8.MemX.expandChip_C _ _ _ _ _ _
  · rw [hprep]
    simp only [List.ofFn_succ, List.ofFn_zero, axisChipJ9, FixedPreprocessingRAP.preprocessingColumn,
      RAP.preprocessingColumn, prep2, List.map_cons, List.map_nil]
    refine congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) rfl)
    · exact Nock.V1J8.MemX.firstMask_interp _
    · exact Nock.V1J8.MemX.lastMask_interp hn _

/-- **`checkSplit_iff`: the split chip, finitely** (`nA` the template parameter). -/
theorem checkSplit_iff (nA : ℕ) {n h : ℕ} (T : TabM n) (hn : 0 < n) (orbit : StrictOrbitDomain (ZMod p) 3 h)
    (P : Fin (splitChipJ9 deltaF nA powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω) (hprep : T.prep = prep2 n)
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (splitChipJ9 deltaF nA powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i))) P ↔ checkM (splitTemplateJ9 deltaF nA) T = true := by
  refine chipM_iff (splitTemplateJ9 deltaF nA) T _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · rw [splitTemplateJ9_baseCols]
    exact Nock.V1J8.MemX.expandChip_C _ _ _ _ _ _
  · rw [hprep]
    simp only [List.ofFn_succ, List.ofFn_zero, splitChipJ9, FixedPreprocessingRAP.preprocessingColumn,
      RAP.preprocessingColumn, prep2, List.map_cons, List.map_nil]
    refine congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) rfl)
    · exact Nock.V1J8.MemX.firstMask_interp _
    · exact Nock.V1J8.MemX.lastMask_interp hn _

/-- **`axOK_iff`: `AXChipOK` (present or absent) is exactly `axOK`.** -/
theorem axOK_iff (I : InJ9A) (hn : 0 < I.AX.n) (ho : OrbOK I.AX)
    (chals pubs : ℕ → KC) (hch : chals = fun i => K3.toK (chalsMJ8E I.χ i))
    (hpub : pubs = fun i => K3.toK (I.pubsX i))
    (P : Fin (axisChipJ9 deltaF powerBasis3 hn (nodesOf I.AX) (mkOrbit I.AX ho) chals pubs).rap.w → (ZMod p)[X])
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ (nodesOf I.AX) (fun i => I.AX.cols j i)) :
    AXChipOK deltaF powerBasis3 I.axOn hn (nodesOf I.AX) (mkOrbit I.AX ho) chals pubs P ↔ axOK I = true := by
  subst hch hpub
  have ha : (∀ (i : Fin I.AX.n) (hi : (i : ℕ) + 1 < I.AX.n),
      nodesOf I.AX ⟨(i : ℕ) + 1, hi⟩ = nodesOf I.AX i * (mkOrbit I.AX ho).ω) ↔
      Nock.V1J8.MemX.adjB (tabAX I) = true := by
    rw [Nock.V1J8.MemX.adjB_iff]; rfl
  have hob : orbB I.AX = true := (orbB_iff _).mpr ho
  have hnb : decide (0 < I.AX.n) = true := decide_eq_true hn
  unfold AXChipOK axOK
  cases hax : I.axOn
  · simp [eq3_iff, K3.toK_zero, and_assoc]
  · simp only [hob, hnb, Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false, Bool.and_eq_true,
      decide_eq_true_eq, nodupB_iff]
    constructor
    · rintro (⟨-, hs, hb, hi, hadj, hlt⟩ | ⟨h, -⟩)
      · exact ⟨⟨⟨(checkAxis_iff (tabAX I) hn (mkOrbit I.AX ho) P hi
          (Nock.V1J8.MemX.adj_core (tabAX I) rfl hadj) rfl rfl hP).mp ⟨hs, hb⟩, hi⟩, ha.mp hadj⟩, hlt⟩
      · exact absurd h (by decide)
    · rintro ⟨⟨⟨hc, hi⟩, hadj⟩, hlt⟩
      have hadj' := ha.mpr hadj
      obtain ⟨hs, hb⟩ := (checkAxis_iff (tabAX I) hn (mkOrbit I.AX ho) P hi
        (Nock.V1J8.MemX.adj_core (tabAX I) rfl hadj') rfl rfl hP).mpr hc
      exact Or.inl ⟨trivial, hs, hb, hi, hadj', hlt⟩

/-- **`spOK_iff`: `SPChipOK` (present or absent) is exactly `spOK`** (template parameter `nA = I.A.n`). -/
theorem spOK_iff (I : InJ9A) (hn : 0 < I.SP.n) (ho : OrbOK I.SP)
    (chals pubs : ℕ → KC) (hch : chals = fun i => K3.toK (chalsMJ8E I.χ i))
    (hpub : pubs = fun i => K3.toK (I.pubsS i))
    (P : Fin (splitChipJ9 deltaF I.A.n powerBasis3 hn (nodesOf I.SP) (mkOrbit I.SP ho) chals pubs).rap.w →
      (ZMod p)[X])
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ (nodesOf I.SP) (fun i => I.SP.cols j i)) :
    SPChipOK deltaF powerBasis3 I.A.n I.spOn hn (nodesOf I.SP) (mkOrbit I.SP ho) chals pubs P ↔
      spOK I = true := by
  subst hch hpub
  have ha : (∀ (i : Fin I.SP.n) (hi : (i : ℕ) + 1 < I.SP.n),
      nodesOf I.SP ⟨(i : ℕ) + 1, hi⟩ = nodesOf I.SP i * (mkOrbit I.SP ho).ω) ↔
      Nock.V1J8.MemX.adjB (tabSP I) = true := by
    rw [Nock.V1J8.MemX.adjB_iff]; rfl
  have hob : orbB I.SP = true := (orbB_iff _).mpr ho
  have hnb : decide (0 < I.SP.n) = true := decide_eq_true hn
  unfold SPChipOK spOK
  cases hsp : I.spOn
  · simp [eq3_iff, K3.toK_zero, and_assoc]
  · simp only [hob, hnb, Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false, Bool.and_eq_true,
      decide_eq_true_eq, nodupB_iff]
    constructor
    · rintro (⟨-, hs, hb, hi, hadj, hlt⟩ | ⟨h, -⟩)
      · exact ⟨⟨⟨(checkSplit_iff I.A.n (tabSP I) hn (mkOrbit I.SP ho) P hi
          (Nock.V1J8.MemX.adj_core (tabSP I) rfl hadj) rfl rfl hP).mp ⟨hs, hb⟩, hi⟩, ha.mp hadj⟩, hlt⟩
      · exact absurd h (by decide)
    · rintro ⟨⟨⟨hc, hi⟩, hadj⟩, hlt⟩
      have hadj' := ha.mpr hadj
      obtain ⟨hs, hb⟩ := (checkSplit_iff I.A.n (tabSP I) hn (mkOrbit I.SP ho) P hi
        (Nock.V1J8.MemX.adj_core (tabSP I) rfl hadj') rfl rfl hP).mpr hc
      exact Or.inl ⟨trivial, hs, hb, hi, hadj', hlt⟩

end NewChips

/-! ## 5. The split `AcceptsJ9A ↔ StaticJ9A ∧ PubEqJ9A ∧ ChipsJ9A` -/

section Split
variable {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **The chip residue of `AcceptsJ9A`** (every chip conjunct verbatim, plus `hTpl`'s registry equation). -/
structure ChipsJ9A (Pb : PubJ9A p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) : Prop where
  hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ (chalVJ8 b χ)
    (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX9 δ b Pb tr (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
  hsatC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.Satisfies
    (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC)
  hbindC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).BindsPreprocessing
    (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC)
  hsatW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).rap.Satisfies
    (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW)
  hbindW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).BindsPreprocessing
    (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW)
  hJk : JGenJ8.JChipOK δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay
    (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ)
  hsatA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  hbindA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  hVk : AWChipOK δ b Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
    (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV)
  hsatL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qAL δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  hbindL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qAL δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  hAXk : AXChipOK δ b Pb.axOn Pb.hnX Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
    (qAX δ b Pb tr (chalsMJ8 δ χ) M.pubsX)
  hSPk : SPChipOK δ b Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS
    (qSP δ b Pb tr (chalsMJ8 δ χ) M.pubsS)
  hreg : ∀ i ∈ Pb.regs, Rg i = some ⟨(Pb.Rt i).toTemplate p, Nock.Jet.Autogen.compile p (Pb.Rt i)⟩ ∧
    (Pb.Rt i).WellTyped p

/-- **The split**: `AcceptsJ9A` is exactly `StaticJ9A ∧ PubEqJ9A ∧ ChipsJ9A` (no conjunct dropped or added). -/
theorem acceptsJ9A_iff (Pb : PubJ9A p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9A' p K δ) (tr : TrJ9A (ZMod p)) (r : RowsJ9A) (g : ℕ) :
    AcceptsJ9A.AcceptsJ9A δ b Pb Rg c χ M tr r g ↔
      StaticJ9A Pb c M.m r g ∧ PubEqJ9A δ b Pb c χ M ∧ ChipsJ9A δ b Pb Rg c χ M tr := by
  have hr : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  constructor
  · intro h
    exact ⟨⟨h.hinjX, h.hadjX, h.hinjC, h.hadjC, lt_of_lt_of_eq h.hnpC hr, h.hinjW, h.hadjW, h.hkW, h.hknW,
      lt_of_lt_of_eq h.hkpW hr, h.hinjA, h.hadjA, h.hnpA, h.hlay, h.hsmall, h.huniq,
      fun i hi => (h.hTpl i hi).2.1, h.hnd, h.hidx, h.hrk,
      fun id hid => by simpa only [hr] using h.hlt id hid, h.hclI, h.hclR, h.hcen', h.hlenC, h.hlenA,
      h.hcellF, h.hnAS, h.hbud, h.hbudV, h.hlenX⟩,
      ⟨h.hGx, h.hGp, h.hGS, h.hsumC', h.hbalA', h.hvalA0, h.hfxC, h.hfxA⟩,
      ⟨h.hsatX, h.hsatC, h.hbindC, h.hsatW, h.hbindW, h.hJk, h.hsatA, h.hbindA, h.hVk, h.hsatL, h.hbindL,
        h.hAXk, h.hSPk, fun i hi => ⟨(h.hTpl i hi).1, (h.hTpl i hi).2.2⟩⟩⟩
  · rintro ⟨s, ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩, k⟩
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21,
      s22, s23, s24, s25, s26, s27, s28, s29, s30, s31⟩ := s
    exact
    { hsatX := k.hsatX, hinjX := s1, hadjX := s2
      hsatC := k.hsatC, hbindC := k.hbindC, hinjC := s3, hadjC := s4, hnpC := lt_of_lt_of_eq s5 hr.symm
      hsatW := k.hsatW, hbindW := k.hbindW, hinjW := s6, hadjW := s7, hkW := s8, hknW := s9
      hkpW := lt_of_lt_of_eq s10 hr.symm
      hJk := k.hJk
      hsatA := k.hsatA, hbindA := k.hbindA, hinjA := s11, hadjA := s12, hnpA := s13
      hVk := k.hVk
      hGx := e1, hGp := e2, hGS := e3
      hlay := s14, hsmall := s15, huniq := s16
      hTpl := fun i hi => ⟨(k.hreg i hi).1, s17 i hi, (k.hreg i hi).2⟩
      hnd := s18, hidx := s19, hrk := s20, hlt := fun id hid => by simpa only [hr] using s21 id hid
      hsumC' := e4, hbalA' := e5, hvalA0 := e6, hfxC := e7, hfxA := e8
      hclI := s22, hclR := s23, hcen' := s24, hlenC := s25, hlenA := s26
      hcellF := s27, hnAS := s28, hbud := s29, hbudV := s30
      hsatL := k.hsatL, hbindL := k.hbindL
      hAXk := k.hAXk, hSPk := k.hSPk, hlenX := s31 }

end Split

/-! ## 6. `checkJ9A_iff` -/

section Iff
variable [iA : Algebra Nock.Atoms.Fp KQ] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- **The chip block**: under the static block, `chipsBJ9A compOK` is exactly `ChipsJ9A`, GIVEN that `compOK` decides the
twin compute RAP (`Hc`, the open piece: see finding F2 in the header). -/
theorem chipsBJ9A_iff (compOK : InJ9A → Bool) (I : InJ9A) (hv : ValidJ9A I) (Rg : Nock.Jet.Registry)
    (hreg : RegOK I.toInJ8 Rg) (hs : StaticJ9A (mkPbA I hv) I.c I.M.m I.toRows I.g)
    (Hc : compOK I = true ↔ RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 (mkPbA I hv).hn (mkPbA I hv).nodes powerBasis3 deltaF (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ)) (mkPbA I hv).orbit)
      (qX9 deltaF powerBasis3 (mkPbA I hv) I.toTr (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ)))) :
    chipsBJ9A compOK I = true ↔
      ChipsJ9A deltaF powerBasis3 (mkPbA I hv) Rg I.c (toχ I.χ) I.toMsg I.toTr := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21,
      s22, s23, s24, s25, s26, s27, s28, s29, s30, s31⟩ := hs
  have eC := checkCellKW_iff (tabC I.toInJ8) hv.nC (mkOrbit I.C hv.oC)
    (qM deltaF powerBasis3 (mkPbA I hv).toPubJ8 I.toTr.toJ8 (fun i => K3.toK ((tabC I.toInJ8).chals i))
      (fun i => K3.toK ((tabC I.toInJ8).pubs i)))
    s3 (adj_of I.C hv.oC s4) rfl rfl (fun j => rfl)
  have eW := checkWalkJ8_iff I.kroots (tabW I.toInJ8) hv.nW (mkOrbit I.W hv.oW)
    (qW deltaF powerBasis3 (mkPbA I hv).toPubJ8 I.toTr.toJ8 (fun i => K3.toK ((tabW I.toInJ8).chals i))
      (fun i => K3.toK ((tabW I.toInJ8).pubs i)))
    s6 (adj_of I.W hv.oW s7) rfl rfl (fun j => rfl)
  have eJ := checkJOK_iff (tabJ I.toInJ8) (mkOrbit I.J hv.oJ) I.lay
    (qJ deltaF powerBasis3 (mkPbA I hv).toPubJ8 I.toTr.toJ8 (fun i => K3.toK ((tabJ I.toInJ8).chals i))
      (fun i => K3.toK ((tabJ I.toInJ8).pubs i)))
    rfl rfl (fun j => rfl)
  have eA := checkAtomHQ_iff (tabA I.toInJ8) hv.nA (mkOrbit I.A hv.oA)
    (qA deltaF powerBasis3 (mkPbA I hv).toPubJ8 I.toTr.toJ8 (fun i => K3.toK ((tabA I.toInJ8).chals i))
      (fun i => K3.toK ((tabA I.toInJ8).pubs i)))
    s11 (adj_of I.A hv.oA s12) rfl rfl (fun j => rfl)
  have eL := checkAtomHQL_iff (tabA I.toInJ8) hv.nA (mkOrbit I.A hv.oA)
    (qAL deltaF powerBasis3 (mkPbA I hv).toPubJ8 I.toTr.toJ8 (fun i => K3.toK ((tabA I.toInJ8).chals i))
      (fun i => K3.toK ((tabA I.toInJ8).pubs i)))
    s11 (adj_of I.A hv.oA s12) rfl rfl (fun j => rfl)
  have eV := checkAWOK_iff I.krootsV (tabV I.toInJ8) hv.nV (mkOrbit I.V hv.oV)
    (qV deltaF powerBasis3 (mkPbA I hv).toPubJ8 I.toTr.toJ8 (fun i => K3.toK ((tabV I.toInJ8).chals i))
      (fun i => K3.toK ((tabV I.toInJ8).pubs i)))
    rfl rfl (fun j => rfl)
  have hM := chalsMJ8_eq I.χ
  have hAZ := chalsAJ8Z_eq I.χ
  have hJJ := chalsJJ8_eq I.χ
  unfold chipsBJ9A
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨hX, hC⟩, hW⟩, hJ⟩, hA⟩, hV⟩, hL⟩, hAX⟩, hSP⟩
    obtain ⟨sC, bC⟩ := eC.mpr hC
    obtain ⟨sW, bW⟩ := eW.mpr hW
    obtain ⟨sA, bA⟩ := eA.mpr hA
    obtain ⟨sL, bL⟩ := eL.mpr hL
    refine ⟨Hc.mp hX, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hreg⟩
    · rw [hM]; exact sC
    · rw [hM]; exact bC
    · rw [hM]; exact sW
    · rw [hM]; exact bW
    · rw [hJJ]; exact eJ.mpr hJ
    · rw [hAZ]; exact sA
    · rw [hAZ]; exact bA
    · rw [hAZ]; exact eV.mpr hV
    · rw [hAZ]; exact sL
    · rw [hAZ]; exact bL
    · exact (axOK_iff I hv.nAX hv.oAX _ _ (hM) rfl _ (fun j => rfl)).mpr hAX
    · exact (spOK_iff I hv.nSP hv.oSP _ _ (hM) rfl _ (fun j => rfl)).mpr hSP
  · intro k
    have kC := k.hsatC
    have kbC := k.hbindC
    have kW := k.hsatW
    have kbW := k.hbindW
    have kJ := k.hJk
    have kA := k.hsatA
    have kbA := k.hbindA
    have kV := k.hVk
    have kL := k.hsatL
    have kbL := k.hbindL
    rw [hM] at kC kbC kW kbW
    rw [hJJ] at kJ
    rw [hAZ] at kA kbA kV kL kbL
    exact ⟨⟨⟨⟨⟨⟨⟨⟨Hc.mpr k.hsatX, eC.mp ⟨kC, kbC⟩⟩, eW.mp ⟨kW, kbW⟩⟩, eJ.mp kJ⟩, eA.mp ⟨kA, kbA⟩⟩, eV.mp kV⟩,
      eL.mp ⟨kL, kbL⟩⟩, (axOK_iff I hv.nAX hv.oAX _ _ (hM) rfl _ (fun j => rfl)).mp k.hAXk⟩,
      (spOK_iff I hv.nSP hv.oSP _ _ (hM) rfl _ (fun j => rfl)).mp k.hSPk⟩

/-- **`checkJ9A_iff`**: under the registry premise, the executable J-9 A
checker (with validity of the axis / split shape, finding F1) holds iff the input is valid and `AcceptsJ9A` holds at
the verifier data `mkPbA I`, the coins `toχ I.χ`, the message `I.toMsg`, the traces `I.toTr`, the rows `I.toRows`. -/
theorem checkJ9A_iff_of_comp (compOK : InJ9A → Bool) (I : InJ9A) (Rg : Nock.Jet.Registry)
    (hreg : RegOK I.toInJ8 Rg)
    (Hc : ∀ hv : ValidJ9A I, compOK I = true ↔ RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 (mkPbA I hv).hn (mkPbA I hv).nodes powerBasis3 deltaF (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ)) (mkPbA I hv).orbit)
      (qX9 deltaF powerBasis3 (mkPbA I hv) I.toTr (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ)))) :
    checkJ9A compOK I = true ↔ ∃ hv : ValidJ9A I,
      AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 (mkPbA I hv) Rg I.c (toχ I.χ) I.toMsg I.toTr I.toRows I.g := by
  unfold checkJ9A
  constructor
  · intro h
    by_cases hb : validB I.toInJ8 = true
    · rw [dif_pos hb] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨hax, hs⟩, hp⟩, hc⟩ := h
      have hv : ValidJ9A I := ValidJ9A.mk' I ((validB_iff _).mp hb) ((validAXSPB_iff I).mp hax)
      have hs' := (checkStaticJ9A_iff (mkPbA I hv) I.c I.M.m I.toRows I.g).mp hs
      refine ⟨hv, (acceptsJ9A_iff deltaF powerBasis3 _ Rg I.c (toχ I.χ) I.toMsg I.toTr I.toRows I.g).mpr
        ⟨hs', (checkPubJ9AE_iff (mkPbA I hv) I.c I.χ I.M I.pubsX I.pubsS).mp hp, ?_⟩⟩
      exact (chipsBJ9A_iff compOK I hv Rg hreg hs' (Hc hv)).mp hc
    · rw [dif_neg hb] at h; exact absurd h Bool.false_ne_true
  · rintro ⟨hv, h⟩
    obtain ⟨hs, hp, hc⟩ := (acceptsJ9A_iff deltaF powerBasis3 _ Rg I.c (toχ I.χ) I.toMsg I.toTr I.toRows I.g).mp h
    have hb : validB I.toInJ8 = true := (validB_iff _).mpr hv.toValidJ8
    rw [dif_pos hb]
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨(validAXSPB_iff I).mpr ⟨hv.nAX, hv.oAX, hv.nSP, hv.oSP⟩,
      (checkStaticJ9A_iff (mkPbA I hv) I.c I.M.m I.toRows I.g).mpr hs⟩,
      (checkPubJ9AE_iff (mkPbA I hv) I.c I.χ I.M I.pubsX I.pubsS).mpr hp⟩,
      (chipsBJ9A_iff compOK I hv Rg hreg hs (Hc hv)).mpr hc⟩

end Iff

end Nock.V1J9A.CheckJ9AIff

section Axioms
open Nock.V1J9A.CheckJ9AIff
#print axioms checkStaticJ9A_iff
#print axioms checkPubJ9AE_iff
#print axioms checkAxis_iff
#print axioms checkSplit_iff
#print axioms axOK_iff
#print axioms spOK_iff
#print axioms acceptsJ9A_iff
#print axioms chipsBJ9A_iff
#print axioms checkJ9A_iff_of_comp
end Axioms
