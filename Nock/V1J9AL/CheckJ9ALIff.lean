/-
  Nock/V1J9AL/CheckJ9ALIff.lean

  **`checkJ9ALX_iff` — the native J-9 AL checker decides `AcceptsJ9AL`** (twin of
  `V1J9A/CheckJ9AIff.lean` + `CheckJ9AIffComp.lean`).

  Premises of the final statement: the registry premise `RegOK I.toInJ8 Rg` (as `checkJ9AX_iff`) and the primitive
  registry premise `hprim : ∀ q ∈ I.prims, Rg q.1 = some (primSpec q.2)` (the `hPrim` field of `AcceptsJ9AL`, an
  equation on the registry FUNCTION, undecidable in the checker).  Nothing else.

  CONJUNCT MAP (`AcceptsJ9AL` field ↔ executable conjunct): as `CheckJ9AIff`, with
  * `hGx hGS hsumC'` ↔ `checkPubJ9ALE` (ALU terminals, `pinRgPE`, `pinOpPE`, `pinRecsPE`);
  * `hcen' hbud` and the added `hlenL hndP hrkP hltP hlenCP hdisjP` ↔ `checkStaticJ9AL`;
  * `hALk` ↔ `alOK` (`checkM` at `aluTemplateSZ`; the `preg` layout is the table's fixed columns 2..4, the premise
    `PregOK` reduces to `prims.length ≤ nL`);
  * `hPrim` ↔ the premise `hprim`.
-/
import Nock.V1J9AL.CheckJ9AL
import Nock.V1J9A.CheckJ9AIffComp

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.V1J9AL.CheckJ9ALIff

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
open Nock.NockVMROM.Thm54.VclL.Handle.TeleCQ (coinsCV)
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.Jet.PinJ8 (pinCons)
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.WalkVCL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (aluSZChipJ9 aluTemplateSZ aluTemplateSZ_baseCols preOf)
open Nock.Atoms (lenL)
open Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.V1J8.MemX (TabM checkM prep2 chipM_iff nodupB_iff adj_core)
open Nock.V1J9 Nock.V1J9.Exe9 Nock.V1J9.Check9
open Nock.V1J9A.CheckJ9A Nock.V1J9A.CheckJ9AIff
open Nock.V1J9AL.CheckJ9AL
open Nock.Jet.Prim (PrimOp primC primSpec)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinK (walkChipHQK)
open Nock.NockVMROM.Thm54.VclL.Handle.WalkJ8 (walkChipJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (qX qM qW qJ qA qV)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8L (qAL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AtomChipHQL (atomChipHQL)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AXChipOK SPChipOK)
open Nock.V1J8.MemX (checkCellKW checkWalkJ8 checkJOK checkAtomHQ checkAtomHQL checkAWOK prep3 prepJ
  checkCellKW_iff checkWalkJ8_iff checkJOK_iff checkAtomHQ_iff checkAtomHQL_iff checkAWOK_iff)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P Nock.NockVMROM.Thm54.VclL.Handle.WeightsJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8Z Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (axisTemplateJ9 pubAXs pubAXp)
open Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9 (splitTemplateJ9 pubSPs)
open Nock.V1J9A

/-! ## 1. The data built from an input -/

/-- Validity of the J-9 AL input: J-9 A validity plus the ALU's admissible shape (always). -/
structure ValidJ9AL (I : InJ9AL) : Prop extends ValidJ9A I.toInJ9A where
  nL : 0 < I.AL.n
  oAL : OrbOK I.AL

/-- **The verifier's public parameters, built from the input.** -/
noncomputable def mkPbAL (I : InJ9AL) (hv : ValidJ9AL I) : PubJ9AL p :=
  { mkPbA I.toInJ9A hv.toValidJ9A with
    hL := I.AL.h, nL := I.AL.n, hnL := hv.nL, nodesL := nodesOf I.AL, orbitL := mkOrbit I.AL hv.oAL,
    aluOn := I.aluOn, prims := I.prims, idxP := I.idxP, rkP := I.rkP,
    preL := fun k => Lagrange.interpolate Finset.univ (nodesOf I.AL) (fun i => pregCol I.prims (k : ℕ) (i : ℕ)) }

/-- The message at the concrete field. -/
noncomputable def _root_.Nock.V1J9AL.CheckJ9AL.InJ9AL.toMsgL (I : InJ9AL) : MsgJ9AL' p KC deltaF :=
  { toMsgJ9A' := I.toInJ9A.toMsg, pubsL := fun i => K3.toK (I.pubsL i) }

/-- The nine traces. -/
noncomputable def _root_.Nock.V1J9AL.CheckJ9AL.InJ9AL.toTrL (I : InJ9AL) : TrJ9AL (ZMod p) :=
  { toTrJ9A := I.toInJ9A.toTr, L := fun j => interpOf I.AL j }

/-- The rows record. -/
def _root_.Nock.V1J9AL.CheckJ9AL.InJ9AL.toRowsL (I : InJ9AL) : RowsJ9AL :=
  { toRowsJ9A := I.toInJ9A.toRows, AL := I.rAL }

theorem validALB_iff (I : InJ9AL) : validALB I = true ↔ (0 < I.AL.n ∧ OrbOK I.AL) := by
  simp only [validALB, Bool.and_eq_true, decide_eq_true_eq, orbB_iff]

/-! ## 2. The static block -/

section Static

theorem budJ9ALB_iff (Pb : PubJ9AL p) (r : RowsJ9AL) (g : ℕ) :
    budJ9ALB Pb.toPubJ8 r.toRowsJ8 g Pb.nX Pb.nS Pb.nL r.AX r.SP r.AL = true ↔ BudJ9AL Pb r (g + r.N) := by
  simp only [budJ9ALB, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **The K-free conjuncts of `AcceptsJ9AL`** (in `checkStaticJ9AL` order). -/
def StaticJ9AL (Pb : PubJ9AL p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ9AL) (g : ℕ) : Prop :=
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
  (∀ x ∈ censusGJ9 Pb.toPubJ8 c ++ censusP Pb, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ Pb.nA + 2) ∧
  3 + Pb.regs.length + 2 * Pb.nC < p ∧
  Pb.nA + Pb.nV < p ∧
  isCellN c.formula = true ∧
  Pb.nA + Pb.nS < 2 ^ 57 ∧
  BudJ9AL Pb r (g + r.N) ∧
  (Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW ∧ Pb.nX ≤ r.AX ∧ Pb.nS ≤ r.SP) ∧
  (Pb.nX + Pb.n < p ∧ 2 * Pb.nS < p) ∧
  (Pb.nL + Pb.n < p ∧ Pb.nL ≤ r.AL ∧ ∀ q ∈ Pb.prims, q.1 < p ∧ Pb.idxP q.1 < p) ∧
  (Pb.prims.map Prod.fst).Nodup ∧
  (∀ q ∈ Pb.prims, Pb.rkP q.1 ≠ (0, 0)) ∧
  (∀ q ∈ Pb.prims, (Pb.rkP q.1).1 < p ∧ (Pb.rkP q.1).2 < p ∧ Pb.idxP q.1 < p) ∧
  3 + Pb.regs.length + Pb.prims.length + Pb.nL + 2 * Pb.nC < p ∧
  (∀ q ∈ Pb.prims, q.1 ∉ Pb.regs)

theorem censusPL_eq (Pb : PubJ9AL p) : censusPL Pb.prims = censusP Pb := rfl

/-- **`checkStaticJ9AL_iff`**: the static check is exactly `StaticJ9AL`. -/
theorem checkStaticJ9AL_iff (Pb : PubJ9AL p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ9AL) (g : ℕ) :
    checkStaticJ9AL Pb.toPubJ8 c m r.toRowsJ8 g Pb.nX Pb.nS r.AX r.SP Pb.nL r.AL Pb.prims Pb.idxP Pb.rkP = true ↔
      StaticJ9AL Pb c m r g := by
  unfold StaticJ9AL
  simp only [checkStaticJ9AL, Bool.and_eq_true, decide_eq_true_eq, injB_iff, adjB_iff, budJ9ALB_iff, and_assoc]
  simp only [censusPL_eq]

end Static

/-! ## 3. The public equations -/

section PubEq
variable {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The eight public equations of `AcceptsJ9AL`**. -/
def PubEqJ9AL (Pb : PubJ9AL p) (c : P8PublicClaim) (χ : Coins frameJ8 K) (M : MsgJ9AL' p K δ) : Prop :=
  (M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3) +
      Quad.mk _ (M.pubsL AluSZChipJ9.pubALx) (M.pubsL (AluSZChipJ9.pubALx + 1))) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))) ∧
  (M.ρ 4 + Quad.mk _ (M.pubsX AxisChipJ9.pubAXp) (M.pubsX (AxisChipJ9.pubAXp + 1)) =
    Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))) ∧
  (M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum +
      ((pinRgP (p := p) (K := K) Pb).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum +
      ((pinOpP (p := p) (K := K) Pb).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) +
      Quad.mk _ (M.pubsX AxisChipJ9.pubAXs) (M.pubsX (AxisChipJ9.pubAXs + 1)) +
      Quad.mk _ (M.pubsL AluSZChipJ9.pubALs) (M.pubsL (AluSZChipJ9.pubALs + 1)) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1)) +
      Quad.mk _ (M.pubsS SplitChipJ9.pubSPs) (M.pubsS (SplitChipJ9.pubSPs + 1))) ∧
  (Quad.mk (algebraMap (ZMod p) K δ) (M.pubsL AluSZChipJ9.pubALv) (M.pubsL (AluSZChipJ9.pubALv + 1)) +
    ((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ ++ pinRecsP δ Pb χ).map fun r => (FiniteIO.compress (m := 5)
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

theorem pinRgPE_spec {iFt : Fintype KQ} {iD : DecidableEq KQ} {iDK : DecidableEq KC} (Pb : PubJ9AL p) :
    (pinRgPE Pb.prims Pb.idxP).map vQ =
      (pinRgP (p := p) (K := KC) Pb).map fun r => BalanceQ.liftRec (L := KQ) r := by
  unfold pinRgPE pinRgP
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun q _ => ?_
  funext c
  simp only [Function.comp, vQ, BalanceQ.liftRec, pinRgVec, pinRgVecE, Nock.Jet.RapJetJ8.keyK, toQ_g6,
    Gold.toZ_ofZ]
  exact (IsScalarTower.algebraMap_apply (ZMod p) KC KQ _)

theorem pinOpPE_spec {iFt : Fintype KQ} {iD : DecidableEq KQ} {iDK : DecidableEq KC} (Pb : PubJ9AL p) :
    (pinOpPE Pb.prims).map vQ =
      (pinOpP (p := p) (K := KC) Pb).map fun r => BalanceQ.liftRec (L := KQ) r := by
  unfold pinOpPE pinOpP
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun q _ => ?_
  funext c
  simp only [Function.comp, vQ, BalanceQ.liftRec, pinOpVecE, Nock.Jet.RapJetJ8.keyK, toQ_g6, Gold.toZ_ofZ]
  exact (IsScalarTower.algebraMap_apply (ZMod p) KC KQ _)

variable [iA : Algebra Nock.Atoms.Fp KQ]

theorem pinRecsPE_spec (Pb : PubJ9AL p) (χe : CoinsE) :
    (pinRecsPE Pb.prims Pb.idxP Pb.rkP χe).map vQ = pinRecsP deltaF Pb (toχ χe) := by
  unfold pinRecsPE pinRecsP
  rw [List.map_map]
  refine List.map_congr_left fun k _ => ?_
  show (fun c => K6.toQ (claimVecE _ _ _ _ c)) = _
  rw [claimVecE_spec, encE_spec, toZ_natG, toZ_natG, toZ_natG]
  rfl

/-- **`checkPubJ9ALE_iff`**: the executable public-equation check is exactly `PubEqJ9AL` at the concrete field. -/
theorem checkPubJ9ALE_iff (Pb : PubJ9AL p) (c : P8PublicClaim) (χe : CoinsE) (M : MsgE)
    (pubsX pubsS pubsL : ℕ → K3) :
    checkPubJ9ALE Pb.toPubJ8 Pb.prims Pb.idxP Pb.rkP c χe M pubsX pubsS pubsL = true ↔
      PubEqJ9AL deltaF powerBasis3 Pb c (toχ χe)
        { toMsgJ9A' := { M.toMsg with pubsX := fun i => K3.toK (pubsX i), pubsS := fun i => K3.toK (pubsS i) }
          pubsL := fun i => K3.toK (pubsL i) } := by
  have hcv := VerJ8.coinsCV_J8 deltaF powerBasis3 (toχ χe)
  unfold checkPubJ9ALE PubEqJ9AL
  simp only [Bool.and_eq_true, eq6_iff, eq3_iff, K6.toQ_add, toQ_pp, toQ_invSum, K3.toK_zero, hcv]
  rw [pinConsE_spec, pinRgPE_spec, pinOpPE_spec]
  simp only [List.map_append]
  rw [claimRecsJ9E_spec, pinRecsJ8E_spec, pinRecsPE_spec]
  simp only [List.map_map, Function.comp_def, and_assoc]
  exact Iff.rfl
  all_goals infer_instance

end PubExe

/-! ## 4. The ALU chip: `checkM` at the ALU template -/

section Alu

/-- **`PregOK` is the length bound**, for nodes injective and `preL` the interpolation of `pregCol`. -/
theorem pregOK_iff {n : ℕ} (nodes : Fin n → ZMod p) (hinj : Function.Injective nodes)
    (prims : List (ℕ × PrimOp)) (pre : Fin 3 → (ZMod p)[X])
    (hpre : ∀ k : Fin 3, pre k = Lagrange.interpolate Finset.univ nodes (fun i => pregCol prims (k : ℕ) (i : ℕ))) :
    PregOK nodes prims pre ↔ prims.length ≤ n := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun i => ?_⟩
    have e : ∀ k : Fin 3, (pre k).eval (nodes i) = pregCol prims (k : ℕ) (i : ℕ) := fun k => by
      rw [hpre k, Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)]
    refine ⟨?_, ?_, ?_⟩
    · rw [e 0]; simp [pregCol]
    · rw [e 1]; simp [pregCol]
    · rw [e 2]; simp [pregCol]

theorem preOf_two {n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (pre : Fin 3 → (ZMod p)[X]) :
    preOf hn nodes pre ⟨2, by omega⟩ = pre 0 := by
  simp [preOf] <;> rfl

theorem preOf_three {n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (pre : Fin 3 → (ZMod p)[X]) :
    preOf hn nodes pre ⟨3, by omega⟩ = pre 1 := by
  simp [preOf] <;> rfl

theorem preOf_four {n : ℕ} (hn : 0 < n) (nodes : Fin n → ZMod p) (pre : Fin 3 → (ZMod p)[X]) :
    preOf hn nodes pre ⟨4, by omega⟩ = pre 2 := by
  simp [preOf] <;> rfl

/-- **`checkAlu_iff`: the ALU chip (satisfies + binds), finitely.** -/
theorem checkAlu_iff (prims : List (ℕ × PrimOp)) {n h : ℕ} (T : TabM n) (hn : 0 < n)
    (orbit : StrictOrbitDomain (ZMod p) 3 h) (pre : Fin 3 → (ZMod p)[X])
    (P : Fin (aluSZChipJ9 deltaF powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i)) pre).rap.w → (ZMod p)[X])
    (hinj : Function.Injective T.nodes)
    (hadj : ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, T.nodes ⟨i + 1, h⟩ = T.ω * T.nodes i)
    (hω : orbit.ω = T.ω) (hprep : T.prep = prepAL n prims)
    (hpre : ∀ k : Fin 3, pre k = Lagrange.interpolate Finset.univ T.nodes (fun i => pregCol prims (k : ℕ) (i : ℕ)))
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ T.nodes (fun i => T.cols j i)) :
    RAP.SatisfiesWithPreprocessing (aluSZChipJ9 deltaF powerBasis3 hn T.nodes orbit (fun i => K3.toK (T.chals i))
      (fun i => K3.toK (T.pubs i)) pre) P ↔ checkM (aluTemplateSZ deltaF) T = true := by
  refine chipM_iff (aluTemplateSZ deltaF) T _ P hinj hadj rfl hω rfl ?_ ?_ hP
  · rw [aluTemplateSZ_baseCols]
    exact Nock.V1J8.MemX.expandChip_C _ _ _ _ _ _
  · rw [hprep]
    simp only [List.ofFn_succ, List.ofFn_zero, aluSZChipJ9, FixedPreprocessingRAP.preprocessingColumn,
      RAP.preprocessingColumn, prepAL, List.map_cons, List.map_nil]
    refine congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_)
      (congrArg₂ _ (Prod.ext rfl ?_) (congrArg₂ _ (Prod.ext rfl ?_) rfl))))
    · exact Nock.V1J8.MemX.firstMask_interp _
    · exact Nock.V1J8.MemX.lastMask_interp hn _
    · exact (preOf_two hn T.nodes pre).trans (hpre 0)
    · exact (preOf_three hn T.nodes pre).trans (hpre 1)
    · exact (preOf_four hn T.nodes pre).trans (hpre 2)

end Alu

section AluChallenges
variable [iA : Algebra Nock.Atoms.Fp KQ]

theorem chalsALJ8E_spec (χe : CoinsE) (j : ℕ) :
    K3.toK (chalsALJ8E χe j) = AluSZChipJ9.chalsALJ8 deltaF (toχ χe) j := by
  unfold chalsALJ8E AluSZChipJ9.chalsALJ8
  by_cases h : 40 ≤ j ∧ j < 106
  · rw [if_pos h, if_pos h]
    have hm := AluSZChipJ9.ypowC_mk deltaF (toχ χe cY1) (toχ χe cY2) ((j - 40) / 2)
    have e1 := congrArg (Quad.re _) hm
    have e2 := congrArg (Quad.im _) hm
    rw [Quad.re_mk] at e1
    rw [Quad.im_mk] at e2
    have q1 := quad_pow_re (χe cY1) (χe cY2) ((j - 40) / 2)
    have q2 := quad_pow_im (χe cY1) (χe cY2) ((j - 40) / 2)
    split_ifs
    · exact q1.symm.trans e1.symm
    · exact q2.symm.trans e2.symm
  · rw [if_neg h, if_neg h]
    exact chalsAJ8ZE_spec χe j

theorem chalsALJ8_eq (χe : CoinsE) :
    AluSZChipJ9.chalsALJ8 deltaF (toχ χe) = fun j => K3.toK (chalsALJ8E χe j) :=
  funext fun j => (chalsALJ8E_spec χe j).symm

end AluChallenges

section AlOK
variable [iA : Algebra Nock.Atoms.Fp KQ]

/-- **`alOK_iff`: `ALChipOK` (present or absent) is exactly `alOK`.** -/
theorem alOK_iff (I : InJ9AL) (hn : 0 < I.AL.n) (ho : OrbOK I.AL)
    (chals pubs : ℕ → KC) (hch : chals = fun i => K3.toK (chalsALJ8E I.χ i))
    (hpub : pubs = fun i => K3.toK (I.pubsL i))
    (pre : Fin 3 → (ZMod p)[X])
    (hpre : ∀ k : Fin 3, pre k =
      Lagrange.interpolate Finset.univ (nodesOf I.AL) (fun i => pregCol I.prims (k : ℕ) (i : ℕ)))
    (P : Fin (aluSZChipJ9 deltaF powerBasis3 hn (nodesOf I.AL) (mkOrbit I.AL ho) chals pubs pre).rap.w →
      (ZMod p)[X])
    (hP : ∀ j, P j = Lagrange.interpolate Finset.univ (nodesOf I.AL) (fun i => I.AL.cols j i)) :
    ALChipOK deltaF powerBasis3 I.aluOn I.prims hn (nodesOf I.AL) (mkOrbit I.AL ho) pre chals pubs P ↔
      alOK I = true := by
  subst hch hpub
  have ha : (∀ (i : Fin I.AL.n) (hi : (i : ℕ) + 1 < I.AL.n),
      nodesOf I.AL ⟨(i : ℕ) + 1, hi⟩ = nodesOf I.AL i * (mkOrbit I.AL ho).ω) ↔
      Nock.V1J8.MemX.adjB (tabAL I) = true := by
    rw [Nock.V1J8.MemX.adjB_iff]; rfl
  have hob : orbB I.AL = true := (orbB_iff _).mpr ho
  have hnb : decide (0 < I.AL.n) = true := decide_eq_true hn
  unfold ALChipOK alOK
  cases hal : I.aluOn
  · simp [eq3_iff, K3.toK_zero, and_assoc]
  · simp only [hob, hnb, Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false, Bool.and_eq_true,
      decide_eq_true_eq, nodupB_iff]
    constructor
    · rintro (⟨-, hs, hb, hi, hadj, hlt, hpr⟩ | ⟨h, -⟩)
      · refine ⟨⟨⟨⟨(checkAlu_iff I.prims (tabAL I) hn (mkOrbit I.AL ho) pre P hi
          (Nock.V1J8.MemX.adj_core (tabAL I) rfl hadj) rfl rfl hpre hP).mp ⟨hs, hb⟩, hi⟩, ha.mp hadj⟩, hlt⟩, ?_⟩
        exact hpr.1
      · exact absurd h (by decide)
    · rintro ⟨⟨⟨⟨hc, hi⟩, hadj⟩, hlt⟩, hlen⟩
      have hadj' := ha.mpr hadj
      obtain ⟨hs, hb⟩ := (checkAlu_iff I.prims (tabAL I) hn (mkOrbit I.AL ho) pre P hi
        (Nock.V1J8.MemX.adj_core (tabAL I) rfl hadj') rfl rfl hpre hP).mpr hc
      exact Or.inl ⟨trivial, hs, hb, hi, hadj', hlt, (pregOK_iff (nodesOf I.AL) hi I.prims pre hpre).mpr hlen⟩

end AlOK

/-! ## 5. The split `AcceptsJ9AL ↔ StaticJ9AL ∧ PubEqJ9AL ∧ ChipsJ9AL` -/

section Split
variable {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

/-- **The chip residue of `AcceptsJ9AL`**: `ChipsJ9A` at the J-9 A projections, the ALU, the primitive registry. -/
structure ChipsJ9AL (Pb : PubJ9AL p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p)) : Prop where
  toChips : ChipsJ9A δ b Pb.toPubJ9A Rg c χ M.toMsgJ9A' tr.toTrJ9A
  hALk : ALChipOK δ b Pb.aluOn Pb.prims Pb.hnL Pb.nodesL Pb.orbitL Pb.preL (AluSZChipJ9.chalsALJ8 δ χ) M.pubsL
    (RealIOJ9AL.qAL δ b Pb tr (AluSZChipJ9.chalsALJ8 δ χ) M.pubsL)
  hPrim : ∀ q ∈ Pb.prims, Rg q.1 = some (Nock.Jet.Prim.primSpec q.2)

/-- **The split**: `AcceptsJ9AL` is exactly `StaticJ9AL ∧ PubEqJ9AL ∧ ChipsJ9AL`. -/
theorem acceptsJ9AL_iff (Pb : PubJ9AL p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p)) (r : RowsJ9AL) (g : ℕ) :
    AcceptsJ9AL δ b Pb Rg c χ M tr r g ↔
      StaticJ9AL Pb c M.m r g ∧ PubEqJ9AL δ b Pb c χ M ∧ ChipsJ9AL δ b Pb Rg c χ M tr := by
  have hr : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  constructor
  · intro h
    exact ⟨⟨h.hinjX, h.hadjX, h.hinjC, h.hadjC, lt_of_lt_of_eq h.hnpC hr, h.hinjW, h.hadjW, h.hkW, h.hknW,
      lt_of_lt_of_eq h.hkpW hr, h.hinjA, h.hadjA, h.hnpA, h.hlay, h.hsmall, h.huniq,
      fun i hi => (h.hTpl i hi).2.1, h.hnd, h.hidx, h.hrk,
      fun id hid => by simpa only [hr] using h.hlt id hid, h.hclI, h.hclR, h.hcen', h.hlenC, h.hlenA,
      h.hcellF, h.hnAS, h.hbud, h.hbudV, h.hlenX, h.hlenL, h.hndP, h.hrkP,
      fun q hq => by simpa only [hr] using h.hltP q hq, h.hlenCP, h.hdisjP⟩,
      ⟨h.hGx, h.hGp, h.hGS, h.hsumC', h.hbalA', h.hvalA0, h.hfxC, h.hfxA⟩,
      ⟨⟨h.hsatX, h.hsatC, h.hbindC, h.hsatW, h.hbindW, h.hJk, h.hsatA, h.hbindA, h.hVk, h.hsatL, h.hbindL,
        h.hAXk, h.hSPk, fun i hi => ⟨(h.hTpl i hi).1, (h.hTpl i hi).2.2⟩⟩, h.hALk, h.hPrim⟩⟩
  · rintro ⟨s, ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩, k, kL, kP⟩
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21,
      s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37⟩ := s
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
      hAXk := k.hAXk, hSPk := k.hSPk, hlenX := s31
      hALk := kL, hPrim := kP, hdisjP := s37, hlenL := s32, hndP := s33, hrkP := s34
      hltP := fun q hq => by simpa only [hr] using s35 q hq, hlenCP := s36 }

end Split

/-! ## 6. The chip block -/

section Chips
variable [iA : Algebra Nock.Atoms.Fp KQ] [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) KC]

/-- The node facts of the six memory chips that `chipsBJ9A_iff` reads from the static block. -/
structure NodesOK9 (Pb : PubJ9A p) : Prop where
  injX : Function.Injective Pb.nodes
  adjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  injC : Function.Injective Pb.nodesC
  adjC : ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω
  injW : Function.Injective Pb.nodesW
  adjW : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω
  injA : Function.Injective Pb.nodesA
  adjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω

theorem NodesOK9.of_static {Pb : PubJ9AL p} {c : P8PublicClaim} {m : ClaimMsgVS} {r : RowsJ9AL} {g : ℕ}
    (s : StaticJ9AL Pb c m r g) : NodesOK9 Pb.toPubJ9A :=
  ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.2.1, s.2.2.2.2.2.2.1, s.2.2.2.2.2.2.2.2.2.2.1,
    s.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- **`hcX9`, from the node facts only**: `checkCompX9` decides the twin compute RAP. -/
theorem hcX9L (I : InJ9A) (hv : ValidJ9A I) (hinj : Function.Injective (mkPbA I hv).nodes)
    (hadj : ∀ (i : Fin (mkPbA I hv).n) (hi : (i : ℕ) + 1 < (mkPbA I hv).n),
      (mkPbA I hv).nodes ⟨(i : ℕ) + 1, hi⟩ = (mkPbA I hv).nodes i * (mkPbA I hv).orbit.ω) :
    CompX9.checkCompX9 (Nock.V1J9A.CheckJ9AIffComp.tabOf I) = true ↔ RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 (mkPbA I hv).hn (mkPbA I hv).nodes powerBasis3 deltaF (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ)) (mkPbA I hv).orbit)
      (qX9 deltaF powerBasis3 (mkPbA I hv) I.toTr (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ))) := by
  have hcv := Nock.V1J8.Check.chalVJ8_eq I.χ
  have hpv := Nock.V1J9.Check9.pubVJ9_eq I.c I.M.m I.M.ρ I.M.ρS I.χ
  have eX := Nock.V1J9A.CheckJ9AIffComp.computeChipX9_iff (Nock.V1J9A.CheckJ9AIffComp.tabOf I) hv.nX
    (mkOrbit I.X hv.oX)
    (qX9 deltaF powerBasis3 (mkPbA I hv) I.toTr (Nock.V1J9A.CheckJ9AIffComp.tabOf I).chal
      (Nock.V1J9A.CheckJ9AIffComp.tabOf I).pub)
    hinj (Nock.V1J8.Check.adj_of I.X hv.oX hadj) rfl (fun j => rfl)
  rw [← eX]
  show RAP.SatisfiesWithPreprocessing _ _ ↔ RAP.SatisfiesWithPreprocessing _ _
  rw [hcv]
  erw [hpv]
  exact Iff.rfl


/-- **`chipsBJ9A_iff`, from the node facts only** (copy of `CheckJ9AIff.chipsBJ9A_iff` with the static block replaced by
`NodesOK9`, the only part of it the proof reads). -/
theorem chipsBJ9A_iff' (compOK : InJ9A → Bool) (I : InJ9A) (hv : ValidJ9A I) (Rg : Nock.Jet.Registry)
    (hreg : RegOK I.toInJ8 Rg) (hs : NodesOK9 (mkPbA I hv))
    (Hc : compOK I = true ↔ RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 (mkPbA I hv).hn (mkPbA I hv).nodes powerBasis3 deltaF (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ)) (mkPbA I hv).orbit)
      (qX9 deltaF powerBasis3 (mkPbA I hv) I.toTr (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ)))) :
    chipsBJ9A compOK I = true ↔
      ChipsJ9A deltaF powerBasis3 (mkPbA I hv) Rg I.c (toχ I.χ) I.toMsg I.toTr := by
  obtain ⟨s1, s2, s3, s4, s6, s7, s11, s12⟩ := hs
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

/-- **The nine-chip block**: `chipsBJ9AL` is exactly `ChipsJ9AL` (primitive registry premise given). -/
theorem chipsBJ9AL_iff (compOK : InJ9A → Bool) (I : InJ9AL) (hv : ValidJ9AL I) (Rg : Nock.Jet.Registry)
    (hreg : RegOK I.toInJ8 Rg) (hprim : ∀ q ∈ I.prims, Rg q.1 = some (primSpec q.2))
    (hs : NodesOK9 (mkPbA I.toInJ9A hv.toValidJ9A))
    (Hc : compOK I.toInJ9A = true ↔ RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 (mkPbA I.toInJ9A hv.toValidJ9A).hn (mkPbA I.toInJ9A hv.toValidJ9A).nodes powerBasis3 deltaF
        (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ))
        (mkPbA I.toInJ9A hv.toValidJ9A).orbit)
      (qX9 deltaF powerBasis3 (mkPbA I.toInJ9A hv.toValidJ9A) I.toTr (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ)))) :
    chipsBJ9AL compOK I = true ↔
      ChipsJ9AL deltaF powerBasis3 (mkPbAL I hv) Rg I.c (toχ I.χ) I.toMsgL I.toTrL := by
  unfold chipsBJ9AL
  rw [Bool.and_eq_true]
  have eA := chipsBJ9A_iff' compOK I.toInJ9A hv.toValidJ9A Rg hreg hs Hc
  have eL := alOK_iff I hv.nL hv.oAL (AluSZChipJ9.chalsALJ8 deltaF (toχ I.χ)) (fun i => K3.toK (I.pubsL i))
    (chalsALJ8_eq I.χ) rfl (mkPbAL I hv).preL (fun k => rfl)
    (RealIOJ9AL.qAL deltaF powerBasis3 (mkPbAL I hv) I.toTrL (AluSZChipJ9.chalsALJ8 deltaF (toχ I.χ))
      (fun i => K3.toK (I.pubsL i))) (fun j => rfl)
  constructor
  · rintro ⟨hA, hL⟩
    exact ⟨eA.mp hA, eL.mpr hL, hprim⟩
  · intro k
    exact ⟨eA.mpr k.toChips, eL.mp k.hALk⟩

/-! ## 7. `checkJ9AL_iff` -/

/-- **`checkJ9AL_iff_of_comp`** (conditional on the compute decision `Hc`). -/
theorem checkJ9AL_iff_of_comp (compOK : InJ9A → Bool) (I : InJ9AL) (Rg : Nock.Jet.Registry)
    (hreg : RegOK I.toInJ8 Rg) (hprim : ∀ q ∈ I.prims, Rg q.1 = some (primSpec q.2))
    (Hc : ∀ hv : ValidJ9AL I, NodesOK9 (mkPbA I.toInJ9A hv.toValidJ9A) →
      (compOK I.toInJ9A = true ↔ RAP.SatisfiesWithPreprocessing
      (computeChipVCLHX9 (mkPbA I.toInJ9A hv.toValidJ9A).hn (mkPbA I.toInJ9A hv.toValidJ9A).nodes powerBasis3 deltaF
        (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ))
        (mkPbA I.toInJ9A hv.toValidJ9A).orbit)
      (qX9 deltaF powerBasis3 (mkPbA I.toInJ9A hv.toValidJ9A) I.toTr (chalVJ8 powerBasis3 (toχ I.χ))
        (pubVJ9 deltaF powerBasis3 I.c I.toMsg.m I.toMsg.ρ I.toMsg.ρS (toχ I.χ))))) :
    checkJ9AL compOK I = true ↔ ∃ hv : ValidJ9AL I,
      AcceptsJ9AL deltaF powerBasis3 (mkPbAL I hv) Rg I.c (toχ I.χ) I.toMsgL I.toTrL I.toRowsL I.g := by
  unfold checkJ9AL
  constructor
  · intro h
    by_cases hb : validB I.toInJ8 = true
    · rw [dif_pos hb] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨hax, hal⟩, hs⟩, hp⟩, hc⟩ := h
      have hv : ValidJ9AL I :=
        { ValidJ9A.mk' I.toInJ9A ((validB_iff _).mp hb) ((validAXSPB_iff I.toInJ9A).mp hax) with
          nL := ((validALB_iff I).mp hal).1, oAL := ((validALB_iff I).mp hal).2 }
      have hs' := (checkStaticJ9AL_iff (mkPbAL I hv) I.c I.M.m I.toRowsL I.g).mp hs
      have hn := NodesOK9.of_static hs'
      refine ⟨hv, (acceptsJ9AL_iff deltaF powerBasis3 _ Rg I.c (toχ I.χ) I.toMsgL I.toTrL I.toRowsL I.g).mpr
        ⟨hs', (checkPubJ9ALE_iff (mkPbAL I hv) I.c I.χ I.M I.pubsX I.pubsS I.pubsL).mp hp, ?_⟩⟩
      exact (chipsBJ9AL_iff compOK I hv Rg hreg hprim hn (Hc hv hn)).mp hc
    · rw [dif_neg hb] at h; exact absurd h Bool.false_ne_true
  · rintro ⟨hv, h⟩
    obtain ⟨hs, hp, hc⟩ := (acceptsJ9AL_iff deltaF powerBasis3 _ Rg I.c (toχ I.χ) I.toMsgL I.toTrL I.toRowsL I.g).mp h
    have hb : validB I.toInJ8 = true := (validB_iff _).mpr hv.toValidJ8
    rw [dif_pos hb]
    simp only [Bool.and_eq_true]
    have hn := NodesOK9.of_static hs
    exact ⟨⟨⟨⟨(validAXSPB_iff I.toInJ9A).mpr ⟨hv.nAX, hv.oAX, hv.nSP, hv.oSP⟩,
      (validALB_iff I).mpr ⟨hv.nL, hv.oAL⟩⟩,
      (checkStaticJ9AL_iff (mkPbAL I hv) I.c I.M.m I.toRowsL I.g).mpr hs⟩,
      (checkPubJ9ALE_iff (mkPbAL I hv) I.c I.χ I.M I.pubsX I.pubsS I.pubsL).mpr hp⟩,
      (chipsBJ9AL_iff compOK I hv Rg hreg hprim hn (Hc hv hn)).mpr hc⟩

/-- **`checkJ9ALX_iff`: the executable J-9 AL checker agrees with the `AcceptsJ9AL` predicate.**
For a jet registry `Rg` that is consistent with the input's registry data (`RegOK`) and registers every primitive
the input uses with its primitive spec, `checkJ9ALX I = true` if and only if the input is valid (`ValidJ9AL`) and
`AcceptsJ9AL` holds at the verifier data built from the input.  No other hypothesis. -/
theorem checkJ9ALX_iff (I : InJ9AL) (Rg : Nock.Jet.Registry) (hreg : RegOK I.toInJ8 Rg)
    (hprim : ∀ q ∈ I.prims, Rg q.1 = some (primSpec q.2)) :
    checkJ9ALX I = true ↔ ∃ hv : ValidJ9AL I,
      AcceptsJ9AL deltaF powerBasis3 (mkPbAL I hv) Rg I.c (toχ I.χ) I.toMsgL I.toTrL I.toRowsL I.g := by
  refine checkJ9AL_iff_of_comp _ I Rg hreg hprim ?_
  intro hv hn
  exact hcX9L I.toInJ9A hv.toValidJ9A hn.injX hn.adjX

end Chips

end Nock.V1J9AL.CheckJ9ALIff
