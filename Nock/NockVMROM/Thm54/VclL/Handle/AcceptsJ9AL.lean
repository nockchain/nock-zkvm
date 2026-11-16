/-
  Nock/NockVMROM/Thm54/VclL/Handle/AcceptsJ9AL.lean

  **Step 2: `AcceptsJ9AL`, the J-9 AL verifier predicate** (the J-9 A
  predicate plus the big-atom ALU `aluSZChipJ9`).

  Against `AcceptsJ9A` (every field verbatim at the projections `Pb.toPubJ9A`, `M.toMsgJ9A'`, `tr.toTrJ9A`,
  `r.toRowsJ9A` unless listed):
  * CHANGED (5): `hGx` (+ `pubALx` terminal with the J chip's), `hGS` (+ the `pinRgP` / `pinOpP` pin sums
    and `pubALs` terminal on the left), `hsumC'` (+ `pubALv` terminal on the LEFT, + the primitive pin records `pinRecsP`),
    `hcen'` (+ the primitive formula nouns `censusP`), `hbud : BudJ9AL`.
  * ADDED (8): `hALk : ALChipOK`, `hPrim`, `hdisjP`, `hlenL`, and `hndP`, `hrkP`,
    `hltP`, `hlenCP`.
  * The cell-side primitive pin: the ALU-side pin `pinRgP` (keyRg `(id, 1, idxP id, 0,0,0,0, 7)`) in `hGS` fixes only the
    handle `(1, idxP id)`; the claim record `(encJ8 (primC op), rkP id, idxP id)` in `hsumC'`, `rkP id ≠ (0, 0)`
    and the census at `primC op` bind the cell at that handle to `primC op` (`hReg_of_pinP`, the prim twin of
    `PinJ8.hReg_of_pin` / `CorJ8F.hReg_of_pinR`).
  * `AcceptsJ9AL.of_A`: an `AcceptsJ9A` with the ALU absent (`aluOn = false`, `prims = []`, `pubsL = 0` at the three
    ALU publics) is an `AcceptsJ9AL`; every field not changed is a bare projection, the four changed equations are
    the `AcceptsJ9A` ones with the zero ALU terms and the empty primitive lists removed, and `BudJ9AL` is derived
    from `BudJ9A` and `nL ≤ AL`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL

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
open Nock.Jet.RapJetJ8 (jRd jProv jCons keyK)
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
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AWChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9

open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A (AXChipOK SPChipOK)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (aluSZChipJ9)
open Nock.Jet.Prim (PrimOp)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (computeChipVCLHX9)



section Accept
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) K]
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]

local notation "𝕂′" => Quad (algebraMap (ZMod p) K δ)

/-- **The `preg` layout of the ALU's preprocessing**: row `i < |prims|` has `sP = 1`, `pId` = the id, `pOp` = the
op code (`primCode`); every other row is `0`.  `pre 0 / 1 / 2` = `sP / pId / pOp` (`AluSZChipJ9.preOf`). -/
def PregOK {nL : ℕ} (nodesL : Fin nL → ZMod p) (prims : List (ℕ × PrimOp)) (preL : Fin 3 → (ZMod p)[X]) : Prop :=
  prims.length ≤ nL ∧ ∀ i : Fin nL,
    (preL 0).eval (nodesL i) = (if (i : ℕ) < prims.length then 1 else 0) ∧
    (preL 1).eval (nodesL i) = (prims.map fun q => ((q.1 : ℕ) : ZMod p)).getD i 0 ∧
    (preL 2).eval (nodesL i) = (prims.map fun q => ((primCode q.2 : ℕ) : ZMod p)).getD i 0

/-- **The ALU, present or absent** (R8: absence is a public flag; the `AXChipOK` shape).  Present: `aluOn = true`,
the chip's conjuncts and the `preg` layout of `prims`.  Absent: `aluOn = false`, `prims = []` and the three ALU
terminals (`pubALv`, `pubALs`, `pubALx`, each `+ 1`) are `0`. -/
def ALChipOK (aluOn : Bool) (prims : List (ℕ × PrimOp)) {hL nL : ℕ} (hnL : 0 < nL) (nodesL : Fin nL → ZMod p)
    (orbitL : StrictOrbitDomain (ZMod p) 3 hL) (preL : Fin 3 → (ZMod p)[X]) (chalsL pubsL : ℕ → K)
    (QL : Fin (aluSZChipJ9 δ b hnL nodesL orbitL chalsL pubsL preL).rap.w → (ZMod p)[X]) : Prop :=
  (aluOn = true ∧ (aluSZChipJ9 δ b hnL nodesL orbitL chalsL pubsL preL).rap.Satisfies QL ∧
      (aluSZChipJ9 δ b hnL nodesL orbitL chalsL pubsL preL).BindsPreprocessing QL ∧
      Function.Injective nodesL ∧
      (∀ (i : Fin nL) (hi : (i : ℕ) + 1 < nL), nodesL ⟨(i : ℕ) + 1, hi⟩ = nodesL i * orbitL.ω) ∧
      nL < p ∧ PregOK nodesL prims preL) ∨
    (aluOn = false ∧ prims = [] ∧ pubsL AluSZChipJ9.pubALv = 0 ∧ pubsL (AluSZChipJ9.pubALv + 1) = 0 ∧
      pubsL AluSZChipJ9.pubALs = 0 ∧ pubsL (AluSZChipJ9.pubALs + 1) = 0 ∧
      pubsL AluSZChipJ9.pubALx = 0 ∧ pubsL (AluSZChipJ9.pubALx + 1) = 0)

/-- **The ALU keyRg pin vector** `(id, 1, idx, 0, 0, 0, 0, 7)` (tag last at `tagRgP`), the chip's `keyRgE` at
`idc = id, kc = 1, vc = idx` (`pinRgP_shape`), as a width-8 `K`-vector. -/
def pinRgVec (id idx : ℕ) : Fin 8 → K :=
  keyK 8 [((id : ℕ) : ZMod p), 1, ((idx : ℕ) : ZMod p), 0, 0, 0, 0, ((AluSZChipJ9.tagRgP : ℕ) : ZMod p)]

/-- **The verifier-computed ALU keyRg pins**: one `pinRgVec id (idxP id)` per `(id, op) ∈ prims`. -/
def pinRgP (Pb : PubJ9AL p) : List (Fin 8 → K) :=
  Pb.prims.map fun q => pinRgVec (p := p) (K := K) q.1 (Pb.idxP q.1)

/-- **The verifier-computed op-record pins**: for each `(id, op) ∈ prims` the op record
`(id, primCode op, 0, 0, 0, 0, 0, 6)` (tag last), encoded as the chip's `opRecE` (`AluSZChipJ9.lean`, `opRecRE`;
opcode numbering `add 1 … mod 6`, `primCode`), as a width-8 `K`-vector (`keyK`). -/
def pinOpP (Pb : PubJ9AL p) : List (Fin 8 → K) :=
  Pb.prims.map fun q => keyK 8
    [((q.1 : ℕ) : ZMod p), ((primCode q.2 : ℕ) : ZMod p), 0, 0, 0, 0, 0, ((AluSZChipJ9.tagOp : ℕ) : ZMod p)]

/-- **`pinRgP_shape`: the pin vector IS the chip's keyRg vector** at `idc = id`, `kc = 1`, `vc = idx`. -/
theorem pinRgP_shape (id idx : ℕ) (eF : Env (ZMod p))
    (hid : eF.trace AluSZChipJ9.idc = (id : ZMod p)) (hk : eF.trace AluSZChipJ9.kc = 1)
    (hv : eF.trace AluSZChipJ9.vc = (idx : ZMod p)) :
    AxisChipJ9.keyVecL (K := K) 8 AluSZChipJ9.keyRgE eF = pinRgVec (p := p) (K := K) id idx := by
  funext c
  fin_cases c <;>
    simp [AxisChipJ9.keyVecL, AluSZChipJ9.keyRgE, AluSZChipJ9.keyRgRE, AluSZChipJ9.reE, CoeffExpr.eval,
      Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP.cv, pinRgVec, keyK, hid, hk, hv]

/-- **`pinRgVec_ne_pinCons`**: the ALU keyRg pin `pinRgVec id idx` (entry 7 = tag 7) is not equal to any element of
`pinCons regs idx'` = `(id', 1, idx, 0,0,0,0, 2)` (`PinJ8.lean:64,74`), so the template pins never absorb it.
Needs `5 ≠ 0` in `ZMod p` (`7 ≠ 2`); the general form is `AluSZChipJ9.keyRgAL_disjoint_J`. -/
theorem pinRgVec_ne_pinCons (h5 : (5 : ZMod p) ≠ 0)
    (id idx : ℕ) (regs : List ℕ) (idx' : ℕ → ℕ) :
    pinRgVec (p := p) (K := K) id idx ∉ pinCons (p := p) (K := K) regs idx' := by
  intro hm
  obtain ⟨id', -, hid'⟩ := List.mem_map.mp hm
  have h7 := congrFun hid' 7
  simp only [pinRgVec, Nock.Jet.RapJetJ8.keyK, Nock.Jet.RapJetJ8.tlF, Nock.Jet.PinJ8.pinKey] at h7
  have h7' := (algebraMap (ZMod p) K).injective h7
  simp [AluSZChipJ9.tagRgP] at h7'
  exact h5 (by linear_combination -h7')

/-- **The verifier-computed primitive pin records** (the prim twin of `AcceptsJ8P.pinRecsJ8`;
check 4): one claim record `claimVec (encJ8 (primC op)) (idxP id) (rkP id)` per `(id, op) ∈ prims`.  Consumed in
the cell validity balance (`hsumC'`), they bind the cell at `idxP id` to the noun `primC op`
(`hReg_of_pinP`). -/
def pinRecsP (Pb : PubJ9AL p) (χ : Coins frameJ8 K) : List (Fin 5 → 𝕂′) :=
  Pb.prims.map fun q => ClaimVS.claimVec δ (encJ8 δ χ (Nock.Jet.Prim.primC q.2)) (Pb.idxP q.1 : ZMod p)
    ((Pb.rkP q.1).1 : ZMod p) ((Pb.rkP q.1).2 : ZMod p)

/-- **The primitive census nouns** (the prim twin of `censusGJ9`'s registered formulas): `primC op` per
`(id, op) ∈ prims`. -/
def censusP (Pb : PubJ9AL p) : List Noun := Pb.prims.map fun q => Nock.Jet.Prim.primC q.2

theorem pinRecsP_nil (Pb : PubJ9AL p) (χ : Coins frameJ8 K) (h : Pb.prims = []) : pinRecsP δ Pb χ = [] := by
  simp [pinRecsP, h]

theorem censusP_nil (Pb : PubJ9AL p) (h : Pb.prims = []) : censusP Pb = [] := by
  simp [censusP, h]

/-- **`AcceptsJ9AL`** (J-9 AL twin of `AcceptsJ9A`, see the module header). -/
structure AcceptsJ9AL (Pb : PubJ9AL p) (Rg : Nock.Jet.Registry) (c : P8PublicClaim) (χ : Coins frameJ8 K)
    (M : MsgJ9AL' p K δ) (tr : TrJ9AL (ZMod p)) (r : RowsJ9AL) (g : ℕ) : Prop where
  -- compute: CHANGED, the twin RAP
  hsatX : RAP.SatisfiesWithPreprocessing (computeChipVCLHX9 Pb.hn Pb.nodes b δ (chalVJ8 b χ)
    (pubVJ9 δ b c M.m M.ρ M.ρS χ) Pb.orbit) (qX9 δ b Pb.toPubJ9A tr.toTrJ9A (chalVJ8 b χ) (pubVJ9 δ b c M.m M.ρ M.ρS χ))
  hinjX : Function.Injective Pb.nodes
  hadjX : ∀ (i : Fin Pb.n) (hi : (i : ℕ) + 1 < Pb.n), Pb.nodes ⟨(i : ℕ) + 1, hi⟩ = Pb.nodes i * Pb.orbit.ω
  -- the cell table
  hsatC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).rap.Satisfies
    (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC)
  hbindC : (cellChipHQKW δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC).BindsPreprocessing
    (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC)
  hinjC : Function.Injective Pb.nodesC
  hadjC : ∀ (i : Fin Pb.nC) (hi : (i : ℕ) + 1 < Pb.nC), Pb.nodesC ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesC i * Pb.orbitC.ω
  hnpC : Pb.nC < ringChar (ZMod p)
  -- the J-8 walk
  hsatW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).rap.Satisfies
    (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW)
  hbindW : (walkChipJ8 δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) M.pubsW).BindsPreprocessing
    (qW δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsW)
  hinjW : Function.Injective Pb.nodesW
  hadjW : ∀ (i : Fin Pb.nW) (hi : (i : ℕ) + 1 < Pb.nW), Pb.nodesW ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesW i * Pb.orbitW.ω
  hkW : 1 ≤ Pb.kroots
  hknW : Pb.kroots ≤ Pb.nW
  hkpW : Pb.kroots + Pb.nW < ringChar (ZMod p)
  -- the J chip: PRESENT (its five conjuncts) or ABSENT (`nJ = 0`, `pubsJ 0..3 = 0`)
  hJk : JGenJ8.JChipOK δ b Pb.nodesJ Pb.orbitJ (chalsJJ8 χ) M.pubsJ Pb.lay
    (qJ δ b Pb.toPubJ8 tr.toJ8 (chalsJJ8 χ) M.pubsJ)
  -- the atom table
  hsatA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  hbindA : (AtomChipHQ.atomChipHQ δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qA δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  hinjA : Function.Injective Pb.nodesA
  hadjA : ∀ (i : Fin Pb.nA) (hi : (i : ℕ) + 1 < Pb.nA), Pb.nodesA ⟨(i : ℕ) + 1, hi⟩ = Pb.nodesA i * Pb.orbitA.ω
  hnpA : Pb.nA < p
  -- the atom walk: PRESENT or ABSENT
  hVk : AWChipOK δ b Pb.krootsV Pb.hnV Pb.nodesV Pb.orbitV (chalsAJ8Z δ χ) M.pubsV
    (qV δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsV)
  -- the public balance equations; CHANGED: + the ALU export terminal (left, with the J chip)
  hGx : M.ρ 3 + (Quad.mk _ (M.pubsW WalkHQ.pubXQ) (M.pubsW (WalkHQ.pubXQ + 1)) + Quad.mk _ (M.pubsJ 2) (M.pubsJ 3) +
      Quad.mk _ (M.pubsL AluSZChipJ9.pubALx) (M.pubsL (AluSZChipJ9.pubALx + 1))) =
    Quad.mk _ (M.pubsC CellHQ.pubHQ) (M.pubsC (CellHQ.pubHQ + 1))
  -- CHANGED: the axis chip consumes path records
  hGp : M.ρ 4 + Quad.mk _ (M.pubsX AxisChipJ9.pubAXp) (M.pubsX (AxisChipJ9.pubAXp + 1)) =
    Quad.mk _ (M.pubsW WalkHQ.pubPQ) (M.pubsW (WalkHQ.pubPQ + 1))
  -- CHANGED: + the axis net service terminal (left), + the split limb provides (right);
  -- CHANGED (AL): + the primitive pins `pinRgP`, `pinOpP` and the ALU service terminal (left)
  /- Two verifier pins per primitive, because the ALU's `invR` (keyRg) and `invO` (op record) inverses carry the SAME
  service weight `wS = sH − sP·mP` (`AluSZChipJ9.lean:479-493`): an honest prover with `c` calls of a prim has
  `mP = c + 1` for keyRg and `mP = c` for the op record unless the verifier consumes BOTH keys once.
  `pinRgP` consumes the keyRg `(id, 1, idxP id, 0,0,0,0, 7)` (the chip's tag-last `keyRgRE`,
  `pinRgP_shape`); `pinOpP` consumes the op record `(id, code, 0,0,0,0,0, 6)`.  Both keys then balance at
  `mP = c + 1`. -/
  hGS : M.ρS + ((pinCons (p := p) (K := K) Pb.regs Pb.idx).map fun r =>
      (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum +
      ((pinRgP (p := p) (K := K) Pb).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum +
      ((pinOpP (p := p) (K := K) Pb).map fun r =>
        (compress (coinsCV b δ (chalVJ8 b χ)) (liftRec (L := 𝕂′) r))⁻¹).sum + Quad.mk _ (M.pubsJ 0) (M.pubsJ 1) +
      Quad.mk _ (M.pubsX AxisChipJ9.pubAXs) (M.pubsX (AxisChipJ9.pubAXs + 1)) +
      Quad.mk _ (M.pubsL AluSZChipJ9.pubALs) (M.pubsL (AluSZChipJ9.pubALs + 1)) =
    Quad.mk _ (M.pubsA AtomChipHQ.pubMI) (M.pubsA (AtomChipHQ.pubMI + 1)) +
      Quad.mk _ (M.pubsV WalkHQ.pubPQ) (M.pubsV (WalkHQ.pubPQ + 1)) +
      Quad.mk _ (M.pubsS SplitChipJ9.pubSPs) (M.pubsS (SplitChipJ9.pubSPs + 1))
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
  -- the cell validity; CHANGED: + the ALU validity terminal (left), + the primitive pin records `pinRecsP`
  hsumC' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsL AluSZChipJ9.pubALv) (M.pubsL (AluSZChipJ9.pubALv + 1)) +
    ((claimRecsJ9 δ χ c M.m ++ pinRecsJ8 δ Pb.toPubJ8 χ ++ pinRecsP δ Pb χ).map fun r => (FiniteIO.compress (m := 5)
      ⟨Quad.mk _ (χ c4) (χ c6), Quad.mk _ (χ c5) (χ c7)⟩ r)⁻¹).sum =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsC 0) (M.pubsC 1) + Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubMB) (M.pubsA (AtomChipHQ.pubMB + 1))
  -- the atom export
  hbalA' : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA CellHQ.pubHQ) (M.pubsA (CellHQ.pubHQ + 1)) =
    Quad.mk (algebraMap (ZMod p) K δ) (M.pubsA AtomChipHQ.pubC) (M.pubsA (AtomChipHQ.pubC + 1)) +
      Quad.mk (algebraMap (ZMod p) K δ) (M.pubsV WalkHQ.pubXQ) (M.pubsV (WalkHQ.pubXQ + 1))
  hvalA0 : M.pubsA 0 = 0 ∧ M.pubsA 1 = 0
  hfxC : M.pubsC 2 = M.pubsW 0 ∧ M.pubsC 3 = M.pubsW 1
  hfxA : M.pubsA 2 = M.pubsV 0 ∧ M.pubsA 3 = M.pubsV 1
  -- the claim checks
  hclI : ∀ k : Fin 3, (isCellN (claimNoun c k) = true ∨ isBigN p (claimNoun c k) = true) → (M.m k).1 < p
  hclR : ∀ k : Fin 3, isCellN (claimNoun c k) = true → (claimNoun c k).internal / 2 ^ 62 < p
  -- CHANGED: + the primitive formula nouns `censusP`
  hcen' : ∀ x ∈ censusGJ9 Pb.toPubJ8 c ++ censusP Pb, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ Pb.nA + 2
  -- public lengths
  hlenC : 3 + Pb.regs.length + 2 * Pb.nC < p
  hlenA : Pb.nA + Pb.nV < p
  hcellF : isCellN c.formula = true
  -- CHANGED: replaces `hnA62 : Pb.nA ≤ 2 ^ 62`
  hnAS : Pb.nA + Pb.nS < 2 ^ 57
  -- CHANGED: the J-9 A budget
  hbud : BudJ9AL Pb r (g + r.N)
  -- CHANGED: + the axis and split row parameters
  hbudV : Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW ∧ Pb.nX ≤ r.AX ∧ Pb.nS ≤ r.SP
  -- the atom table at the variant chip
  hsatL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).rap.Satisfies
    (qAL δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  hbindL : (atomChipHQL δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) M.pubsA).BindsPreprocessing
    (qAL δ b Pb.toPubJ8 tr.toJ8 (chalsAJ8Z δ χ) M.pubsA)
  -- ADDED: the axis chip, present or absent
  hAXk : AXChipOK δ b Pb.axOn Pb.hnX Pb.nodesX Pb.orbitX (chalsMJ8 δ χ) M.pubsX
    (qAX δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsX)
  -- ADDED: the split chip, present or absent
  hSPk : SPChipOK δ b Pb.nA Pb.spOn Pb.hnS Pb.nodesS Pb.orbitS (chalsMJ8 δ χ) M.pubsS
    (qSP δ b Pb.toPubJ9A tr.toTrJ9A (chalsMJ8 δ χ) M.pubsS)
  -- ADDED: the LogUp counts for `hcount`
  hlenX : Pb.nX + Pb.n < p ∧ 2 * Pb.nS < p
  -- ADDED (AL): the ALU, present or absent
  hALk : ALChipOK δ b Pb.aluOn Pb.prims Pb.hnL Pb.nodesL Pb.orbitL Pb.preL (AluSZChipJ9.chalsALJ8 δ χ) M.pubsL
    (RealIOJ9AL.qAL δ b Pb tr (AluSZChipJ9.chalsALJ8 δ χ) M.pubsL)
  -- ADDED (AL): every primitive id is registered at its `primSpec`
  hPrim : ∀ q ∈ Pb.prims, Rg q.1 = some (Nock.Jet.Prim.primSpec q.2)
  -- ADDED (AL): primitive ids are disjoint from the J-chip registry ids
  hdisjP : ∀ q ∈ Pb.prims, q.1 ∉ Pb.regs
  -- ADDED (AL): the LogUp counts, the ALU row budget, the id / index ranges
  hlenL : Pb.nL + Pb.n < p ∧ Pb.nL ≤ r.AL ∧ ∀ q ∈ Pb.prims, q.1 < p ∧ Pb.idxP q.1 < p
  -- ADDED: the primitive ids are distinct (the twin of `hnd`)
  hndP : (Pb.prims.map Prod.fst).Nodup
  -- ADDED: the public primitive rank is not the atom-root rank (the twin of `hrk`)
  hrkP : ∀ q ∈ Pb.prims, Pb.rkP q.1 ≠ (0, 0)
  -- ADDED: the primitive ranks and indices are field elements (the twin of `hlt`)
  hltP : ∀ q ∈ Pb.prims, (Pb.rkP q.1).1 < ringChar (ZMod p) ∧ (Pb.rkP q.1).2 < ringChar (ZMod p) ∧
    Pb.idxP q.1 < ringChar (ZMod p)
  -- ADDED: the cell validity balance's consumer count (the `hlenC` twin, with the primitive pins and the
  -- ALU validity consumes, at most one per ALU row)
  hlenCP : 3 + Pb.regs.length + Pb.prims.length + Pb.nL + 2 * Pb.nC < p


/-- **`AcceptsJ9AL.of_A`: the ALU-absent receipt.**  An `AcceptsJ9A` at the J-9 A projections, with the ALU absent
(`hALk` in its absent branch, forced by `hoff : Pb.aluOn = false`: `prims = []`, the three ALU terminals `0`) and
the two AL length facts (`hlenL`, `hlenCP`), IS an `AcceptsJ9AL`.  Every field the AL predicate does not change is
a bare projection of `h`; `hGx`, `hGS`, `hsumC'`, `hcen'` are `h`'s with the zero ALU terms and the empty
primitive lists removed; `hbud : BudJ9AL` is derived from `h.hbud : BudJ9A` and `nL ≤ AL` (`hlenL.2.1`). -/
theorem AcceptsJ9AL.of_A {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g : ℕ}
    (h : AcceptsJ9A.AcceptsJ9A δ b Pb.toPubJ9A Rg c χ M.toMsgJ9A' tr.toTrJ9A r.toRowsJ9A g)
    (hALk : ALChipOK δ b Pb.aluOn Pb.prims Pb.hnL Pb.nodesL Pb.orbitL Pb.preL (AluSZChipJ9.chalsALJ8 δ χ) M.pubsL
      (RealIOJ9AL.qAL δ b Pb tr (AluSZChipJ9.chalsALJ8 δ χ) M.pubsL))
    (hoff : Pb.aluOn = false)
    (hlenL : Pb.nL + Pb.n < p ∧ Pb.nL ≤ r.AL ∧ ∀ q ∈ Pb.prims, q.1 < p ∧ Pb.idxP q.1 < p)
    (hlenCP : 3 + Pb.regs.length + Pb.prims.length + Pb.nL + 2 * Pb.nC < p) :
    AcceptsJ9AL δ b Pb Rg c χ M tr r g := by
  have h0 : Pb.prims = [] ∧ M.pubsL AluSZChipJ9.pubALv = 0 ∧ M.pubsL (AluSZChipJ9.pubALv + 1) = 0 ∧
      M.pubsL AluSZChipJ9.pubALs = 0 ∧ M.pubsL (AluSZChipJ9.pubALs + 1) = 0 ∧
      M.pubsL AluSZChipJ9.pubALx = 0 ∧ M.pubsL (AluSZChipJ9.pubALx + 1) = 0 := by
    rcases hALk with ⟨hon, -⟩ | ⟨-, hp, hv1, hv2, hs1, hs2, hx1, hx2⟩
    · exact absurd hon (by simp [hoff])
    · exact ⟨hp, hv1, hv2, hs1, hs2, hx1, hx2⟩
  obtain ⟨hp, hv1, hv2, hs1, hs2, hx1, hx2⟩ := h0
  have zv : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsL AluSZChipJ9.pubALv) (M.pubsL (AluSZChipJ9.pubALv + 1)) = 0 := by
    rw [hv1, hv2, Quad.mk_zero']
  have zs : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsL AluSZChipJ9.pubALs) (M.pubsL (AluSZChipJ9.pubALs + 1)) = 0 := by
    rw [hs1, hs2, Quad.mk_zero']
  have zx : Quad.mk (algebraMap (ZMod p) K δ) (M.pubsL AluSZChipJ9.pubALx) (M.pubsL (AluSZChipJ9.pubALx + 1)) = 0 := by
    rw [hx1, hx2, Quad.mk_zero']
  -- the AL budget from the J-9 A budget and `nL ≤ AL` (`hlenL.2.1`): the ALU rows are charged to `AL`
  have hb := h.hbud
  have hAL := hlenL.2.1
  have hbudL : BudJ9AL Pb r (g + r.N) :=
    { x1 := by have := hb.x1; omega
      x2 := hb.x2
      p1 := hb.p1
      p2 := hb.p2
      s1 := by have := hb.s1; omega
      s2 := by have := hb.s2; omega }
  exact
  { hGx := by rw [zx, add_zero]; exact h.hGx
    hGS := by
      have e : pinRgP (p := p) (K := K) Pb = [] := by rw [pinRgP, hp]; rfl
      have e2 : pinOpP (p := p) (K := K) Pb = [] := by rw [pinOpP, hp]; rfl
      rw [e, e2]
      simp only [List.map_nil, List.sum_nil, add_zero]
      rw [zs, add_zero]
      exact h.hGS
    hsumC' := by rw [zv, zero_add, pinRecsP_nil δ Pb χ hp, List.append_nil]; exact h.hsumC'
    hbud := hbudL
    hcen' := by rw [censusP_nil Pb hp, List.append_nil]; exact h.hcen'
    hndP := by rw [hp]; exact List.nodup_nil
    hrkP := by rw [hp]; intro q hq; exact absurd hq (List.not_mem_nil)
    hltP := by rw [hp]; intro q hq; exact absurd hq (List.not_mem_nil)
    hlenCP := hlenCP
    hALk := hALk
    hPrim := by rw [hp]; intro q hq; exact absurd hq (List.not_mem_nil)
    hdisjP := by rw [hp]; intro q hq; exact absurd hq (List.not_mem_nil)
    hlenL := hlenL
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
    hJk := h.hJk
    hsatA := h.hsatA
    hbindA := h.hbindA
    hinjA := h.hinjA
    hadjA := h.hadjA
    hnpA := h.hnpA
    hVk := h.hVk
    hGp := h.hGp
    hlay := h.hlay
    hsmall := h.hsmall
    huniq := h.huniq
    hTpl := h.hTpl
    hnd := h.hnd
    hidx := h.hidx
    hrk := h.hrk
    hlt := h.hlt
    hbalA' := h.hbalA'
    hvalA0 := h.hvalA0
    hfxC := h.hfxC
    hfxA := h.hfxA
    hclI := h.hclI
    hclR := h.hclR
    hlenC := h.hlenC
    hlenA := h.hlenA
    hcellF := h.hcellF
    hnAS := h.hnAS
    hbudV := h.hbudV
    hsatL := h.hsatL
    hbindL := h.hbindL
    hAXk := h.hAXk
    hSPk := h.hSPk
    hlenX := h.hlenX
  }

/-! ## The cell-side primitive pin -/

/-- The primitive pin records are among the cell validity consumers of `hsumC'`. -/
theorem pinRecsP_mem_consumers (Pb : PubJ9AL p) (χ : Coins frameJ8 K) (c : P8PublicClaim) (m : ClaimMsgVS) :
    ∀ x ∈ pinRecsP δ Pb χ, x ∈ claimRecsJ9 δ χ c m ++ pinRecsJ8 δ Pb.toPubJ8 χ ++ pinRecsP δ Pb χ :=
  fun _ hx => List.mem_append_right _ hx

/-- **`hReg_of_pinP`: the prim twin of `PinJ8.hReg_of_pin` / `CorJ8F.hReg_of_pinR`.**  From the predicate
(`AcceptsJ9AL`: the cell chip `hsatC hbindC hinjC hadjC hnpC`, the public rank `hrkP : rkP id ≠ (0, 0)` and the
ranges `hltP`), the cell validity balance in its consumer form over a list `reqsC` that contains the primitive pin
records `pinRecsP` (the assembly builds it from `hsumC'`: `claimRecsJ9 ++ pinRecsJ8 ++ pinRecsP` plus the ALU validity
consumes), the encoder facts at `E` (agreeing with `encJ8` at the primitive nouns), the atom-root keys `vp`
(`AtomLeaves`) and the census conclusion at each `primC op` (`hinjP`, summand #10, priced through `hcen'`):
**the cell at `idxP id` denotes `primC op`** for every `(id, op) ∈ prims`.  With the J-side pin
`pinRgP` in `hGS` (keyRg `(id, 1, idxP id, 0,0,0,0, 7)`) this is the binding `D (kc, vc) = primC op`. -/
theorem hReg_of_pinP [DecidableEq 𝕂′] [CharP 𝕂′ p] (hq : 2 ^ 63 < p)
    {Pb : PubJ9AL p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
    {M : MsgJ9AL' p K δ} {tr : TrJ9AL (ZMod p)} {r : RowsJ9AL} {g : ℕ}
    (h : AcceptsJ9AL δ b Pb Rg c χ M tr r g)
    -- the cell validity balance, consumer form
    (hzC : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0)
    (γV ρV : 𝕂′) (hokC : ChalsOK δ (chalsMJ8 δ χ) γV ρV 11)
    (reqsC : List (Fin 5 → 𝕂′)) (xsC : List ((Fin 5 → 𝕂′) × 𝕂′))
    (hsumC : (reqsC.map fun r => (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ r)⁻¹).sum =
      Quad.mk _ (M.pubsC 0) (M.pubsC 1) +
        (xsC.map fun x => x.2 * (FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1)⁻¹).sum)
    (houtC : (γV, ρV) ∉ FiniteIO.IOFailureEventW
      (reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
          (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC)))
      (SVFrame.liftWts (cellVRecords δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
          (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC))) ++ xsC))
    (hxneC : ∀ x ∈ xsC, FiniteIO.compress (m := 5) ⟨γV, ρV⟩ x.1 ≠ 0)
    (hcountC : (reqsC ++ cellVInternal δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC))).length < p)
    (vp : List (VKey 𝕂′))
    (hxC : ∀ x ∈ xsC, ∃ k ∈ vp, x.1 = ClaimVS.claimVec δ k.1 (k.2.2.2 : ZMod p) (k.2.1 : ZMod p) (k.2.2.1 : ZMod p))
    (hvp0 : ∀ k ∈ vp, k.2.1 = 0 ∧ k.2.2.1 = 0 ∧ k.2.2.2 < ringChar (ZMod p))
    -- the primitive pin records are consumed
    (hpinCP : ∀ x ∈ pinRecsP δ Pb χ, x ∈ reqsC)
    -- the encoder
    (E : Noun → FP 𝕂′)
    (hconsE : ∀ a b, E (.cell a b) = FP.cons (Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3))
      (E a) (E b))
    (hE : InlineAtoms (ringChar (ZMod p)) (Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3)) E)
    (hEP : ∀ q ∈ Pb.prims, E (Nock.Jet.Prim.primC q.2) = encJ8 δ χ (Nock.Jet.Prim.primC q.2))
    {ext : ℕ → Option Noun} (hvp : AtomLeaves E vp ext)
    -- the census conclusion at the primitive nouns (summand #10, named; priced through `hcen'`)
    (hinjP : ∀ q ∈ Pb.prims, ∀ d ∈ decodedNouns2 ((cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
          (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC))).map (·.b0)) ext,
      E (Nock.Jet.Prim.primC q.2) = E d → Nock.Jet.Prim.primC q.2 = d) :
    ∀ q ∈ Pb.prims,
      denK ((cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
        (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
          (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC))).map (·.b0)) ext (1, Pb.idxP q.1) =
        some (Nock.Jet.Prim.primC q.2) := by
  intro q hqm
  have hrc : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
  have hq' : 2 ^ 63 < ringChar (ZMod p) := by rw [hrc]; exact hq
  have hF' := GeneratedField.primeFieldElems_zmod p
  have hsatC0 := CellTwinKW.cellChipHQKW_restrict_cell_sat δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ h.hsatC
  have hbindC0 := CellTwinKW.cellChipHQKW_restrict_bind δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    _ h.hbindC
  have htabC := TwoProviderQ.cellTable_accepts2 δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC _ hF' hq'
    hzC hsatC0 hbindC0 h.hinjC h.hadjC h.hnpC γV ρV hokC reqsC xsC hsumC houtC hxneC hcountC vp hxC hvp0
  have hvpr : ∀ k ∈ vp, k.2.1 < ringChar (ZMod p) ∧ k.2.2.1 < ringChar (ZMod p) ∧ k.2.2.2 < ringChar (ZMod p) := by
    intro k hk
    obtain ⟨h1, h2, h3⟩ := hvp0 k hk
    exact ⟨by omega, by omega, h3⟩
  -- the one claim key of `q`, as a singleton registry for `regClaims_provided`
  have hpin : ∀ id ∈ [q.1], ClaimVS.claimVec δ ((fun _ => E (Nock.Jet.Prim.primC q.2)) id)
      (((fun _ => Pb.idxP q.1) id : ℕ) : ZMod p) ((((fun _ => Pb.rkP q.1) id).1 : ℕ) : ZMod p)
      ((((fun _ => Pb.rkP q.1) id).2 : ℕ) : ZMod p) ∈ reqsC := by
    intro id _
    apply hpinCP
    rw [hEP q hqm]
    exact List.mem_map.mpr ⟨q, hqm, rfl⟩
  have hlt : ∀ id ∈ [q.1], (((fun _ => Pb.rkP q.1) id).1 < ringChar (ZMod p) ∧
      ((fun _ => Pb.rkP q.1) id).2 < ringChar (ZMod p) ∧ (fun _ => Pb.idxP q.1) id < ringChar (ZMod p)) :=
    fun _ _ => h.hltP q hqm
  have hcl := Nock.Jet.PinJ8.regClaims_provided δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
    (CellTwinKW.restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (qM δ b Pb.toPubJ8 tr.toJ8 (chalsMJ8 δ χ) M.pubsC)) hF' hsatC0 hbindC0 h.hinjC h.hadjC γV ρV hokC
    reqsC xsC hsumC houtC hxneC hcountC vp hxC hvpr (regs := [q.1])
    (Ef := fun _ => E (Nock.Jet.Prim.primC q.2)) (rk := fun _ => Pb.rkP q.1) (idx := fun _ => Pb.idxP q.1)
    hpin hlt q.1 (List.mem_singleton_self _)
  rcases hcl with hc | hv
  · exact claimK_genuine_cell hq' hconsE hE htabC hvp (hinjP q hqm) hc
  · exfalso
    obtain ⟨h1, h2, -⟩ := hvp _ hv
    exact h.hrkP q hqm (Prod.ext h1 h2)

end Accept

end

end Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL
#print axioms AcceptsJ9AL.of_A
#print axioms AcceptsJ9AL
#print axioms hReg_of_pinP
#print axioms pinRecsP_mem_consumers
end Axioms
