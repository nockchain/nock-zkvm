/-
  Nock/V1J9AL/CheckJ9AL.lean

  **`InJ9AL` and the native nine-table checker `checkJ9AL`** (twin of `V1J9A/CheckJ9A.lean`).
  The finite link `checkJ9AL_iff` is in `CheckJ9ALIff.lean`.

  * `InJ9AL` = `InJ9A` + the ALU chip `AL` (196 columns), `pubsL`, the presence flag `aluOn`, the primitive table
    `prims`, the registry index `idxP`, the public ranks `rkP` and the row parameter `rAL`.
  * `checkStaticJ9AL` = `checkStaticJ9A` with the three conjuncts the AL record changes (`hcen'` + `censusP`,
    `BudJ9A → BudJ9AL`) and the added `hlenL hndP hrkP hltP hlenCP hdisjP`.
  * `checkPubJ9ALE` = `checkPubJ9AE` with `hGx`, `hGS`, `hsumC'` as in `AcceptsJ9AL` (ALU terminals `pubALx`, `pubALs`,
    `pubALv`; primitive pins `pinRgPE`, `pinOpPE`, `pinRecsPE`).
  * `alOK` = `ALChipOK` decided: `checkM` at `aluTemplateSZ` with the five fixed columns (masks + the `preg` layout).
  * `chipsBJ9AL` = `chipsBJ9A` + `alOK`.
-/
import Nock.V1J9A.CheckJ9A
import Nock.V1J9A.CompX9
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9AL

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J9AL.CheckJ9AL

open Nock Nock.Reified Nock.Framework Nock.TraceGenExe Nock.Field Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.Jet.ChipJ8 (entsX ents0T ents1T ents2T ents3)
open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8
open Nock.Atoms (lenL)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8PP
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V
open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9V
open Nock.Jet.ChipJ8 (jetChipJ8 PRow layoutJ8 tvKey axPosB)
open Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.V1J8.MemX (TabM checkM prep2)
open Nock.V1J9 Nock.V1J9.Exe9 Nock.V1J9.Check9
open Nock.V1J9A.CheckJ9A
open Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9AL (primCode)
open Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9 (pubALv pubALs pubALx tagRgP tagOp)
open Nock.Jet.Prim (PrimOp primC)

/-! ## 1. The input -/

/-- **The J-9 AL checker's input**: `InJ9A` + the ALU chip and its public data. -/
structure InJ9AL extends InJ9A where
  AL : ChipIn
  pubsL : ℕ → K3
  aluOn : Bool
  prims : List (ℕ × PrimOp)
  idxP : ℕ → ℕ
  rkP : ℕ → ℕ × ℕ
  rAL : ℕ

/-! ## 2. The ALU's fixed columns and challenge vector, executably -/

/-- The `preg` layout column `k` (`0 = sP`, `1 = pId`, `2 = pOp`) at row `i` (`PregOK`). -/
def pregCol (prims : List (ℕ × PrimOp)) (k : ℕ) (i : ℕ) : ZMod p :=
  if k = 0 then (if i < prims.length then 1 else 0)
  else if k = 1 then (prims.map fun q => ((q.1 : ℕ) : ZMod p)).getD i 0
  else (prims.map fun q => ((primCode q.2 : ℕ) : ZMod p)).getD i 0

/-- The five fixed columns of the ALU chip: masks at `0, 1`; `sP, pId, pOp` at `2, 3, 4`. -/
def prepAL (n : ℕ) (prims : List (ℕ × PrimOp)) : List (ℕ × (Fin n → ZMod p)) :=
  [(0, Nock.V1J8.CompX.firstMaskE n), (1, Nock.V1J8.CompX.lastMaskE n),
    (2, fun i => pregCol prims 0 i), (3, fun i => pregCol prims 1 i), (4, fun i => pregCol prims 2 i)]

/-- **The ALU's challenge vector, executable** (`AluSZChipJ9.chalsALJ8`: powers `y^t` of the limb coin at leaves
`40 + 2t / 41 + 2t`). -/
def chalsALJ8E (χe : CoinsE) (j : ℕ) : K3 :=
  if 40 ≤ j ∧ j < 106 then
    (if j % 2 = 0 then (powE (yE χe) ((j - 40) / 2)).re else (powE (yE χe) ((j - 40) / 2)).im)
  else chalsAJ8ZE χe j

/-! ## 3. The table -/

def tabAL (I : InJ9AL) : TabM I.AL.n :=
  ⟨nodesOf I.AL, I.AL.ω.toZ, I.AL.cols, chalsALJ8E I.χ, I.pubsL, prepAL I.AL.n I.prims⟩

/-! ## 4. The static block -/

/-- The primitive formula nouns (`censusP`). -/
def censusPL (prims : List (ℕ × PrimOp)) : List Noun := prims.map fun q => primC q.2

/-- `BudJ9AL` as a `Bool` (at `g + N`). -/
def budJ9ALB (Pb : PubJ8 p) (r : RowsJ8) (g nX nS nL rAX rSP rAL : ℕ) : Bool :=
  decide (3 * Pb.n + Pb.nW + Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount entsX Pb.lay + nL ≤
    3 * r.N + r.W + r.rd + rAL) &&
  decide (Pb.nC ≤ r.D) && decide (Pb.n + nX ≤ r.N) && decide (Pb.nW ≤ r.W) &&
  decide (2 * Pb.n + Pb.regs.length + (Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount ents0T Pb.lay +
      Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount ents1T Pb.lay) + nX + 2 * nL ≤
    (r.N + 2 * r.J + (g + r.N)) + rAX + 2 * rAL) &&
  decide (Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount ents2T Pb.lay +
      Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount ents3 Pb.lay + Pb.nA + 2 * Pb.nV + nX + 2 * nS + 2 * nL ≤
    r.calls + r.heads + r.blocks + r.J + rAX + 2 * rSP + 2 * rAL)

/-- **The J-9 AL static check** (`checkStaticJ9A` with `hcen'`, `BudJ9AL` changed; `+ hlenL hndP hrkP hltP hlenCP
hdisjP`). -/
def checkStaticJ9AL (Pb : PubJ8 p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ8)
    (g nX nS rAX rSP nL rAL : ℕ) (prims : List (ℕ × PrimOp)) (idxP : ℕ → ℕ) (rkP : ℕ → ℕ × ℕ) : Bool :=
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
  decide (∀ x ∈ censusGJ9 Pb c ++ censusPL prims, x.leaves ≤ fuelChip ∧ ∀ v ∈ x.leafList, lenL v ≤ Pb.nA + 2) &&
  decide (3 + Pb.regs.length + 2 * Pb.nC < p) &&
  decide (Pb.nA + Pb.nV < p) &&
  isCellN c.formula &&
  decide (Pb.nA + nS < 2 ^ 57) &&
  budJ9ALB Pb r g nX nS nL rAX rSP rAL &&
  decide (Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW ∧ nX ≤ rAX ∧ nS ≤ rSP) &&
  decide (nX + Pb.n < p ∧ 2 * nS < p) &&
  decide (nL + Pb.n < p ∧ nL ≤ rAL ∧ ∀ q ∈ prims, q.1 < p ∧ idxP q.1 < p) &&
  decide (prims.map Prod.fst).Nodup &&
  decide (∀ q ∈ prims, rkP q.1 ≠ (0, 0)) &&
  decide (∀ q ∈ prims, (rkP q.1).1 < p ∧ (rkP q.1).2 < p ∧ idxP q.1 < p) &&
  decide (3 + Pb.regs.length + prims.length + nL + 2 * Pb.nC < p) &&
  decide (∀ q ∈ prims, q.1 ∉ Pb.regs)

/-! ## 5. The primitive pins, executably -/

/-- The ALU keyRg pin vector `(id, 1, idx, 0, 0, 0, 0, 7)` as a `K6` vector. -/
def pinRgVecE (id idx : ℕ) : Fin 8 → K6 := fun c =>
  g6 (Gold.ofZ (([((id : ℕ) : ZMod p), 1, ((idx : ℕ) : ZMod p), 0, 0, 0, 0, ((tagRgP : ℕ) : ZMod p)] :
    List (ZMod p)).getD c 0))

/-- The op record pin `(id, code, 0, 0, 0, 0, 0, 6)` as a `K6` vector. -/
def pinOpVecE (id code : ℕ) : Fin 8 → K6 := fun c =>
  g6 (Gold.ofZ (([((id : ℕ) : ZMod p), ((code : ℕ) : ZMod p), 0, 0, 0, 0, 0, ((tagOp : ℕ) : ZMod p)] :
    List (ZMod p)).getD c 0))

def pinRgPE (prims : List (ℕ × PrimOp)) (idxP : ℕ → ℕ) : List (Fin 8 → K6) :=
  prims.map fun q => pinRgVecE q.1 (idxP q.1)

def pinOpPE (prims : List (ℕ × PrimOp)) : List (Fin 8 → K6) :=
  prims.map fun q => pinOpVecE q.1 (primCode q.2)

/-- **The executable primitive pin records** (`pinRecsP`). -/
def pinRecsPE (prims : List (ℕ × PrimOp)) (idxP : ℕ → ℕ) (rkP : ℕ → ℕ × ℕ) (χe : CoinsE) : List (Fin 5 → K6) :=
  prims.map fun q => claimVecE (encE (zE χe) (yE χe) (primC q.2)) (natG (idxP q.1)) (natG (rkP q.1).1)
    (natG (rkP q.1).2)

/-! ## 6. The public equations -/

/-- **`checkPubJ9ALE`** = `checkPubJ9AE` with `hGx`, `hGS`, `hsumC'` as `AcceptsJ9AL`. -/
def checkPubJ9ALE (Pb : PubJ8 p) (prims : List (ℕ × PrimOp)) (idxP : ℕ → ℕ) (rkP : ℕ → ℕ × ℕ)
    (c : P8PublicClaim) (χe : CoinsE) (M : MsgE) (pubsX pubsS pubsL : ℕ → K3) : Bool :=
  eq6 (M.ρ 3 + (pp M.pubsW WalkHQ.pubXQ + pp M.pubsJ 2 + pp pubsL pubALx)) (pp M.pubsC CellHQ.pubHQ) &&
  eq6 (M.ρ 4 + pp pubsX Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXp) (pp M.pubsW WalkHQ.pubPQ) &&
  eq6 (M.ρS + lsum ((pinConsE Pb.regs Pb.idx).map fun r => (compressE (γHE χe) (ρHE χe) r)⁻¹) +
      lsum ((pinRgPE prims idxP).map fun r => (compressE (γHE χe) (ρHE χe) r)⁻¹) +
      lsum ((pinOpPE prims).map fun r => (compressE (γHE χe) (ρHE χe) r)⁻¹) + pp M.pubsJ 0 +
      pp pubsX Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9.pubAXs + pp pubsL pubALs)
    (pp M.pubsA AtomChipHQ.pubMI + pp M.pubsV WalkHQ.pubPQ + pp pubsS Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9.pubSPs) &&
  eq6 (pp pubsL pubALv + lsum ((claimRecsJ9E χe c M.m ++ pinRecsJ8E Pb χe ++ pinRecsPE prims idxP rkP χe).map
      fun r => (compressE (γVE χe) (ρVE χe) r)⁻¹))
    (pp M.pubsC 0 + pp M.pubsA AtomChipHQ.pubMB) &&
  eq6 (pp M.pubsA CellHQ.pubHQ) (pp M.pubsA AtomChipHQ.pubC + pp M.pubsV WalkHQ.pubXQ) &&
  (eq3 (M.pubsA 0) 0 && eq3 (M.pubsA 1) 0) &&
  (eq3 (M.pubsC 2) (M.pubsW 0) && eq3 (M.pubsC 3) (M.pubsW 1)) &&
  (eq3 (M.pubsA 2) (M.pubsV 0) && eq3 (M.pubsA 3) (M.pubsV 1))

/-! ## 7. The chips -/

/-- **The ALU, present or absent** (`ALChipOK`): present = `aluOn`, the template check, injective / adjacent nodes,
`nL < p`, `prims.length ≤ nL` (the `preg` layout is the prep columns, by construction); absent = `¬aluOn`,
`prims = []` and the six ALU publics `0`. -/
def alOK (I : InJ9AL) : Bool :=
  (I.aluOn && decide (0 < I.AL.n) && orbB I.AL &&
    checkM (Nock.NockVMROM.Thm54.VclL.Handle.AluSZChipJ9.aluTemplateSZ (F := ZMod p) deltaF) (tabAL I) &&
    Nock.V1J8.MemX.nodupB (tabAL I) && Nock.V1J8.MemX.adjB (tabAL I) && decide (I.AL.n < p) &&
    decide (I.prims.length ≤ I.AL.n)) ||
  (!I.aluOn && decide (I.prims = []) && eq3 (I.pubsL pubALv) 0 && eq3 (I.pubsL (pubALv + 1)) 0 &&
    eq3 (I.pubsL pubALs) 0 && eq3 (I.pubsL (pubALs + 1)) 0 &&
    eq3 (I.pubsL pubALx) 0 && eq3 (I.pubsL (pubALx + 1)) 0)

/-- **The nine chip checks**: the eight of `chipsBJ9A`, then the ALU. -/
def chipsBJ9AL (compOK : InJ9A → Bool) (I : InJ9AL) : Bool :=
  chipsBJ9A compOK I.toInJ9A && alOK I

/-- The ALU's shape (needed even when the chip is absent: `PubJ9AL` has fields for it). -/
def validALB (I : InJ9AL) : Bool := decide (0 < I.AL.n) && orbB I.AL

/-- **The executable J-9 AL checker** (compute check a parameter, as `checkJ9A`). -/
def checkJ9AL (compOK : InJ9A → Bool) (I : InJ9AL) : Bool :=
  if hv : validB I.toInJ8 = true then
    validAXSPB I.toInJ9A && validALB I &&
    checkStaticJ9AL (mkPb I.toInJ8 ((validB_iff I.toInJ8).mp hv)) I.c I.M.m I.r I.g I.AX.n I.SP.n I.rAX I.rSP
      I.AL.n I.rAL I.prims I.idxP I.rkP &&
    checkPubJ9ALE (mkPb I.toInJ8 ((validB_iff I.toInJ8).mp hv)) I.prims I.idxP I.rkP I.c I.χ I.M I.pubsX I.pubsS
      I.pubsL &&
    chipsBJ9AL compOK I
  else false

/-- **`checkJ9AL` with the twin compute check wired in** (as `GenJ9AX.checkJ9AX`). -/
def checkJ9ALX (I : InJ9AL) : Bool :=
  checkJ9AL (fun I => Nock.V1J9A.CompX9.checkCompX9
    (⟨(tabX9A I).nodes, (tabX9A I).ω, (tabX9A I).cols, (tabX9A I).chal, (tabX9A I).pub⟩ :
      Nock.V1J9A.CompX9.TabX9 I.X.n)) I

end Nock.V1J9AL.CheckJ9AL
