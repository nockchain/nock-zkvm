/-
  Nock/V1J9A/CheckJ9A.lean

  Nothing here is a kernel theorem (`checkJ9A_iff` is a later link piece, L5).

  * `InJ9A` = `InJ8` (compute = the TWIN chip, 137 cols RAP order; C W J A V as J-8) + axis chip `AX` (52 cols),
    split chip `SP` (90 cols), `pubsX`, `pubsS`, the presence flags `axOn spOn`, the row parameters `rAX rSP`.
  * `checkStaticJ9A` = `checkStaticJ9` with the three conjuncts the J-9 A record changes (`hnA62 → hnAS`,
    `BudJ8 → BudJ9A`, `hbudV` + `nX ≤ AX ∧ nS ≤ SP`) plus `hlenX`.
  * `checkPubJ9AE` = `checkPubJ9E` with `hGp`, `hGS` as `AcceptsJ9A`.
  * `chipsBJ9A` = compute check (a PARAMETER `compOK`: P2's `checkCompX9` is on another branch, P7's merge wires it)
    + the six memory checks of `chipsB9` + `axOK` + `spOK` (`MemX.checkM` at the axis / split templates).
-/
import Nock.V1J9.CheckJ9
import Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.V1J9A.CheckJ9A

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
open Nock.V1J8.MemX (TabM checkM checkCellKW checkWalkJ8 checkJOK checkAtomHQ checkAtomHQL checkAWOK prep2)
open Nock.V1J9 Nock.V1J9.Exe9 Nock.V1J9.Check9
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (axisTemplateJ9 pubAXs pubAXp)
open Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9 (splitTemplateJ9 pubSPs)

/-! ## 1. The input -/

/-- **The J-9 A checker's input**: `InJ8` (compute = the twin chip) + the axis and split chips. -/
structure InJ9A extends InJ8 where
  AX : ChipIn
  SP : ChipIn
  pubsX : ℕ → K3
  pubsS : ℕ → K3
  axOn : Bool
  spOn : Bool
  rAX : ℕ
  rSP : ℕ

/-! ## 2. The tables -/

def tabAX (I : InJ9A) : TabM I.AX.n :=
  ⟨nodesOf I.AX, I.AX.ω.toZ, I.AX.cols, chalsMJ8E I.χ, I.pubsX, prep2 I.AX.n⟩

def tabSP (I : InJ9A) : TabM I.SP.n :=
  ⟨nodesOf I.SP, I.SP.ω.toZ, I.SP.cols, chalsMJ8E I.χ, I.pubsS, prep2 I.SP.n⟩

/-- The twin compute table (137 columns, RAP order) at the J-9 publics — the same shape as `tabX9`; the compute
check itself is wired by P7 (`CompX9.checkCompX9`, another branch). -/
def tabX9A (I : InJ9A) : Nock.V1J8.CompX.TabX I.X.n := tabX9 I.toInJ8

/-! ## 3. The static block -/

/-- `BudJ9A` as a `Bool` (the `Bud` structure of `RealIOJ9A`, at `g + N`). -/
def budJ9AB (Pb : PubJ8 p) (r : RowsJ8) (g nX nS rAX rSP : ℕ) : Bool :=
  decide (3 * Pb.n + Pb.nW + Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount entsX Pb.lay ≤
    3 * r.N + r.W + r.rd) &&
  decide (Pb.nC ≤ r.D) && decide (Pb.n + nX ≤ r.N) && decide (Pb.nW ≤ r.W) &&
  decide (2 * Pb.n + Pb.regs.length + (Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount ents0T Pb.lay +
      Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount ents1T Pb.lay) + nX ≤
    (r.N + 2 * r.J + (g + r.N)) + rAX) &&
  decide (Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount ents2T Pb.lay +
      Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ8.jCount ents3 Pb.lay + Pb.nA + 2 * Pb.nV + nX + 2 * nS ≤
    r.calls + r.heads + r.blocks + r.J + rAX + 2 * rSP)

/-- **The J-9 A static check** (`checkStaticJ9` with `hnA62 → hnAS`, `BudJ8 → BudJ9A`, `hbudV` extended, `+ hlenX`). -/
def checkStaticJ9A (Pb : PubJ8 p) (c : P8PublicClaim) (m : ClaimMsgVS) (r : RowsJ8) (g nX nS rAX rSP : ℕ) : Bool :=
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
  decide (Pb.nA + nS < 2 ^ 57) &&
  budJ9AB Pb r g nX nS rAX rSP &&
  decide (Pb.regs.length ≤ g ∧ Pb.nA ≤ r.mb ∧ Pb.nA ≤ r.A ∧ Pb.nV ≤ r.AW ∧ nX ≤ rAX ∧ nS ≤ rSP) &&
  decide (nX + Pb.n < p ∧ 2 * nS < p)

/-! ## 4. The public equations -/

/-- **`checkPubJ9AE`** = `checkPubJ9E` with `hGp`, `hGS` as `AcceptsJ9A` (`+ pubsX pubAXp` left of `hGp`;
`+ pubsX pubAXs` left and `+ pubsS pubSPs` right of `hGS`). -/
def checkPubJ9AE (Pb : PubJ8 p) (c : P8PublicClaim) (χe : CoinsE) (M : MsgE) (pubsX pubsS : ℕ → K3) : Bool :=
  eq6 (M.ρ 3 + (pp M.pubsW WalkHQ.pubXQ + pp M.pubsJ 2)) (pp M.pubsC CellHQ.pubHQ) &&
  eq6 (M.ρ 4 + pp pubsX pubAXp) (pp M.pubsW WalkHQ.pubPQ) &&
  eq6 (M.ρS + lsum ((pinConsE Pb.regs Pb.idx).map fun r => (compressE (γHE χe) (ρHE χe) r)⁻¹) + pp M.pubsJ 0 +
      pp pubsX pubAXs)
    (pp M.pubsA AtomChipHQ.pubMI + pp M.pubsV WalkHQ.pubPQ + pp pubsS pubSPs) &&
  eq6 (lsum ((claimRecsJ9E χe c M.m ++ pinRecsJ8E Pb χe).map fun r => (compressE (γVE χe) (ρVE χe) r)⁻¹))
    (pp M.pubsC 0 + pp M.pubsA AtomChipHQ.pubMB) &&
  eq6 (pp M.pubsA CellHQ.pubHQ) (pp M.pubsA AtomChipHQ.pubC + pp M.pubsV WalkHQ.pubXQ) &&
  (eq3 (M.pubsA 0) 0 && eq3 (M.pubsA 1) 0) &&
  (eq3 (M.pubsC 2) (M.pubsW 0) && eq3 (M.pubsC 3) (M.pubsW 1)) &&
  (eq3 (M.pubsA 2) (M.pubsV 0) && eq3 (M.pubsA 3) (M.pubsV 1))

/-! ## 5. The chips -/

/-- **The axis chip, present or absent** (`AXChipOK`): present = `axOn`, the template check, injective / adjacent
nodes, `nX < p`; absent = `¬axOn` and the four axis publics `0`. -/
def axOK (I : InJ9A) : Bool :=
  (I.axOn && decide (0 < I.AX.n) && orbB I.AX &&
    checkM (axisTemplateJ9 (F := ZMod p) deltaF) (tabAX I) &&
    Nock.V1J8.MemX.nodupB (tabAX I) && Nock.V1J8.MemX.adjB (tabAX I) && decide (I.AX.n < p)) ||
  (!I.axOn && eq3 (I.pubsX pubAXs) 0 && eq3 (I.pubsX (pubAXs + 1)) 0 &&
    eq3 (I.pubsX pubAXp) 0 && eq3 (I.pubsX (pubAXp + 1)) 0)

/-- **The split chip, present or absent** (`SPChipOK`), template at `nA = I.A.n` (the atom rows). -/
def spOK (I : InJ9A) : Bool :=
  (I.spOn && decide (0 < I.SP.n) && orbB I.SP &&
    checkM (splitTemplateJ9 (F := ZMod p) deltaF I.A.n) (tabSP I) &&
    Nock.V1J8.MemX.nodupB (tabSP I) && Nock.V1J8.MemX.adjB (tabSP I) && decide (I.SP.n < p)) ||
  (!I.spOn && eq3 (I.pubsS pubSPs) 0 && eq3 (I.pubsS (pubSPs + 1)) 0)

/-- **The eight chip checks**: the compute check is the PARAMETER `compOK` (P2's `checkCompX9`, wired by P7),
then the six memory checks of `chipsB9`, then axis and split. -/
def chipsBJ9A (compOK : InJ9A → Bool) (I : InJ9A) : Bool :=
  compOK I && checkCellKW (tabC I.toInJ8) && checkWalkJ8 I.kroots (tabW I.toInJ8) && checkJOK (tabJ I.toInJ8) &&
  checkAtomHQ (tabA I.toInJ8) && checkAWOK I.krootsV (tabV I.toInJ8) && checkAtomHQL (tabA I.toInJ8) &&
  axOK I && spOK I

/-- The Boolean validity of the axis and split chips' shape (needed even when a chip is absent, because `PubJ9A`
has fields for them). -/
def validAXSPB (I : InJ9A) : Bool :=
  decide (0 < I.AX.n) && orbB I.AX && decide (0 < I.SP.n) && orbB I.SP

theorem validAXSPB_iff (I : InJ9A) :
    validAXSPB I = true ↔ (0 < I.AX.n ∧ OrbOK I.AX ∧ 0 < I.SP.n ∧ OrbOK I.SP) := by
  simp only [validAXSPB, Bool.and_eq_true, decide_eq_true_eq, orbB_iff, and_assoc]

/-- **The executable J-9 A checker**: validity (incl. the axis / split shape, always), the static block, the
public equations, the eight chips. -/
def checkJ9A (compOK : InJ9A → Bool) (I : InJ9A) : Bool :=
  if hv : validB I.toInJ8 = true then
    validAXSPB I &&
    checkStaticJ9A (mkPb I.toInJ8 ((validB_iff I.toInJ8).mp hv)) I.c I.M.m I.r I.g I.AX.n I.SP.n I.rAX I.rSP &&
    checkPubJ9AE (mkPb I.toInJ8 ((validB_iff I.toInJ8).mp hv)) I.c I.χ I.M I.pubsX I.pubsS &&
    chipsBJ9A compOK I
  else false

end Nock.V1J9A.CheckJ9A
