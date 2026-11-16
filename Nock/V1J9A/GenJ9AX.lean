/-
  Nock/V1J9A/GenJ9AX.lean

  EXECUTABLE evidence only (no theorem here).

  `genJ9AX` = `genJ9A`'s let-chain with the two read lists swapped (`readsA`, `preadsA`), the cell-handle
  multiplicity `mh` at the twin compute's `.x` consumes (`mhCountsX9E`, the executable twin of `mhCountsX9`, which
  sits in a `noncomputable section`), the twin compute table (`GenCompX9.compGenX9`), the axis chip (`GenAxE`) and the
  split chip (`GenSpE`).  Orbits: `chipOf` picks `ωOf h` (toy `ω6g` at `h ≤ 1`, a real Goldilocks root otherwise).
-/
import Nock.V1J9A.CheckJ9A
import Nock.V1J9A.GenCompX9
import Nock.V1J9A.GenAxE
import Nock.V1J9A.GenSpE
import Nock.V1J9.GenJ9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J9A.GenJ9AX

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Edit Nock.Edit.GenX Nock.Walk Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9 genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads (walkReadsX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axChainReadsK9 axReadsK9 axKeys9 splitVals9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains (idOf9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData (fieldAx9)
open Nock.NockVMROM.Thm54.VclL.Handle.ChipHX9 (slotsX9)
open Nock.V1J9.Gen9 (mbCounts9)
open Nock.V1J9A.CheckJ9A

/-! ## 1. `mhCountsX9E` -/

/-- The twin compute's handle-export consumes at one row environment (`xConsumesX9` at `ZMod P`, executable). -/
def xConsumesX9E (e : Nock.Reified.Env (ZMod P)) : List (ℕ × ℕ) :=
  (slotsX9 (F := ZMod P)).flatMap fun S =>
    (S.ents.filter fun x => decide (x.bal = ChipHX.Bal.x)).filterMap fun x =>
      let a := (x.act.eval e).val
      if a = 0 then none
      else match x.rcd with
        | ChipHX.RE.col i :: _ => some ((e.trace i).val, a)
        | _ => none

/-- **`mhCountsX9E`**: executable twin of `ComplJ9ADataRec.mhCountsX9` (`jrows = []`, so `mhJP` is the identity). -/
def mhCountsX9E (cs : List Noun) (bs : List (ℕ → ZMod P)) (ws : List WRow) : Array ℕ :=
  let a := bs.foldl (fun a b => (xConsumesX9E (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod P))).foldl
    (fun a q => bump a q.1 q.2) a) (Array.replicate cs.length 0)
  ws.foldl (fun a w => match w.node with
    | .cell _ _ => bump a (idxOf cs w.node) 1
    | .atom _ => a) a

/-! ## 2. `genJ9AX` -/

/-- **The J-9 A tracegen.** -/
def genJ9AX (R : Nock.Jet.Registry) (fuel : ℕ) (s f : Noun) (χe : CoinsE) : Option InJ9A :=
  match runX R fuel s f with
  | none => none
  | some Rn =>
    if !(noJets Rn.rows) then none else
    let c : P8PublicClaim := ⟨s, f, Rn.res⟩
    let roots := rootsOf c Rn.rows
    let cs := cellsOfRoots roots
    let acsL := acsOfD (bigsOf roots Rn.rows) ((incOps Rn.rows).any fun x => x.1 + 1 = P)
    let H := hdlB cs acsL
    let pt := ptrE acsL (stopEdges Rn.rows)
    let pd := HonestPairX.pdX (sxE pt)
    let rows9 := rowsOfT9 Rn.t
    let W9 := bfsForest [genX9T Rn.t]
    let fx := fieldAx9 P rows9
    let idOf := idOf9 P acsL.length H fx
    let comp := GenCompX9.compGenX9 c H pd idOf W9 χe
    let (ws, kr) := walkGen (cs.headD (.atom 0)) (walkReadsX9 rows9 ++ axChainReadsK9 rows9)
    let mv := mvCounts cs c
    let mx := mxCounts cs ws
    let mx1 := Array.replicate cs.length 0
    let mh := mhCountsX9E cs comp.bases ws
    let k := coOf χe
    let α := chalsMJ8E χe 0
    let γ := chalsMJ8E χe 1
    let (cR, cP) := cellGenB k (yE χe) H (bigIdOf acsL) cs mv mx mx1 mh
    let (wR, wP) := walkGenRowsB k (yE χe) α γ H (idxN cs) HonestK8.certB8 cs ws kr
    let reads := pairReads H pd Rn.rows ++ axReadsK9 P rows9
    let (vs, krV) := if reads.isEmpty then ([], 0) else walkGen padN reads
    let HA := hdl acsL
    let rIA : Noun → ℕ := fun n => if n = combP then lastIdxOf acsL combP else idxN acsL n
    let (aR, aP) := atomGenE pt χe acsL (infoOfE acsL pt Rn.rows) (mbCounts9 acsL cs c) (wCounts rIA acsL vs)
      (wCounts rIA acsL vs)
    let (vR, vP) : Array (Array (ZMod P)) × (ℕ → K3) := if krV = 0 then (#[Array.replicate 166 0], fun _ => 0)
      else walkGenRowsBE pt (coOfA χe) (yE χe) (chalsAJ8ZE χe 0) (chalsAJ8ZE χe 1) HA rIA WalkJ8.certB acsL vs krV
    let axOn := !(axKeys9 rows9).isEmpty
    let spOn := !fx.isEmpty
    let (xR, xP) := GenAxE.axGenOf χe acsL.length H rows9 axOn
    let (sR, sP) := if spOn then GenSpE.spGenE χe acsL.length (GenSpE.vSE rows9) (GenSpE.mSE rows9 (GenSpE.vSE rows9))
      else (#[Array.replicate 90 0], fun _ => (0 : K3))
    let m := max comp.rows.size (max cR.size (max wR.size (max aR.size (max vR.size (max xR.size sR.size)))))
    let B := max 10 (2 * m)
    some
      { c := c
        M := { m := mOf c H, ρ := comp.ρ, ρS := comp.ρS, pubsC := cP, pubsW := wP,
               pubsJ := fun _ => 0, pubsA := aP, pubsV := vP }
        χ := χe
        r := budget m
        g := 0
        X := chipOf comp.rows
        C := chipOf cR
        W := chipOf wR
        J := ⟨1, 0, Example.ω6g, fun _ => Fin.elim0⟩
        A := chipOf aR
        V := chipOf vR
        kroots := kr
        krootsV := krV
        lay := Fin.elim0
        Rt := Example.RtG
        regs := []
        ids := []
        idx := fun _ => 0
        rk := fun _ => (0, 0)
        AX := chipOf xR
        SP := chipOf sR
        pubsX := xP
        pubsS := sP
        axOn := axOn
        spOn := spOn
        rAX := B
        rSP := B }

/-- **`checkJ9A` with P2's compute check wired in.** -/
def checkJ9AX (I : InJ9A) : Bool :=
  checkJ9A (fun I => CompX9.checkCompX9 (⟨(tabX9A I).nodes, (tabX9A I).ω, (tabX9A I).cols, (tabX9A I).chal, (tabX9A I).pub⟩ : CompX9.TabX9 I.X.n)) I

end Nock.V1J9A.GenJ9AX
