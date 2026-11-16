/-
  Nock/V1J9AL/GenJ9ALXJ.lean

  **`genJ9ALXJ` — the executable J-9 AL tracegen** (twin of `V1J9A/GenJ9AXJ.lean`). EXECUTABLE evidence only.  `genJ9AXJ`'s let-chain with the ALU split of
  `ComplJ9ALData.j9alDataOf`:
  * the calls are split by id (`jCallsP` / `aCallsP`); the J chip, `regs`, `ids`, `lay`, `jrows` are over the J calls;
  * the root nouns `jn` are built over ALL calls, exactly as `genJ9AXJ` (callers pass `Rt := rtP Rt0 prims`; the `primC`
    nouns are cells of the record by `primC_mem_cells`, so no append);
  * `mv` gains the primitive claim pins (`primPinL`), `mh` the ALU's hdr export reads (`aluXL`), the atom table's `mb`
    the ALU's validity reads (`aluBL`);
  * the ALU chip is `GenAluE.aluGenE` over the primitive calls `pcallsR`; absent (no primitive call) it is
    `GenAluE.zeroChip`, `aluOn = false`, `prims = []`.
-/
import Nock.V1J9AL.CheckJ9AL
import Nock.V1J9AL.GenAluE
import Nock.V1J9A.GenJ9AXJ
import Nock.V1J9A.GenCompX9
import Nock.V1J9A.GenAxE
import Nock.V1J9A.GenSpE

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J9AL.GenJ9ALXJ

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Edit Nock.Edit.GenX Nock.Walk Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9 genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads (walkReadsX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axChainReadsK9 axReadsK9 axKeys9 splitVals9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains (idOf9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData (fieldAx9)
open Nock.V1J9.Gen9 (mbCounts9)
open Nock.V1J9A.CheckJ9A
open Nock.V1J9A.GenJ9AX (mhCountsX9E)
open Nock.Jet.ChipJ8 (layoutJ8)
open Nock.Jet.Autogen (compile)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (jNounsP mvFixP pinsOfP hJd mhJP bumpAll)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (jCallsP aCallsP pcallsR primsC idxPOf rkPOf aluXL aluBL primPinL)
open Nock.V1J9AL.CheckJ9AL
open Nock.V1J9A
open Nock.Jet.Prim (PrimOp primC)

/-- **The J-9 AL tracegen.**  `prims` is the primitive table `(id, op)` (registered ids; only the called ones enter
the chip). -/
def genJ9ALXJ (R : Nock.Jet.Registry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) (prims : List (ℕ × PrimOp)) (fuel : ℕ)
    (s f : Noun) (χe : CoinsE) : Option InJ9AL :=
  match runX R fuel s f with
  | none => none
  | some Rn =>
    let c : P8PublicClaim := ⟨s, f, Rn.res⟩
    let pids := prims.map Prod.fst
    let calls := callsOf Rn.rows
    let allIds := calls.map Prod.fst
    let callsJ := jCallsP pids calls
    let ids := callsJ.map Prod.fst
    let regs := ids.dedup
    let psC := primsC prims allIds
    let pc := pcallsR pids Rn.rows
    let jn := jNounsP P Rt allIds.dedup calls
    let roots := rootsOf c Rn.rows ++ jn
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
    let idx : ℕ → ℕ := fun id => idxOf cs (compile P (Rt id))
    let layL := layoutJ8 Rt regs ids
    let jrows := mvFixP P (Nock.Jet.ChipJ8.honestJ8G (hJd P cs acsL) Rt regs callsJ) (pinsOfP P regs idx)
    let jg := jGen χe jrows
    let mv := bumpAll (mvPins (mvCounts cs c) regs idx) (primPinL cs prims allIds)
    let mx := mxCounts cs ws
    let mx1 := Array.replicate cs.length 0
    let mh := bumpAll (mhJP P (mhCountsX9E cs comp.bases ws) jrows) (aluXL cs pc)
    let k := coOf χe
    let α := chalsMJ8E χe 0
    let γ := chalsMJ8E χe 1
    let (cR, cP) := cellGenB k (yE χe) H (bigIdOf acsL) cs mv mx mx1 mh
    let (wR, wP) := walkGenRowsB k (yE χe) α γ H (idxN cs) HonestK8.certB8 cs ws kr
    let reads := pairReads H pd Rn.rows ++ axReadsK9 P rows9
    let (vs, krV) := if reads.isEmpty then ([], 0) else walkGen padN reads
    let HA := Nock.V1J8.Gen.hdl acsL
    let rIA : Noun → ℕ := fun n => if n = combP then lastIdxOf acsL combP else idxN acsL n
    let (aR, aP) := atomGenE pt χe acsL (infoOfE acsL pt Rn.rows)
      (bumpAll (mbCounts9 acsL cs c) (aluBL P acsL pc)) (wCounts rIA acsL vs) (wCounts rIA acsL vs)
    let (vR, vP) : Array (Array (ZMod P)) × (ℕ → K3) := if krV = 0 then (#[Array.replicate 166 0], fun _ => 0)
      else walkGenRowsBE pt (coOfA χe) (yE χe) (chalsAJ8ZE χe 0) (chalsAJ8ZE χe 1) HA rIA WalkJ8.certB acsL vs krV
    let axOn := !(axKeys9 rows9).isEmpty
    let spOn := !fx.isEmpty
    let (xR, xP) := GenAxE.axGenOf χe acsL.length H rows9 axOn
    let (sR, sP) := if spOn then GenSpE.spGenE χe acsL.length (GenSpE.vSE rows9) (GenSpE.mSE rows9 (GenSpE.vSE rows9))
      else (#[Array.replicate 90 0], fun _ => (0 : K3))
    let aluOn := !pc.isEmpty
    let (lR, lP) := if aluOn then GenAluE.aluGenE χe cs H psC allIds pc else GenAluE.zeroChip
    let m := max comp.rows.size (max cR.size (max wR.size (max aR.size (max vR.size (max xR.size
      (max sR.size (max layL.length lR.size)))))))
    let B := max 10 (2 * m)
    some
      { c := c
        M := { m := mOf c H, ρ := comp.ρ, ρS := comp.ρS, pubsC := cP, pubsW := wP,
               pubsJ := jg.2, pubsA := aP, pubsV := vP }
        χ := χe
        r := budget m
        g := regs.length
        X := chipOf comp.rows
        C := chipOf cR
        W := chipOf wR
        J := ⟨hOf layL.length, layL.length, ωOf (hOf layL.length), colsOf jg.1 layL.length⟩
        A := chipOf aR
        V := chipOf vR
        kroots := kr
        krootsV := krV
        lay := layL.get
        Rt := Rt
        regs := regs
        ids := ids
        idx := idx
        rk := fun id => Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P.rkC (compile P (Rt id))
        AX := chipOf xR
        SP := chipOf sR
        pubsX := xP
        pubsS := sP
        axOn := axOn
        spOn := spOn
        rAX := B
        rSP := B
        AL := chipOf lR
        pubsL := lP
        aluOn := aluOn
        prims := if aluOn then psC else []
        idxP := idxPOf cs prims
        rkP := rkPOf prims
        rAL := B }

end Nock.V1J9AL.GenJ9ALXJ
