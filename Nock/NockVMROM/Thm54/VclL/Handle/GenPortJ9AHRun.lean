/-
  Nock/NockVMROM/Thm54/VclL/Handle/GenPortJ9AHRun.lean

* `recJ9AX s f χe t r`: `genJ9AX`'s let-chain with the run `Rn` replaced by `⟨t, r, bfsForest [t], rowsOfT t⟩`;
  * `noJets_callsOf`: `noJets (rowsOfT t) = true → callsOf (rowsOfT t) = []`;
  * `noJets_calledIds`: `noJets (rowsOfT t) = true → CalledIds t = ∅`;
  * **`genJ9AX_some`**: `genJ9AX R fuel s f χe = some I → ∃ t r, genX R fuel s f = some (t, r) ∧
    callsOf (rowsOfT t) = [] ∧ CalledIds t = ∅ ∧ I = recJ9AX s f χe t r`;
  * `regOK_genJ9AX`: `RegOK I.toInJ8 Rg` for `I = recJ9AX …` (`regs = []`), and `genJ9AX_some'` bundling it.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9A
import Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8BigBound
import Nock.V1J9A.CheckJ9AIff

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

/-- **The explicit record**: `genJ9AX`'s body over the run `⟨t, r, bfsForest [t], rowsOfT t⟩`. -/
def recJ9AXRn (s f : Noun) (χe : CoinsE) (Rn : RunX) : InJ9A :=
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

/-- **`recJ9AX s f χe t r`**: the record over the run `⟨t, r, bfsForest [t], rowsOfT t⟩`. -/
def recJ9AX (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun) : InJ9A :=
  recJ9AXRn s f χe ⟨t, r, bfsForest [t], ComplJ8Data.rowsOfT t⟩

/-- `genJ9AX` is `recJ9AXRn` on a jet-free run. -/
theorem genJ9AX_eq (R : Nock.Jet.Registry) (fuel : ℕ) (s f : Noun) (χe : CoinsE) :
    genJ9AX R fuel s f χe = (runX R fuel s f).bind fun Rn =>
      if !(noJets Rn.rows) then none else some (recJ9AXRn s f χe Rn) := by
  unfold genJ9AX
  cases runX R fuel s f with
  | none => rfl
  | some Rn => rfl

end Nock.V1J9A.GenJ9AX

namespace Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun

open Nock Nock.Edit Nock.Edit.GenX Nock.Walk Nock.V1J8 Nock.V1J8.Gen Nock.V1J8.Exe Nock.V1J8.Check
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Jet (CalledIds)

/-- `noJets` on the run's rows gives an empty call list. -/
theorem noJets_callsOf {t : NTree SkelX} (h : noJets (ComplJ8Data.rowsOfT t) = true) :
    callsOf (ComplJ8Data.rowsOfT t) = [] := by
  unfold noJets at h
  unfold callsOf
  rw [List.filterMap_eq_nil_iff]
  intro r hr
  have := List.all_eq_true.mp h r hr
  have hne : ¬ r.st = .s11j := by simpa using this
  simp [hne]

/-- `noJets` on the run's rows: no row calls a jet. -/
theorem noJets_calledIds {t : NTree SkelX} (h : noJets (ComplJ8Data.rowsOfT t) = true) :
    CalledIds t = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro id hid
  obtain ⟨u, hu, hst, -⟩ := hid
  have hmem : rowOfSkelX u.label ∈ (ComplJ8Data.rowsOfT t).toList := by
    simp only [ComplJ8Data.rowsOfT, List.toList_toArray, List.mem_map]
    exact ⟨u, (mem_bfsForest [t] u).2 ⟨t, List.mem_singleton_self t, hu⟩, rfl⟩
  unfold noJets at h
  have := List.all_eq_true.mp h _ hmem
  have hne : ¬ (rowOfSkelX u.label).st = .s11j := by simpa using this
  exact hne hst

/-- **`genJ9AX` succeeds only on a jet-free run, and its record is `recJ9AX`.** -/
theorem genJ9AX_some {R : Nock.Jet.Registry} {fuel : ℕ} {s f : Noun} {χe : CoinsE} {I : InJ9A}
    (h : genJ9AX R fuel s f χe = some I) :
    ∃ (t : NTree SkelX) (r : Noun), genX R fuel s f = some (t, r) ∧
      callsOf (ComplJ8Data.rowsOfT t) = [] ∧ CalledIds t = ∅ ∧ I = recJ9AX s f χe t r := by
  rw [genJ9AX_eq] at h
  have hr : runX R fuel s f = (genX R fuel s f).map fun tr =>
      (⟨tr.1, tr.2, bfsForest [tr.1], ComplJ8Data.rowsOfT tr.1⟩ : RunX) := by
    unfold runX; cases genX R fuel s f <;> rfl
  rw [hr] at h
  cases hg : genX R fuel s f with
  | none => rw [hg] at h; simp at h
  | some tr =>
    obtain ⟨t, r⟩ := tr
    rw [hg] at h
    simp only [Option.map_some, Option.bind_some] at h
    by_cases hnj : noJets (ComplJ8Data.rowsOfT t) = true
    · have hnj' : (!noJets (ComplJ8Data.rowsOfT t)) = false := by rw [hnj]; rfl
      refine ⟨t, r, rfl, noJets_callsOf hnj, noJets_calledIds hnj, ?_⟩
      simp only [hnj'] at h
      have h' := Option.some.inj h
      exact h'.symm
    · exfalso
      have hnj' : (!noJets (ComplJ8Data.rowsOfT t)) = true := by simpa using hnj
      simp only [hnj'] at h
      simp at h

/-- **The registry premise is vacuous** (`regs = []`). -/
theorem regOK_recJ9AX (s f : Noun) (χe : CoinsE) (t : NTree SkelX) (r : Noun) (Rg : Nock.Jet.Registry) :
    RegOK (recJ9AX s f χe t r).toInJ8 Rg := by
  intro i hi
  exact absurd hi (by simp [recJ9AX, recJ9AXRn])

/-- **G1, bundled**: `genJ9AX_some` plus `RegOK`. -/
theorem genJ9AX_some' {R : Nock.Jet.Registry} {fuel : ℕ} {s f : Noun} {χe : CoinsE} {I : InJ9A}
    (h : genJ9AX R fuel s f χe = some I) :
    (∃ (t : NTree SkelX) (r : Noun), genX R fuel s f = some (t, r) ∧
      callsOf (ComplJ8Data.rowsOfT t) = [] ∧ CalledIds t = ∅ ∧ I = recJ9AX s f χe t r) ∧
    RegOK I.toInJ8 R := by
  refine ⟨genJ9AX_some h, ?_⟩
  obtain ⟨t, r, -, -, -, rfl⟩ := genJ9AX_some h
  exact regOK_recJ9AX s f χe t r R

end Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun.noJets_callsOf
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun.noJets_calledIds
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun.genJ9AX_some
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun.regOK_recJ9AX
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.GenPortJ9AHRun.genJ9AX_some'
