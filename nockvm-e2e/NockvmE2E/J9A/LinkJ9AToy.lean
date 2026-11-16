/-
J9A-LINK: the setup at the executed toy.
  1. `withOrb`, `validJ9A_withOrb` (our local twin of the `withOrb` nockvm's F1 `genJ9AX_honest_at` will use).
  2. `recSp` (the spelled generator record), `genJ9AX_toy : genJ9AX … toyS toyF χe = some (recSp …)` (a local twin of nock's `genJ9AX_eq`).
  3. `mkPbA_withOrb_eq`: the bridge `mkPbA (withOrb I o) hv = PbOfX9 …` field by field, generic in `I`.
  4. `toy9_air_of_hF1`: AccJ9A ∧ PubP9A at DX9 from the NAMED hypothesis `hF1` (F1's shape) plus 1-3.
No existing file edited.
-/
import Nock.V1J9A.GenJ9AX
import Nock.V1J9A.CheckJ9AIff
import Nock.RedTeam.Batch4883Thm54J9AComplToy
import NockvmE2E.J9A.E2EJ9AToyR

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace NockvmE2E.J9A.LinkJ9AToy

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.FillMem
open Nock.Edit Nock.Edit.GenX Nock.Walk Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9 genX9T)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AReads (walkReadsX9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axChainReadsK9 axReadsK9 axKeys9 splitVals9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChains (idOf9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AData (fieldAx9)
open Nock.V1J9.Gen9 (mbCounts9)
open Nock.V1J9A Nock.V1J9A.CheckJ9A Nock.V1J9A.GenJ9AX Nock.V1J9A.CheckJ9AIff

/-! ## 1. `withOrb` -/

/-- **`withOrb I o`**: the record `I` with every chip moved onto the orbit `o i = (h, ω)` of its index (order X C W J A V AX SP = 0..7);
`n` and `cols` are untouched, so `(withOrb I o).X.cols = I.X.cols` is `rfl`.  Honest because the column values do not depend on the
orbit (the generator picks `ωOf (hOf n)` only after the tables are built). -/
def withOrb (I : InJ9A) (o : Fin 8 → ℕ × Gold) : InJ9A :=
  { I with
    «X» := ⟨(o 0).1, I.X.n, (o 0).2, I.X.cols⟩
    C := ⟨(o 1).1, I.C.n, (o 1).2, I.C.cols⟩
    W := ⟨(o 2).1, I.W.n, (o 2).2, I.W.cols⟩
    J := ⟨(o 3).1, I.J.n, (o 3).2, I.J.cols⟩
    A := ⟨(o 4).1, I.A.n, (o 4).2, I.A.cols⟩
    V := ⟨(o 5).1, I.V.n, (o 5).2, I.V.cols⟩
    AX := ⟨(o 6).1, I.AX.n, (o 6).2, I.AX.cols⟩
    SP := ⟨(o 7).1, I.SP.n, (o 7).2, I.SP.cols⟩ }

theorem withOrb_X_cols (I : InJ9A) (o : Fin 8 → ℕ × Gold) : (withOrb I o).X.cols = I.X.cols := rfl
theorem withOrb_n (I : InJ9A) (o : Fin 8 → ℕ × Gold) :
    (withOrb I o).X.n = I.X.n ∧ (withOrb I o).C.n = I.C.n ∧ (withOrb I o).W.n = I.W.n ∧ (withOrb I o).J.n = I.J.n ∧
    (withOrb I o).A.n = I.A.n ∧ (withOrb I o).V.n = I.V.n ∧ (withOrb I o).AX.n = I.AX.n ∧ (withOrb I o).SP.n = I.SP.n :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- an admissible orbit assignment at the rows of `I`: every row count is positive and every `(h, ω)` is an `OrbOK` orbit -/
theorem validJ9A_withOrb (I : InJ9A) (o : Fin 8 → ℕ × Gold)
    (hX : 0 < I.X.n) (hC : 0 < I.C.n) (hW : 0 < I.W.n) (hA : 0 < I.A.n) (hV : 0 < I.V.n) (hAX : 0 < I.AX.n) (hSP : 0 < I.SP.n)
    (ho : ∀ i, 1 ≤ (o i).1 ∧ orderOf (o i).2.toZ = 3 * 2 ^ (o i).1) : ValidJ9A (withOrb I o) :=
  { nX := hX, nC := hC, nW := hW, nA := hA, nV := hV
    oX := ⟨(ho 0).1, (ho 0).2⟩, oC := ⟨(ho 1).1, (ho 1).2⟩, oW := ⟨(ho 2).1, (ho 2).2⟩, oJ := ⟨(ho 3).1, (ho 3).2⟩
    oA := ⟨(ho 4).1, (ho 4).2⟩, oV := ⟨(ho 5).1, (ho 5).2⟩
    nAX := hAX, oAX := ⟨(ho 6).1, (ho 6).2⟩, nSP := hSP, oSP := ⟨(ho 7).1, (ho 7).2⟩ }


/-! ## 2. the spelled record and `genJ9AX_toy` -/

/-- **`recSp`**: `genJ9AX`'s body with the run's data (`s f res`, the rows, `rowsOfT9 t`, `bfsForest [genX9T t]`) as parameters
(spelled, so that the kernel never unfolds the WF `bfsForest`).  Twin of nockvm's `recJ9AXRn`, generalised in the three slots. -/
def recSp (s f res : Noun) (rowsR : Array RowNX) (rows9 : Array Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen.LX9) (W9 : List (NTree ComplJ9AGen.LX9)) (χe : CoinsE) : InJ9A :=
    let c : P8PublicClaim := ⟨s, f, res⟩
    let roots := rootsOf c rowsR
    let cs := cellsOfRoots roots
    let acsL := acsOfD (bigsOf roots rowsR) ((incOps rowsR).any fun x => x.1 + 1 = P)
    let H := hdlB cs acsL
    let pt := ptrE acsL (stopEdges rowsR)
    let pd := HonestPairX.pdX (sxE pt)
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
    let reads := pairReads H pd rowsR ++ axReadsK9 P rows9
    let (vs, krV) := if reads.isEmpty then ([], 0) else walkGen padN reads
    let HA := hdl acsL
    let rIA : Noun → ℕ := fun n => if n = combP then lastIdxOf acsL combP else idxN acsL n
    let (aR, aP) := atomGenE pt χe acsL (infoOfE acsL pt rowsR) (mbCounts9 acsL cs c) (wCounts rIA acsL vs)
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
      «X» := chipOf comp.rows
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



theorem genJ9AX_eq_recSp (R : Nock.Jet.Registry) (fuel : ℕ) (s f : Noun) (χe : CoinsE) :
    genJ9AX R fuel s f χe = (runX R fuel s f).bind fun Rn =>
      if !(noJets Rn.rows) then none
      else some (recSp s f Rn.res Rn.rows (rowsOfT9 Rn.t) (bfsForest [genX9T Rn.t]) χe) := by
  unfold genJ9AX
  cases runX R fuel s f with
  | none => rfl
  | some Rn => rfl

open Nock.RedTeam.Batch4883 in
theorem genX_toy : genX (fun _ => none) 1000 sA fA = some (tA, rA) := by
  show genX Nock.Jet.VerifiedRegistry.empty.R 1000 sA fA = _
  simp only [genX, fA, genComputeSkeletonX, slotB, slotF]
  rfl

open Nock.RedTeam.Batch4883 in
theorem runX_toy : runX (fun _ => none) 1000 sA fA = some ⟨tA, rA, [tA, kB, kF], rowsL⟩ := by
  unfold runX
  rw [genX_toy]
  simp only [bfsA]
  rfl

open Nock.RedTeam.Batch4883 in
/-- the spelled J-9 A rows of the toy tree (= `rowsOfT9 tA`, `rows9A`) -/
def R9 : Array Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen.LX9 :=
  #[{ row := ComplJ9AGen.rowX9 tA.label, chip := ComplJ9AGen.ChipSt9.old, n := 0, m := 0, rn := rowOfSkelX tA.label },
    { row := ComplJ9AGen.rowX9 kB.label, chip := ComplJ9AGen.ChipSt9.s0B, n := AB, m := 0, rn := rowOfSkelX kB.label },
    { row := ComplJ9AGen.rowX9 kF.label, chip := ComplJ9AGen.ChipSt9.s0B, n := AF, m := 0, rn := rowOfSkelX kF.label }]

open Nock.RedTeam.Batch4883 in
def W9T : List (NTree ComplJ9AGen.LX9) := [gT9, .node ⟨ComplJ9AGen.rowX9 kB.label, .s0B, AB, 0, rowOfSkelX kB.label⟩ [],
    .node ⟨ComplJ9AGen.rowX9 kF.label, .s0B, AF, 0, rowOfSkelX kF.label⟩ []]

open Nock.RedTeam.Batch4883 in
theorem R9_eq : rowsOfT9 tA = R9 := rows9A
open Nock.RedTeam.Batch4883 in
theorem W9T_eq : bfsForest [genX9T tA] = W9T := by rw [genX9T_A]; exact bfs9A

open Nock.RedTeam.Batch4883 in
theorem noJets_toy : noJets rowsL = true := by decide +kernel

open Nock.RedTeam.Batch4883 in
/-- **[kernel] `genJ9AX` on the toy program is the spelled record** (any coins).  Sizes etc. below. -/
theorem genJ9AX_toy (χe : CoinsE) :
    genJ9AX (fun _ => none) 1000 sA fA χe = some (recSp sA fA rA rowsL R9 W9T χe) := by
  rw [genJ9AX_eq_recSp, runX_toy]
  simp only [Option.bind_some]
  rw [if_neg (by rw [noJets_toy]; decide), ← R9_eq, ← W9T_eq]


open Nock.RedTeam.Batch4883 in
/-- the toy record at the dump's coins -/
def Isp : InJ9A := recSp sA fA rA rowsL R9 W9T (prngCoins 1)

/-- **[kernel] sizes of the toy record** = `toy.inst.json` `tabs[].hN` and the two root counts -/
theorem toy_sizes : Isp.X.n = 3 ∧ Isp.C.n = 66 ∧ Isp.W.n = 95 ∧ Isp.A.n = 2 ∧ Isp.V.n = 1 ∧ Isp.AX.n = 4 ∧ Isp.SP.n = 1 ∧
    Isp.kroots = 3 ∧ Isp.krootsV = 1 ∧ Isp.axOn = true ∧ Isp.spOn = true := by
  decide +kernel


theorem L1 (k : Co) (y : K6) (α γ : K3) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cert : ℕ → ℕ → ℕ) (cs : List Noun)
    (ws : List WRow) (kr : ℕ) : (walkGenRowsB k y α γ H rI cert cs ws kr).1.size = ws.length := by
  simp [walkGenRowsB]
theorem L3 (ptr : Noun → ℕ) (k : Co) (y : K6) (α γ : K3) (H : Noun → ℕ × ℕ) (rI : Noun → ℕ) (cert : ℕ → ℕ → ℕ) (cs : List Noun)
    (ws : List WRow) (kr : ℕ) : (walkGenRowsBE ptr k y α γ H rI cert cs ws kr).1.size = ws.length := by
  simp [walkGenRowsBE]
theorem L2 (ptr : Noun → ℕ) (χe : CoinsE) (acsL : List Noun) (info : Array AInfo) (mb mxA mhA : Array ℕ) :
    (atomGenE ptr χe acsL info mb mxA mhA).1.size = acsL.length := by
  simp [atomGenE]
theorem L4 (χe : CoinsE) (nA : ℕ) (H : Noun → ℕ × ℕ) (rows9 : Array ComplJ9AGen.LX9) (on : Bool) :
    (Nock.V1J9A.GenAxE.axGenOf χe nA H rows9 on).1.size =
      if on then (ComplJ9AAxisRows.tableRows (ComplJ9AChainsRun.axChains9 P nA H rows9)).length else 1 := by
  unfold Nock.V1J9A.GenAxE.axGenOf Nock.V1J9A.GenAxE.axGenE Nock.V1J9A.GenAxE.axRows Nock.V1J9A.GenAxE.zeroChip
  have hq : ∀ rows, (Nock.V1J9A.GenAxE.qvRows χe rows).length = rows.length := by intro rows; simp [Nock.V1J9A.GenAxE.qvRows]
  split <;> simp [hq]
section Indep
variable (s f res : Noun) (rowsR : Array RowNX) (rows9 : Array ComplJ9AGen.LX9) (W9 : List (NTree ComplJ9AGen.LX9)) (χe χ' : CoinsE)
theorem A_n_ind : (recSp s f res rowsR rows9 W9 χe).A.n = (recSp s f res rowsR rows9 W9 χ').A.n := by
  show (atomGenE _ _ _ _ _ _ _).1.size = (atomGenE _ _ _ _ _ _ _).1.size
  rw [L2, L2]
theorem AX_n_ind : (recSp s f res rowsR rows9 W9 χe).AX.n = (recSp s f res rowsR rows9 W9 χ').AX.n := by
  unfold recSp
  simp only [chipOf]
  rw [L4, L4]
theorem W_n_ind : (recSp s f res rowsR rows9 W9 χe).W.n = (recSp s f res rowsR rows9 W9 χ').W.n := by
  show (walkGenRowsB _ _ _ _ _ _ _ _ _ _).1.size = (walkGenRowsB _ _ _ _ _ _ _ _ _ _).1.size
  rw [L1, L1]
theorem kr_ind : (recSp s f res rowsR rows9 W9 χe).kroots = (recSp s f res rowsR rows9 W9 χ').kroots := by
  unfold recSp; simp only []
theorem krV_ind : (recSp s f res rowsR rows9 W9 χe).krootsV = (recSp s f res rowsR rows9 W9 χ').krootsV := by
  unfold recSp; simp only []
theorem ax_ind : (recSp s f res rowsR rows9 W9 χe).axOn = (recSp s f res rowsR rows9 W9 χ').axOn := by
  unfold recSp; simp only []
theorem sp_ind : (recSp s f res rowsR rows9 W9 χe).spOn = (recSp s f res rowsR rows9 W9 χ').spOn := by
  unfold recSp; simp only []
end Indep

open Nock.RedTeam.Batch4883 in
set_option maxHeartbeats 4000000 in
/-- **[kernel] the sizes do not depend on the coins**: for EVERY `χe`, the spelled record has the toy's table sizes, root counts and
presence flags (the coins only fill column values).  X, C, V, SP, J by `rfl`; W, A, AX by the size lemmas `L1/L2/L4`
(each table is `(List.range N).map _ |>.toArray`); roots and flags do not read `χe`. -/
theorem toy_sizes_gen (χe : CoinsE) :
    (recSp sA fA rA rowsL R9 W9T χe).X.n = 3 ∧ (recSp sA fA rA rowsL R9 W9T χe).C.n = 66 ∧ (recSp sA fA rA rowsL R9 W9T χe).W.n = 95 ∧
    (recSp sA fA rA rowsL R9 W9T χe).A.n = 2 ∧ (recSp sA fA rA rowsL R9 W9T χe).V.n = 1 ∧ (recSp sA fA rA rowsL R9 W9T χe).AX.n = 4 ∧
    (recSp sA fA rA rowsL R9 W9T χe).SP.n = 1 ∧ (recSp sA fA rA rowsL R9 W9T χe).J.n = 0 ∧
    (recSp sA fA rA rowsL R9 W9T χe).kroots = 3 ∧ (recSp sA fA rA rowsL R9 W9T χe).krootsV = 1 ∧
    (recSp sA fA rA rowsL R9 W9T χe).axOn = true ∧ (recSp sA fA rA rowsL R9 W9T χe).spOn = true :=
  ⟨rfl, rfl, (W_n_ind _ _ _ _ _ _ χe _).trans toy_sizes.2.2.1, (A_n_ind _ _ _ _ _ _ χe _).trans toy_sizes.2.2.2.1, rfl,
    (AX_n_ind _ _ _ _ _ _ χe _).trans toy_sizes.2.2.2.2.2.1, rfl, rfl,
    (kr_ind _ _ _ _ _ _ χe _).trans toy_sizes.2.2.2.2.2.2.2.1, (krV_ind _ _ _ _ _ _ χe _).trans toy_sizes.2.2.2.2.2.2.2.2.1,
    (ax_ind _ _ _ _ _ _ χe _).trans toy_sizes.2.2.2.2.2.2.2.2.2.1, (sp_ind _ _ _ _ _ _ χe _).trans toy_sizes.2.2.2.2.2.2.2.2.2.2⟩

/-! ## 5. the absent program `*[[(p+5) 0] [0 2]]` (spelled record, sizes, bridge) -/

def sB : Noun := .cell (.atom (Nock.Field.p + 5)) (.atom 0)
def fB : Noun := .cell (.atom 0) (.atom 2)
def kAbs : NTree SkelX := mkX .s0 sB fB (.atom (Nock.Field.p + 5)) []

theorem slot_abs : Noun.slot 2 sB = some (.atom (Nock.Field.p + 5)) := by decide +kernel

theorem genX_abs : genX (fun _ => none) 1000 sB fB = some (kAbs, .atom (Nock.Field.p + 5)) := by
  show genX Nock.Jet.VerifiedRegistry.empty.R 1000 sB fB = _
  simp only [genX, fB, genComputeSkeletonX, slot_abs]
  rfl

theorem bfs_abs : bfsForest [kAbs] = [kAbs] := by simp [bfsForest, kAbs, mkX]

def rowsAbs : Array RowNX := #[rowOfSkelX kAbs.label]

theorem runX_abs : runX (fun _ => none) 1000 sB fB = some ⟨kAbs, .atom (Nock.Field.p + 5), [kAbs], rowsAbs⟩ := by
  unfold runX
  rw [genX_abs]
  simp only [bfs_abs]
  rfl

theorem chip_abs : ComplJ9AGen.chipOf kAbs.label = (.old, 0) := by decide

theorem genX9T_abs : ComplJ9AGen.genX9T kAbs = .node ⟨ComplJ9AGen.rowX9 kAbs.label, .old, 0, 0, rowOfSkelX kAbs.label⟩ [] := by
  show ComplJ9AGen.genX9T (.node kAbs.label []) = _
  rw [ComplJ9AGen.genX9T_node, chip_abs]; rfl

def R9a : Array ComplJ9AGen.LX9 := #[⟨ComplJ9AGen.rowX9 kAbs.label, .old, 0, 0, rowOfSkelX kAbs.label⟩]
def W9a : List (NTree ComplJ9AGen.LX9) := [.node ⟨ComplJ9AGen.rowX9 kAbs.label, .old, 0, 0, rowOfSkelX kAbs.label⟩ []]

theorem R9a_eq : rowsOfT9 kAbs = R9a := by
  simp only [ComplJ9AGen.rowsOfT9, genX9T_abs, R9a]; simp [bfsForest]
theorem W9a_eq : bfsForest [genX9T kAbs] = W9a := by
  rw [genX9T_abs]; simp [bfsForest, W9a]

theorem noJets_abs : noJets rowsAbs = true := by decide +kernel

theorem genJ9AX_abs (χe : CoinsE) :
    genJ9AX (fun _ => none) 1000 sB fB χe = some (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe) := by
  rw [genJ9AX_eq_recSp, runX_abs]
  simp only [Option.bind_some]
  rw [if_neg (by rw [noJets_abs]; decide), ← R9a_eq, ← W9a_eq]

def Iabs : InJ9A := recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a (prngCoins 1)

theorem abs_sizes : Iabs.X.n = 1 ∧ Iabs.C.n = 2 ∧ Iabs.W.n = 1 ∧ Iabs.A.n = 2 ∧ Iabs.V.n = 1 ∧ Iabs.AX.n = 1 ∧ Iabs.SP.n = 1 ∧
    Iabs.kroots = 1 ∧ Iabs.krootsV = 0 ∧ Iabs.axOn = false ∧ Iabs.spOn = false := by
  decide +kernel


set_option maxHeartbeats 4000000 in
/-- generic-coins sizes of the absent record (as `toy_sizes_gen`) -/
theorem abs_sizes_gen (χe : CoinsE) :
    (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).X.n = 1 ∧ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).C.n = 2 ∧ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).W.n = 1 ∧ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).A.n = 2 ∧ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).V.n = 1 ∧ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).AX.n = 1 ∧ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).SP.n = 1 ∧
    (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).J.n = 0 ∧ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).kroots = 1 ∧ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).krootsV = 0 ∧ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).axOn = false ∧ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).spOn = false :=
  ⟨rfl, rfl, (W_n_ind _ _ _ _ _ _ χe _).trans abs_sizes.2.2.1, (A_n_ind _ _ _ _ _ _ χe _).trans abs_sizes.2.2.2.1, rfl,
    (AX_n_ind _ _ _ _ _ _ χe _).trans abs_sizes.2.2.2.2.2.1, rfl, rfl,
    (kr_ind _ _ _ _ _ _ χe _).trans abs_sizes.2.2.2.2.2.2.2.1, (krV_ind _ _ _ _ _ _ χe _).trans abs_sizes.2.2.2.2.2.2.2.2.1,
    (ax_ind _ _ _ _ _ _ χe _).trans abs_sizes.2.2.2.2.2.2.2.2.2.1, (sp_ind _ _ _ _ _ _ χe _).trans abs_sizes.2.2.2.2.2.2.2.2.2.2⟩

/-! ## 3. the bridge `mkPbA (withOrb I o) hv = PbOfX9 …` -/

section Bridge
open NockvmE2E.Exec.V (ExecInst)
open NockvmE2E.Exec.ShapeF (shapeOkF)
open NockvmE2E.Exec.J9AChips (famJ9A)
open NockvmE2E.Exec.VL (zv)
open NockvmE2E.J9A.PbOfX9 (PbOfX9 orbX9 nOpt)
open NockvmE2E.J8.InstJ8 (tabOf hNof)

theorem nodesOf_eq_pow (h n : ℕ) (ω : Gold) (cols : ℕ → Fin n → ZMod Nock.Field.p) (z : ZMod Nock.Field.p) (hz : ω.toZ = z) :
    nodesOf ⟨h, n, ω, cols⟩ = fun i : Fin n => z ^ (i : ℕ) := by
  funext i; rw [nodesOf_eq]; simp [hz]

theorem nodes_hGen (XI : ExecInst) (n : ℕ) (cols : ℕ → Fin n → ZMod Nock.Field.p) :
    nodesOf ⟨XI.k + 1, n, Nock.TraceGenExe.Gold.ofU64 XI.hGen, cols⟩ = fun i : Fin n => zv XI.hGen ^ (i : ℕ) :=
  nodesOf_eq_pow _ _ _ _ _ (Nock.TraceGenExe.Gold.ofU64_toZ _)

theorem orbit_hGen (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (n : ℕ) (cols : ℕ → Fin n → ZMod Nock.Field.p)
    (ho : OrbOK ⟨XI.k + 1, n, Nock.TraceGenExe.Gold.ofU64 XI.hGen, cols⟩) :
    mkOrbit ⟨XI.k + 1, n, Nock.TraceGenExe.Gold.ofU64 XI.hGen, cols⟩ ho = orbX9 XI h := by
  unfold mkOrbit orbX9
  congr 1
  exact Nock.TraceGenExe.Gold.ofU64_toZ _

/-- **The bridge, generic in `I`**: if the row counts, root counts, registry data, layout and presence flags of `I` are those
`PbOfX9` prescribes, and every chip sits on the single orbit `(k+1, ofU64 hGen)`, then nockvm's `mkPbA` of the moved record IS
`PbOfX9` (field by field; the proof fields are irrelevant, the nodes are `ω^i` by `Gold.toZ_pow`). -/
theorem mkPbA_withOrb_eq (XI : ExecInst) (h : shapeOkF famJ9A XI = true) (kroots krootsV : ℕ) (Rt : ℕ → Nock.Jet.Autogen.Tpl)
    (regs ids : List ℕ) (idx : ℕ → ℕ) (rk : ℕ → ℕ × ℕ) (lay : Fin (hNof XI "jetChipJ8") → Nock.Jet.ChipJ8.PRow)
    (I : InJ9A) (hv : ValidJ9A (withOrb I (fun _ => (XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen))))
    (hX : I.X.n = hNof XI "computeChipVCLHX9") (hC : I.C.n = hNof XI "cellChipHQKW") (hW : I.W.n = hNof XI "walkChipJ8")
    (hJ : I.J.n = hNof XI "jetChipJ8") (hA : I.A.n = hNof XI "atomChipHQL") (hV : I.V.n = nOpt XI "walkChipHQK")
    (hAX : I.AX.n = nOpt XI "axisChipJ9") (hSP : I.SP.n = nOpt XI "splitChipJ9")
    (hk : I.kroots = kroots) (hkV : I.krootsV = if (tabOf XI "walkChipHQK").isSome then krootsV else 0)
    (hRt : I.Rt = Rt) (hr : I.regs = regs) (hi : I.ids = ids) (hx : I.idx = idx) (hrk : I.rk = rk)
    (hlay : HEq I.lay lay) (hax : I.axOn = (tabOf XI "axisChipJ9").isSome) (hsp : I.spOn = (tabOf XI "splitChipJ9").isSome) :
    mkPbA (withOrb I (fun _ => (XI.k + 1, Nock.TraceGenExe.Gold.ofU64 XI.hGen))) hv = PbOfX9 XI h kroots krootsV Rt regs ids idx rk lay := by
  obtain ⟨⟨c, M, χ, r, g, «X», C, W, J, A, V, kr, krV, lay', Rt', regs', ids', idx', rk'⟩, AX, SP, pX, pS, aX, aS, rX, rS⟩ := I
  obtain ⟨hX0, nX, wX, cX⟩ := «X»
  obtain ⟨hC0, nC, wC, cC⟩ := C
  obtain ⟨hW0, nW, wW, cW⟩ := W
  obtain ⟨hJ0, nJ, wJ, cJ⟩ := J
  obtain ⟨hA0, nA, wA, cA⟩ := A
  obtain ⟨hV0, nV, wV, cV⟩ := V
  obtain ⟨hAX0, nAX, wAX, cAX⟩ := AX
  obtain ⟨hSP0, nSP, wSP, cSP⟩ := SP
  dsimp only at *
  subst hX hC hW hJ hA hV hAX hSP hk hkV hRt hr hi hx hrk
  have hlay' := eq_of_heq hlay
  subst hlay'
  simp only [mkPbA, mkPb, PbOfX9, withOrb]
  congr 2 <;> first | exact nodes_hGen _ _ _ | exact orbit_hGen _ _ _ _ _

end Bridge

/-! ## 4. the toy instance: validity, the bridge at `DX9`, and `toy9_air` from `hF1` -/

section Toy
open NockvmE2E.Exec.V (ExecInst)
open NockvmE2E.Exec.ShapeF (shapeOkF)
open NockvmE2E.Exec.J9AChips (famJ9A)
open NockvmE2E.J9A.PbOfX9 (PbOfX9 orbX9 nOpt)
open NockvmE2E.J8.InstJ8 (tabOf hNof)
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.Exec.Toy9R (toy9R)
open NockvmE2E.J9A.DatX9Ok (DX9)
open NockvmE2E.J9A.E2EJ9AToyR (hJ_toy cToy toyS toyF)
open NockvmE2E.J9A.InstJ9A (AccJ9A PubP9A stmt_pub_of_acc9 acceptsJ9A_mono_rows)
open Nock.RedTeam.Batch4883 (sA fA rA rowsL)

/-- the executed toy instance, as the datum sees it -/
abbrev XT : ExecInst := XI170 toy9R

/-- the orbit assignment of the instance: every chip on `(k+1, hGen)` -/
def orbToy : Fin 8 → ℕ × Gold := fun _ => (XT.k + 1, Nock.TraceGenExe.Gold.ofU64 XT.hGen)

theorem orbToy_ok (hsh : shapeOkF famJ9A XT = true) : ∀ i, 1 ≤ (orbToy i).1 ∧ orderOf (orbToy i).2.toZ = 3 * 2 ^ (orbToy i).1 := by
  intro i
  refine ⟨Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  show orderOf (Nock.TraceGenExe.Gold.ofU64 XT.hGen).toZ = 3 * 2 ^ (XT.k + 1)
  rw [Nock.TraceGenExe.Gold.ofU64_toZ]
  exact NockvmE2E.Exec.ShapeF.orbit_order_of_shapeF hsh

theorem toy_valid (hsh : shapeOkF famJ9A XT = true) (χe : CoinsE) :
    ValidJ9A (withOrb (recSp sA fA rA rowsL R9 W9T χe) orbToy) := by
  obtain ⟨hX, hC, hW, hA, hV, hAX, hSP, -⟩ := toy_sizes_gen χe
  exact validJ9A_withOrb _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (orbToy_ok hsh)

theorem hNof_toy : hNof XT "computeChipVCLHX9" = 3 ∧ hNof XT "cellChipHQKW" = 66 ∧ hNof XT "walkChipJ8" = 95 ∧
    hNof XT "jetChipJ8" = 0 ∧ hNof XT "atomChipHQL" = 2 ∧ nOpt XT "walkChipHQK" = 1 ∧ nOpt XT "axisChipJ9" = 4 ∧
    nOpt XT "splitChipJ9" = 1 ∧ (tabOf XT "walkChipHQK").isSome = true ∧ (tabOf XT "axisChipJ9").isSome = true ∧
    (tabOf XT "splitChipJ9").isSome = true := by
  decide +kernel

theorem heq_of_zero {α : Type} (n m : ℕ) (hn : n = 0) (hm : m = 0) (f : Fin n → α) (g : Fin m → α) : HEq f g := by
  subst hn; subst hm; exact heq_of_eq (funext fun i => i.elim0)

/-- **THE BRIDGE at the executed toy datum** [kernel, modulo `hsh`]: nockvm's `mkPbA (withOrb I orbToy) hv` of the generator's record
(any coins) IS `(DX9 XT … cToy).Pb`, i.e. `PbOfX9 XT hsh 3 1 (fun _ => tplDummy) [] [] 0 (0,0) layNil` of `toy9_witness`. -/
theorem mkPbA_withOrb_toy (hsh : shapeOkF famJ9A XT = true) (χe : CoinsE)
    (hv : ValidJ9A (withOrb (recSp sA fA rA rowsL R9 W9T χe) orbToy)) :
    mkPbA (withOrb (recSp sA fA rA rowsL R9 W9T χe) orbToy) hv = (DX9 XT hsh hJ_toy 3 1 cToy).Pb := by
  obtain ⟨hX, hC, hW, hA, hV, hAX, hSP, hJ, hk, hkV, hax, hsp⟩ := toy_sizes_gen χe
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, t1, t2, t3⟩ := hNof_toy
  exact mkPbA_withOrb_eq XT hsh 3 1 _ [] [] _ _ _ _ _ (hX.trans n1.symm) (hC.trans n2.symm) (hW.trans n3.symm)
    (hJ.trans n4.symm) (hA.trans n5.symm) (hV.trans n6.symm) (hAX.trans n7.symm) (hSP.trans n8.symm) hk
    (by rw [hkV, if_pos t1]) rfl rfl rfl rfl rfl (heq_of_zero _ _ hJ n4 _ _) (by rw [hax, t2]) (by rw [hsp, t3])

/-- the row budgets of the spelled record are `budget 95` / `190` for every coins (`m = max` of the seven sizes) -/
theorem toy_budget (χe : CoinsE) :
    (recSp sA fA rA rowsL R9 W9T χe).r = budget 95 ∧ (recSp sA fA rA rowsL R9 W9T χe).rAX = 190 ∧
    (recSp sA fA rA rowsL R9 W9T χe).rSP = 190 := by
  have h := toy_sizes_gen χe
  unfold recSp at h ⊢
  simp only [chipOf] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  rw [h1, h2, h3, h4, h5, h6, h7]
  exact ⟨rfl, rfl, rfl⟩

/-- **`hF1`, the exact shape of nockvm's L4 F1 (`genJ9AX_honest_at`) at the toy program** (existential part only; F1's `Good`
conjunct is not needed): for SOME coins `χe`, `genJ9AX` returns `I`, and `AcceptsJ9A` holds of the generator's record moved onto the
orbit assignment `orbToy` (`I' := withOrb I orbToy`), at `mkPbA I' hv`, `I'.c`, `toχ I'.χ`, `I'.toMsg`, `I'.toTr`, `I'.toRows`, `I'.g`. -/
def HF1 : Prop :=
  ∃ (χe : CoinsE) (I : InJ9A), genJ9AX Nock.Jet.VerifiedRegistry.empty.R 1000 toyS toyF χe = some I ∧
    ∃ hv : ValidJ9A (withOrb I orbToy),
      Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 (mkPbA (withOrb I orbToy) hv)
        Nock.Jet.VerifiedRegistry.empty.R (withOrb I orbToy).c (toχ (withOrb I orbToy).χ) (withOrb I orbToy).toMsg
        (withOrb I orbToy).toTr (withOrb I orbToy).toRows (withOrb I orbToy).g

open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9) in
set_option maxHeartbeats 2000000 in
/-- **`toy9_air`** [kernel, modulo `hsh` (executed gate) and `hF1` (nockvm F1, not yet proved)]: at the executed toy datum `DX9 XT … cToy`
(the datum of `toy9_witness`), `AccJ9A` and `PubP9A` hold, with the generator's own trace.  This is ' minus the F1 instance. -/
theorem toy9_air (hsh : shapeOkF famJ9A XT = true) (hF1 : HF1) :
    ∃ χ M tr,
      AccJ9A (DX9 XT hsh hJ_toy 3 1 cToy) χ M tr ∧
      PubP9A (DX9 XT hsh hJ_toy 3 1 cToy) χ (M, fun j => pubVJ9 deltaF powerBasis3 cToy M.m M.ρ M.ρS χ j) := by
  obtain ⟨χe, I, hgen, hv, hacc⟩ := hF1
  have e1 : toyS = sA := rfl
  have e2 : toyF = fA := rfl
  have e3 : Nock.Jet.VerifiedRegistry.empty.R = fun _ => none := rfl
  rw [e1, e2, e3, genJ9AX_toy] at hgen
  have hI := Option.some.inj hgen
  subst hI
  rw [mkPbA_withOrb_toy hsh χe hv] at hacc
  obtain ⟨hb, hbX, hbS⟩ := toy_budget χe
  have hacc' : AccJ9A (DX9 XT hsh hJ_toy 3 1 cToy) (toχ (recSp sA fA rA rowsL R9 W9T χe).χ)
      (recSp sA fA rA rowsL R9 W9T χe).toMsg (withOrb (recSp sA fA rA rowsL R9 W9T χe) orbToy).toTr := by
    have hr : (withOrb (recSp sA fA rA rowsL R9 W9T χe) orbToy).toRows =
        (⟨budget 95, 190, 190⟩ : Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A.RowsJ9A) := by
      show (⟨(recSp sA fA rA rowsL R9 W9T χe).r, (recSp sA fA rA rowsL R9 W9T χe).rAX,
        (recSp sA fA rA rowsL R9 W9T χe).rSP⟩ : Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A.RowsJ9A) = _
      rw [hb, hbX, hbS]
    have hg : (withOrb (recSp sA fA rA rowsL R9 W9T χe) orbToy).g = 0 := by
      show (recSp sA fA rA rowsL R9 W9T χe).g = 0
      unfold recSp; simp only []
    have hrd : (DX9 XT hsh hJ_toy 3 1 cToy).r = Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A.cornerC9 := rfl
    rw [hr, hg] at hacc
    refine acceptsJ9A_mono_rows hacc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | exact Nat.zero_le _ | (rw [hrd]; decide +kernel)
  exact ⟨_, _, _, hacc', (stmt_pub_of_acc9 _ _ _ _ hacc').2⟩

end Toy

/-! ## 6. the absent datum: validity, bridge, `abs9_air` from `hF1` -/

section Abs
open NockvmE2E.Exec.V (ExecInst)
open NockvmE2E.Exec.ShapeF (shapeOkF)
open NockvmE2E.Exec.J9AChips (famJ9A)
open NockvmE2E.J9A.PbOfX9 (PbOfX9 orbX9 nOpt)
open NockvmE2E.J8.InstJ8 (tabOf hNof)
open NockvmE2E.Exec.E2EMain (XI170)
open NockvmE2E.Exec.Abs9R (abs9R)
open NockvmE2E.J9A.DatX9Ok (DX9)
open NockvmE2E.J9A.E2EJ9AToyR (hJ_abs cAbs absS absF)
open NockvmE2E.J9A.InstJ9A (AccJ9A PubP9A stmt_pub_of_acc9 acceptsJ9A_mono_rows)

/-- the executed absent instance (`abs9R`), as the datum sees it -/
abbrev XA : ExecInst := XI170 abs9R

/-- the orbit assignment of the instance: every chip on `(k+1, hGen)` -/
def orbAbs : Fin 8 → ℕ × Gold := fun _ => (XA.k + 1, Nock.TraceGenExe.Gold.ofU64 XA.hGen)

theorem orbAbs_ok (hsh : shapeOkF famJ9A XA = true) : ∀ i, 1 ≤ (orbAbs i).1 ∧ orderOf (orbAbs i).2.toZ = 3 * 2 ^ (orbAbs i).1 := by
  intro i
  refine ⟨Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  show orderOf (Nock.TraceGenExe.Gold.ofU64 XA.hGen).toZ = 3 * 2 ^ (XA.k + 1)
  rw [Nock.TraceGenExe.Gold.ofU64_toZ]
  exact NockvmE2E.Exec.ShapeF.orbit_order_of_shapeF hsh

theorem abs_valid (hsh : shapeOkF famJ9A XA = true) (χe : CoinsE) :
    ValidJ9A (withOrb (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe) orbAbs) := by
  obtain ⟨hX, hC, hW, hA, hV, hAX, hSP, -⟩ := abs_sizes_gen χe
  exact validJ9A_withOrb _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (orbAbs_ok hsh)

theorem hNof_abs : hNof XA "computeChipVCLHX9" = 1 ∧ hNof XA "cellChipHQKW" = 2 ∧ hNof XA "walkChipJ8" = 1 ∧
    hNof XA "jetChipJ8" = 0 ∧ hNof XA "atomChipHQL" = 2 ∧ nOpt XA "walkChipHQK" = 1 ∧ nOpt XA "axisChipJ9" = 1 ∧
    nOpt XA "splitChipJ9" = 1 ∧ (tabOf XA "walkChipHQK").isSome = false ∧ (tabOf XA "axisChipJ9").isSome = false ∧
    (tabOf XA "splitChipJ9").isSome = false := by
  decide +kernel

/-- **THE BRIDGE at the executed absent datum** [kernel, modulo `hsh`]: nockvm's `mkPbA (withOrb I orbAbs) hv` of the generator's record
(any coins) IS `(DX9 XA hsh hJ_abs 1 0 cAbs).Pb`, the datum that `wit_abs` (E2EJ9AToyR.lean) passes into `witness9`. -/
theorem mkPbA_withOrb_abs (hsh : shapeOkF famJ9A XA = true) (χe : CoinsE)
    (hv : ValidJ9A (withOrb (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe) orbAbs)) :
    mkPbA (withOrb (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe) orbAbs) hv = (DX9 XA hsh hJ_abs 1 0 cAbs).Pb := by
  obtain ⟨hX, hC, hW, hA, hV, hAX, hSP, hJ, hk, hkV, hax, hsp⟩ := abs_sizes_gen χe
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, t1, t2, t3⟩ := hNof_abs
  exact mkPbA_withOrb_eq XA hsh 1 0 _ [] [] _ _ _ _ _ (hX.trans n1.symm) (hC.trans n2.symm) (hW.trans n3.symm)
    (hJ.trans n4.symm) (hA.trans n5.symm) (hV.trans n6.symm) (hAX.trans n7.symm) (hSP.trans n8.symm) hk
    (by rw [hkV]; simp) rfl rfl rfl rfl rfl (heq_of_zero _ _ hJ n4 _ _) (by rw [hax, t2]) (by rw [hsp, t3])

/-- the row budgets of the spelled record are `budget 2` / `190` for every coins (`m = max` of the seven sizes) -/
theorem abs_budget (χe : CoinsE) :
    (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).r = budget 2 ∧ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).rAX = 10 ∧
    (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).rSP = 10 := by
  have h := abs_sizes_gen χe
  unfold recSp at h ⊢
  simp only [chipOf] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := h
  rw [h1, h2, h3, h4, h5, h6, h7]
  exact ⟨rfl, rfl, rfl⟩

/-- **`hF1`, the exact shape of nockvm's L4 F1 (`genJ9AX_honest_at`) at the absent program** (existential part only; F1's `Good`
conjunct is not needed): for SOME coins `χe`, `genJ9AX` returns `I`, and `AcceptsJ9A` holds of the generator's record moved onto the
orbit assignment `orbAbs` (`I' := withOrb I orbAbs`), at `mkPbA I' hv`, `I'.c`, `toχ I'.χ`, `I'.toMsg`, `I'.toTr`, `I'.toRows`, `I'.g`. -/
def HF1abs : Prop :=
  ∃ (χe : CoinsE) (I : InJ9A), genJ9AX Nock.Jet.VerifiedRegistry.empty.R 1000 absS absF χe = some I ∧
    ∃ hv : ValidJ9A (withOrb I orbAbs),
      Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ9A.AcceptsJ9A deltaF powerBasis3 (mkPbA (withOrb I orbAbs) hv)
        Nock.Jet.VerifiedRegistry.empty.R (withOrb I orbAbs).c (toχ (withOrb I orbAbs).χ) (withOrb I orbAbs).toMsg
        (withOrb I orbAbs).toTr (withOrb I orbAbs).toRows (withOrb I orbAbs).g

open Nock.NockVMROM.Thm54.VclL.Handle.ClaimJ9 (pubVJ9) in
set_option maxHeartbeats 2000000 in
/-- **`abs9_air`** [kernel, modulo `hsh` (executed gate) and `hF1` (nockvm F1, not yet proved)]: at the executed absent datum `DX9 XA hsh hJ_abs 1 0 cAbs`
(the datum of `wit_abs`), `AccJ9A` and `PubP9A` hold, with the generator's own trace.  This is ' minus the F1 instance. -/
theorem abs9_air (hsh : shapeOkF famJ9A XA = true) (hF1 : HF1abs) :
    ∃ χ M tr,
      AccJ9A (DX9 XA hsh hJ_abs 1 0 cAbs) χ M tr ∧
      PubP9A (DX9 XA hsh hJ_abs 1 0 cAbs) χ (M, fun j => pubVJ9 deltaF powerBasis3 cAbs M.m M.ρ M.ρS χ j) := by
  obtain ⟨χe, I, hgen, hv, hacc⟩ := hF1
  have e1 : absS = sB := rfl
  have e2 : absF = fB := rfl
  have e3 : Nock.Jet.VerifiedRegistry.empty.R = fun _ => none := rfl
  rw [e1, e2, e3, genJ9AX_abs] at hgen
  have hI := Option.some.inj hgen
  subst hI
  rw [mkPbA_withOrb_abs hsh χe hv] at hacc
  obtain ⟨hb, hbX, hbS⟩ := abs_budget χe
  have hacc' : AccJ9A (DX9 XA hsh hJ_abs 1 0 cAbs) (toχ (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).χ)
      (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).toMsg (withOrb (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe) orbAbs).toTr := by
    have hr : (withOrb (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe) orbAbs).toRows =
        (⟨budget 2, 10, 10⟩ : Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A.RowsJ9A) := by
      show (⟨(recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).r, (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).rAX,
        (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).rSP⟩ : Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A.RowsJ9A) = _
      rw [hb, hbX, hbS]
    have hg : (withOrb (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe) orbAbs).g = 0 := by
      show (recSp sB fB (.atom (Nock.Field.p + 5)) rowsAbs R9a W9a χe).g = 0
      unfold recSp; simp only []
    have hrd : (DX9 XA hsh hJ_abs 1 0 cAbs).r = Nock.NockVMROM.Thm54.VclL.Handle.RealIOJ9A.cornerC9 := rfl
    rw [hr, hg] at hacc
    refine acceptsJ9A_mono_rows hacc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | exact Nat.zero_le _ | (rw [hrd]; decide +kernel)
  exact ⟨_, _, _, hacc', (stmt_pub_of_acc9 _ _ _ _ hacc').2⟩

end Abs

end NockvmE2E.J9A.LinkJ9AToy


#print axioms NockvmE2E.J9A.LinkJ9AToy.validJ9A_withOrb
#print axioms NockvmE2E.J9A.LinkJ9AToy.genJ9AX_toy
#print axioms NockvmE2E.J9A.LinkJ9AToy.toy_sizes
#print axioms NockvmE2E.J9A.LinkJ9AToy.toy_sizes_gen
#print axioms NockvmE2E.J9A.LinkJ9AToy.mkPbA_withOrb_eq
#print axioms NockvmE2E.J9A.LinkJ9AToy.mkPbA_withOrb_toy
#print axioms NockvmE2E.J9A.LinkJ9AToy.toy_valid
#print axioms NockvmE2E.J9A.LinkJ9AToy.toy_budget
#print axioms NockvmE2E.J9A.LinkJ9AToy.toy9_air
#print axioms NockvmE2E.J9A.LinkJ9AToy.genJ9AX_abs
#print axioms NockvmE2E.J9A.LinkJ9AToy.abs_sizes
#print axioms NockvmE2E.J9A.LinkJ9AToy.abs_sizes_gen
#print axioms NockvmE2E.J9A.LinkJ9AToy.abs_valid
#print axioms NockvmE2E.J9A.LinkJ9AToy.mkPbA_withOrb_abs
#print axioms NockvmE2E.J9A.LinkJ9AToy.abs_budget
#print axioms NockvmE2E.J9A.LinkJ9AToy.abs9_air
