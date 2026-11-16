/-
  Nock/V1J9AL/GenAluE.lean

  **The executable ALU-chip filler** (twin of `V1J9A/GenAxE.lean`). EXECUTABLE evidence only (no theorem here): the filler mirrors the honest ALU table of
  `J9AL/AluHonestTable.lean` (`callsLOf`, `pregsOf`, `aluRowsB`, `blockQ`) and the LogUp lane of `AluSatRows.lean`
  (`dK`, `tV`, `tS`, `tX`, `qv2`) over the executable `K6`.

  * base columns `0..93` = `BRow.col` of the honest base table, with the two masks `0 / 1` (first / last row) set and
    the table PADDED to exactly `3·2^h` rows (so the checker's last-row successor, the interpolant at `ω·x_{n-1}`,
    wraps to row `0` whose `sL = 0`: it equals the honest trace's corrected `sL` at the last successor, `AluTraceFix`);
  * round 1 (`H HO L D1 D2 S1 S2 RL RO`): `blockQE`, the `K6` copy of `AluHonestRows.blockQ` (`K6` is no `CommRing`);
  * round 2 (`invV invR invO invJ invX accV accS accX`): inverses of the key denominators (`compressE` at the
    validity coins for `valKey = [z, 0, L, 0, sv]`, at the handle coins for the four service keys), inclusive prefix
    sums of the row terms `tV tS tX`;
  * publics `pubsLE`: `pubALv / pubALs / pubALx` (`0/1`, `2/3`, `4/5`) = `Σ tV / Σ tS / Σ tX`.
-/
import Nock.V1J9A.GenAxE
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluHonestTable
import Nock.V1J8.GenJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J9AL.GenAluE

open Nock Nock.Reified Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData (opOf primsC idxPOf)
open Nock.V1J9A.GenAxE (inclSums roleLimbs)
local notation "zq" => Nock.V1J9A.GenAxE.zq
open Nock.Jet.Prim (PrimOp)

/-! ## 1. `K6` casts and the round-1 rows (`blockQ` at `K6`) -/

def nK (n : ℕ) : K6 := zq (n : ZMod p)
def iK (z : ℤ) : K6 := zq (z : ZMod p)

def evRE (y : K6) : List ℤ → K6
  | [] => 0
  | d :: ds => iK d + y * evRE y ds

def hornerE (y : K6) (ws : List ℕ) : K6 := evRE y (zl ws)
def hornerFromE (y : K6) (ws : List ℕ) (i : ℕ) : K6 := hornerE y (ws.drop i)

def packVE (y : K6) (w : ℕ) : K6 :=
  ((List.range 32).map fun t => nK (bitOf w t) * powE y t).foldl (· + ·) 0

def hornerQ1E (y : K6) : List ℕ → K6
  | [] => 0
  | w :: ws => packVE y w + powE y 32 * hornerQ1E y ws

def slotHE (y : K6) (s : SlotL) (i : ℕ) : K6 :=
  if s.mode = 4 then hornerQ1E y (s.words.drop i)
  else if s.mode = 0 then 0 else hornerFromE y s.words i

def slotHOE (y : K6) (s : SlotL) (i : ℕ) : K6 :=
  if s.mode = 0 ∨ s.mode = 4 then 0 else hornerFromE y (hiL s.words) i

def slotLE (y : K6) (s : SlotL) : K6 :=
  if s.mode = 4 ∨ s.mode = 5 then (y - nK Bn) * slotHE y s 0 else hornerE y s.vw

def latchOfE (p : ℕ) (y : K6) (cl : CallL) : K6 × K6 :=
  match (slotsOf p cl).find? (fun s => isF1 cl.op s) with
  | some s => (slotLE y s, slotHOE y s 0)
  | none => (0, 0)

def slotDE (p : ℕ) (y : K6) (cl : CallL) (s : SlotL) : K6 × K6 :=
  let L := slotLE y s
  let lt := latchOfE p y cl
  if isF2 cl.op s then (lt.1 * L + (y - nK Bn) * (lt.2 * slotHOE y s 0), iK s.cf2 * L)
  else (iK s.cf1 * L, iK s.cf2 * L)

def hdrDE (cl : CallL) : K6 × K6 :=
  ((if cl.op = .lt then (1 - nK cl.lbv) else 0), (if cl.op = .div ∨ cl.op = .mod then 1 else 0))

def laneDE (p : ℕ) (y : K6) (cl : CallL) : List (K6 × K6) :=
  (slotsOf p cl).flatMap fun s =>
    (List.range s.words.length).map fun i => if i = 0 then slotDE p y cl s else (0, 0)

def runSumsE : K6 × K6 → List (K6 × K6) → List (K6 × K6)
  | _, [] => []
  | acc, d :: ds => (acc.1 + d.1, acc.2 + d.2) :: runSumsE (acc.1 + d.1, acc.2 + d.2) ds

def laneHLE (y : K6) (cl : CallL) (p : ℕ) : List (K6 × K6 × K6) :=
  (slotsOf p cl).flatMap fun s =>
    (List.range s.words.length).map fun i => (slotHE y s i, slotHOE y s i, if i = 0 then slotLE y s else 0)

/-- **The `K6` rows of a call's block** (hdr first); the executable twin of `blockQ`. -/
def blockQE (p : ℕ) (y : K6) (cl : CallL) : List (QRow K6) :=
  let lt := latchOfE p y cl
  let d0 := hdrDE cl
  let ds := laneDE p y cl
  let ss := runSumsE d0 ds
  ⟨0, 0, 0, d0.1, d0.2, d0.1, d0.2, lt.1, lt.2⟩ ::
    ((laneHLE y cl p).zip (ds.zip ss)).map fun x =>
      ⟨x.1.1, x.1.2.1, x.1.2.2, x.2.1.1, x.2.1.2, x.2.2.1, x.2.2.2, lt.1, lt.2⟩

/-! ## 2. The LogUp lane -/

/-- A width-`m` key from its entries, as `K6` vector. -/
def keyOf {m : ℕ} (l : List (ZMod p)) : Fin m → K6 := fun c => zq (l.getD c 0)

/-- The row terms and inverses of one row: `(tV, tS, tX, invV, invR, invO, invJ, invX)`. -/
def laneRow (χe : CoinsE) (r : BRow (ZMod p)) (q : QRow K6) :
    K6 × K6 × K6 × K6 × K6 × K6 × K6 × K6 :=
  let dV : K6 := compressE (γVE χe) (ρVE χe) (fun c : Fin 5 =>
    match (c : ℕ) with
    | 0 => zE χe
    | 1 => 0
    | 2 => q.L
    | 3 => 0
    | _ => zq r.sv)
  let hk := fun (l : List (ZMod p)) => compressE (γHE χe) (ρHE χe) (keyOf (m := 8) l)
  let dR := hk [r.idc, r.kc, r.vc, 0, 0, 0, 0, 7]
  let dO := hk [r.idc, r.opc, 0, 0, 0, 0, 0, 6]
  let dJ := hk [r.idc, r.kc, r.vc, r.kS, r.vS, r.kE, r.vE, 3]
  let dX : K6 := compressE (γHE χe) (ρHE χe) (keyOf (m := 5) [r.vS, r.kA, r.vA, r.kB, r.vB])
  let w := r.sH - r.sP * r.mP
  (zq r.aV * dV⁻¹, zq w * dR⁻¹ + zq w * dO⁻¹ - zq (r.sH * r.mJ) * dJ⁻¹, zq r.sH * dX⁻¹,
    dV⁻¹, dR⁻¹, dO⁻¹, dJ⁻¹, dX⁻¹)

/-! ## 3. The table -/

/-- **The ALU chip of a run**: rows (196 columns) padded to `3·2^h`, and the publics.  Inputs: the cell list `cs`, the
handle map `Hm`, the primitive table `prims` (the called primitives, `primsC`), all call ids `ids`, the primitive calls
`pc` (id, subject, result). -/
def aluGenE (χe : CoinsE) (cs : List Noun) (Hm : Noun → ℕ × ℕ) (prims : List (ℕ × PrimOp)) (ids : List ℕ)
    (pc : List (ℕ × Noun × Noun)) : Array (Array (ZMod p)) × (ℕ → K3) :=
  let cls := callsLOf cs Hm prims pc
  let pregs : List (BRow (ZMod p)) := pregsOf cs prims ids
  let base : List (BRow (ZMod p)) := aluRowsB p pregs cls
  let y := yE χe
  let qs : List (QRow K6) :=
    List.replicate pregs.length QRow.zero ++ cls.flatMap (blockQE p y) ++ [QRow.zero]
  let n0 := base.length
  let N := 3 * 2 ^ (Nock.V1J8.Gen.hOf n0)
  let rowB (i : ℕ) : BRow (ZMod p) := base.getD i padRow
  let rowQ (i : ℕ) : QRow K6 := qs.getD i QRow.zero
  let lr := (List.range N).map fun i => laneRow χe (rowB i) (rowQ i)
  let tVs := lr.map fun x => x.1
  let tSs := lr.map fun x => x.2.1
  let tXs := lr.map fun x => x.2.2.1
  let accV := inclSums tVs
  let accS := inclSums tSs
  let accX := inclSums tXs
  let rows : Array (Array (ZMod p)) := ((List.range N).zip lr).toArray.map fun (i, x) =>
    let b := rowB i
    let cols94 := (List.range 94).map fun j =>
      if j = 0 then (if i = 0 then (1 : ZMod p) else 0)
      else if j = 1 then (if i + 1 = N then (1 : ZMod p) else 0)
      else b.col j
    let q := rowQ i
    let roles : List K6 := [q.H, q.HO, q.L, q.D1, q.D2, q.S1, q.S2, q.RL, q.RO, x.2.2.2.1, x.2.2.2.2.1,
      x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2, accV.getD i 0, accS.getD i 0, accX.getD i 0]
    (cols94 ++ roleLimbs roles).toArray
  let sV := tVs.foldl (· + ·) 0
  let sS := tSs.foldl (· + ·) 0
  let sX := tXs.foldl (· + ·) 0
  (rows, fun j =>
    if j = 0 then sV.re else if j = 1 then sV.im else if j = 2 then sS.re else if j = 3 then sS.im
    else if j = 4 then sX.re else if j = 5 then sX.im else 0)

/-- The absent ALU: one zero row of width 196, publics `0`. -/
def zeroChip : Array (Array (ZMod p)) × (ℕ → K3) := (#[Array.replicate 196 0], fun _ => 0)

end Nock.V1J9AL.GenAluE
