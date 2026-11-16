/-
  Nock/V1J9A/GenAxE.lean

  Nothing here is a kernel theorem: the filler
  mirrors `ComplJ9AAxisH` (`dKey`, `sRow`, `pRow`, `accSN`, `accPN`, `qv`, `roleV`, `colAx`) and
  `ComplJ9AChipsOK.pubsXOf` over the executable `K6` (the `𝕂′` twin), and is checked only by `#eval` of
  `MemX.checkM (axisTemplateJ9 deltaF)`.

  * base columns `0..21` = `ARow.col` of `tableRows (axChains9 P nA H rows9)` (masks `0 / 1` = first / last row);
  * `𝕂′` columns (`invL invP invT accS accP`, slots `22 + 6 s`): `dKeyE` = `compressE γHE ρHE` of the key read at
    the row (the handle coins `κ = (γH′, ρH′)` of `chalsMJ8E 33..36`), inclusive prefix sums of `sRowE`/`pRowE`;
  * publics `pubsXE`: slots `0,1` = `Σ sRow` (`K6.re`/`K6.im`), `2,3` = `Σ pRow`;
  * `zeroChip`: the absent axis chip (1 zero row of width 52, publics 0).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChainsRun
import Nock.V1J8.MemX
import Nock.V1J8.CheckJ8

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J9A.GenAxE

open Nock Nock.Reified Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AAxisRows (ARow)
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (limbKey pathKey tagKey mu z1a)

/-- A base-field value as a base element of `𝕂′`. -/
def zq (x : ZMod p) : K6 := g6 (Gold.ofZ x)

/-- Row `i` of the table (`0` row past the end), masks `0 / 1` = first / last row, as column function. -/
def colAt (rows : List (ARow (ZMod p))) (i : ℕ) (c : ℕ) : ZMod p :=
  match rows[i]? with
  | some r => r.col (if i = 0 then 1 else 0) (if i + 1 = rows.length then 1 else 0) c
  | none => 0

/-- The intended base environment of row `i` (`ComplJ9AAxisH.envC`, `nxt = 0`; coins and publics unread). -/
def envE (rows : List (ARow (ZMod p))) (i : ℕ) : Env (ZMod p) :=
  ⟨fun j => colAt rows i j, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- A key denominator at the handle coins `κ = (γHE, ρHE)` (`dKey`, width 8, zero padded). -/
def dKeyE (χe : CoinsE) (rows : List (ARow (ZMod p))) (key : List (CoeffExpr (ZMod p))) (i : ℕ) : K6 :=
  compressE (γHE χe) (ρHE χe)
    (fun c : Fin 8 => zq ((key.getD c (.const 0)).eval (envE rows i)))

/-- The service row term `invL − mu·invT` (`sRow`). -/
def sRowE (χe : CoinsE) (rows : List (ARow (ZMod p))) (i : ℕ) : K6 :=
  (dKeyE χe rows limbKey i)⁻¹ - zq (colAt rows i mu) * (dKeyE χe rows tagKey i)⁻¹

/-- The path row term `(1 − z1a)·invP` (`pRow`). -/
def pRowE (χe : CoinsE) (rows : List (ARow (ZMod p))) (i : ℕ) : K6 :=
  zq (1 - colAt rows i z1a) * (dKeyE χe rows pathKey i)⁻¹

/-- Inclusive prefix sums. -/
def inclSums (l : List K6) : List K6 :=
  (l.foldl (fun (s : K6 × List K6) x => let a := s.1 + x; (a, a :: s.2)) (0, [])).2.reverse

/-- The five `𝕂′` columns (`invL invP invT accS accP`) of every row. -/
def qvRows (χe : CoinsE) (rows : List (ARow (ZMod p))) : List (List K6) :=
  let n := rows.length
  let accS := inclSums ((List.range n).map (sRowE χe rows))
  let accP := inclSums ((List.range n).map (pRowE χe rows))
  (List.range n).map fun i =>
    [(dKeyE χe rows limbKey i)⁻¹, (dKeyE χe rows pathKey i)⁻¹, (dKeyE χe rows tagKey i)⁻¹,
      accS.getD i 0, accP.getD i 0]

/-- The 30 role limbs of one row: role `r` = Re / Im of `𝕂′` column `r / 2`, limbs `c0 c1 c2` (`colAx`). -/
def roleLimbs (q : List K6) : List (ZMod p) :=
  (q.flatMap fun a => [a.re, a.im]).flatMap fun k => [k.c0.toZ, k.c1.toZ, k.c2.toZ]

/-- **The axis table**: 52 columns per row (`colAx`: base `0..21`, role limbs `22..51`). -/
def axRows (χe : CoinsE) (rows : List (ARow (ZMod p))) : Array (Array (ZMod p)) :=
  ((List.range rows.length).zip (qvRows χe rows)).toArray.map fun (i, q) =>
    ((List.range 22).map (colAt rows i) ++ roleLimbs q).toArray

/-- **The axis publics** (`pubsXOf`): slots `0,1` = Re/Im `Σ sRow`, `2,3` = Re/Im `Σ pRow`, else `0`. -/
def pubsXE (χe : CoinsE) (rows : List (ARow (ZMod p))) : ℕ → K3 :=
  let n := rows.length
  let s : K6 := ((List.range n).map (sRowE χe rows)).foldl (· + ·) 0
  let q : K6 := ((List.range n).map (pRowE χe rows)).foldl (· + ·) 0
  fun j => if j = 0 then s.re else if j = 1 then s.im else if j = 2 then q.re else if j = 3 then q.im else 0

/-- **The axis chip of the honest chains**: rows of `tableRows (axChains9 P nA H rows9)` and its publics. -/
def axGenE (χe : CoinsE) (cs : List (ComplJ9AAxisRows.ChainSpec (ZMod p))) :
    Array (Array (ZMod p)) × (ℕ → K3) :=
  let rows := ComplJ9AAxisRows.tableRows cs
  (axRows χe rows, pubsXE χe rows)

/-- The absent axis chip: one zero row of width 52, publics 0. -/
def zeroChip : Array (Array (ZMod p)) × (ℕ → K3) := (#[Array.replicate 52 0], fun _ => 0)

/-- The axis chip from the run's rows (`axChains9`) — the `genJ9AX` entry point. -/
def axGenOf (χe : CoinsE) (nA : ℕ) (H : Noun → ℕ × ℕ) (rows9 : Array ComplJ9AGen.LX9) (on : Bool) :
    Array (Array (ZMod p)) × (ℕ → K3) :=
  if on then axGenE χe (ComplJ9AChainsRun.axChains9 p nA H rows9) else zeroChip

end Nock.V1J9A.GenAxE
