/-
  NockvmE2E/Z38/JetPreGate.lean

  `jetPreOkF`: the executed check of the J table's 18 verifier-fixed columns, the analogue of `pregOkF` (RunGate9L).  At the jet table, with
  `lay := layoutJ8 catJ.Rt regs calls` (`regs` = the keys of `pubIn.pins`, `calls` = `pubIn.calls`; nock `Jet/ChipJ8.lean` `layoutJ8`):
  (i)   `lay.length = hN_J` (no padding row, `n_J = |layoutJ8 Rt regs ids|`);
  (ii)  the masks at columns 11 / 12 are the first-row / last-row patterns (`maskCol`);
  (iii) the columns `0..10, 13..17` evaluate, on the `hN_J` nodes `hGen^i`, to `preColG (lay i) c` (executable twin of nock `Jet/ChipJ8T.lean` `preCol`,
        which `jetPre` / `jetChipJ8.preprocessing` interpolate), and have at most `hN_J` coefficients (so they ARE the Lagrange interpolants).
  Executable `Bool`.  Tables other than the jet are not constrained.  Not zero-knowledge.
-/
import NockvmE2E.J9A.RunGate9L
import NockvmE2E.Z38.CatJ
set_option autoImplicit false

namespace NockvmE2E.Z38.JetPre
open NockvmE2E.Exec NockvmE2E.Exec.V NockvmE2E.Exec.MaskOk
open NockvmE2E.Exec.VF (G PN)
open Nock.Jet.ChipJ8 (PRow Kd layoutJ8)

/-- the registry ids of the public input: the keys of its pins, in order -/
def regsOfPub (p : PE.PubIn) : List ℕ := p.pins.map (·.key)

/-- the pin index of a registry id (`0` if absent) -/
def idxOfPub (p : PE.PubIn) (id : ℕ) : ℕ := ((p.pins.find? (fun q => q.key == id)).map (·.idx)).getD 0

/-- the pin rank limbs `(hi, lo)` of a registry id (`(0, 0)` if absent) -/
def rkOfPub (p : PE.PubIn) (id : ℕ) : ℕ × ℕ := ((p.pins.find? (fun q => q.key == id)).map (fun q => (q.hi, q.lo))).getD (0, 0)

/-- the J layout of the public input, over the catalogue's templates -/
def layJ (p : PE.PubIn) : List PRow := layoutJ8 CatJ.catJ.toCR.Rt (regsOfPub p) p.calls

/-- executable `Nock.Jet.ChipJ8.preCol` (`j ≠ 11, 12`): the selector one-hot for `j < 11`, then `id, cid, nid, n1, n2` at `13 .. 17` -/
def preColG (q : PRow) (j : ℕ) : G :=
  if j < 11 then (if q.kd.sel = j then (1 : G) else 0)
  else if j == 13 then UInt64.ofNat q.id
  else if j == 14 then UInt64.ofNat q.cid
  else if j == 15 then UInt64.ofNat q.nid
  else if j == 16 then UInt64.ofNat q.n1
  else if j == 17 then UInt64.ofNat q.n2
  else 0

/-- (i) the layout length is the jet table's height -/
def jetLayLenOk (XX : ExecInst) (t : TabInst) : Bool := decide ((layJ XX.pubIn).length = t.hN)

/-- (ii) the first-row mask at column 11 and the last-row mask at column 12 -/
def jetMasksOk (XX : ExecInst) (t : TabInst) : Bool :=
  (maskCol XX t.hN 0 (XX.pre.getD (t.col0 + 11) #[])).isSome && (maskCol XX t.hN 1 (XX.pre.getD (t.col0 + 12) #[])).isSome

/-- (iii) one layout column `c` -/
def jetColOk (XX : ExecInst) (t : TabInst) (c : ℕ) : Bool :=
  let p := XX.pre.getD (t.col0 + c) #[]
  decide (p.size ≤ t.hN) && evalNodes p XX.hGen t.hN == ((layJ XX.pubIn).map (fun q => preColG q c)).toArray

/-- (iii) the layout columns `0..10, 13..17` -/
def jetColsOk (XX : ExecInst) (t : TabInst) : Bool :=
  (List.range 18).all fun c => c == 11 || c == 12 || jetColOk XX t c

/-- **`jetPreOkF`** -/
def jetPreOkF (XX : ExecInst) : Bool := XX.tabs.all fun t =>
  if t.chip.id == "jetChipJ8" then jetLayLenOk XX t && jetMasksOk XX t && jetColsOk XX t else true

end NockvmE2E.Z38.JetPre
