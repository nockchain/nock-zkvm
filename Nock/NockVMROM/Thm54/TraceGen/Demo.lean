import Nock.Reference
import Nock.NockVMROM.Thm54.TraceGen.Gen
import Nock.NockVMROM.Thm54.TraceGen.GenMem
import Nock.NockVMROM.Thm54.TraceGen.Encode

/-! # End-to-end trace-generation demo

This module demonstrates the full NockVM pipeline on small Nock programs:
a Nock expression goes in, and concrete compute / memory table rows come out
as field elements over `ZMod 97`, ready for the AIR constraint system.

Nothing here is proved — it is pure `#eval` output showing the generator in action.
-/

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

namespace Nock.NockVMROM.Thm54.TraceGen.Demo

open Nock Nock.Walk
open Nock.NockVMROM.Thm54.TraceGen

section ReprInstances

variable {K : Type*} [Repr K]

instance : Repr (ComputeTable.FP K) where
  reprPrec fp _ := s!"⟨size={repr fp.size}, dyck={repr fp.dyck}, leaf={repr fp.leaf}⟩"

instance : Repr (ComputeTable.MemRec K) where
  reprPrec m _ :=
    s!"⟨root={repr m.root}, child={repr m.child}, axis={repr m.axis}, ts={repr m.ts}⟩"

instance : Repr (ComputeTable.Inputs K) where
  reprPrec i _ := s!"⟨α={repr i.α}, z={repr i.z}, a={repr i.a}, b={repr i.b}, c={repr i.c}⟩"

instance : Repr (ComputeTable.Pub K) where
  reprPrec p _ :=
    s!"⟨state={repr p.state}, s={repr p.s}, f={repr p.f}, e={repr p.e}, " ++
    s!"sf1=({repr p.sf1_s},{repr p.sf1_f},{repr p.sf1_e}), " ++
    s!"sf2=({repr p.sf2_s},{repr p.sf2_f},{repr p.sf2_e}), " ++
    s!"sf3=({repr p.sf3_s},{repr p.sf3_f},{repr p.sf3_e}), " ++
    s!"ln_prev={repr p.ln_prev}, ln={repr p.ln}, " ++
    s!"mr1={repr p.mr1}, mr2={repr p.mr2}, mr3={repr p.mr3}⟩"

instance : Repr (ComputeTable.Dec K) where
  reprPrec d _ :=
    s!"⟨f_h={repr d.f_h}, f_t={repr d.f_t}, f_th={repr d.f_th}, " ++
    s!"f_tt={repr d.f_tt}, f_tth={repr d.f_tth}, f_ttt={repr d.f_ttt}⟩"

instance : Repr (MemoryTable.Cell K) where
  reprPrec c _ := s!"⟨noun={repr c.noun}, ind={repr c.indicator}, cnt={repr c.counts}⟩"

instance : Repr (MemoryTable.Inputs K) where
  reprPrec i _ := s!"⟨z={repr i.z}, β={repr i.β}, γ={repr i.γ}⟩"

instance : Repr (MemoryTable.Pub K) where
  reprPrec p _ :=
    s!"⟨st={repr p.st}, pt={repr p.pt}, lc={repr p.lc}, rc={repr p.rc}, " ++
    s!"lcSt={repr p.lcSt}, rcSt={repr p.rcSt}, mem={repr p.mem}, " ++
    s!"ipre={repr p.ipre}, icur={repr p.icur}, ver={repr p.ver}⟩"

private def reprNTree {LT : Type*} [Repr LT] : NTree LT → Std.Format
  | .node l [] => s!"(leaf {repr l})"
  | .node l cs =>
    let cs' := cs.map fun c => toString (reprNTree c)
    s!"(node {repr l} [{", ".intercalate cs'}])"

instance {LT : Type*} [Repr LT] : Repr (NTree LT) where
  reprPrec t _ := reprNTree t

end ReprInstances

section ReprInstances0

variable {K : Type} [Repr K] [Field K]

instance : Repr (ServiceReq K) where
  reprPrec sr _ :=
    s!"⟨root={repr sr.root}, child={repr sr.child}, axis={sr.axis}, ts={repr sr.ts}⟩"

instance : Repr (GenComputeRow K) where
  reprPrec g _ :=
    let (st, inp, pub, dec) := (g.row.1, g.row.2.1, g.row.2.2.1, g.row.2.2.2)
    s!"ComputeRow(state={repr st}, inputs={repr inp}, pub={repr pub}, dec={repr dec})"

instance : Repr (GenMemoryRow K) where
  reprPrec g _ :=
    let (mst, inp, pub) := (g.row.1, g.row.2.1, g.row.2.2)
    s!"MemoryRow(state={repr mst}, inputs={repr inp}, pub={repr pub})"

variable {F : Type} [Field F] [Algebra F K]

instance : Repr (GenTrace F K) where
  reprPrec t _ :=
    s!"GenTrace(\n  subject={repr t.subject}\n  formula={repr t.formula}\n" ++
    s!"  result={repr t.result}\n  fuel={t.fuel}\n" ++
    s!"  computeNodes={repr t.computeNodes}\n" ++
    s!"  memoryNodes={repr t.memoryNodes}\n)"

end ReprInstances0

noncomputable section

private noncomputable def runTrace (subject formula : Noun) :=
  match genTraceGeneric 97 3 (8 : ZMod 97) (4 : ZMod 97) MemoryTable.formRDefault 100 subject formula with
  | .ok t => toString (repr t)
  | .error _ => "trace generation failed"

private noncomputable def runServiceReqs (subject formula : Noun) :=
  match genTraceGeneric 97 3 (8 : ZMod 97) (4 : ZMod 97) MemoryTable.formRDefault 100 subject formula with
  | .ok t => toString (repr (genServiceReqs t.computeNodes))
  | .error _ => "trace generation failed"

/-! ## Demo 1: Increment 42

`*[42 [4 0 1]]` evaluates to `43`.  Opcode 4 is "increment", formula `[0 1]` is "slot 1"
(the subject itself), so this increments the subject.
-/

private def subj42 : Noun := .atom 42
private def fmInc : Noun := .cell (.atom 4) (.cell (.atom 0) (.atom 1))

#eval evalN 100 subj42 fmInc

#eval encC (8 : ZMod 97) subj42
#eval encC (8 : ZMod 97) fmInc

-- `genTraceGeneric` is noncomputable (`pwScaleExp`); keep the wrappers as
-- noncomputable defs and do not `#eval` them.
#check runTrace
#check runServiceReqs

/-! ## Demo 2: Cell test on an atom

`*[42 [3 0 1]]` — opcode 3 tests whether the subject (slot 1) is a cell.
42 is an atom, so the result is `1` (false / "not a cell").
-/

private def fmCellTest : Noun := .cell (.atom 3) (.cell (.atom 0) (.atom 1))

#eval evalN 100 subj42 fmCellTest

/-! ## Demo 3: Cell test on a cell

`*[[1 2] [3 0 1]]` — the subject `[1 2]` is a cell, so the result is `0` (true / "is a cell").
-/

private def subjCell : Noun := .cell (.atom 1) (.atom 2)

#eval evalN 100 subjCell fmCellTest

/-! ## Demo 4: Quote

`*[42 [1 [5 6]]]` — opcode 1 is "quote", so it returns the tail of the formula literally: `[5 6]`.
-/

private def fmQuote : Noun := .cell (.atom 1) (.cell (.atom 5) (.atom 6))

#eval evalN 100 subj42 fmQuote

end

end Nock.NockVMROM.Thm54.TraceGen.Demo
