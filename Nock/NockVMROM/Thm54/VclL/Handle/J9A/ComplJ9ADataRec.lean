/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9A/ComplJ9ADataRec.lean

* **`j9aDataOf p Rg Rt hgen : J8Data p Rg fuel s f r`**: J-9 B's `j9DataOf` (= `j8DataOf` with the claim-bumped
    `mb`) with the walk data overridden:
    - `reads` := `readsA t` = `walkReadsX9 rows9 ++ axChainReads9 rows9` (the J-9 A cell-walk reads), `ws kr` :=
      `walkGen` on them (as `j8DataOf`), `mx` := `mxCounts cells ws` (the cell walk's root consumes);
    - `preads` := `preadsA` = `DD.preads ++ axReads9 p rows9` (the J-9 A atom-walk reads: the J-8 pair reads and
      the big axis atoms' limb reads), `vs krV` := `walkGen padN` on them (empty when there are none, as
      `j8DataOf`), `mxA mhA` := `wCounts (rIAP p acs) acs vs` (as `j8DataOf`).
    - KEPT: `t rows Rt calls ids regs jn idx rk lay roots cells bigs dupP acs H pd bases jrows mv info` (`j8DataOf`'s,
      `rfl`: `j9aDataOf_*`), `mb` (J-9 B's `mbX DD [s, f, r]`).
    - `mh`: `mhJP (mhCountsX9 cells (basesA9 …) ws) jrows`, the J-8 formula with the twin compute's
      `.x` consumes (`xConsumesX9` over `slotsX9` at the twin base columns `basesA9`) and the J-9 A walk rows `ws`.
      J-8's `mh` counted the J-8 compute rows' consumes and the J-8 walk rows, so it disagreed with the J-9 A
      consumers (`s0B` / `s10B` cell consumes, the segment tries of the cell walk): `hGx` needs this value.
  * Why `mb`, `bases` are not recomputed here (and why the old `mh` was harmless for acceptance): the cell table's acceptance takes ANY handle multiplicity
    (`cellChipHQKW_honest_listE` is generic in `mhF`), the J-8 walk's and the atom walk's acceptance read no
    multiplicity of the tables they consume from, and the atom table's acceptance reads `mb` only through
    `GenHyp.mb` (nonzero entries sit at big roots; `ComplJ9BAtom.atomOK_mb`), which J-9 B's `mbX` meets.
  * Read-backs: `cells acs bigs H roots info rows dupP` unchanged (`rfl`); **`walkDepthOK_readsA`** (from `hwalk9`)
    and **`walkDepthOK_preadsA`** (from J-9 B's `hwalkA` and `hax9`): the two `WalkDepthOK` facts the walk / atom
    walk acceptance consume.  Neither acceptance reads root membership of the reads (only `WalkDepthOK` and the row
    bound), so no root lemma is needed for M2/M3.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AData
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChainsRun
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.HonestTraceX9

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec

open Nock Nock.Walk Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ8Data (J8Data j8DataOf rowsOfT rIAP)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ABinders (ProgAxOK9A WalkDepthOK9A)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (rowsOfT9)

noncomputable section

/-! ## 1. The record -/

section Def
variable (p : ℕ) [Fact p.Prime] (Rg : Nock.Jet.VerifiedRegistry) (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

/-- **The J-9 A cell-walk reads**: J-8's routed reads and the `s10S` pairs (`walkReadsX9`), plus the axis chains'
segment reads (`axChainReads9`). -/
def readsA (t : NTree SkelX) : List (Noun × ℕ) :=
  ComplJ9AReads.walkReadsX9 (rowsOfT9 t) ++ ComplJ9AChainsRun.axChainReadsK9 (rowsOfT9 t)

/-- **The J-9 A atom-walk reads**: the J-8 pair reads and the big axis atoms' limb reads (balanced: once per
chain key and per `s10B` row). -/
def preadsA : List (Noun × ℕ) :=
  (j8DataOf p Rg Rt hgen).preads ++ ComplJ9AChainsRun.axReadsK9 p (rowsOfT9 t)

/-- **The twin compute chip's handle-export consumes at one row's environment** (`ComplJ8Data.xConsumesP` over the
twin slots `ChipHX9.slotsX9`: every active `.x` entry consumes the handle at its record's first column, with the
entry's activity as multiplicity).  The twin adds `s0B`'s formula-cell consume and `s10B`'s three cell consumes. -/
def xConsumesX9 (e : Nock.Reified.Env (ZMod p)) : List (ℕ × ℕ) :=
  (ChipHX9.slotsX9 (F := ZMod p)).flatMap fun S =>
    (S.ents.filter fun x => decide (x.bal = ChipHX.Bal.x)).filterMap fun x =>
      let a := (x.act.eval e).val
      if a = 0 then none
      else match x.rcd with
        | ChipHX.RE.col i :: _ => some ((e.trace i).val, a)
        | _ => none

/-- **The J-9 A handle multiplicity before the J reads** (`ComplJ8Data.mhCountsP` with the twin consumes): the twin
compute's export consumes plus one per cell-walk row at a cell. -/
def mhCountsX9 (cs : List Noun) (bs : List (ℕ → ZMod p)) (ws : List Nock.V1J8.Gen.WRow) : Array ℕ :=
  let a := bs.foldl (fun a b => (xConsumesX9 p (⟨b, b, fun _ => 0, fun _ => 0⟩ : Nock.Reified.Env (ZMod p))).foldl
    (fun a q => Nock.V1J8.Gen.bump a q.1 q.2) a) (Array.replicate cs.length 0)
  ws.foldl (fun a w => match w.node with
    | .cell _ _ => Nock.V1J8.Gen.bump a (Nock.V1J8.Gen.idxOf cs w.node) 1
    | .atom _ => a) a

/-- **The twin compute rows' base columns** (chip row `j`'s stage-1 columns `HonestTraceX9.baseT9`, `j < |W|`). -/
def basesA9 (H : Noun → ℕ × ℕ) (pd : RowNX → ℕ × (ℕ × ℕ) × (ℕ × ℕ)) (idOf : ℕ → ℕ) (W : List (NTree ComplJ9AGen.LX9)) :
    List (ℕ → ZMod p) :=
  (List.range W.length).map fun j => HonestTraceX9.baseT9 (F := ZMod p) H pd idOf W j

/-- **The J-9 A honest data of a run** (option B): J-9 B's `j9DataOf` with the cell-walk and atom-walk reads, their
walk rows / root counts and the walk multiplicities `mx mxA mhA` recomputed, and the cell handle multiplicity `mh`
recomputed at the twin compute's `.x` consumes and the J-9 A cell walk. -/
def j9aDataOf : J8Data p Rg fuel s f r :=
  let D := ComplJ9BOf.j9DataOf p Rg Rt hgen
  let wg := Nock.V1J8.Gen.walkGen (D.cells.headD (.atom 0)) (readsA t)
  let vg : List Nock.V1J8.Gen.WRow × ℕ :=
    if (preadsA p Rg Rt hgen).isEmpty then ([], 0) else Nock.V1J8.Gen.walkGen Nock.V1J8.Gen.padN (preadsA p Rg Rt hgen)
  { D with
    reads := readsA t
    ws := wg.1
    kr := wg.2
    preads := preadsA p Rg Rt hgen
    vs := vg.1
    krV := vg.2
    mx := Nock.V1J8.Gen.mxCounts D.cells wg.1
    mxA := Nock.V1J8.Gen.wCounts (rIAP p D.acs) D.acs vg.1
    mhA := Nock.V1J8.Gen.wCounts (rIAP p D.acs) D.acs vg.1
    mh := ComplJ8Data.mhJP p (mhCountsX9 p D.cells
      (basesA9 p D.H D.pd (ComplJ9AChains.idOf9 p D.acs.length D.H (ComplJ9AData.fieldAx9 p (rowsOfT9 t)))
        (bfsForest [ComplJ9AGen.genX9T t])) wg.1) D.jrows }

end Def

/-! ## 2. Read-backs -/

section Back
variable {p : ℕ} [Fact p.Prime] {Rg : Nock.Jet.VerifiedRegistry} (Rt : ℕ → Nock.Jet.Autogen.Tpl) {fuel : ℕ}
  {s f r : Noun} {t : NTree SkelX} (hgen : genX Rg.R fuel s f = some (t, r))

local notation "DD" => j8DataOf p Rg Rt hgen
local notation "DA" => j9aDataOf p Rg Rt hgen

theorem j9aDataOf_t : (DA).t = t := rfl
theorem j9aDataOf_rows : (DA).rows = (DD).rows := rfl
theorem j9aDataOf_roots : (DA).roots = (DD).roots := rfl
theorem j9aDataOf_cells : (DA).cells = (DD).cells := rfl
theorem j9aDataOf_bigs : (DA).bigs = (DD).bigs := rfl
theorem j9aDataOf_dupP : (DA).dupP = (DD).dupP := rfl
theorem j9aDataOf_acs : (DA).acs = (DD).acs := rfl
theorem j9aDataOf_H : (DA).H = (DD).H := rfl
theorem j9aDataOf_pd : (DA).pd = (DD).pd := rfl
theorem j9aDataOf_info : (DA).info = (DD).info := rfl
theorem j9aDataOf_jrows : (DA).jrows = (DD).jrows := rfl
theorem j9aDataOf_mv : (DA).mv = (DD).mv := rfl
theorem j9aDataOf_mh : (DA).mh = ComplJ8Data.mhJP p (mhCountsX9 p (DD).cells
    (basesA9 p (DD).H (DD).pd (ComplJ9AChains.idOf9 p (DD).acs.length (DD).H (ComplJ9AData.fieldAx9 p (rowsOfT9 t)))
      (bfsForest [ComplJ9AGen.genX9T t])) (DA).ws) (DD).jrows := rfl
theorem j9aDataOf_bases : (DA).bases = (DD).bases := rfl
theorem j9aDataOf_mb : (DA).mb = ComplJ9BAtom.mbX (DD) [s, f, r] := rfl
theorem j9aDataOf_reads : (DA).reads = readsA t := rfl
theorem j9aDataOf_preads : (DA).preads = (DD).preads ++ ComplJ9AChainsRun.axReadsK9 p (rowsOfT9 t) := rfl

/-- **`WalkDepthOK` of the J-9 A cell-walk reads** (from the J-9 A binder `hwalk9` alone). -/
theorem walkDepthOK_readsA (hwalk9 : WalkDepthOK9A (rowsOfT t)) : ComplJ8Walk.WalkDepthOK (DA).reads :=
  ComplJ9AData.walkDepthOK_append (ComplJ9AReads.walkDepthOK_X9 hgen hwalk9)
    (ComplJ9AChainsRun.walkDepthOK_axChainReadsK9 _)

/-- **`WalkDepthOK` of the J-9 A atom-walk reads** (from J-9 B's `hwalkA` on the J-8 pair reads and the J-9 A
binder `hax9`). -/
theorem walkDepthOK_preadsA (hax9 : ProgAxOK9A p t) (hwalkA : ComplJ8Walk.WalkDepthOK (DD).preads) :
    ComplJ8Walk.WalkDepthOK (DA).preads :=
  ComplJ9AData.walkDepthOK_append hwalkA (ComplJ9AChainsRun.walkDepthOK_axReadsK9 hgen hax9)

/-- The cell list is non-empty. -/
theorem cellsA_pos [Fact (ringChar (ZMod p)).Prime] : 0 < (DA).cells.length := ComplJ8Of.cells_pos Rt hgen

/-- The atom cell list is non-empty. -/
theorem acsA_pos [Fact (ringChar (ZMod p)).Prime] : 0 < (DA).acs.length := ComplJ8Of.acs_pos Rt hgen

end Back

end

end Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ADataRec
#print axioms j9aDataOf
#print axioms j9aDataOf_cells
#print axioms j9aDataOf_acs
#print axioms j9aDataOf_mb
#print axioms walkDepthOK_readsA
#print axioms walkDepthOK_preadsA
#print axioms cellsA_pos
#print axioms acsA_pos
end Axioms
