/-
  Nock/NockVMROM/Thm54/VclL/Handle/J9AL/AluHonestTable.lean

  **The honest ALU table of a run.**

  * `pregRow_base`, `padRow_base`: every base gate at a preg / padding row against any successor with `sL = 0`
    (preg, hdr and padding rows all have `sL = 0`).
  * `callsLOf`: the run's primitive calls as `CallL`s (`ComplJ9ALData.pcallsR`, handles by the data's handle map
    `H`, the subject's cell serial, the registry index `idxPOf`).
  * `aluRowsB`: the honest base table = one preg row per called primitive, the blocks in call order, one padding
    row.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.AluHonestRows
import Nock.NockVMROM.Thm54.VclL.Handle.J9AL.ComplJ9ALData

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable

open Nock Nock.Reified
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestRows
open Nock.NockVMROM.Thm54.VclL.Handle.AxisChipJ9 (AG CopyG Op)
open Nock.Jet.Prim (PrimOp)

noncomputable section

/-! ## 1. Preg and padding rows -/

section Rows
variable {F : Type} [Field F]

/-- The base gates at a row whose kind/role/mode/flag/bit/counter columns are all `0` and whose successor has
`sL = 0`: every gate is `0` (each has a zero factor). -/
theorem quiet_base (r nxt : BRow F) (hH : r.sH = 0) (hL : r.sL = 0) (hop : ∀ i, r.op i = 0)
    (hro : ∀ i, r.role i = 0) (hmo : ∀ i, r.mode i = 0) (hfst : r.fst = 0) (heos : r.eos = 0) (hf1 : r.f1 = 0)
    (hf2 : r.f2 = 0) (hsf : r.sf = 0) (haV : r.aV = 0) (hcf1 : r.cf1 = 0) (hcf2 : r.cf2 = 0)
    (hbit : ∀ t, r.bit t = 0) (hcn : r.cn = 0) (hcb : ∀ i, r.cb i = 0) (hcA : r.cA = 0) (hcB : r.cB = 0)
    (hsP : r.sP = 0 ∨ r.sP = 1) (hlb : r.lb = 0) (hopc : r.opc = r.pOp) (hid : r.idc = r.pId) (hns : nxt.sL = 0) :
    ∀ a ∈ (AluSZChipJ9.baseAG : List (AG F)), (AG.gate a).eval (envB r.col nxt.col) = 0 := by
  have hb : ∀ t < 32, r.col (AluSZChipJ9.bt0 + t) = 0 := fun t ht => (BRow.col_bit r t ht).trans (hbit t)
  have hc : ∀ i < 6, r.col (AluSZChipJ9.cb0 + i) = 0 := fun i hi => (BRow.col_cb r i hi).trans (hcb i)
  have hbN : ∀ t < 32, r.col (34 + t) = 0 := hb
  have hcN : ∀ i < 6, r.col (86 + i) = 0 := hc
  have hc0 : r.col AluSZChipJ9.cb0 = 0 := by simpa using hc 0 (by norm_num)
  have hsP' : r.sP = 0 ∨ r.sP - 1 = 0 := by rcases hsP with h | h <;> simp [h]
  simp only [AluSZChipJ9.baseAG, AluSZChipJ9.gKind, AluSZChipJ9.gSlot, AluSZChipJ9.gSeq, AluSZChipJ9.gCompat,
    AluSZChipJ9.gFlag, AluSZChipJ9.gCoef, AluSZChipJ9.gHdr, AluSZChipJ9.gConst, AluSZChipJ9.gBind,
    AluSZChipJ9.gBits, AluSZChipJ9.gSplit, AluSZChipJ9.gCap, AluSZChipJ9.opCols, AluSZChipJ9.roleCols,
    AluSZChipJ9.modeCols, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map, List.mem_range,
    List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  simp (config := { contextual := true }) [AG.gate, AluSZChipJ9.ar, AluSZChipJ9.succ, AluSZChipJ9.coef,
    AluSZChipJ9.bind, CopyG.gate, Op.expr, CoeffExpr.eval, envB, AluSZChipJ9.prod3, boolE, notE,
    AluSZChipJ9.sumC, AluSZChipJ9.lE, AluSZChipJ9.lN, AluSZChipJ9.cnE, AluSZChipJ9.opCode,
    AluSZChipJ9.gHdrNotLast, AluSZChipJ9.gKS, AluSZChipJ9.gLtP, AluSZChipJ9.gSplitV, AluSZChipJ9.sgnLt,
    AluSZChipJ9.hzV, bitSum, CoeffExpr.eval_sumList, hH, hL, hop, hro, hmo, hfst, heos, hf1, hf2, hsf, haV, hcf1, hcf2, hcn,
    hcA, hcB, hlb, hopc, hid, hns, hbN, hcN, hb, hc, hc0, hsP', cv, nv, BRow.col_isFT, BRow.col_isLT]
  all_goals
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hc i (List.mem_range.mp hi), mul_zero]

/-- **The base gates at a preg row** (successor with `sL = 0`). -/
theorem pregRow_base (pid pcode pvc pm : ℕ) (nxt : BRow F) (hns : nxt.sL = 0) :
    ∀ a ∈ (AluSZChipJ9.baseAG : List (AG F)), (AG.gate a).eval (envB (pregRow pid pcode pvc pm).col nxt.col) = 0 :=
  quiet_base _ nxt rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ => rfl) rfl (fun _ => rfl) rfl rfl (Or.inr rfl) rfl rfl rfl hns

/-- **The base gates at a padding row** (successor with `sL = 0`). -/
theorem padRow_base (nxt : BRow F) (hns : nxt.sL = 0) :
    ∀ a ∈ (AluSZChipJ9.baseAG : List (AG F)), (AG.gate a).eval (envB (padRow : BRow F).col nxt.col) = 0 :=
  quiet_base _ nxt rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ => rfl) rfl (fun _ => rfl) rfl rfl (Or.inl rfl) rfl rfl rfl hns

end Rows

/-! ## 2. The `𝕂′` identities at quiet rows -/

section QRows
variable {F K : Type} [Field F] [Field K] [Algebra F K] [Fintype K] (δ : F)
  [Fact (¬ IsSquare (algebraMap F K δ))]

open Nock.NockVMROM.Thm54.T0Tower

theorem equiv_symm_zero : (Quad.equiv (algebraMap F K δ)).symm 0 = (0, 0) := by
  rw [Equiv.symm_apply_eq]
  exact (Quad.mk_zero' _).symm

theorem kvec_zero (j : ℕ) : kvec δ (QRow.zero : QRow (Quad (algebraMap F K δ))) j = 0 := by
  have h0 : (QRow.zero : QRow (Quad (algebraMap F K δ))).role (j - j % 2) = 0 := by
    unfold QRow.role QRow.zero; split_ifs <;> rfl
  simp only [kvec, h0, equiv_symm_zero]
  split_ifs <;> rfl

/-- **The `identQ` equations at a quiet row with zero `𝕂′` roles** (successor with `sL = 0`). -/
theorem quiet_ident (r nxt : BRow F) (hH : r.sH = 0) (hL : r.sL = 0) (hmo : ∀ i, r.mode i = 0)
    (hfst : r.fst = 0) (heos : r.eos = 0) (hf1 : r.f1 = 0) (hf2 : r.f2 = 0) (hns : nxt.sL = 0)
    (chal : ℕ → K) (nq : ℕ → K) :
    ∀ e ∈ AluSZChipJ9.identQ δ,
      e.ev δ ⟨kvec δ (QRow.zero : QRow (Quad (algebraMap F K δ))), nq, chal, fun _ => 0⟩ (envB r.col nxt.col) = 0 := by
  have hz : ∀ j, kvec δ (QRow.zero : QRow (Quad (algebraMap F K δ))) j = 0 := kvec_zero δ
  simp only [AluSZChipJ9.identQ, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  simp [AluSZChipJ9.qz, ev_scale, ev_sub, ev_add, ev_var, ev_base, ev_mul, CoeffExpr.eval, envB, notE,
    AluSZChipJ9.hz, AluSZChipJ9.hzV, AluSZChipJ9.sumC, CoeffExpr.eval_sumList, cv, nv, hH, hL, hmo, hfst, heos,
    hf1, hf2, hns, hz, liftQ, Quad.mk_zero']

end QRows

/-! ## 3. The run's calls and the honest table -/

section Run
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9ALData
open Nock.V1J8.Gen (idxOf hdN' tlN' atomV)

/-- **The run's primitive calls as `CallL`s**: from `pcallsR` (id, subject, result), the handle map `Hm`, the cell
list `cs` (subject serial, registry index `idxPOf`). -/
def callsLOf (cs : List Noun) (Hm : Noun → ℕ × ℕ) (prims : List (ℕ × PrimOp)) (pc : List (ℕ × Noun × Noun)) :
    List CallL :=
  pc.map fun x =>
    { op := opOf prims x.1, id := x.1, vc := idxPOf cs prims x.1, vS := idxOf cs x.2.1,
      kA := (Hm (hdN' x.2.1)).1, vA := (Hm (hdN' x.2.1)).2, kB := (Hm (tlN' x.2.1)).1,
      vB := (Hm (tlN' x.2.1)).2, kE := (Hm x.2.2).1, vE := (Hm x.2.2).2,
      a := atomV (hdN' x.2.1), b := atomV (tlN' x.2.1), c := atomV x.2.2 }

/-- **The preg rows**: one per called primitive `(id, op)`, multiplicity `c + 1` (the hdr consumes plus the
verifier's pin). -/
def pregsOf {F : Type} [Field F] (cs : List Noun) (prims : List (ℕ × PrimOp)) (ids : List ℕ) : List (BRow F) :=
  (primsC prims ids).map fun q =>
    pregRow q.1 (opIx q.2 + 1) (idxPOf cs prims q.1) (ids.count q.1 + 1)

/-- **The honest ALU base table**: preg rows, the blocks in call order, one padding row. -/
def aluRowsB {F : Type} [Field F] (p : ℕ) (pregs : List (BRow F)) (cls : List CallL) : List (BRow F) :=
  pregs ++ cls.flatMap (blockB p) ++ [padRow]

/-- **The honest `𝕂′` round-1 rows** (zero on preg / padding rows). -/
def aluRowsQ {Q : Type} [CommRing Q] (p : ℕ) (y : Q) (npreg : ℕ) (cls : List CallL) : List (QRow Q) :=
  List.replicate npreg QRow.zero ++ cls.flatMap (blockQ p y) ++ [QRow.zero]

end Run

end

end Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable

section Axioms
open Nock.NockVMROM.Thm54.VclL.Handle.AluHonestTable
#print axioms quiet_base
#print axioms pregRow_base
#print axioms padRow_base
#print axioms kvec_zero
#print axioms quiet_ident
end Axioms
