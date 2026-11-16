/-
  Nock/RedTeam/Batch2040Thm54VSHandleChip.lean

  1. **Width** (`rfl`): `70 = 14 + 5 + 24 + 9 + 6 + 12` (VERDICT §3 target ≈ 76, cap 91).
  2. **Degree `≤ 4`** for every gate (`gatesH_degree`, kernel `decide` on the closed `ℚ`-template
     plus `mixedCompile_degree_le`); the tuple `(e, w, s, d, k) = (3, 70, SH, 4, 2)`.
  3. Every other base gate is
     serial-free.  Positive controls: the instrument flags a successor on handle values, a serial
     product, an inverse of a serial difference, and a serial inside a selector; and it does see the
     real serial reads (OP1's `e = f_t`, slot 0's key).
  4. **Lookup activity by state**: slots active `[2,1,2,2,1,3,3,2,3,3,2]`, records consumed
     `[2,1,2,2,1,4,3,2,3,3,2]` (OP0 … OP9, cons); at most one entry per slot per state.  OP5 consumes
     4 records (L1, L2 and the batched first-difference READ PAIR) through 3 slots.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.ChipH

set_option autoImplicit false

namespace Nock.RedTeam.Batch2040

open Nock Nock.Reified Module
open Nock.NockVMROM.Thm54.CoordinateCompiler Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH
open Nock.NockVMROM.Thm54.StrictExtension Nock.Framework

/-! ## 1. Width -/

theorem width_receipt : widthH = 70 ∧ widthH = 14 + 5 + 12 * 2 + 3 * 3 + 2 * 3 + 4 * 3 ∧
    widthH ≤ 91 := ⟨rfl, rfl, by decide⟩

theorem rap_tuple {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] {h : ℕ}
    (b : Basis (Fin 3) F K) (chalV pubVal : ℕ → F) (orbit : StrictOrbitDomain F 3 h) (H : Finset F) :
    (vclRAPH b chalV pubVal orbit H).w = 70 ∧ (vclRAPH b chalV pubVal orbit H).d = 4 ∧
      (vclRAPH b chalV pubVal orbit H).k = 2 ∧ (vclRAPH b chalV pubVal orbit H).e = 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Gate count** `s = 119 + 3 · 12 = 155` (52 arithmetic, 18 accumulator, 49 equality base gates;
3 slot + 9 walk `𝕂` gates, 3 coordinates each). -/
theorem gatesH_length {F K : Type} [Field F] [Field K] [Algebra F K] (b : Basis (Fin 3) F K) :
    (gatesH b).length = 155 := by
  have h1 : (baseGatesH (F := ℚ)).length = 119 := by decide +kernel
  have h2 : (kGatesH (F := ℚ)).length = 12 := by decide +kernel
  have h3 : ((arithGates (F := ℚ)).length, (accGatesH (F := ℚ)).length, (eqGates (F := ℚ)).length)
      = (52, 18, 49) := by decide +kernel
  clear h3
  simp only [gatesH, baseGatesF, kGatesF, List.length_append, List.length_map, List.length_flatMap,
    List.length_ofFn, h1, List.map_map, Function.comp_def, List.map_const', List.sum_replicate, h2]
  rfl

/-! ## 2. Degree -/

theorem degree_receipt {F K : Type} [Field F] [Field K] [Algebra F K] (b : Basis (Fin 3) F K) :
    ∀ g ∈ gatesH b, g.degree ≤ 4 := gatesH_degree b

/-! ## 3. Read set -/

theorem arith_serial_free : ((arithGates (F := ℚ)).all serialFreeB) = true := by decide +kernel
theorem acc_serial_free : ((accGatesH (F := ℚ)).all serialFreeB) = true := by decide +kernel
theorem eq_selectors_serial_free : ((eqGates (F := ℚ)).all EqG.okB) = true := by decide +kernel
theorem eq_operands_are_columns :
    ((eqGates (F := ℚ)).all fun g => match g.y with | .col _ => true | .cst _ => true | .pub _ => true)
      = true := by decide +kernel
theorem k_gates_key_only : ((kGatesH (F := ℚ)).all keyOK) = true := by decide +kernel

/-- Constant transport does not change the columns read. -/
theorem colsOf_mapC {F G : Type} [Field F] [Field G] (φ : G → F) (g : CoeffExpr G) :
    colsOf (mapC φ g) = colsOf g := by
  induction g with
  | const c => rfl
  | var k i => cases k <;> rfl
  | add a b iha ihb => simp only [mapC, colsOf, iha, ihb]
  | sub a b iha ihb => simp only [mapC, colsOf, iha, ihb]
  | mul a b iha ihb => simp only [mapC, colsOf, iha, ihb]
  | neg a iha => simp only [mapC, colsOf, iha]
  | pow a n iha => simp only [mapC, colsOf, iha]

/-- **Read-set receipt.**  The chip's base gates over any `F` are the template's
`arithGates ++ accGatesH` (serial-free) followed by the equality tests (serial-free selectors);
its `𝕂` gates are the template's, whose serial reads are key entries only. -/
theorem readset_receipt {F : Type} [Field F] :
    (baseGatesF : List (CoeffExpr F)) =
      ((arithGates (F := ℚ)) ++ accGatesH ++ (eqGates (F := ℚ)).map EqG.gate).map
        (mapC (fun q : ℚ => (q : F))) ∧
    (∀ g ∈ (arithGates (F := ℚ)) ++ accGatesH, serialFreeB (mapC (fun q : ℚ => (q : F)) g) = true) ∧
    ((eqGates (F := ℚ)).all EqG.okB) = true ∧ ((kGatesH (F := ℚ)).all keyOK) = true := by
  refine ⟨rfl, ?_, eq_selectors_serial_free, k_gates_key_only⟩
  intro g hg
  have h : serialFreeB g = true := by
    rcases List.mem_append.mp hg with h | h
    · exact List.all_eq_true.mp arith_serial_free g h
    · exact List.all_eq_true.mp acc_serial_free g h
  simpa [serialFreeB, colsOf_mapC] using h

/-! ### Positive controls: the instrument discriminates -/

/-- OP4's successor written directly on handle values (forbidden: successor on a serial-capable
column) — flagged. -/
theorem pc_successor_on_handles :
    serialFreeB (F := ℚ) (.mul (cc 4) (.sub (.sub (cc hE.v) (cc hSf1.v)) (.const 1))) = false := by
  decide +kernel

/-- OP5 "≠" by an inverse of the SERIAL difference (forbidden) — flagged. -/
theorem pc_inverse_of_serial_difference :
    serialFreeB (F := ℚ) (.mul (.sub (cc hSf1.v) (cc hSf2.v)) (cc wC)) = false := by decide +kernel

/-- A serial inside an equality's selector (an ordering / mux on a serial) — flagged. -/
theorem pc_serial_selector : EqG.okB (F := ℚ) ⟨cc hSf1.v, hE.v, .col hSf2.v⟩ = false := by
  decide +kernel

/-- A `𝕂` gate multiplying two lifted serials (arithmetic, not a key entry) — flagged. -/
theorem pc_serial_product_in_K :
    keyOK (F := ℚ) (.Mul (.Lift (cc hSf1.v)) (.Lift (cc hSf2.v))) = false := by decide +kernel

/-- The instrument SEES the real serial reads: OP1's equality `e = f_t` reads the handle values
(so it passes only by the equality rule), and slot 0's gate reads `f.val` (a key entry). -/
theorem pc_sees_real_reads :
    serialFreeB (F := ℚ) (EqG.gate ⟨cc 1, hE.v, .col hFt.v⟩) = false ∧
    ((eqGates (F := ℚ)).any fun g => serialFreeB g.gate == false) = true ∧
    (cellRec hF hFh hFt).contains hF.v = true ∧ serialCols.contains hF.v = true := by
  decide +kernel

/-! ## 4. Lookup activity by state -/

/-- Slots active in state `st` (upper bound: OP0 / OP9 reads count even when `z1 = 1`). -/
def activeSlots (st : ℕ) : ℕ :=
  (slots (F := ℚ)).countP fun S =>
    S.ents.any (fun x => x.states.contains st) || (S.pair.isSome && S.pairStates.contains st)

/-- Records consumed in state `st` (a read pair counts `2`). -/
def recordsAt (st : ℕ) : ℕ :=
  ((slots (F := ℚ)).map fun S =>
    (S.ents.filter fun x => x.states.contains st).length +
      (if S.pair.isSome && S.pairStates.contains st then 2 else 0)).sum

theorem lookup_count_receipt :
    allStates.map activeSlots = [2, 1, 2, 2, 1, 3, 3, 2, 3, 3, 2] ∧
    allStates.map recordsAt = [2, 1, 2, 2, 1, 4, 3, 2, 3, 3, 2] ∧
    (allStates.all fun st => decide (activeSlots st ≤ 3)) = true ∧
    ((slots (F := ℚ)).all fun S => allStates.all fun st =>
      decide ((S.ents.filter fun x => x.states.contains st).length +
        (if S.pair.isSome && S.pairStates.contains st then 1 else 0) ≤ 1)) = true := by
  decide +kernel

/-- The pair flag lives on `s5` only: its defining gate `pr − s5·β·(1 − z1)` is a chip gate. -/
theorem pair_flag_defined {F : Type} [Field F] : (prGate : CoeffExpr F) ∈ arithGates := by
  simp [arithGates]

/-! ## 5. NC: OP5 "≠" is never by serial inequality -/

/-- On an OP5 "≠" row with both first-difference leaves cells (whatever their serials), the
both-cells gate does not vanish: it evaluates to `1`. -/
theorem nc_op5_ne_both_cells {F : Type} [Field F] (env : Env F)
    (h5 : env.trace 5 = 1) (hb : env.trace betaC = 1) (h1 : env.trace hFtth.k = 1)
    (h2 : env.trace hFttt.k = 1) :
    (mapC (fun q : ℚ => (q : F)) (prodL [cc 5, cc betaC, cc hFtth.k, cc hFttt.k])).eval env = 1 := by
  simp only [prodL, List.foldr, mapC, cc, CoeffExpr.eval]
  rw [h5, hb, h1, h2]
  simp

end Nock.RedTeam.Batch2040

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ChipH.gatesH_degree
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.ChipH.computeChipVCLH
#print axioms Nock.RedTeam.Batch2040.width_receipt
#print axioms Nock.RedTeam.Batch2040.rap_tuple
#print axioms Nock.RedTeam.Batch2040.gatesH_length
#print axioms Nock.RedTeam.Batch2040.degree_receipt
#print axioms Nock.RedTeam.Batch2040.readset_receipt
#print axioms Nock.RedTeam.Batch2040.pc_successor_on_handles
#print axioms Nock.RedTeam.Batch2040.pc_inverse_of_serial_difference
#print axioms Nock.RedTeam.Batch2040.pc_serial_selector
#print axioms Nock.RedTeam.Batch2040.pc_serial_product_in_K
#print axioms Nock.RedTeam.Batch2040.pc_sees_real_reads
#print axioms Nock.RedTeam.Batch2040.lookup_count_receipt
#print axioms Nock.RedTeam.Batch2040.pair_flag_defined
#print axioms Nock.RedTeam.Batch2040.nc_op5_ne_both_cells
