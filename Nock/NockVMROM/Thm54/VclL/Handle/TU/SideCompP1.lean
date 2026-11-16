/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/SideCompP1.lean

 **Trace uniqueness on the P1 fragment: the compute side template for the round-1 free columns.**

 Two columns of the compute chip are unconstrained by the chip's gates, so two accepted traces with the same
 round-0 columns can differ there:
 * **E8** the slot inverses `inv_s` (columns `69 .. 92`) at a row where the slot is inactive: the slot gate reads
 `inv·0 = 0` and the accumulator term is `act·inv = 0`;
 * **E9** the compute walk's `wInv` (columns `120 .. 122`) at the last row: its only gate is scaled by `1 − isLast`.

 The side gates `(1 − A_s)·inv_{s,k} = 0` (`A_s` the slot's total activity) and `isLast·wInv_k = 0` pin them to `0`.
 `canonC2Gates` (degree `≤ 3`), `canonC2T` (one round, `123` base columns), `canonC2` the RAP over the compute rows and
 `sideC2Q` the side trace (`tr.C`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.T0Tower Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.ChipH Nock.NockVMROM.Thm54.VclL.Handle.ChipHX
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

section Gates
variable {F : Type} [Field F]

/-- The total activity of a slot: its entries' activities and its pair flag. -/
def actTotX (S : SlotX F) : CoeffExpr F :=
  .add (CoeffExpr.sumList S.ents EntX.act)
    (match S.pair with
     | some (fl, _, _, _) => cc fl
     | none => .const 0)

/-- **The extra pin (E8) for one slot**: `(1 − A)·inv` on the three limbs of the real and the imaginary inverse. -/
def e8Slot (S : SlotX F) : List (CoeffExpr F) :=
  ((List.range 3).map fun k => .mul (.sub (.const 1) (actTotX S)) (cc (S.inv + k))) ++
    ((List.range 3).map fun k => .mul (.sub (.const 1) (actTotX S)) (cc (S.invIm + k)))

/-- **The extra pin (E9)**: `isLast·wInv` on the three limbs. -/
def e9Gates : List (CoeffExpr F) := (List.range 3).map fun k => .mul (cc lastX) (cc (wInvX + k))

/-- **The compute side gates E8 and E9.** -/
def canonC2Gates : List (CoeffExpr F) := (ChipHX.slotsX (F := F)).flatMap e8Slot ++ e9Gates

theorem actTotX_deg (S : SlotX F) (h : ∀ x ∈ S.ents, x.act.degree ≤ 2) : (actTotX S).degree ≤ 2 := by
  have h1 := CoeffExpr.degree_sumList_le S.ents EntX.act 2 h
  unfold actTotX
  rcases hp : S.pair with _ | ⟨fl, a, b, bb⟩
  · simp only [CoeffExpr.degree, hp]; omega
  · simp only [CoeffExpr.degree, hp, cc]; omega

theorem e8Slot_deg (S : SlotX F) (h : ∀ x ∈ S.ents, x.act.degree ≤ 2) : ∀ g ∈ e8Slot S, g.degree ≤ 3 := by
  have h1 := actTotX_deg S h
  intro g hg
  simp only [e8Slot, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩ <;> simp only [CoeffExpr.degree, cc] <;> omega

/-- **Every side gate has degree `≤ 3`.** -/
theorem canonC2Gates_deg3 : ∀ g ∈ canonC2Gates (F := F), g.degree ≤ 3 := by
  intro g hg
  unfold canonC2Gates at hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨S, hS, hg⟩ := List.mem_flatMap.mp hg
    exact e8Slot_deg S (slotsX_act_deg S hS) g hg
  · simp only [e9Gates, List.mem_map] at hg
    obtain ⟨k, -, rfl⟩ := hg
    simp only [CoeffExpr.degree, cc]; omega

theorem canonC2Gates_deg : ∀ g ∈ canonC2Gates (F := F), g.degree ≤ 4 :=
  fun g hg => (canonC2Gates_deg3 g hg).trans (by norm_num)

/-- The compute side template: one round, `123` base columns. -/
def canonC2T : ChipTemplate F := sideT 123 canonC2Gates canonC2Gates_deg

theorem canonC2T_width : (canonC2T (F := F)).width 3 = 123 := sideT_width _ _ _

end Gates

section SideRAP
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  (b : Basis (Fin 3) (ZMod p) K)

/-- **`canonC2`** over the compute rows. -/
def canonC2 (Pb : PubJ8 p) : RAP (ZMod p) :=
  expandChip canonC2T b (fun _ => 0) (fun _ => 0) Pb.orbit (rowNodeSet Pb.nodes)

/-- The compute side trace: all `123` columns. -/
def sideC2Q (tr : TrJ8 (ZMod p)) : Fin ((canonC2T (F := ZMod p)).width 3) → (ZMod p)[X] := fun j =>
  tr.C ⟨j, by have := j.isLt; have h2 := canonC2T_width (F := ZMod p); omega⟩

end SideRAP

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1.canonC2Gates_deg3
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1.canonC2T_width
