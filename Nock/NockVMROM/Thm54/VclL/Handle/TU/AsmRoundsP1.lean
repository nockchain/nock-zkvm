/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/AsmRoundsP1.lean

 **Trace uniqueness on the P1 fragment, assembly: rounds 1 and 2 of every table from the verifier's checks
 (steps 8, 9), and the row equality of the whole trace.**

 Setting: two accepted tuples `AcceptsJ8V δ b Pb Rg c χ M tr r g` and `… M' tr' r g` at one layout, claim and coin.

 * §1 the atom table: with the pad pin on both traces and the coin `y` nonzero, every atom column agrees at the
 row node and the publics `pubsA 0 .. 11` agree (`atom_rows_eq`), from `RoundsAtomP1`.
 * §2 the cell table: equal round-0 rows (`< 134`), `ValidityServed` tables and the seed `z ≠ 0` give every cell
 column and the publics `pubsC 0 .. 5` (`cell_rows_eq'`), from `RoundsCellP1.cell_rows_eq`.
 * §3 the J-8 walk: equal round-0 rows lift to equal round-0 polynomials under `DegOK` (`walk_round0_poly`); with
 equal round-1 label columns (`25 .. 96`) every walk column and the publics `pubsW 0 .. 7` agree
 (`walk_rows_eq'`), from `RoundsWalkP1`.
 * §4 the compute table: `Comp12P1`, the statement that equal round-0 compute columns give equal round-1/2 compute
 columns between two accepted traces with `canonC2` on both (the conclusion of the compute rounds lemma, taken
 here as a hypothesis), and the assembly of `RowsEqP1` (`rowsEq_of_round0`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsCellP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsWalkP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.RoundsAtomP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1
import Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRoundsP1

noncomputable section

open Nock Nock.Reified Nock.Framework Module Polynomial
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.CoordinateBasis Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.StrictExtension Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.VclL Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.FiniteIO Nock.NockVMROM.Thm54.SVFrame Nock.NockVMROM.Thm54.VclL.Handle.FrameVS
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8 qM qW qA)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8P (MsgJ8')
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V (AcceptsJ8V)
open Nock.NockVMROM.Thm54.VclL.Handle.VerJ8 (chalsMJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.ChalsAZJ8 (chalsAJ8Z)
open Nock.NockVMROM.Thm54.VclL.Handle.CellTwinKW (cellChipHQKW restrictHQKWCell)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1
open Nock.NockVMROM.Thm54.VclL.Handle.TU.SideCompP1

section Asm
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [FiniteDimensional (ZMod p) K]
  [Fintype K] [DecidableEq K] (δ : ZMod p) [Fact (¬ IsSquare (algebraMap (ZMod p) K δ))]
  (b : Basis (Fin 3) (ZMod p) K)
  [Algebra Nock.Atoms.Fp (Quad (algebraMap (ZMod p) K δ))]
  {Pb : PubJ8 p} {Rg : Nock.Jet.Registry} {c : P8PublicClaim} {χ : Coins frameJ8 K}
  {M M' : MsgJ8' p K δ} {tr tr' : TrJ8 (ZMod p)} {r : RowsJ8} {g : ℕ}

/-! ## 1. The atom table -/

/-- **The atom table is determined** (rounds 0, 1, 2 and the publics `0 .. 11`): the pad pin on both traces and
the atom table's coin `z′ = y` nonzero. -/
theorem atom_rows_eq (h : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h' : AcceptsJ8V δ b Pb Rg c χ M' tr' r g)
    (hpad : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j))
    (hpad' : ∀ j : Fin 349, (j : ℕ) < 205 → tr'.A j = Polynomial.C (padA j))
    (hy : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) ≠ 0) :
    (∀ j i, (tr.A j).eval (Pb.nodesA i) = (tr'.A j).eval (Pb.nodesA i)) ∧
      ∀ j < 12, M.pubsA j = M'.pubsA j :=
  ⟨RoundsAtomP1.atom_cols_eq δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) (A := tr.A) (A' := tr'.A)
      h.hsatA h'.hsatA hpad hpad' hy,
    RoundsAtomP1.atom_pubs_eq δ b Pb.hnA Pb.nodesA Pb.orbitA (chalsAJ8Z δ χ) (A := tr.A) (A' := tr'.A)
      h.hsatA h'.hsatA hpad hpad' hy⟩

/-! ## 2. The cell table -/

/-- **The cell table's rounds 1 and 2 and the publics `0 .. 5`** from equal round-0 rows, the two
`ValidityServed` tables and the seed `z ≠ 0`. -/
theorem cell_rows_eq' [Fact (ringChar (ZMod p)).Prime] [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
    (h : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h' : AcceptsJ8V δ b Pb Rg c χ M' tr' r g)
    (hq : 2 ^ 63 < ringChar (ZMod p))
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0)
    (hserved : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))))
    (hserved' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
        (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC))))
    (h0 : ∀ j : Fin 242, (j : ℕ) < 134 → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) :
    (∀ j i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)) ∧ ∀ j < 6, M.pubsC j = M'.pubsC j := by
  obtain ⟨hr, hp⟩ := RoundsCellP1.cell_rows_eq δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC M'.pubsC
    (GeneratedField.primeFieldElems_zmod p) hq hz (Q := qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC)
    (Q' := qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC) h.hsatC h'.hsatC h.hbindC h'.hbindC h.hinjC h.hadjC h.hnpC
    hserved hserved' (fun i j hj => h0 ⟨j, by omega⟩ hj i)
  exact ⟨fun j i => hr i j j.isLt, hp⟩

/-! ## 3. The J-8 walk -/

/-- **Round 0 of the walk as polynomials**: equal rows and `DegOK` on both traces. -/
theorem walk_round0_poly {ax ax' : AuxP1 (ZMod p)} (hinj : Function.Injective Pb.nodesW)
    (hd : DegOK Pb tr ax) (hd' : DegOK Pb tr' ax')
    (h0 : ∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) :
    ∀ j : Fin 166, (j : ℕ) < 25 → tr.W j = tr'.W j :=
  fun j hj => poly_eq_of_rows hinj (hd.W j) (hd'.W j) (h0 j hj)

/-- **The walk's rounds 1 and 2 and the publics `0 .. 7`** from equal round-0 polynomials and equal round-1
label columns (`25 .. 96`). -/
theorem walk_rows_eq' (h : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h' : AcceptsJ8V δ b Pb Rg c χ M' tr' r g)
    (h0 : ∀ j : Fin 166, (j : ℕ) < 25 → tr.W j = tr'.W j)
    (hr1 : ∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 →
      ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) :
    (∀ j i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) ∧ ∀ j < 8, M.pubsW j = M'.pubsW j :=
  ⟨RoundsWalkP1.walk_cols_eq δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) (W := tr.W) (W' := tr'.W)
      h.hsatW h'.hsatW h.hbindW h'.hbindW h.hinjW h.hadjW h0 hr1,
    RoundsWalkP1.walk_pubs_eq δ Pb.kroots b Pb.hnW Pb.nodesW Pb.orbitW (chalsMJ8 δ χ) (W := tr.W) (W' := tr'.W)
      h.hsatW h'.hsatW h.hbindW h'.hbindW h.hinjW h.hadjW h0 hr1⟩

/-! ## 4. The compute table and the whole trace -/

variable (Pb Rg c χ r g) in
/-- **`Comp12P1`: rounds 1 and 2 of the compute table are determined by round 0.** For any two accepted tuples at
the layout, claim and coin, with the compute side template `canonC2` satisfied by both traces, equal round-0
compute columns (`< 69`) at every row node give equal compute columns (all `123`) at every row node. This is the
conclusion of the compute rounds lemma (`RoundsCompP1`, being written separately); here it is a hypothesis. -/
def Comp12P1 : Prop :=
  ∀ (M M' : MsgJ8' p K δ) (tr tr' : TrJ8 (ZMod p)),
    AcceptsJ8V δ b Pb Rg c χ M tr r g → AcceptsJ8V δ b Pb Rg c χ M' tr' r g →
    (canonC2 b Pb).Satisfies (sideC2Q tr) → (canonC2 b Pb).Satisfies (sideC2Q tr') →
    (∀ j : Fin 123, (j : ℕ) < 69 → ∀ i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i)) →
    ∀ j i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i)

/-- **The whole trace's rows from round 0** (steps 8, 9): equal round-0 rows of the compute, cell and walk tables,
equal round-1 walk labels, and the atom table's pad pin give `RowsEqP1`, together with equal publics of the
cell, walk and atom tables. -/
theorem rowsEq_of_round0 [Fact (ringChar (ZMod p)).Prime]
    [Algebra (ZMod (ringChar (ZMod p))) (Quad (algebraMap (ZMod p) K δ))]
    {ax ax' : AuxP1 (ZMod p)}
    (h : AcceptsJ8V δ b Pb Rg c χ M tr r g) (h' : AcceptsJ8V δ b Pb Rg c χ M' tr' r g)
    (hd : DegOK Pb tr ax) (hd' : DegOK Pb tr' ax')
    (hC2 : (canonC2 b Pb).Satisfies (sideC2Q tr)) (hC2' : (canonC2 b Pb).Satisfies (sideC2Q tr'))
    (hpad : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j))
    (hpad' : ∀ j : Fin 349, (j : ℕ) < 205 → tr'.A j = Polynomial.C (padA j))
    (hcomp12 : Comp12P1 δ b Pb Rg c χ r g)
    (hq : 2 ^ 63 < ringChar (ZMod p))
    (hz : Quad.mk (algebraMap (ZMod p) K δ) (chalsMJ8 δ χ 2) (chalsMJ8 δ χ 3) ≠ 0)
    (hy : Quad.mk (algebraMap (ZMod p) K δ) (chalsAJ8Z δ χ 2) (chalsAJ8Z δ χ 3) ≠ 0)
    (hserved : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M.pubsC (qM δ b Pb tr (chalsMJ8 δ χ) M.pubsC))))
    (hserved' : ValidityServed (cellTableOf δ b Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
      (restrictHQKWCell δ b Pb.hnC Pb.nodesC Pb.orbitC (chalsMJ8 δ χ) M'.pubsC
        (qM δ b Pb tr' (chalsMJ8 δ χ) M'.pubsC))))
    (h0C : ∀ j : Fin 123, (j : ℕ) < 69 → ∀ i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i))
    (h0M : ∀ j : Fin 242, (j : ℕ) < 134 → ∀ i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i))
    (h0W : ∀ j : Fin 166, (j : ℕ) < 25 → ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i))
    (hr1 : ∀ j : Fin 166, 25 ≤ (j : ℕ) → (j : ℕ) < 97 →
      ∀ i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)) :
    RowsEqP1 Pb tr tr' ∧ (∀ j < 6, M.pubsC j = M'.pubsC j) ∧ (∀ j < 8, M.pubsW j = M'.pubsW j) ∧
      (∀ j < 12, M.pubsA j = M'.pubsA j) := by
  obtain ⟨hA, pA⟩ := atom_rows_eq δ b h h' hpad hpad' hy
  obtain ⟨hM, pC⟩ := cell_rows_eq' δ b h h' hq hz hserved hserved' h0M
  obtain ⟨hW, pW⟩ := walk_rows_eq' δ b h h' (walk_round0_poly h.hinjW hd hd' h0W) hr1
  exact ⟨⟨hcomp12 M M' tr tr' h h' hC2 hC2' h0C, hM, hW, hA⟩, pC, pW, pA⟩

end Asm

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRoundsP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRoundsP1.atom_rows_eq
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRoundsP1.cell_rows_eq'
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRoundsP1.walk_round0_poly
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRoundsP1.walk_rows_eq'
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRoundsP1.rowsEq_of_round0
