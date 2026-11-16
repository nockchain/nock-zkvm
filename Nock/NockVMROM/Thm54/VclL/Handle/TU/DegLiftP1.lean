/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/DegLiftP1.lean

 **Trace uniqueness on the P1 fragment: the degree lift and the absent / pad pieces.**

 * §1 the Lagrange lift: two polynomials of degree below `n` that agree at the `n` row nodes are equal; the column
 form (`cols_eq_of_rows`), and the table form under `DegOK`.
 * §2 `RowsEqP1`: two traces agree on every committed column of the four live tables at every row node.
 `tr_eq_of_rows`: under `DegOK` of both traces, `tr.V = 0` (E4) and the atom pad (E5), this is `tr = tr'`.
 The J table is `0` at `nJ = 0` by `DegOK` alone (E4, `trJ_zero_of_degOK`).
 * §3 the aux columns: `aux_eq_of_rows`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1

noncomputable section

open Nock Nock.Reified Nock.Framework Polynomial
open Nock.NockVMROM.Thm54.VclL.Handle
open Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8 (TrJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8 (PubJ8)
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1

/-! ## 1. The Lagrange lift -/

section Lift
variable {F : Type*} [Field F]

/-- Membership in the row-node set. -/
theorem mem_rowNodeSet' {n : ℕ} (nodes : Fin n → F) (x : F) :
    x ∈ rowNodeSet nodes ↔ ∃ i, nodes i = x := by
  classical
  unfold rowNodeSet
  simp

/-- The row-node set of an injective node family has `n` elements. -/
theorem card_rowNodeSet {n : ℕ} {nodes : Fin n → F} (hinj : Function.Injective nodes) :
    (rowNodeSet nodes).card = n := by
  classical
  unfold rowNodeSet
  rw [Finset.card_image_of_injective _ hinj]
  simp

/-- **The lift.** Two polynomials of degree `< n` that agree at the `n` row nodes are equal
(`Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq` over `rowNodeSet`). -/
theorem poly_eq_of_rows {n : ℕ} {nodes : Fin n → F} (hinj : Function.Injective nodes) {P Q : F[X]}
    (hP : P.degree < (n : WithBot ℕ)) (hQ : Q.degree < (n : WithBot ℕ))
    (h : ∀ i : Fin n, P.eval (nodes i) = Q.eval (nodes i)) : P = Q := by
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (rowNodeSet nodes) ?_ ?_
  · rw [card_rowNodeSet hinj]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le P Q) (max_lt hP hQ)
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_rowNodeSet' nodes x).mp hx
    exact h i

/-- The column form: two column families of degree `< n` agreeing at every row node of every column are equal. -/
theorem cols_eq_of_rows {n m : ℕ} {nodes : Fin n → F} (hinj : Function.Injective nodes) {P Q : Fin m → F[X]}
    (hP : ∀ j, (P j).degree < (n : WithBot ℕ)) (hQ : ∀ j, (Q j).degree < (n : WithBot ℕ))
    (h : ∀ j i, (P j).eval (nodes i) = (Q j).eval (nodes i)) : P = Q :=
  funext fun j => poly_eq_of_rows hinj (hP j) (hQ j) (h j)

/-- A column of degree `< 1` is a constant, so one row node determines it. -/
theorem poly_eq_of_one_row {nodes : Fin 1 → F} {P Q : F[X]}
    (hP : P.degree < ((1 : ℕ) : WithBot ℕ)) (hQ : Q.degree < ((1 : ℕ) : WithBot ℕ))
    (h : P.eval (nodes 0) = Q.eval (nodes 0)) : P = Q :=
  poly_eq_of_rows (fun a b _ => Subsingleton.elim a b) hP hQ fun i => by
    rw [Subsingleton.elim i 0]; exact h

end Lift

/-! ## 2. Rows equal, under `DegOK`, E4 and E5, give traces equal -/

section Traces
variable {p : ℕ} [Fact p.Prime]

/-- **Two traces agree on every row of the four live tables**: compute (`nodes`), cell (`nodesC`), walk
(`nodesW`) and atom (`nodesA`), every column of every round. -/
structure RowsEqP1 (Pb : PubJ8 p) (tr tr' : TrJ8 (ZMod p)) : Prop where
  C : ∀ j i, (tr.C j).eval (Pb.nodes i) = (tr'.C j).eval (Pb.nodes i)
  M : ∀ j i, (tr.M j).eval (Pb.nodesC i) = (tr'.M j).eval (Pb.nodesC i)
  W : ∀ j i, (tr.W j).eval (Pb.nodesW i) = (tr'.W j).eval (Pb.nodesW i)
  A : ∀ j i, (tr.A j).eval (Pb.nodesA i) = (tr'.A j).eval (Pb.nodesA i)

/-- **The extra pin (E4) (J)**: at `nJ = 0`, `DegOK` alone gives equal J tables (both are `0`). -/
theorem trJ_eq_of_degOK {Pb : PubJ8 p} {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (hd : DegOK Pb tr ax) (hd' : DegOK Pb tr' ax') (h0 : Pb.nJ = 0) : tr.J = tr'.J :=
  funext fun j => (trJ_zero_of_degOK hd h0 j).trans (trJ_zero_of_degOK hd' h0 j).symm

/-- **The extra pin (E4) (V)**: the pin `tr.V = 0` on both traces gives equal atom-walk tables. (At `nV = 1` this pin is
stronger than `DegOK`, which only makes each column a constant.) -/
theorem trV_eq_of_pin {tr tr' : TrJ8 (ZMod p)} (h : tr.V = fun _ => 0) (h' : tr'.V = fun _ => 0) :
    tr.V = tr'.V := h.trans h'.symm

/-- **The extra pin (E5)**: the atom pad row constants, round-0 columns `< 205`, agree on both traces. -/
theorem trA_round0_eq {tr tr' : TrJ8 (ZMod p)} (h : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j))
    (h' : ∀ j : Fin 349, (j : ℕ) < 205 → tr'.A j = Polynomial.C (padA j)) :
    ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = tr'.A j := fun j hj => (h j hj).trans (h' j hj).symm

/-- **The extra pin (E5), row form**: with the pad pin on both traces, the atom rows agree on all columns as soon as they agree on
the round-1 and round-2 columns `≥ 205`. -/
theorem rowsA_of_pad {Pb : PubJ8 p} {tr tr' : TrJ8 (ZMod p)}
    (h : ∀ j : Fin 349, (j : ℕ) < 205 → tr.A j = Polynomial.C (padA j))
    (h' : ∀ j : Fin 349, (j : ℕ) < 205 → tr'.A j = Polynomial.C (padA j))
    (hr : ∀ j : Fin 349, 205 ≤ (j : ℕ) → ∀ i, (tr.A j).eval (Pb.nodesA i) = (tr'.A j).eval (Pb.nodesA i)) :
    ∀ j i, (tr.A j).eval (Pb.nodesA i) = (tr'.A j).eval (Pb.nodesA i) := by
  intro j i
  by_cases hj : (j : ℕ) < 205
  · rw [h j hj, h' j hj]
  · exact hr j (by omega) i

/-- **The table lift.** Under `DegOK` of both traces, the pin `tr.V = 0` and `nJ = 0`, equal rows give equal
traces. The atom table needs no separate pad hypothesis: its row equality (round 0 included) is the input,
discharged by `rowsA_of_pad` from the pad pin. -/
theorem tr_eq_of_rows {Pb : PubJ8 p} {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (hd : DegOK Pb tr ax) (hd' : DegOK Pb tr' ax') (h0 : Pb.nJ = 0)
    (hV : tr.V = fun _ => 0) (hV' : tr'.V = fun _ => 0)
    (hinjC0 : Function.Injective Pb.nodes) (hinjC : Function.Injective Pb.nodesC)
    (hinjW : Function.Injective Pb.nodesW) (hinjA : Function.Injective Pb.nodesA)
    (hr : RowsEqP1 Pb tr tr') : tr = tr' := by
  obtain ⟨C, M, W, J, A, V⟩ := tr
  obtain ⟨C', M', W', J', A', V'⟩ := tr'
  have hJ := trJ_eq_of_degOK hd hd' h0
  have hV2 := trV_eq_of_pin hV hV'
  have hC := cols_eq_of_rows hinjC0 hd.C hd'.C hr.C
  have hM := cols_eq_of_rows hinjC hd.M hd'.M hr.M
  have hW := cols_eq_of_rows hinjW hd.W hd'.W hr.W
  have hA := cols_eq_of_rows hinjA hd.A hd'.A hr.A
  simp only at hJ hV2 hC hM hW hA
  subst hJ hV2 hC hM hW hA
  rfl

end Traces

/-! ## 3. The aux columns -/

section Aux
variable {p : ℕ} [Fact p.Prime]

/-- **The aux columns lift the same way**: under `DegOK` of both aux families, equal rows give equal aux. -/
theorem aux_eq_of_rows {Pb : PubJ8 p} {tr tr' : TrJ8 (ZMod p)} {ax ax' : AuxP1 (ZMod p)}
    (hd : DegOK Pb tr ax) (hd' : DegOK Pb tr' ax')
    (hinjC : Function.Injective Pb.nodesC) (hinjW : Function.Injective Pb.nodesW)
    (hM : ∀ j i, (ax.M j).eval (Pb.nodesC i) = (ax'.M j).eval (Pb.nodesC i))
    (hW : ∀ j i, (ax.W j).eval (Pb.nodesW i) = (ax'.W j).eval (Pb.nodesW i)) : ax = ax' := by
  obtain ⟨M, W⟩ := ax
  obtain ⟨M', W'⟩ := ax'
  have h1 := cols_eq_of_rows hinjC hd.auxM hd'.auxM hM
  have h2 := cols_eq_of_rows hinjW hd.auxW hd'.auxW hW
  simp only at h1 h2
  subst h1 h2
  rfl

end Aux

end

end Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1.poly_eq_of_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1.cols_eq_of_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1.trJ_eq_of_degOK
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1.rowsA_of_pad
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1.tr_eq_of_rows
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.DegLiftP1.aux_eq_of_rows
