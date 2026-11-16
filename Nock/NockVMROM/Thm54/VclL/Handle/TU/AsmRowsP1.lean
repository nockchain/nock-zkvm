/-
 Nock/NockVMROM/Thm54/VclL/Handle/TU/AsmRowsP1.lean

 **Trace uniqueness on the P1 fragment, assembly: the fragment predicate and the publics (steps 0, 1).**

 * §1 the bridge between the statement's syntactic fragment `opsB` (the placeholder `OpsP1`) and the inductive
 `GenX.P1Frag`: `p1Frag_of_opsB`, `opsB_of_p1Frag`, `opsP1_iff_p1Frag`. So the claim-level
 fragment `P1FragC` gives `P1Frag c.formula`, which is what `GenXDet.genuineNX_eq_genX` and
 `RowBridgeP1.rowBridge` take.
 * §2 step 0, the publics: at `Pb = canonPb …` the J table and the atom walk are absent (`nJ = 0`,
 `krootsV = 0`), the atom table has one row, the registry is empty.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
import Nock.Edit.GenXDet

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRowsP1

open Nock
open Nock.NockVMROM.Thm54.VclL.Handle.TU.StatementP1
open Nock.Edit.GenX (P1Frag)

/-! ## 1. `opsB` and `P1Frag` -/

/-- **`opsB f = true` gives `P1Frag f`**, by the recursion of `opsB`. -/
theorem p1Frag_of_opsB (f : Noun) (h : opsB f = true) : P1Frag f := by
  fun_induction opsB f with
  | case1 a b y ih1 ih2 =>
    simp only [Bool.and_eq_true] at h
    exact P1Frag.cons (ih1 h.1) (ih2 h.2)
  | case2 ax => exact P1Frag.op0 ax
  | case3 b c ih1 ih2 =>
    simp only [Bool.and_eq_true] at h
    exact P1Frag.op7 (ih1 h.1) (ih2 h.2)
  | case4 ax d e ih1 ih2 =>
    simp only [Bool.and_eq_true] at h
    exact P1Frag.op10 (ih1 h.1) (ih2 h.2)
  | case5 x hx1 hx2 hx3 hx4 =>
    exact absurd h (by decide)

/-- **`P1Frag f` gives `opsB f = true`.** -/
theorem opsB_of_p1Frag {f : Noun} (h : P1Frag f) : opsB f = true := by
  induction h with
  | op0 ax => simp [opsB]
  | op7 _ _ ih1 ih2 => simp only [opsB, ih1, ih2, Bool.and_self]
  | op10 _ _ ih1 ih2 => simp only [opsB, ih1, ih2, Bool.and_self]
  | cons _ _ ih1 ih2 => simp only [opsB, ih1, ih2, Bool.and_self]

/-- **The placeholder is the P1 fragment's fragment.** -/
theorem opsP1_iff_p1Frag (f : Noun) : OpsP1 f ↔ P1Frag f :=
  ⟨p1Frag_of_opsB f, opsB_of_p1Frag⟩

/-- The claim-level fragment gives `P1Frag` of the claim formula. -/
theorem P1FragC.p1Frag {c : P8PublicClaim} (h : P1FragC c) : P1Frag c.formula :=
  (opsP1_iff_p1Frag _).mp h.ops

/-! ## 2. Step 0: the publics of the canonical layout -/

section Pub
variable {p : ℕ} [Fact p.Prime]

/-- **Step 0.** At `Pb = canonPb …`: `nJ = 0`, `nA = nV = 1`, `krootsV = 0`, no registered template. -/
theorem step0_publics {hpG : p = Nock.Atoms.p} {sz : P8PublicClaim → SizesP1} {c : P8PublicClaim}
    {Pb : NockVMROM.Thm54.VclL.Handle.AcceptsJ8.PubJ8 p} (hPb : Pb = canonPb hpG sz c) :
    Pb.nJ = 0 ∧ Pb.nA = 1 ∧ Pb.nV = 1 ∧ Pb.krootsV = 0 ∧ Pb.regs = [] ∧ Pb.ids = [] := by
  subst hPb
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := canonPb_consts hpG sz c
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Pub

end Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRowsP1

#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRowsP1.p1Frag_of_opsB
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRowsP1.opsB_of_p1Frag
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRowsP1.opsP1_iff_p1Frag
#print axioms Nock.NockVMROM.Thm54.VclL.Handle.TU.AsmRowsP1.step0_publics
