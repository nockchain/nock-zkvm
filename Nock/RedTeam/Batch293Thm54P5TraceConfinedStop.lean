/-
  Nock/RedTeam/Batch293Thm54P5TraceConfinedStop.lean

  `TraceConfined Λ t` (`GenTraceConfined.lean::TraceConfined`) is

      ∀ g ∈ bfsRows t, RowNounsConfined Λ g

  with `RowNounsConfined Λ g` the three comparisons
  `subject.leaves ≤ Λ ∧ formula.leaves ≤ Λ ∧ evaluation.leaves ≤ Λ`.
  It is the generator-side image of `λ ≤ Λ` on `NockProgram^Λ` and `FiniteTransitions^Λ` (`:1147`).

  That pattern does not generalise to 401 Goldilocks rows:
  `decide` does not reduce at `GaloisField Field.p 3`, there is no
  `mm_air_bfsRows`, and `genComputeSkeleton_subISA_traceConfined`
  excludes OP7/OP9, both present in the matmul program text (`slam` /
  `invokeAxis`).

  `SeedGood` is **not** vacuous: `mmTree` root is `cons`
  (`mmTree_root_is_cons`).  The 769 `dot_seedGood` path does not copy.
  `hbad` / `hout` are not reached.  No new `∀` premise and no new
  failure-event summand.  No `nockCompiles` instance.
-/
import Nock.Field
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulConfigGoldilocks
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulLeafBound
import Nock.NockVMROM.Thm54.TraceGen.GenLeafWindow
import Nock.NockVMROM.Thm54.TraceGen.GenTraceConfined
import Nock.NockVMROM.Thm54.TraceGen.GenSubISAWindow
import Nock.NockVMROM.Thm54.TraceGen.GenDyckBadSeed

set_option autoImplicit false

namespace Nock.RedTeam.Batch293

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.TraceGen.MatmulConfigGoldilocks
open ComputeTable

abbrev GK := MatmulConfigGoldilocks.K

/-! ## 1. What `TraceConfined` is. -/

theorem b293_type (Λ : ℕ) (t : NTree (GenComputeRow GK)) :
    TraceConfined Λ t =
      ∀ g ∈ bfsRows t, RowNounsConfined Λ g :=
  rfl

theorem b293_rowNouns (Λ : ℕ) (g : GenComputeRow GK) :
    RowNounsConfined Λ g =
      (g.skel.subject.leaves ≤ Λ ∧
        g.skel.formula.leaves ≤ Λ ∧
          g.skel.evaluation.leaves ≤ Λ) :=
  rfl

/-! ## 2. Program-text numbers (Field-free).  Not a 401-row window. -/

theorem b293_mmFormula_leaves : mmFormula.leaves = 568 :=
  mmFormula_leaves

theorem b293_mmSubject_leaves : mmSubject.leaves = 8 := by
  simp [mmSubject, mmA, mmB, cell_leaves, atom_leaves]

theorem b293_mmC_leaves : mmC.leaves = 4 :=
  mmC_leaves

theorem b293_mmBattery_leaves : mmBattery.leaves = 58 :=
  mmBattery_leaves

/-- Root public triple fits `568`.  Intermediates are the residual:
OP7 threads a computed subject; OP9 invokes an arm
(`:1070`). -/
theorem b293_root_nouns_le_formula :
    mmSubject.leaves ≤ mmFormula.leaves ∧
      mmC.leaves ≤ mmFormula.leaves := by
  rw [b293_mmSubject_leaves, mmC_leaves, mmFormula_leaves]
  exact ⟨by decide, by decide⟩

/-! ## 3. Why the existing suppliers miss this program. -/

theorem b293_slam_is_op7 (b s : Noun) (ax : ℕ) :
    slam b s ax =
      .cell (.atom 7) (.cell (.cell b s) (invokeAxis ax)) :=
  slam_is_op7 b s ax

theorem b293_invokeAxis_is_op9 (ax : ℕ) :
    invokeAxis ax =
      .cell (.atom 9) (.cell (.atom ax) (.cell (.atom 0) (.atom 1))) :=
  invokeAxis_is_op9 ax

theorem b293_mmC00_is_mac2 :
    mmC00 = mac2 (op1 0) (op0 8) (op0 12) (op0 9) (op0 14) :=
  mmC00_is_mac2

/-- SubISA excludes OP7/OP9.  The matmul program text is built from
`slam` / `invokeAxis`, so `genComputeSkeleton_subISA_traceConfined`
does not apply. -/
theorem b293_subISA_excludes_op7_op9 (g : GenComputeRow GK) :
    RowSubISA g → g.skel.state ≠ .s7 ∧ g.skel.state ≠ .s9 :=
  fun h => ⟨h.2.1, h.2.2.2⟩

/-! ## 4. `SeedGood` is not the vacuous Tier-A predicate. -/

theorem b293_root_is_cons :
    (mmTree (K := GK)).label.skel.state = .cons :=
  mmTree_root_is_cons

/-- `SeedGood` at a `cons` root requires a Dyck check on the formula
head (`GenDyckBadSeed.lean::RowSeedGood`).  That is field-dependent
and was discharged at `ZMod 65537` by `seedOK_mm`, not at Goldilocks. -/
theorem b293_seedGood_asks_dyck (z : GK) :
    SeedGood z (mmTree (K := GK)) →
      (encC z (formulaHead (mmTree (K := GK)).label.skel.formula)).dyck ≠ 0 := by
  intro h
  have hr := h (mmTree (K := GK)) (InTree.here _)
  exact hr.1 mmTree_root_is_cons

/-! ## 5. No new binder. -/

theorem b293_p62_still_wants_traceConfined :
    (∀ {Λ : ℕ}, TraceConfined Λ (airReorder (mmTree (K := GK))) → True) :=
  fun _ => trivial

end Nock.RedTeam.Batch293

#print axioms Nock.RedTeam.Batch293.b293_type
#print axioms Nock.RedTeam.Batch293.b293_mmFormula_leaves
#print axioms Nock.RedTeam.Batch293.b293_root_is_cons
#print axioms Nock.RedTeam.Batch293.b293_seedGood_asks_dyck
#print axioms Nock.RedTeam.Batch293.b293_p62_still_wants_traceConfined
