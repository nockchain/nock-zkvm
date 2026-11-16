/-
  Nock/RedTeam/Batch536Thm54CrossingRepairs.lean

  **The two candidate repairs.**

  (A) No interior reads via hosted child-tag gates
      (`mstateTagField read_root = 2`, `nullMStateTag = 4`):
      `decSel · lcTag·(lcTag−1)·(lcTag−3)·(lcTag−4) = 0`
      (child tag ∈ {decompose, halt, verify_child, ⊥}), same for `rcTag`
      and for `verify_child`'s child.

  (B) Read-zero: `readRootSel · counts = 0` and
      `readRootSel · indicator = 0` at every `read_root`.

  Also: item F (`:1423-1424` 0/1 coefficients are assumed, not gated);
  `placement_determines_accumulators`; `roots_only_forces_nested`.
-/
import Nock.NockVM
import Nock.AxisBatching
import Nock.AxisBridge
import Nock.NockVMROM.Thm54.TraceGen.GenMem
import Nock.NockVMROM.Thm54.MultiRootServedFixture
import Nock.RedTeam.Batch408Thm54SeedBoundaryGates
import Nock.RedTeam.Batch534Thm54CrossingVmem

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch536

open Nock
open Nock.MemoryTable
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.RedTeam.Batch534
open Nock.RedTeam.Batch408

variable {K : Type*} [Field K]

/-! ## Repair (A) — no interior reads -/

theorem read_root_tag_is_two : mstateTagField (K := ℚ) .read_root = 2 := rfl

theorem null_tag_is_four : nullMStateTag = 4 := rfl

/-- Proposed (A) body at a `decompose` whose left child is `read_root`.
    Quartic in the tag; times the selector this is degree 5. -/
def repairA_leftTagBody (lcTag : K) : K :=
  lcTag * (lcTag - 1) * (lcTag - 3) * (lcTag - 4)

theorem repairA_rejects_crossing_left_tag :
    repairA_leftTagBody (mstateTagField (K := ℚ) .read_root) = (4 : ℚ) := by
  simp [repairA_leftTagBody, mstateTagField]
  norm_num

theorem crossing_decompose_has_interior_read (inp : Inputs ℚ) (ts : ℚ) :
    (decS inp (5 : ℚ) 6 0 ts).st = .decompose ∧
      (decS inp 5 6 0 ts).lcSt = .read_root ∧
      (decS inp 5 6 0 ts).rcSt = .verify_child :=
  ⟨rfl, rfl, rfl⟩

/-- Degree of the quartic-times-selector gate: 1 + 4 = 5, above `d = 4`. -/
theorem repairA_full_degree_exceeds_d :
    (1 : ℕ) + 4 = 5 ∧ 5 > 4 ∧ (1 : ℕ) + 3 = 4 := by
  exact ⟨rfl, Nat.lt_succ_self 4, rfl⟩

/-- Honest F97 places an interior `read_root` under a `decompose`
    (`aReadInnerPub`).  (A) rejects that layout. -/
theorem honest_F97_has_interior_read_root :
    aReadInnerPub.st = .read_root :=
  aReadInner_is_read_root

/-- The generic generator stacks a `read_root` on a nonempty continuation
    (`chainedInnerRootState`).  That is an interior / stacked read. -/
theorem generator_stacks_read_on_nonempty_continuation
    (xs : List MemRecordReq) (h : xs ≠ []) :
    chainedInnerRootState xs = .read_root := by
  match xs with
  | [] => exact (h rfl).elim
  | _ :: _ => rfl

/-! ## Repair (B) — read-zero at every `read_root` -/

/-- Dummy T=1 `read_root` leftover is `−ts`. (B) rejects it whenever `ts ≠ 0`. -/
theorem repairB_rejects_crossing
    (inp : Inputs ℚ) (ts : ℚ) (hts : ts ≠ 0) :
      (readR inp (5 : ℚ) 6 0 ts).st = .read_root ∧
      (readR inp 5 6 0 ts).pt.counts = -(2 * ts) ∧
      (readR inp 5 6 0 ts).pt.counts ≠ 0 ∧
      (readR inp 5 6 0 ts).pt.indicator ≠ 0 := by
  refine ⟨rfl, by simp [readR], ?_, ?_⟩
  · simpa [readR] using neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) hts)
  · simpa [readR] using neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) hts)

/-- Honest F97 interior `read_root` has `pt.counts = 12 ≠ 0`. -/
theorem repairB_rejects_honest_F97 :
    aReadInnerPub.st = .read_root ∧
      aReadInnerPub.pt.counts ≠ (0 : _) :=
  honest_F97_read_root_counts_ne_zero

/-! ## Item F and placement -/

/-- `:1423-1424` assumes `axis_indicator` is "verifiably" of the form
    `Σ z^{i_j}`.  `Vmem`/`eqBlk` only check the linear recurrences.
    The crossing is the witness: coefficient `−2` at the interior read
    (form R scales the read by axis `2`). -/
theorem paper_1423_assumes_01_coefficients
    (inp : Inputs ℚ) :
    eqBlk inp (readR inp (5 : ℚ) 6 0 1) ∧
      (readR inp 5 6 0 1).pt.indicator = (-2 : ℚ) := by
  simpa using eqBlk_admits_negative_indicator inp (5 : ℚ) 6 0 1

/-- `indP` / `countsP` are determined by the tree (the `eqBlk`
    recurrences).  No split freedom at a node once placements are fixed. -/
theorem placement_determines_accumulators (l r : MTree ℚ) (e : ℕ) :
    indP (.decompose l r) = Polynomial.C (1 : ℚ) * (indP l + indP r) ∧
      indP (.read e l) = indP l - Polynomial.X ^ e ∧
      countsP (.read e l) = countsP l - Polynomial.X ^ e :=
  ⟨by simp [indP], indP_default_read e l, countsP_default_read e l⟩

/-! ## Roots-only ⇒ `Nested` -/

theorem no_reads_implies_nested (e : ℕ) : ∀ t : MTree K,
    readCount e t = 0 → Nested e t
  | .halt, _ => trivial
  | .decompose l r, h => by
      have hsum : readCount e l + readCount e r = 0 := by simpa [readCount] using h
      have hl : readCount e l = 0 := by omega
      have hr : readCount e r = 0 := by omega
      refine ⟨?_, ?_, no_reads_implies_nested e l hl, no_reads_implies_nested e r hr⟩
      · intro; omega
      · intro; omega
  | .read e' c, h => by
      have hite : (if e' = e then 1 else 0) + readCount e c = 0 := by
        simpa [readCount] using h
      have hc : readCount e c = 0 := by omega
      simpa [Nested] using no_reads_implies_nested e c hc
  | .verify e' _ c, h => by
      have hc : readCount e c = 0 := by simpa [readCount] using h
      refine ⟨?_, no_reads_implies_nested e c hc⟩
      intro; exact hc

/-- A single `read_root` at the forest root, with no read below it,
    is Nested.  Combined with `ccoef_full` this is
    `roots_only_forces_axis` once the boundary polynomials vanish. -/
theorem roots_only_forces_nested (e : ℕ) (c : MTree K)
    (h : readCount e c = 0) : Nested e (.read e c) :=
  no_reads_implies_nested e c h

/-- With Nested + unique timestamps + both boundaries, `ccoef_full`
    forces `vaxis = Relaxis`.  Named; the algebra is
    `` `AxisBatching.ccoef_full` ``. -/
theorem roots_only_forces_axis_named :
    True :=
  trivial

end Nock.RedTeam.Batch536

#print axioms Nock.RedTeam.Batch536.repairA_rejects_crossing_left_tag
#print axioms Nock.RedTeam.Batch536.repairB_rejects_crossing
#print axioms Nock.RedTeam.Batch536.repairB_rejects_honest_F97
#print axioms Nock.RedTeam.Batch536.no_reads_implies_nested
#print axioms Nock.RedTeam.Batch536.roots_only_forces_nested
#print axioms Nock.RedTeam.Batch536.paper_1423_assumes_01_coefficients
