/-
  Nock/NockVMROM/Thm54/TraceGen/GenCommitmentBridge.lean

  **Wiring the generated trace into `SkeletonCommitment`, and reconciling it with `TraceConfined`.**

      CanonicalCommitmentCheck p C  :=  ∀ n ∈ commitmentNouns C,
        FieldEmbedding.BoundedBy p n ∧ n.leaves ≤ C.nounSizeBound

  over the finite *active* slot inventory of both tables, together with
  `CanonicalCommitmentCheck.skeletonBoundedBy : C.skeleton.BoundedBy p` (`SkeletonCommitment.lean:384`).
  It does not need to be
  built, only instantiated at the generated skeleton, which is what `genCommitment` does here.

  `DW` also asserted, **without compiling it**, that `RowLeafWindow` follows from the same check.

  **The relationship between the two premises, stated exactly.**  Neither implies the other in
  general — one ranges over active committed slots of a skeleton, the other over the generator's own
  rows — but at the generated skeleton the commitment check is the **stronger** of the two on the
  leaf axis, and `traceConfined_of_canonical` proves it. So `TraceConfined` is a
  genuinely weaker premise reaching the same conclusion, and this module is where that stops being
  an assertion.

  **⚠ Status: this route has no witness.**  Nothing in the tree discharges
  `CanonicalCommitmentCheck q (genCommitment Λ t mf)` at a generated trace — `genCommitment` occurs
  only in its own definition and in hypothesis positions.  So every theorem below
  that takes `hcanon` is **conditional on a premise no program has been shown to satisfy**, and it
  is a *harder* measurement than the one it was introduced to replace: roughly twenty-one active
  slots per compute row plus every active slot of every memory row, with atom bounds, against the
  three nouns per row that `Batch164.dot_traceConfined` actually discharges — and with the same
  `decide`-does-not-reduce obstacle (`DX`).

  **Use `TraceConfined` instead** (`GenTraceConfined.lean`): it is the weaker premise, it is what
  `traceConfined_of_canonical` shows this check implies, and it is the one with a witness.  For
  `skeletonBounded`, take `S.BoundedBy q` directly — that is the form a configuration actually
  proves (`DotConfig769.semanticSkeleton_bounded`, `GenTierABounded.lean:908`), and it is why
  `genNounRealization` and `genCombinedBounded` were changed to take it rather than `hcanon`.

  Nothing here is retracted: the implications are sound and stay available for whoever exhibits the
  check.  What is recorded is that **availability of a form is not availability of a route.**
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericCensusWindow
import Nock.NockVMROM.Thm54.SkeletonCommitment
import Nock.NockVMROM.Thm54.CensusExtraClosure
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.CensusExtraClosure
open Nock.NockVMROM.Thm54.StrictCommitment

variable {K : Type} [Field K]

/-! ## `RowLeafWindow` from the commitment check -/

/-- **The leaf window at one committed row.**

The three public nouns are unconditionally active. A subformula slot is active exactly inside the
fan-out, and outside it the total projection is `.atom 0`, whose single leaf fits any `Λ ≥ 1`. -/
theorem rowLeafWindow_of_canonical {p : ℕ} {C : SkeletonCommitment}
    (hΛ : 1 ≤ C.nounSizeBound)
    (h : CanonicalCommitmentCheck p C)
    {s : ComputeRowSkeleton} (hs : s ∈ computeSkeletonRows C.skeleton) :
    RowLeafWindow C.nounSizeBound s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.computeSlot_leaves hs (a := ComputeSlotAddress.subject)
      (by simp [mem_activeComputeSlotAddresses_iff, computeSlotActive])
  · exact h.computeSlot_leaves hs (a := ComputeSlotAddress.formula)
      (by simp [mem_activeComputeSlotAddresses_iff, computeSlotActive])
  · exact h.computeSlot_leaves hs (a := ComputeSlotAddress.evaluation)
      (by simp [mem_activeComputeSlotAddresses_iff, computeSlotActive])
  · intro i slot
    by_cases hi : (i : ℕ) < ComputeTable.fanoutComp s.state
    · exact h.computeSlot_leaves hs (a := ComputeSlotAddress.sub i slot)
        (by simp [mem_activeComputeSlotAddresses_iff, computeSlotActive, hi])
    · simp only [P8Census.skeletonSubformula, dif_neg hi]
      exact atom_leaves_le hΛ 0

/-- The same over the whole skeleton, at the shape §G's reduction consumes. -/
theorem leafWindow_of_canonical {p : ℕ} {C : SkeletonCommitment}
    (hΛ : 1 ≤ C.nounSizeBound) (h : CanonicalCommitmentCheck p C) :
    ∀ s ∈ computeSkeletonRows C.skeleton, RowLeafWindow C.nounSizeBound s :=
  fun _ hs => rowLeafWindow_of_canonical hΛ h hs

/-! ## The commitment at a generated trace -/

/-- The `SkeletonCommitment` a generated trace commits: its semantic skeleton, at leaf bound `Λ`. -/
def genCommitment (Λ : ℕ) (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) : SkeletonCommitment :=
  { skeleton := genSemanticSkeleton (bfsAssign (airReorder t)) mf
    nounSizeBound := Λ }

@[simp] theorem genCommitment_skeleton (Λ : ℕ) (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    (genCommitment Λ t mf).skeleton = genSemanticSkeleton (bfsAssign (airReorder t)) mf := rfl

@[simp] theorem genCommitment_nounSizeBound (Λ : ℕ) (t : NTree (GenComputeRow K))
    (mf : List (NTree (GenMemoryRow K))) :
    (genCommitment Λ t mf).nounSizeBound = Λ := rfl

/-- **`Data.skeletonBounded` for any generated trace**, from the decidable check. -/
theorem genCommitment_skeletonBounded {q Λ : ℕ} {t : NTree (GenComputeRow K)}
    {mf : List (NTree (GenMemoryRow K))}
    (h : CanonicalCommitmentCheck q (genCommitment Λ t mf)) :
    (genSemanticSkeleton (bfsAssign (airReorder t)) mf).BoundedBy q :=
  h.skeletonBoundedBy

/-- **The leaf window at every generated row**, from the same check — the second output of one
measurement. -/
theorem genCommitment_leafWindow {q Λ : ℕ} (hΛ : 1 ≤ Λ) {t : NTree (GenComputeRow K)}
    {mf : List (NTree (GenMemoryRow K))}
    (h : CanonicalCommitmentCheck q (genCommitment Λ t mf)) :
    ∀ s ∈ computeSkeletonRows (genSemanticSkeleton (bfsAssign (airReorder t)) mf),
      RowLeafWindow Λ s :=
  leafWindow_of_canonical (C := genCommitment Λ t mf) hΛ h

/-! ## Reconciliation with `TraceConfined`

`DP`'s premise and this one are different objects; this says which is stronger where it matters. -/

/-- **The commitment check implies `TraceConfined`** at the generated tree.

So `TraceConfined` is genuinely the weaker premise on the leaf axis, and `DP`'s route is not a
duplicate of the commitment route but a strengthening of it. The converse does not hold:
`TraceConfined` says nothing about atom magnitude, nor about the memory table. -/
theorem traceConfined_of_canonical {q Λ : ℕ} {t : NTree (GenComputeRow K)}
    {mf : List (NTree (GenMemoryRow K))}
    (h : CanonicalCommitmentCheck q (genCommitment Λ t mf)) :
    TraceConfined Λ (bfsAssign (airReorder t)) := by
  intro g hg
  have hs : g.skel ∈
      computeSkeletonRows (genSemanticSkeleton (bfsAssign (airReorder t)) mf) := by
    rw [computeSkeletonRows_genSemantic, computeSkeletonRows_genCompute]
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hg
    exact List.mem_map.mpr ⟨n, hn, rfl⟩
  have h1 := h.computeSlot_leaves (C := genCommitment Λ t mf) hs
    (a := ComputeSlotAddress.subject)
    (by simp [mem_activeComputeSlotAddresses_iff, computeSlotActive])
  have h2 := h.computeSlot_leaves (C := genCommitment Λ t mf) hs
    (a := ComputeSlotAddress.formula)
    (by simp [mem_activeComputeSlotAddresses_iff, computeSlotActive])
  have h3 := h.computeSlot_leaves (C := genCommitment Λ t mf) hs
    (a := ComputeSlotAddress.evaluation)
    (by simp [mem_activeComputeSlotAddresses_iff, computeSlotActive])
  exact ⟨h1, h2, h3⟩

/-! ## The `bfsAssign` bridge

`traceConfined_of_canonical` concludes at `bfsAssign (airReorder t)`, while every consumer of `DP`'s
premise wants it at `airReorder t` (`genSkeletonP8Census`, `genComputeSkeleton_census_air`, …).

It composes: `bfsAssign` rewrites exponents and preserves `.skel` in BFS order
(`bfsAssign_skel_list`, `GenTierABounded.lean:312`), and `RowNounsConfined` reads only `.skel`. -/

/-- `TraceConfined` is invariant under `bfsAssign`, in both directions. -/
theorem traceConfined_bfsAssign_iff {Λ : ℕ} (t : NTree (GenComputeRow K)) :
    TraceConfined Λ (bfsAssign t) ↔ TraceConfined Λ t := by
  have hskel : (bfsRows (bfsAssign t)).map (fun g => g.skel)
      = (bfsRows t).map (fun g => g.skel) := by
    unfold bfsRows
    rw [List.map_map, List.map_map]
    exact bfsAssign_skel_list t
  constructor <;> intro h g hg <;>
    [ (have : g.skel ∈ (bfsRows (bfsAssign t)).map (fun g => g.skel) := by
        rw [hskel]; exact List.mem_map_of_mem hg);
      (have : g.skel ∈ (bfsRows t).map (fun g => g.skel) := by
        rw [← hskel]; exact List.mem_map_of_mem hg) ] <;>
    · obtain ⟨g', hg', hEq⟩ := List.mem_map.mp this
      have := h g' hg'
      unfold RowNounsConfined at this ⊢
      rw [← hEq]
      exact this

/-- **The reconciliation, at the tree the consumers use.**  `DY`'s statement composed with the
`bfsAssign` bridge. -/
theorem traceConfined_airReorder_of_canonical {q Λ : ℕ} {t : NTree (GenComputeRow K)}
    {mf : List (NTree (GenMemoryRow K))}
    (h : CanonicalCommitmentCheck q (genCommitment Λ t mf)) :
    TraceConfined Λ (airReorder t) :=
  (traceConfined_bfsAssign_iff (airReorder t)).mp (traceConfined_of_canonical h)

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.rowLeafWindow_of_canonical
#print axioms Nock.NockVMROM.Thm54.TraceGen.genCommitment_skeletonBounded
#print axioms Nock.NockVMROM.Thm54.TraceGen.genCommitment_leafWindow
#print axioms Nock.NockVMROM.Thm54.TraceGen.traceConfined_of_canonical
#print axioms Nock.NockVMROM.Thm54.TraceGen.traceConfined_bfsAssign_iff
#print axioms Nock.NockVMROM.Thm54.TraceGen.traceConfined_airReorder_of_canonical
