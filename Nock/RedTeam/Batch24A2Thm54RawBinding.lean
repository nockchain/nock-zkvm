/-
  Nock/RedTeam/Batch24A2Thm54RawBinding.lean

  Three attacks, all answered by compiled artifacts.

  1. **Vacuity.**  Is the A2 hypothesis bundle (seed pin + tree-shape datum + frame checks + A1's
     scan) satisfiable at all?  `b24a2_jointly_nonvacuous` reuses Batch24A1's concrete `ℚ` witness:
     the same commitment and raw family, at every seed, satisfy all four inputs, and
     `b24a2_bindsAt_of_scan_nonvacuous` runs `bindsAt_of_scanOn` on them to produce a real `BindsAt`.
     The scanned list is nonempty (`Batch24A1.b24a1_sample_scan_ne_nil`), so nothing is proved about
     an empty premise.

  2. **Is A2 really the converse of A1, or a different statement?**  `b24a2_a1_a2_inverse` compiles
     the round trip: A1's `activeFingerprintChecksOn_of_bindsAt`, fed the residual data that a genuine
     binding supplies for free (`execTreeShapeMatchesAt_of_bindsAt`, `rowFrameChecksAt_of_bindsAt`),
     is inverted by A2's `bindsAt_of_scanOn`, and conversely.  What the artifact pins is that the two
     maps have *exactly matching types* on the same objects — that is the content; the proof-term
     equality is then automatic because `BindsAt` is `Prop`-valued.  `b24a2_sample_equivalence_holds`
     shows the resulting equivalence `bindsAt_iff_scanOn` is inhabited on both sides at the concrete
     witness, so it is not an equivalence between two false statements.

  3. **Is the tree-shape datum gratuitous?**  No.  `b24a2_shape_datum_is_load_bearing` compiles a
     concrete pair of two-node trees over `ℚ` on which *every canonical BFS row binding holds*
     (`b24a2_mismatch_bfs_rows_bound`) and yet `ComputeTreeBinds` provably does not exist, because the
     committed `.s1` root has `fanoutComp = 0` while the committed tree branches once.  So the
     structural datum is exactly the information the flat scan cannot carry, not an extra assumption
     smuggled in to make the proof go through.  `b24a2_shape_datum_is_not_extra_strength` records the
     other half: a genuine binding always supplies the datum, so A2 never strengthens `BindsAt`.

  Scope honesty (unchanged by these receipts): A2 derives `BindsAt` from the *checks*.  It does **not**
  derive the checks from raw `RawMessage.Accepts` — that is Packet B — and it does not close the two
  `GlobalCarryAxis.ServedLookup` obligations or the IO-capacity premises.  Nothing below assumes
  acceptance.
-/

import Nock.NockVMROM.Thm54.RawSemanticAssembly
import Nock.RedTeam.Batch24A1Thm54StrictCommitment

namespace Nock.RedTeam.Batch24A2

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.StrictCommitment
open Nock.NockVMROM.Thm54.ActiveFingerprintScan
open Nock.NockVMROM.Thm54.RawSemanticAssembly

noncomputable section

/-! ## Attack 1: is the A2 hypothesis bundle satisfiable?

Everything is the Batch24A1 witness: one `.s1` compute leaf, one `halt` memory leaf, over `ℚ`. -/

/-- The committed compute tree and the concrete execution compute tree agree structurally: the
committed `.s1` root has `fanoutComp = 0`, and both trees are leaves. -/
theorem b24a2_sample_computeShapeMatch (z : ℚ) :
    ComputeShapeMatch sampleCommitment.skeleton.computeTree
      (Batch24A1.sampleFamily z).exec.computeTree := by
  have hs : sampleCommitment.skeleton.computeTree =
      .node sampleComputeRow [] := rfl
  have he : (Batch24A1.sampleFamily z).exec.computeTree =
      .node (Batch24A1.sampleComputeExecRow z) [] := rfl
  rw [hs, he]
  exact .node (by simp [sampleComputeRow, ComputeTable.fanoutComp]) .nil

/-- The committed memory forest and the concrete execution memory forest agree structurally: the
committed `halt` root has `fanoutMem = 0`. -/
theorem b24a2_sample_memoryShapeMatch (z : ℚ) :
    List.Forall₂ MemoryShapeMatch sampleCommitment.skeleton.memoryForest
      (Batch24A1.sampleFamily z).exec.memoryForest := by
  have hs : sampleCommitment.skeleton.memoryForest =
      [.node sampleMemoryRow []] := rfl
  have he : (Batch24A1.sampleFamily z).exec.memoryForest =
      [.node (Batch24A1.sampleMemoryExecRow z) []] := rfl
  rw [hs, he]
  exact .cons (.node (by simp [sampleMemoryRow, MemoryTable.fanoutMem]) .nil) .nil

/-- The tree-shape datum, bundled. -/
theorem b24a2_sample_shape (z : ℚ) :
    ExecTreeShapeMatchesAt sampleCommitment (Batch24A1.sampleFamily z).exec :=
  { compute := b24a2_sample_computeShapeMatch z
    memory := b24a2_sample_memoryShapeMatch z }

/-- The frame datum: the per-row non-fingerprint residual on the concrete witness. -/
theorem b24a2_sample_frame (z : ℚ) :
    RowFrameChecksAt z sampleCommitment (Batch24A1.sampleFamily z).exec := by
  constructor
  · intro e he
    rw [sampleCommitment_computeRows, Batch24A1.sampleFamily_computeRows] at he
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at he
    subst he
    exact bindComputeRow_frame (Batch24A1.sample_bindComputeRow z)
  · intro e he
    rw [sampleCommitment_memoryRows, Batch24A1.sampleFamily_memoryRows] at he
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at he
    subst he
    exact bindMemoryRow_frame (Batch24A1.sample_bindMemoryRow z)

/-- **Attack 1 answered: the A2 inputs are jointly satisfiable, non-vacuously.**  One concrete
commitment over `ℚ` simultaneously pins the seed, matches the execution tree shape, discharges the
frame checks, and passes A1's active fingerprint scan — with a nonempty scan list. -/
theorem b24a2_jointly_nonvacuous (z : ℚ) :
    (Batch24A1.sampleFamily z).cfg.challenges.z = z ∧
      ExecTreeShapeMatchesAt sampleCommitment (Batch24A1.sampleFamily z).exec ∧
      RowFrameChecksAt z sampleCommitment (Batch24A1.sampleFamily z).exec ∧
      ActiveFingerprintChecksOn z sampleCommitment (Batch24A1.sampleFamily z) ∧
      activeComputeSlotsOn sampleCommitment (Batch24A1.sampleFamily z) ≠ [] :=
  ⟨rfl, b24a2_sample_shape z, b24a2_sample_frame z,
    Batch24A1.sample_activeFingerprintChecks z, Batch24A1.b24a1_sample_scan_ne_nil z⟩

/-- **The A2 reconstruction runs on a real instance.** -/
theorem b24a2_bindsAt_of_scan_nonvacuous (z : ℚ) :
    SemanticStrategy.BindsAt z sampleCommitment.skeleton
      (Batch24A1.sampleFamily z).cfg (Batch24A1.sampleFamily z).exec :=
  bindsAt_of_scanOn rfl (b24a2_sample_shape z) (b24a2_sample_frame z)
    (Batch24A1.sample_activeFingerprintChecks z)

/-- The A2-derived binding also drives the established consumer: whole-execution noun realization at
the strict prime `3`, from the two deterministic A1 checks plus the two named A2 data. -/
theorem b24a2_sample_nounRealization (z : ℚ) (hz : z ≠ 0) :
    ExactExecutionNounRealization 3 (Batch24A1.sampleFamily z).cfg
      (Batch24A1.sampleFamily z).exec :=
  (b24a2_bindsAt_of_scan_nonvacuous z).nounRealization hz
    sampleCommitment_canonical.1.skeletonBoundedBy

/-! ## Attack 2: is A2 the genuine converse of A1?

A1's map is `BindsAt ⟹ scan`; A2's map is `seed ∧ shape ∧ frame ∧ scan ⟹ BindsAt`.  The round trip
below compiles both compositions on the *same* objects.  Since `SemanticStrategy.BindsAt` is
`Prop`-valued, the proof terms are equal automatically; the receipt's content is that the two maps'
domains and codomains line up exactly, i.e. A2 rebuilds the very object A1 consumed, with the residual
data that a genuine binding itself supplies. -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- **Round trip, both directions.**  Feeding A1's scan output back through A2's reconstruction — with
the shape and frame data that the binding itself provides — returns the same binding; and A1's forward
map applied to an A2-reconstructed binding returns the scan it was built from. -/
theorem b24a2_a1_a2_inverse {z : K} {C : SkeletonCommitment}
    {R : RawPlusIOSegmentedFamily F K}
    (h : SemanticStrategy.BindsAt z C.skeleton R.cfg R.exec)
    (hseed : R.cfg.challenges.z = z)
    (hshape : ExecTreeShapeMatchesAt C R.exec)
    (hframe : RowFrameChecksAt z C R.exec)
    (hscan : ActiveFingerprintChecksOn z C R) :
    bindsAt_of_scanOn h.sampledSeed (execTreeShapeMatchesAt_of_bindsAt h)
        (rowFrameChecksAt_of_bindsAt h) (activeFingerprintChecksOn_of_bindsAt h) = h ∧
      activeFingerprintChecksOn_of_bindsAt
        (bindsAt_of_scanOn hseed hshape hframe hscan) = hscan :=
  ⟨rfl, rfl⟩

/-- **The equivalence is inhabited on both sides at the concrete witness**, so
`bindsAt_iff_scanOn` is not an equivalence of two false statements. -/
theorem b24a2_sample_equivalence_holds (z : ℚ) :
    (SemanticStrategy.BindsAt z sampleCommitment.skeleton
        (Batch24A1.sampleFamily z).cfg (Batch24A1.sampleFamily z).exec ↔
      ((Batch24A1.sampleFamily z).cfg.challenges.z = z ∧
        ExecTreeShapeMatchesAt sampleCommitment (Batch24A1.sampleFamily z).exec ∧
        RowFrameChecksAt z sampleCommitment (Batch24A1.sampleFamily z).exec ∧
        ActiveFingerprintChecksOn z sampleCommitment (Batch24A1.sampleFamily z))) ∧
      SemanticStrategy.BindsAt z sampleCommitment.skeleton
        (Batch24A1.sampleFamily z).cfg (Batch24A1.sampleFamily z).exec :=
  ⟨bindsAt_iff_scanOn, b24a2_bindsAt_of_scan_nonvacuous z⟩

/-! ## Attack 3: is the tree-shape datum gratuitous?

The counter-witness reuses the Batch24A1 row pair but stacks it into a **two-node** tree.  The
committed root state is `.s1`, whose `fanoutComp` is `0`, so a committed tree with one child violates
its own arity — while every canonical BFS *row* is still perfectly bound.  Hence the flat scan cannot
possibly see the defect, and the structural datum is load-bearing. -/

/-- The mismatched committed tree: an `.s1` row with one child, though `fanoutComp.s1 = 0`. -/
def mismatchedSkeletonTree : NTree SemanticStrategy.ComputeRowSkeleton :=
  .node sampleComputeRow [.node sampleComputeRow []]

/-- The correspondingly shaped execution tree. -/
def mismatchedExecTree (z : ℚ) :
    NTree (ComputeTable.State × ComputeTable.DTcomp ℚ) :=
  .node (Batch24A1.sampleComputeExecRow z) [.node (Batch24A1.sampleComputeExecRow z) []]

private theorem bfs_two_node {LT : Type} (x : LT) :
    bfsForest [NTree.node x [NTree.node x []]] =
      [NTree.node x [NTree.node x []], NTree.node x []] := by
  rw [bfsForest_cons_eq _ (by simp)]
  simp [Batch24A1.bfs_singleton_leaf]

/-- **Every canonical BFS row binding holds** on the mismatched pair: the flat data the scan sees is
completely healthy. -/
theorem b24a2_mismatch_bfs_rows_bound (z : ℚ) :
    List.Forall₂ (SemanticStrategy.BindComputeRow z)
      ((bfsForest [mismatchedSkeletonTree]).map NTree.label)
      ((bfsForest [mismatchedExecTree z]).map NTree.label) := by
  rw [mismatchedSkeletonTree, mismatchedExecTree, bfs_two_node, bfs_two_node]
  exact .cons (Batch24A1.sample_bindComputeRow z)
    (.cons (Batch24A1.sample_bindComputeRow z) .nil)

/-- The mismatched pair has no structural match: the committed arity is wrong. -/
theorem b24a2_mismatch_no_shapeMatch (z : ℚ) :
    ¬ ComputeShapeMatch mismatchedSkeletonTree (mismatchedExecTree z) := by
  intro h
  cases h with
  | node harity _ =>
      simp [sampleComputeRow, ComputeTable.fanoutComp] at harity

/-- **Attack 3 answered: the tree-shape datum is load-bearing.**  On the mismatched pair every
canonical BFS row is bound — so A1's scan and the frame checks are fully satisfiable there — and yet
`ComputeTreeBinds`, hence `BindsAt`, provably does not exist.  Without the structural datum the tree
assembly of step 2 cannot proceed, and no amount of flat fingerprint checking can supply it. -/
theorem b24a2_shape_datum_is_load_bearing (z : ℚ) :
    List.Forall₂ (SemanticStrategy.BindComputeRow z)
        ((bfsForest [mismatchedSkeletonTree]).map NTree.label)
        ((bfsForest [mismatchedExecTree z]).map NTree.label) ∧
      ¬ ComputeShapeMatch mismatchedSkeletonTree (mismatchedExecTree z) ∧
      ¬ SemanticStrategy.ComputeTreeBinds z mismatchedSkeletonTree
        (mismatchedExecTree z) :=
  ⟨b24a2_mismatch_bfs_rows_bound z, b24a2_mismatch_no_shapeMatch z,
    fun hbind =>
      b24a2_mismatch_no_shapeMatch z (computeTreeBinds_shapeMatch hbind)⟩

/-- Any genuine binding supplies
both named A2 data, so A2's hypothesis bundle is implied by `BindsAt` and the reconstruction is an
equivalence rather than a strengthening. -/
theorem b24a2_shape_datum_is_not_extra_strength {z : K} {C : SkeletonCommitment}
    {R : RawPlusIOSegmentedFamily F K}
    (h : SemanticStrategy.BindsAt z C.skeleton R.cfg R.exec) :
    ExecTreeShapeMatchesAt C R.exec ∧ RowFrameChecksAt z C R.exec :=
  ⟨execTreeShapeMatchesAt_of_bindsAt h, rowFrameChecksAt_of_bindsAt h⟩

end

end Nock.RedTeam.Batch24A2

#print axioms Nock.RedTeam.Batch24A2.b24a2_sample_computeShapeMatch
#print axioms Nock.RedTeam.Batch24A2.b24a2_sample_memoryShapeMatch
#print axioms Nock.RedTeam.Batch24A2.b24a2_sample_shape
#print axioms Nock.RedTeam.Batch24A2.b24a2_sample_frame
#print axioms Nock.RedTeam.Batch24A2.b24a2_jointly_nonvacuous
#print axioms Nock.RedTeam.Batch24A2.b24a2_bindsAt_of_scan_nonvacuous
#print axioms Nock.RedTeam.Batch24A2.b24a2_sample_nounRealization
#print axioms Nock.RedTeam.Batch24A2.b24a2_a1_a2_inverse
#print axioms Nock.RedTeam.Batch24A2.b24a2_sample_equivalence_holds
#print axioms Nock.RedTeam.Batch24A2.b24a2_mismatch_bfs_rows_bound
#print axioms Nock.RedTeam.Batch24A2.b24a2_mismatch_no_shapeMatch
#print axioms Nock.RedTeam.Batch24A2.b24a2_shape_datum_is_load_bearing
#print axioms Nock.RedTeam.Batch24A2.b24a2_shape_datum_is_not_extra_strength
