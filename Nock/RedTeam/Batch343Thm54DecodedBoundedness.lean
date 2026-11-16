/-
  Nock/RedTeam/Batch343Thm54DecodedBoundedness.lean

  **`BoundedBy (ringChar K)` and
  `SizeWindowNounsBoundedBy … M`.**

  Decoding lands in `[0, q)` by construction (`leafAtomOf_lt_of_pos`).
-/
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding

namespace Nock.RedTeam.Batch343

open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SizeWindowCounting

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem leafAtom_in_window {q : ℕ} (hq : 0 < q) (v : K) :
    leafAtomOf q v < q :=
  leafAtomOf_lt_of_pos hq v

/-- Halt decode is an atom in `[0, q)`. -/
theorem halt_decode_bounded {q : ℕ} (hq : 0 < q)
    (data : MemoryTable.DTmem K) :
    FieldEmbedding.BoundedBy q
      (decodeNoun q (.node (.halt, data) [])) := by
  simp [decodeNoun]
  exact leafAtomOf_lt_of_pos hq _

theorem sizeWindow_at_M {M : ℕ} (join : ComputeJoin) (q : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    (h : JoinWindow join M) :
    SizeWindowNounsBoundedBy (decodedSkeleton q join forest) M :=
  sizeWindow_of_join join q forest h

/-- At a positive characteristic the leaf window `q := ringChar K` is
admissible for `leafAtomOf`. -/
theorem ringChar_pos_of_prime {p : ℕ} [Fact p.Prime]
    (h : ringChar K = p) : 0 < ringChar K := by
  rw [h]
  exact Nat.Prime.pos (Fact.out (p := p.Prime))

/-- `decodedSkeleton.BoundedBy q` at `0 < q` (in particular `q = ringChar K`
when `ringChar K` is prime). -/
theorem skeleton_bounded {q : ℕ} (hq : 0 < q)
    (join : ComputeJoin) (hjoin : JoinBounded q join)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    SemanticSkeleton.BoundedBy q
      (decodedSkeleton q join forest) :=
  decodedSkeleton_bounded hq join hjoin forest

/-- Specialization at `q = ringChar K` under a prime characteristic. -/
theorem skeleton_bounded_ringChar {p : ℕ} [Fact p.Prime]
    (hchar : ringChar K = p) (join : ComputeJoin)
    (hjoin : JoinBounded (ringChar K) join)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    SemanticSkeleton.BoundedBy (ringChar K)
      (decodedSkeleton (ringChar K) join forest) :=
  skeleton_bounded (ringChar_pos_of_prime hchar) join hjoin forest

end

#print axioms Nock.RedTeam.Batch343.leafAtom_in_window
#print axioms Nock.RedTeam.Batch343.halt_decode_bounded
#print axioms Nock.RedTeam.Batch343.sizeWindow_at_M
#print axioms Nock.RedTeam.Batch343.skeleton_bounded
#print axioms Nock.RedTeam.Batch343.skeleton_bounded_ringChar

end Nock.RedTeam.Batch343
