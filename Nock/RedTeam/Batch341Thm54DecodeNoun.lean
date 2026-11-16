/-
  Nock/RedTeam/Batch341Thm54DecodeNoun.lean

  **`decodeNoun`, `decode_fingerprint`, `hostileCensus`.**

  Receipts against `HostileSkeletonDecoding`.  Paper re-read at source:
  `Lem:NPR_decomp` the paper, `lem:ion_univariate_sec` `:1188`,
  `Thm:Noun_Validation` `:1268`.
-/
import Nock.NockVMROM.Thm54.HostileSkeletonDecoding
import Nock.RedTeam.Batch340Thm54MemoryTripleGates

namespace Nock.RedTeam.Batch341

open Nock
open Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- `decode_fingerprint` at a halt leaf: the committed triple is `fn` of the
decoded atom (`GlobalCarryRecognizer.enc_atom`). -/
theorem decode_fingerprint_halt {z : K} (hz : z ≠ 0) {q : ℕ}
    (data : MemoryTable.DTmem K)
    (atomShape : data.2.pt.noun.size = z ∧ data.2.pt.noun.dyck = 0)
    (hleaves : ∃ k : ℕ, k < q ∧ (k : K) = data.2.pt.noun.leaf) :
    GlobalCarryRecognizer.enc z
        (decodeNoun q (.node (.halt, data) []))
      = data.2.pt.noun :=
  decode_fingerprint hz (.halt data atomShape) hleaves

/-- MC majorant: `|hostileCensus| ≤ M²` in the BFS row count. -/
theorem census_majorant (q Λ : ℕ)
    (forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)))
    (hbound : ∀ n ∈ decodedNodes q forest, n.leaves ≤ Λ) :
    (hostileCensus q Λ forest hbound).count
      ≤ (bfsForest forest).length * (bfsForest forest).length :=
  hostileCensus_count_le q Λ forest hbound

/-- Negative control: colliding distinct NPR bit-strings sit in `badSeeds`. -/
theorem collision_in_badSeeds
    {Λ : ℕ} (C : ComparisonCensus Λ) [Fintype K] [DecidableEq K]
    (z : K) (i : Fin C.count)
    (hbits :
      (NPR.leafF (K := K) (C.pair i).1, NPR.dyckBits (K := K) (C.pair i).1)
        ≠ (NPR.leafF (K := K) (C.pair i).2, NPR.dyckBits (K := K) (C.pair i).2))
    (hfn : NPR.fn (C.pair i).1 z = NPR.fn (C.pair i).2 z) :
    z ∈ C.badSeeds (K := K) :=
  collision_mem_badSeeds C z i hbits hfn

end

#print axioms Nock.RedTeam.Batch341.decode_fingerprint_halt
#print axioms Nock.RedTeam.Batch341.census_majorant
#print axioms Nock.RedTeam.Batch341.collision_in_badSeeds

end Nock.RedTeam.Batch341
