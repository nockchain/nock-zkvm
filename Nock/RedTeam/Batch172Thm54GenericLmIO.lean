/-
  Nock/RedTeam/Batch172Thm54GenericLmIO.lean

  **The generic `L_mIO` is not a fixture claim, and it is not vacuous.**

  `genSemantic_lmio` / `genTimestampSkeleton_lmio` (`GenSemanticLmIO.lean`) prove `Def:L_mIO` between the compute table's requests and the memory table's responses for
  *any* program `genComputeSkeleton` accepts, at *any* field, over *any* seed and challenge.
  Two things have to be checked before that sentence is worth anything.

  1. **It applies where the writer was not looking.**  Here
     that is `DotConfig769` — a different field (`GaloisField 769 3` vs `GaloisField 65537 3`), a
     different program, and, decisively, a carrier that does **not** use `genTimestampSkeleton` at
     all: Tier A hand-writes thirteen request and thirteen response records
     (`GenTierASemantic.lean`).  So Tier A has no stake in this route and cannot have been fitted
     to it.  `dot_lmio` below is the generic theorem at Tier A's program, field, seed, challenge
     and declared `Ksz = 64`.

  2. **The lists are not empty.**  `L_mIO` with an empty request list would be satisfiable and
     say nothing; `Def:L_mIO`'s own `1 ≤ |requests|` rules that out, and `dot_requests_pos` /
     `dot_responses_pos` witness it concretely at Tier A.

  A third check comes for free from the shape of the side condition.  `hKsz` is
  `accAt … ≤ Ksz` — the `[K]` window of the paper — and `lmio_at_own_window` discharges it by
  `le_rfl` for every accepted program, so no program is excluded by it; a configuration only has to
  declare a `Ksz` at least as large as its own request count.

  Also recorded: the relation is `L_IO`, not merely `L_mIO` — the generator is
  *unique request*, so `cor_uni_req_uni_resp` (`:613`)
  applies.  `dot_lio` is that at Tier A.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticLmIO
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrder
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulNodup
import Nock.NockVMROM.Thm54.TraceGen.GenTierAConfig769
import Nock.NockVMROM.Thm54.ForestExponentWindow

set_option autoImplicit false

namespace Nock.RedTeam.Batch172

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

/-! ## The side condition never excludes a program -/

variable {K : Type} [Field K] {F : Type} [Field F] [Algebra F K]

/-- **`hKsz` is satisfiable at every accepted program**, by taking the window to be the request
count itself.  So the only hypothesis of `genSemantic_lmio` beyond acceptance is a *declaration*
about `Ksz`, not a restriction on which programs compile. -/
theorem lmio_at_own_window (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    IO.LmIO (accAt (airReorder t) (bfsRows (airReorder t)).length)
      ((genSemanticRequests
          (genSemanticSkeleton (bfsAssign (airReorder t))
            (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (airReorder t))))
          (bfsStamps (bfsAssign (airReorder t)))).map (SemanticTimestampSkeleton.semanticRecordAt (F := F) z))
      ((genSemanticResponses
          (genSemanticSkeleton (bfsAssign (airReorder t))
            (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (airReorder t))))
          (genMemoryStamps
            (genMemForestFromTree (encC z) z α MemoryTable.formRDefault (bfsAssign (airReorder t))))).map
        (SemanticTimestampSkeleton.semanticRecordAt (F := F) z)) :=
  genSemantic_lmio (F := F) _ z α h le_rfl

/-! ## At Tier A: a different field, a different program, and a carrier built the other way -/

/-- Tier A's field: `GaloisField 769 3`. -/
abbrev DK := DotConfig769.K

/-- Tier A's base field: `ZMod 769`. -/
abbrev DF := DotConfig769.F

/-- Tier A's seed and table challenge.  Qualified: `TraceGen.seedZ` is a different (`ZMod 97`)
constant. -/
noncomputable abbrev dz : DK := DotConfig769.seedZ

/-- Tier A's table challenge. -/
noncomputable abbrev da : DK := DotConfig769.alphaA

/-- The AIR-ordered dot tree has eight BFS rows.  `airReorder_dotTree` identifies the generic
route's tree with the one the configuration commits. -/
theorem dot_air_rows :
    (bfsRows (airReorder (dotTree (K := DK)))).length = 8 := by
  rw [airReorder_dotTree, dot_air_bfsRows]
  rfl

/-- The window condition at Tier A's **declared** `Ksz = 64`: at most three records per row over
eight rows. -/
theorem dot_accAt_le_Ksz :
    accAt (airReorder (dotTree (K := DK)))
        (bfsRows (airReorder (dotTree (K := DK)))).length
      ≤ (DotConfig769.cfg dz da).Ksz := by
  rw [dot_air_rows]
  exact le_trans (accAt_le_three_mul _ 8) (by norm_num [DotConfig769.cfg])

/-- The memory forest the generic route serves for Tier A's program. -/
noncomputable def dotForest : List (NTree (GenMemoryRow DK)) :=
  genMemForestFromTree (encC dz) dz da MemoryTable.formRDefault
    (bfsAssign (airReorder (dotTree (K := DK))))

theorem dotForest_wf : ∀ root ∈ dotForest, memoryStampsWellFormed root :=
  genComputeSkeleton_memForest_stampsWellFormed dz da
    (genComputeSkeleton_dot 0)

/-- The generic timestamp skeleton at Tier A's program.  Tier A's own carrier never builds this
object — it hand-writes its records instead — which is exactly why it is a fair target. -/
noncomputable def dotTS :
    SemanticTimestampSkeleton DF DK
      (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK)))) dotForest) :=
  genTimestampSkeleton DF (airReorder (dotTree (K := DK))) dotForest dotForest_wf

/-- **`L_mIO` at Tier A**, from the generic theorem alone. -/
theorem dot_lmio :
    IO.LmIO (DotConfig769.cfg dz da).Ksz
      (dotTS.semanticRequestsAt dz)
      (dotTS.semanticResponsesAt dz) :=
  genTimestampSkeleton_lmio (F := DF) _ dz da (genComputeSkeleton_dot 0)
    dotForest_wf dot_accAt_le_Ksz

/-- **And `L_IO` at Tier A** — the strict sub-language, because the
generator is unique request. -/
theorem dot_lio :
    IO.LIO (DotConfig769.cfg dz da).Ksz
      ((genSemanticRequests
          (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK)))) dotForest)
          (bfsStamps (bfsAssign (airReorder (dotTree (K := DK)))))).map
        (SemanticTimestampSkeleton.semanticRecordAt (F := DF) dz))
      ((genSemanticResponses
          (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK)))) dotForest)
          (genMemoryStamps dotForest)).map (SemanticTimestampSkeleton.semanticRecordAt (F := DF) dz)) :=
  genSemantic_lio (F := DF) _ dz da (genComputeSkeleton_dot 0) dot_accAt_le_Ksz

/-! ## Non-vacuity: the lists are nonempty -/

theorem dot_requests_pos : 1 ≤ (dotTS.semanticRequestsAt dz).length := by
  simp only [SemanticTimestampSkeleton.semanticRequestsAt, List.length_map]
  exact genSemanticRequests_length_pos (airReorder (dotTree (K := DK))) dotForest

theorem dot_responses_pos : 1 ≤ (dotTS.semanticResponsesAt dz).length := by
  have hlen : dotTS.semanticResponses.length = dotTS.semanticRequests.length :=
    genSemantic_length dz da (airReorder (dotTree (K := DK)))
      (genComputeSkeleton_air_requestsMatch (genComputeSkeleton_dot 0))
      (genComputeSkeleton_memForest_memPubSt dz da (genComputeSkeleton_dot 0))
  simp only [SemanticTimestampSkeleton.semanticResponsesAt, List.length_map]
  rw [hlen]
  exact genSemanticRequests_length_pos (airReorder (dotTree (K := DK))) dotForest

end Nock.RedTeam.Batch172

#print axioms Nock.RedTeam.Batch172.lmio_at_own_window
#print axioms Nock.RedTeam.Batch172.dot_lmio
#print axioms Nock.RedTeam.Batch172.dot_lio
#print axioms Nock.RedTeam.Batch172.dot_requests_pos
#print axioms Nock.RedTeam.Batch172.dot_responses_pos
