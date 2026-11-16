/-
  Nock/RedTeam/Batch166Thm54GenericPipeAtTierA.lean

  **The generic route reproduces a live configuration's own census extras.**

  `DP` made `census` generic and `DT` added `sizeWindowBound` alongside it, both resting on the
  decidable `TraceConfined`.  That is worth nothing if the generic statements are the *wrong shape*
  — close enough to look right in prose, not close enough for a configuration to consume.  The
  claim needs a live target.

  `DotConfig769` is that target: a released Tier A configuration whose `Data` is built and whose
  `census` and `sizeWindowBound` fields are proved by hand, `census_skel` by an eight-way case split
  over the row list (`GenTierAHonestData.lean:433`) resting on `compute_row_leaves` (`:326`), which
  is `RowLeafWindow` written out inline.

  This module re-derives **both** of that configuration's statements, verbatim, from the generic
  theorems with the measurement as the only input.  Nothing here replaces the configuration's own
  proofs — two independent derivations agreeing is stronger evidence than one replacing the other.

  **The size-window half is much weaker evidence than the census half, and is labelled as such.**
  At Tier A the row states are `{s6, s2, s1×5, s9}`, so `requiredSizeWindowNouns` yields exactly
  **one** noun, of **one leaf**: `dot_sizeWindowBound_from_generic` therefore asserts `1 ≤ 22` about a
  single noun, which any `Λ ≥ 1` satisfies.  The general theorem `sizeWindowBound_of_leafWindow` is
  stated at full generality and is fine; but this instance barely exercises it, and "both extras
  re-derived" would be an overstatement without this paragraph.  The census half is the real check.

  **The number checks out independently.**  `DotConfig769.Λ` is `22` (`GenTierASemanticData.lean:34`),
  fixed when the configuration was written.  `Batch164.dot_traceConfined` measures the same tree and
  gets `22`, with `dot_not_traceConfined_21` showing `21` fails.  So the hand-chosen window and the
  decidable measurement agree, and agree *tightly*.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericCensusWindow
import Nock.NockVMROM.Thm54.TraceGen.GenTierAHonestData
import Nock.RedTeam.Batch164Thm54TraceConfined

set_option autoImplicit false

namespace Nock.RedTeam.Batch166

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.EdgeComparisonCensus
open Nock.NockVMROM.Thm54.SizeWindowCounting

/-- The configuration's field: `GaloisField 769 3`. -/
abbrev DK := DotConfig769.K

/-- The generated tree at the AIR ordering is the one the configuration commits, and it is
`Λ`-confined at the configuration's own `Λ = 22`. -/
theorem dot_air_traceConfined :
    TraceConfined DotConfig769.Λ (airReorder (dotTree (K := DK))) := by
  rw [airReorder_dotTree]
  exact Batch164.dot_traceConfined

/-- **`DotConfig769.census_skel`, re-derived generically.**

The configuration's own proof is an eight-way case split over its row list; this one knows nothing
about the program except that `genComputeSkeleton` accepted it and that `22` confines it. -/
theorem dot_census_from_generic (z α : DK) :
    CombinedSkeletonCensus DK
      (genSemanticSkeleton (bfsAssign (dotTreeAir (K := DK)))
        (DotConfig769.assignedForest z α)) DotConfig769.Λ := by
  have h := genComputeSkeleton_census_gen (K := DK) (Λ := DotConfig769.Λ) (by decide)
    (genComputeSkeleton_dot 0) dot_air_traceConfined (DotConfig769.assignedForest z α)
  rwa [airReorder_dotTree] at h

/-- **`DotConfig769.sizeWindowBound_skel`, re-derived generically** — from the *same* measurement,
with no separate argument. -/
theorem dot_sizeWindowBound_from_generic (z α : DK) :
    SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (dotTreeAir (K := DK)))
        (DotConfig769.assignedForest z α)) DotConfig769.Λ := by
  have h := genComputeSkeleton_sizeWindowBound_gen (K := DK) (Λ := DotConfig769.Λ) (by decide)
    (genComputeSkeleton_dot 0) dot_air_traceConfined (DotConfig769.assignedForest z α)
  rwa [airReorder_dotTree] at h

/-- The configuration's own skeleton, spelled as the configuration spells it. -/
theorem dot_census_at_semanticSkeleton :
    CombinedSkeletonCensus DK
      (DotConfig769.semanticSkeleton DotConfig769.seedZ DotConfig769.alphaA) DotConfig769.Λ :=
  dot_census_from_generic _ _

theorem dot_sizeWindowBound_at_semanticSkeleton :
    SizeWindowNounsBoundedBy
      (DotConfig769.semanticSkeleton DotConfig769.seedZ DotConfig769.alphaA) DotConfig769.Λ :=
  dot_sizeWindowBound_from_generic _ _

/-! ## The types are identical, not merely similar

Stated as theorems so the claim is checked by the elaborator rather than by reading. -/

/-- The configuration's own `census` field inhabits exactly the type derived above. -/
theorem dot_census_types_agree :
    CombinedSkeletonCensus DK
      (DotConfig769.semanticSkeleton DotConfig769.seedZ DotConfig769.alphaA) DotConfig769.Λ :=
  DotConfig769.census_skel

/-- Likewise for `sizeWindowBound`. -/
theorem dot_sizeWindowBound_types_agree :
    SizeWindowNounsBoundedBy
      (DotConfig769.semanticSkeleton DotConfig769.seedZ DotConfig769.alphaA) DotConfig769.Λ :=
  DotConfig769.sizeWindowBound_skel

/-- The configuration's hand-chosen window and the decidable measurement are the same number, and
it is the least one: `Batch164.dot_not_traceConfined_21`. -/
theorem dot_Lambda_is_the_measurement : DotConfig769.Λ = 22 := rfl

end Nock.RedTeam.Batch166

#print axioms Nock.RedTeam.Batch166.dot_air_traceConfined
#print axioms Nock.RedTeam.Batch166.dot_census_from_generic
#print axioms Nock.RedTeam.Batch166.dot_sizeWindowBound_from_generic
#print axioms Nock.RedTeam.Batch166.dot_census_at_semanticSkeleton
#print axioms Nock.RedTeam.Batch166.dot_sizeWindowBound_at_semanticSkeleton
