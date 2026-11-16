/-
  Nock/RedTeam/Batch1590Thm54SVFrameFibre.lean

* the summand lists of both families and the statement's `joint` list carry no verifier datum
        (their types, `#check`): a summand cannot read `CF.skeleton V x b`, `windowAt … V msg …` or
        any `V`-indexed weight;
      * `s0_census_reads_axis` / `s0_census_depends_on_axis`: the C2 join's comparison list at an
        OP0 row contains the pair `(f_t, atom (ax (S+2)))`, so the NPR census bad set is a function
        of the axis oracle `ax`; in `CtxWObligation` that oracle is `axisOfRecords … (CF.reqFacts …
        hacc.compute …)`, i.e. it exists only under an acceptance proof, not as a function of the
        traces.
-/
import Nock.NockVMROM.Thm54.P8Core.SVFrame.FibreBound
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1590

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.SVFrame
open Nock.ComputeTable (State)
open Nock.MemoryTable (MState)

/-! ## §A  The frame -/

#print axioms Nock.NockVMROM.Thm54.SVFrame.frame12_sampledAfter
#print axioms Nock.NockVMROM.Thm54.SVFrame.ioCoins12
#print axioms Nock.NockVMROM.Thm54.SVFrame.chipWalk_width
#print axioms Nock.NockVMROM.Thm54.SVFrame.tracesStaged_const
#check @Nock.NockVMROM.Thm54.SVFrame.RecordView
#check @Nock.NockVMROM.Thm54.SVFrame.VerifierData.Checks.hp
#check @Nock.NockVMROM.Thm54.SVFrame.MemSoundnessFamily.ioFacts
#check @Nock.NockVMROM.Thm54.SVFrame.MemSoundnessFamily.serves
#check @Nock.NockVMROM.Thm54.SVFrame.CompSoundnessFamily.reqFacts
#check @Nock.NockVMROM.Thm54.SVFrame.StandaloneThm54Statement
#check @Nock.NockVMROM.Thm54.SVFrame.CtxWObligation

/-! ## §B  The fibre bound, the union bound, the negative control -/

#print axioms Nock.NockVMROM.Thm54.SVFrame.BadSummand.event_card_le
#print axioms Nock.NockVMROM.Thm54.SVFrame.BadSummand.event_prob_le
#print axioms Nock.NockVMROM.Thm54.SVFrame.union_card_le
#print axioms Nock.NockVMROM.Thm54.SVFrame.union_prob_le
#print axioms Nock.NockVMROM.Thm54.SVFrame.dep_meets_coins_no_bound



-- The summand lists are not indexed by the verifier datum `V` nor by the B0 messages:
#check @Nock.NockVMROM.Thm54.SVFrame.MemSoundnessFamily.summands
#check @Nock.NockVMROM.Thm54.SVFrame.CompSoundnessFamily.summands
#check @Nock.NockVMROM.Thm54.SVFrame.StandaloneThm54Statement.soundness

section Census

variable {K : Type} [Field K]

/-- **The NPR census reads the axis oracle.**  At an OP0 row of the field C2 join, the comparison
list contains `(f_t, atom (ax (S + 2)))` (`P8Census.skeletonComparisons`, `.s0` arm, third use:
`.atom (skeletonMemoryAxis s 1)`, record 1 = `⟨subj, …, ax (S + 2)⟩`). -/
theorem s0_census_reads_axis (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (S : ℕ)
    (subj f : Noun) (kids : List SemanticStrategy.ComputeRowSkeleton) :
    ∃ c ∈ P8Census.skeletonComparisons (K := K) (SVJoinF.c2SkeletonRowF q sv ax .s0 S subj f kids),
      c.right = .atom (ax (S + 2)) := by
  simp [P8Census.skeletonComparisons, P8Census.skeletonMemoryAxis, Nock.Framework.recordCount,
    SVJoinF.c2SkeletonRowF, P8Census.skeletonUse]
  <;> (right; rfl)

/-- The OP0 row's third comparison, by definition. -/
theorem s0_third_comparison (q : ℕ) (sv : MState → ℕ → Noun) (ax : ℕ → ℕ) (S : ℕ)
    (subj f : Noun) (kids : List SemanticStrategy.ComputeRowSkeleton) :
    (P8Census.skeletonComparisons (K := K) (SVJoinF.c2SkeletonRowF q sv ax .s0 S subj f kids))[2]? =
      some (P8Census.skeletonUse .recursiveFormula (StrategyOfTracesLift.nounTail f)
        (.atom (ax (S + 2)))) := rfl

/-- Two axis oracles that differ at `S + 2` give different OP0 comparison lists: the census bad
set at a skeleton is not determined by the skeleton and the served nouns alone. -/
theorem s0_census_depends_on_axis (q : ℕ) (sv : MState → ℕ → Noun) (ax ax' : ℕ → ℕ) (S : ℕ)
    (subj f : Noun) (kids : List SemanticStrategy.ComputeRowSkeleton) (h : ax (S + 2) ≠ ax' (S + 2)) :
    P8Census.skeletonComparisons (K := K) (SVJoinF.c2SkeletonRowF q sv ax .s0 S subj f kids) ≠
      P8Census.skeletonComparisons (K := K) (SVJoinF.c2SkeletonRowF q sv ax' .s0 S subj f kids) := by
  intro he
  have h3 := congrArg (fun l : List SemanticTrace.ComparisonUse => l[2]?) he
  simp only [s0_third_comparison, Option.some.injEq, P8Census.skeletonUse,
    SemanticTrace.ComparisonUse.mk.injEq, Noun.atom.injEq] at h3
  exact h h3.2.2

end Census

#print axioms s0_census_reads_axis
#print axioms s0_census_depends_on_axis

end Nock.RedTeam.Batch1590
