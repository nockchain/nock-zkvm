/-
  Nock/RedTeam/Batch180Thm54GenericSemanticDataAtTierA.lean

  This module supplies every hypothesis at Tier A — `GaloisField 769 3`, `Λ = 22`, `q = 769` — and
  obtains `dot_semanticData`.

  1. **Nothing was undischargeable.**  They exist only
     noncomputably (`Fintype.ofFinite`, `Classical.decEq`), so `local instance`s below.  Tier A's
     own `semanticData` needs neither, because it supplies `PairFaithful` per comparison and never
     forms a `Finset K` of bad seeds.

  2. **Two of the three counted seed conditions are vacuous here, and the third is thin.**  Tier A's
     row states are `{s6, s2, s1×5, s9}`, so `SeedGood` — whose three clauses are about `cons`,
     `.s5` and `.s3` rows — holds at **every** seed (`dot_seedGood`, universally quantified in `z`),
     and `ComputeCoinsGeneric` holds at **every** coin vector (`dot_computeCoins`).  The size-window
     condition is one noun of one leaf (`dot_sizeWindowNouns`, `dot_condResult_leaves`), so `hout`
     reduces to `1 < orderOf z`.  Only `hbad` has genuine content, and exactly one of its pairs is
     off-diagonal over all eight rows (`dot_offdiagonal_count`): the OP6 taken/else formula pair,
     separated because
     `8^5 ≠ 1` in `𝔽_769`.

  3. **The generic skeleton *is* Tier A's own, but the generic config is not.**  `dot_genSkeleton`
     proves `genSemanticSkeleton (bfsAssign (airReorder dotTree)) (genMemoryForest …)` **equals**
     `DotConfig769.semanticSkeleton seedZ alphaA`, and `dot_computeTree_agrees` /
     `dot_memoryForest_agrees` prove the carrier's two data fields are Tier A's own.  Nothing here closes that.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticData
import Nock.NockVMROM.Thm54.TraceGen.GenRequestAxisBound
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticLmIO
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulNodup
import Nock.RedTeam.Batch164Thm54TraceConfined
import Nock.RedTeam.Batch167Thm54GenericCarrierAtTierA
import Nock.RedTeam.Batch168Thm54AxisRangeWitness
import Nock.RedTeam.Batch169Thm54CarrierAtBothConventions

set_option autoImplicit false

namespace Nock.RedTeam.Batch180

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy

/-- Tier A's table field. -/
abbrev DK := DotConfig769.K

/-- Tier A's base field. -/
abbrev DF := DotConfig769.F

/-! ## The two instances the counted-seed formulation forces

`badSeeds` and `sizeWindowFailureSeeds` are `Finset.univ.filter`s over `K`, so `genRows` carries
`[Fintype K] [DecidableEq K]`.  Instance search finds **neither** at `GaloisField 769 3`: Mathlib
derives `Finite`, not `Fintype`, and the splitting-field construction carries no `DecidableEq`.  Both
exist, but only noncomputably.  They are `local` so nothing downstream inherits them, and the type of
`dot_semanticData` does not mention them. -/

noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _

/-! ## Identifying the generic objects with Tier A's committed ones -/

open DotConfig769 in
/-- The generic memory forest at Tier A's program **is** the forest Tier A commits. -/
theorem dot_genMemoryForest :
    genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
        (memInputs DotConfig769.seedZ) (dotTree (K := DK))
      = DotConfig769.threadedForest DotConfig769.seedZ DotConfig769.alphaA := by
  unfold genMemoryForest DotConfig769.threadedForest DotConfig769.assignedForest
  rw [airReorder_dotTree]

open DotConfig769 in
/-- The generic compute tree at Tier A's program is Tier A's rendered AIR tree. -/
theorem dot_genComputeRows :
    genComputeRows DotConfig769.seedZ DotConfig769.alphaA (dotTree (K := DK))
      = renderRows DotConfig769.seedZ DotConfig769.alphaA (bfsAssign (dotTreeAir (K := DK))) := by
  unfold genComputeRows
  rw [airReorder_dotTree]

open DotConfig769 in
/-- **The generic semantic skeleton is Tier A's own.**  Threading rewrites only the LogUp
accumulators, so it is invisible to the skeleton (`genSemanticSkeleton_threadGenForest`).  Every
skeleton-level hypothesis below transports along this equation. -/
theorem dot_genSkeleton :
    genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
          (memInputs DotConfig769.seedZ) (dotTree (K := DK)))
      = DotConfig769.semanticSkeleton DotConfig769.seedZ DotConfig769.alphaA := by
  rw [airReorder_dotTree, dot_genMemoryForest]
  unfold DotConfig769.threadedForest
  rw [genSemanticSkeleton_threadGenForest]
  rfl

/-! ## `SeedGood` — vacuous at Tier A, at every seed -/

open DotConfig769 in
/-- **`SeedGood` at Tier A holds for every `z`.**  Its three clauses are conditioned on `cons`,
`.s5` and `.s3` rows and this program has none, so the first of the three counted seed events
excludes nothing here.  Quantifying over `z` is the point: it makes the vacuity visible. -/
theorem dot_seedGood (z : DK) : SeedGood z (dotTree (K := DK)) := by
  refine seedGood_of_bfsRows z _ ?_
  intro g hg
  rw [dot_bfsRows] at hg
  fin_cases hg <;>
    exact ⟨by intro h; simp [dotTree, dotOp2Tree, dotCondTree, dotOp1BTree,
             dotOp1CTree, dotOp9Tree, dotOp9CoreTree, dotOp9InvokeTree, skelNode, genSkelOp6,
             genSkelOp2, genSkelOp1, genSkelOp9, dotOp6Skel, dotOp2Skel, dotOp9Skel] at h,
      by intro h; simp [dotTree, dotOp2Tree, dotCondTree, dotOp1BTree,
             dotOp1CTree, dotOp9Tree, dotOp9CoreTree, dotOp9InvokeTree, skelNode, genSkelOp6,
             genSkelOp2, genSkelOp1, genSkelOp9, dotOp6Skel, dotOp2Skel, dotOp9Skel] at h,
      by intro h; simp [dotTree, dotOp2Tree, dotCondTree, dotOp1BTree,
             dotOp1CTree, dotOp9Tree, dotOp9CoreTree, dotOp9InvokeTree, skelNode, genSkelOp6,
             genSkelOp2, genSkelOp1, genSkelOp9, dotOp6Skel, dotOp2Skel, dotOp9Skel] at h⟩

/-! ## `ComputeCoinsGeneric` — vacuous at Tier A, at every coin vector -/

open DotConfig769 in
/-- No `.s5` row, on the AIR-ordered tree. -/
theorem dot_air_noOp5 :
    ∀ v, InTree (airReorder (dotTree (K := DK))) v →
      v.label.skel.state ≠ ComputeTable.State.s5 := by
  rw [airReorder_dotTree]
  intro v hv
  have hmem : v ∈ bfsForest [dotTreeAir (K := DK)] :=
    (mem_bfsForest _ v).mpr ⟨_, by simp, hv⟩
  rw [dot_air_bfsForest] at hmem
  fin_cases hmem <;>
    simp [dotTreeAir, dotOp2Tree, dotCondTree, dotOp1BTree, dotOp1CTree, dotOp9Tree,
      dotOp9CoreTree, dotOp9InvokeTree, skelNode, genSkelOp6, genSkelOp2, genSkelOp1,
      genSkelOp9, dotOp6Skel, dotOp2Skel, dotOp9Skel]

open DotConfig769 in
theorem dot_computeCoins (z α a b c : DK) :
    ComputeCoinsGeneric z α a b c (airReorder (dotTree (K := DK))) :=
  computeCoinsGeneric_of_noOp5 z α a b c _ dot_air_noOp5

/-! ## The size-window seed condition — one noun, of one leaf -/

open DotConfig769 SizeWindowCounting in
/-- **The whole size-window inventory of Tier A is a single noun.**  Only `.s3`, `.s4` and `.s6`
rows contribute and this program has one `.s6` row. -/
theorem dot_sizeWindowNouns :
    skeletonSizeWindowNouns
        (DotConfig769.semanticSkeleton DotConfig769.seedZ DotConfig769.alphaA)
      = [dotCondResult] := by
  rw [skeletonSizeWindowNouns, DotConfig769.semanticSkeleton_computeRows]
  simp [requiredSizeWindowNouns, dotTreeAir, dotOp2Tree, dotCondTree, dotOp1BTree,
    dotOp1CTree, dotOp9Tree, dotOp9CoreTree, dotOp9InvokeTree, skelNode, genSkelOp6,
    genSkelOp2, genSkelOp1, genSkelOp9, dotOp6Skel, dotOp2Skel, dotOp9Skel,
    P8Census.skeletonSubformula, ComputeTable.fanoutComp]

open DotConfig769 in
/-- And that noun has **one** leaf, so both conjuncts of `SizeWindow` collapse to
`1 < orderOf z`. -/
theorem dot_condResult_leaves : dotCondResult.leaves = 1 := by
  simp [dotCondResult, Noun.leaves]

open DotConfig769 SizeWindowCounting in
/-- The second counted seed event, discharged at Tier A's seed. -/
theorem dot_hout :
    DotConfig769.seedZ ∉ sizeWindowFailureSeeds (K := DK)
      (DotConfig769.semanticSkeleton DotConfig769.seedZ DotConfig769.alphaA) := by
  intro hmem
  rw [mem_sizeWindowFailureSeeds_iff] at hmem
  obtain ⟨-, n, hn, hw⟩ := hmem
  rw [dot_sizeWindowNouns] at hn
  simp only [List.mem_singleton] at hn
  subst hn
  exact hw ⟨DotConfig769.seedZ_order_gt_one,
    by rw [dot_condResult_leaves]; exact DotConfig769.seedZ_order_gt_one⟩

/-! ## The third counted seed event — `badSeeds`

Tier A's own `semanticData` never forms this set: `rowSemanticDataOf` takes `PairFaithful` per
comparison directly.  The generic route routes the same content through `z ∉ badSeeds`, so the
bridge below is what the instantiation needs. -/

/-- `z ∉ badSeeds` is exactly separation at every census pair. -/
theorem not_mem_badSeeds_of_pairs {S : SemanticSkeleton} {Λ : ℕ}
    (C : BoundSemanticTrace.SkeletonP8Census DK S Λ) (z : DK)
    (h : ∀ pr ∈ BoundSemanticTrace.skeletonPairs DK S,
      GlobalCarryRecognizer.SepSeed z pr.1 pr.2) :
    z ∉ C.census.badSeeds (K := DK) := by
  intro hmem
  obtain ⟨i, hi⟩ := (ComparisonCensus.mem_badSeeds_iff _ z).mp hmem
  exact hi (h _ (List.get_mem _ i))

open DotConfig769 in
/-- Separation at every pair of Tier A's census.  The first three pairs are the root/public-claim
bindings, which are **definitionally self-pairs**; the rest are the row comparisons, supplied by the
configuration's own `row_comparison_faithful`. -/
theorem dot_pairs_sep :
    ∀ pr ∈ BoundSemanticTrace.skeletonPairs DK
        (DotConfig769.semanticSkeleton DotConfig769.seedZ DotConfig769.alphaA),
      GlobalCarryRecognizer.SepSeed DotConfig769.seedZ pr.1 pr.2 := by
  intro pr hpr
  simp only [BoundSemanticTrace.skeletonPairs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hpr
  rcases hpr with (rfl | rfl | rfl) | h
  · exact fun hne => absurd rfl hne
  · exact fun hne => absurd rfl hne
  · exact fun hne => absurd rfl hne
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    rw [P8Census.skeletonComparisonCensus, List.mem_flatMap] at hc
    obtain ⟨s, hs, hcs⟩ := hc
    exact (DotConfig769.row_comparison_faithful s hs c hcs).separates

/-- **The first three census pairs are self-pairs at every skeleton** — they are the root row's
subject/formula/evaluation against the public claim, and `publicClaim` is *defined* as those three
projections.  `SepSeed` on a self-pair is vacuously true, so they contribute nothing to `badSeeds`
for any program. -/
theorem skeletonPairs_root_self (S : SemanticSkeleton) :
    (BoundSemanticTrace.skeletonPairs DK S).take 3
      = [(S.computeTree.label.subject, S.computeTree.label.subject),
         (S.computeTree.label.formula, S.computeTree.label.formula),
         (S.computeTree.label.evaluation, S.computeTree.label.evaluation)] := rfl

open DotConfig769 in
/-- **`hbad` is thin but not vacuous: exactly one comparison of the whole census is off-diagonal.**
Counted over all eight rows.  It is the OP6 taken/else formula pair, which
`DotConfig769.then_else_pairFaithful` separates because `8 ^ 5 ≠ 1` in `𝔽_769`; every other
comparison, and all three root pairs above, is a self-pair on which `SepSeed` is trivial. -/
theorem dot_offdiagonal_count :
    ((computeSkeletonRows
        (DotConfig769.semanticSkeleton DotConfig769.seedZ DotConfig769.alphaA)).flatMap
      (P8Census.skeletonComparisons (K := DK))).countP
        (fun c => decide (c.left ≠ c.right)) = 1 := by
  rw [DotConfig769.semanticSkeleton_computeRows]
  decide

open DotConfig769 in
/-- The off-diagonal pair is a real one: the two formulas differ and their fingerprints differ at
Tier A's seed. -/
theorem dot_offdiagonal_is_real :
    dotThenFormula ≠ dotElseFormula ∧
      NPR.fn (K := DK) dotThenFormula DotConfig769.seedZ
        ≠ NPR.fn dotElseFormula DotConfig769.seedZ :=
  ⟨by decide, DotConfig769.then_else_fn_ne⟩

/-! ## Transport of the skeleton-level hypotheses to the generic skeleton -/

open DotConfig769 in
theorem dot_gen_pairs_sep :
    ∀ pr ∈ BoundSemanticTrace.skeletonPairs DK
        (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
          (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
            (memInputs DotConfig769.seedZ) (dotTree (K := DK)))),
      GlobalCarryRecognizer.SepSeed DotConfig769.seedZ pr.1 pr.2 := by
  rw [dot_genSkeleton]
  exact dot_pairs_sep

open DotConfig769 in
theorem dot_air_traceConfined :
    TraceConfined DotConfig769.Λ (airReorder (dotTree (K := DK))) := by
  rw [airReorder_dotTree]
  exact Batch164.dot_traceConfined

open DotConfig769 in
theorem dot_hb :
    (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
      (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
        (memInputs DotConfig769.seedZ) (dotTree (K := DK)))).BoundedBy 769 := by
  rw [dot_genSkeleton]
  exact DotConfig769.semanticSkeleton_bounded _ _

open DotConfig769 in
theorem dot_haxis :
    SkeletonAxisRange 769
      (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
          (memInputs DotConfig769.seedZ) (dotTree (K := DK)))) := by
  rw [dot_genSkeleton]
  exact Batch168.dot_skeletonAxisRange

open DotConfig769 SizeWindowCounting in
theorem dot_gen_hout :
    DotConfig769.seedZ ∉ sizeWindowFailureSeeds (K := DK)
      (genSemanticSkeleton (bfsAssign (airReorder (dotTree (K := DK))))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
          (memInputs DotConfig769.seedZ) (dotTree (K := DK)))) := by
  rw [dot_genSkeleton]
  exact dot_hout

/-! ## Row counts and the timestamp window -/

open DotConfig769 in
theorem dot_memRowsLen :
    (bfsForest (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
        (memInputs DotConfig769.seedZ) (dotTree (K := DK)))).length = 184 := by
  rw [dot_genMemoryForest, bfsForest_length]
  exact DotConfig769.threaded_memRows _ _

open DotConfig769 in
theorem dot_compRowsLen :
    (bfsForest [genComputeRows DotConfig769.seedZ DotConfig769.alphaA
      (dotTree (K := DK))]).length = 8 := by
  rw [dot_genComputeRows]
  exact Batch167.tierA_compRows

open DotConfig769 in
theorem dot_air_rowsLen :
    (bfsRows (airReorder (dotTree (K := DK)))).length = 8 := by
  rw [airReorder_dotTree, dot_air_bfsRows]; rfl

open DotConfig769 in
/-- Three records per row over eight rows. -/
theorem dot_accAt_le :
    accAt (airReorder (dotTree (K := DK)))
        (bfsRows (airReorder (dotTree (K := DK)))).length ≤ 24 := by
  rw [dot_air_rowsLen]
  exact accAt_le_three_mul _ 8

/-! ## `orderOf α`

The tree carried only `14 ≤ orderOf alphaA` (`GenTierASemantic.lean:791`), which is **not** enough:
the timestamp window needs `accAt + 3 < B ≤ orderOf α` and `accAt + 3` can be `27` here.  The exact
order is computed instead, from the power table the configuration already had. -/

theorem nat_of_dvd_192 {d : ℕ} (h : d ∣ 192) (h96 : ¬ d ∣ 96) (h64 : ¬ d ∣ 64) : d = 192 := by
  have hle : d ≤ 192 := Nat.le_of_dvd (by norm_num) h
  interval_cases d <;> revert h h96 h64 <;> decide

open DotConfig769 in
theorem four_order_eq_192 : orderOf (4 : DF) = 192 := by
  refine nat_of_dvd_192 (orderOf_dvd_of_pow_eq_one DotConfig769.four_pow_192) ?_ ?_
  · intro h
    have hp : (4 : DF) ^ 96 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    rw [DotConfig769.four_pow_96] at hp
    exact absurd hp (by decide)
  · intro h
    have hp : (4 : DF) ^ 64 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    rw [DotConfig769.four_pow_64] at hp
    exact absurd hp (by decide)

open DotConfig769 in
/-- **`orderOf alphaA = 192`** — `768 = |𝔽_769^*|` and `4` generates the index-4 subgroup. -/
theorem alphaA_order_eq_192 : orderOf DotConfig769.alphaA = 192 := by
  have h := orderOf_injective DotConfig769.φ.toMonoidHom DotConfig769.φ_injective (4 : DF)
  simpa [DotConfig769.alphaA] using (h ▸ four_order_eq_192)

open DotConfig769 in
theorem dot_hinp :
    (DotConfig769.cfg DotConfig769.seedZ DotConfig769.alphaA).challenges.computeInputs
      = ⟨DotConfig769.alphaA, DotConfig769.seedZ, 0, 0, 0⟩ := rfl


open DotConfig769 in
/-- Every request axis of the assigned, AIR-reordered Tier A tree is `< ringChar`: from the
guarded ROM run at `769` and `BoundedBy 769` subject/formula (`GenRequestAxisBound`). -/
theorem dot_hlt :
    ∀ n, InTree (bfsAssign (airReorder (dotTree (K := DK)))) n →
      ∀ r ∈ extractNodeReqs n.label, r.axis < ringChar DK := by
  rw [DotConfig769.ringChar_K]
  exact skeleton_assigned_request_axes_lt (K := DK) (by norm_num)
    (genComputeSkeleton_dot (K := DK) 0)
    (show evalGRom 769 4 dotSubject dotFormula = some dotResult by
      simp [evalGRom, dotSubject, dotFormula, dotParentTail,
        dotBranchPair, dotCondFormula, dotThenFormula, dotElseFormula,
        dotThenTail, dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula,
        dotCore, dotElem0, dotElem1, dotResult, Noun.slot])
    (by simp [dotSubject])
    (by simp [dotFormula, dotParentTail, dotBranchPair, dotCondFormula, dotThenFormula,
      dotElseFormula, dotThenTail, dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail,
      dotCoreFormula, dotCore, dotElem0, dotElem1, FieldEmbedding.BoundedBy])

/-! ## The instantiation -/

open DotConfig769 in
/-- **`sd : ExactExecutionSemanticData` at `DotConfig769`, from `genSemanticData`.**

Every one of the generic theorem's hypotheses is supplied at Tier A's own field, seed, `α`,
challenge vector, coins `(0,0,0)`, `Ksz = 64`, orbit and `Λ = 22`. -/
noncomputable def dot_semanticData :
    SemanticTrace.ExactExecutionSemanticData 769 DotConfig769.Λ
      (genExactConfig (F := DF)
        (DotConfig769.cfg DotConfig769.seedZ DotConfig769.alphaA).challenges
        64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit])
        (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (dotTree (K := DK)))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault (memInputs DotConfig769.seedZ)
          (dotTree (K := DK)))
        (by rw [dot_memRowsLen]; norm_num)
        (by rw [dot_compRowsLen]; norm_num [DotConfig769.executionOrbit])
        (by rw [dot_memRowsLen]; norm_num [DotConfig769.executionOrbit]))
      (genExactExecution (F := DF)
        (DotConfig769.cfg DotConfig769.seedZ DotConfig769.alphaA).challenges
        64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit]) 0 0 0
        (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (dotTree (K := DK)))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault (memInputs DotConfig769.seedZ)
          (dotTree (K := DK)))
        (by rw [dot_memRowsLen]; norm_num)
        (by rw [dot_compRowsLen]; norm_num [DotConfig769.executionOrbit])
        (by rw [dot_memRowsLen]; norm_num [DotConfig769.executionOrbit])) :=
  genSemanticData (F := DF) DotConfig769.seedZ DotConfig769.alphaA
    DotConfig769.seedZ_ne_zero DotConfig769.two_ne_zero 0 0 0
    (DotConfig769.cfg DotConfig769.seedZ DotConfig769.alphaA).challenges
    dot_hinp (DotConfig769.memoryInputs_eq _ _)
    64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit])
    (genComputeSkeleton_dot 0)
    (dot_seedGood _)
    (dot_computeCoins _ _ _ _ _)
    (by norm_num [DotConfig769.Λ]) dot_air_traceConfined
    (by show 0 < (bfsForest (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA
        MemoryTable.formRDefault (memInputs DotConfig769.seedZ) (dotTree (K := DK)))).length
        rw [dot_memRowsLen]; norm_num)
    (by rw [dot_compRowsLen]; norm_num [DotConfig769.executionOrbit])
    (by show (bfsForest (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA
        MemoryTable.formRDefault (memInputs DotConfig769.seedZ) (dotTree (K := DK)))).length ≤ 2 ^ DotConfig769.executionOrbit.h
        rw [dot_memRowsLen]; norm_num [DotConfig769.executionOrbit])
    192 (le_of_eq alphaA_order_eq_192.symm)
    (by have := dot_accAt_le; omega)
    (by have := dot_accAt_le; omega)
    dot_hb (by norm_num) DotConfig769.ringChar_K.symm dot_haxis
    (not_mem_badSeeds_of_pairs _ _ dot_gen_pairs_sep)
    dot_gen_hout dot_hlt

/-! ## How much of Tier A's own carrier the generic one reproduces

`Batch167` established agreement on three of `ExactConfig`'s seventeen fields and explicitly deferred
the rest.  Two more agreements are available at the *execution* level and are recorded here; the
config-level equality is still **not** claimed. -/

open DotConfig769 in
/-- **The generic carrier's compute tree is Tier A's own**, once the coin overwrite at `(0,0,0)` is
pushed through the rendering. -/
theorem dot_computeTree_agrees :
    (genExactExecution (F := DF)
        (DotConfig769.cfg DotConfig769.seedZ DotConfig769.alphaA).challenges
        64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit]) 0 0 0
        (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (dotTree (K := DK)))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault (memInputs DotConfig769.seedZ)
          (dotTree (K := DK)))
        (by rw [dot_memRowsLen]; norm_num)
        (by rw [dot_compRowsLen]; norm_num [DotConfig769.executionOrbit])
        (by rw [dot_memRowsLen]; norm_num [DotConfig769.executionOrbit])).computeTree
      = DotConfig769.computeTree DotConfig769.seedZ DotConfig769.alphaA := by
  show mapNTree (fun g : GenComputeRow DK => setRowCoins 0 0 0 g.row)
      (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (dotTree (K := DK))) = _
  rw [Batch169.carrier_at_tierA_convention, dot_genComputeRows]
  rfl

open DotConfig769 in
theorem dot_memoryForest_agrees :
    (genExactExecutionA (F := DF)
        (DotConfig769.cfg DotConfig769.seedZ DotConfig769.alphaA).challenges
        64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit]) 0 0 0
        (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (dotTree (K := DK)))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault (memInputs DotConfig769.seedZ)
          (dotTree (K := DK)))
        (by rw [dot_memRowsLen]; norm_num)
        (by rw [dot_compRowsLen]; norm_num [DotConfig769.executionOrbit])
        (by rw [dot_memRowsLen]; norm_num [DotConfig769.executionOrbit])).memoryForest
      = DotConfig769.memoryForestThreaded DotConfig769.seedZ DotConfig769.alphaA := by
  show (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault (memInputs DotConfig769.seedZ)
      (dotTree (K := DK))).map (mapNTree GenMemoryRow.row) = _
  rw [dot_genMemoryForest]
  rfl

end Nock.RedTeam.Batch180

#print axioms Nock.RedTeam.Batch180.dot_genSkeleton
#print axioms Nock.RedTeam.Batch180.dot_seedGood
#print axioms Nock.RedTeam.Batch180.dot_computeCoins
#print axioms Nock.RedTeam.Batch180.dot_sizeWindowNouns
#print axioms Nock.RedTeam.Batch180.skeletonPairs_root_self
#print axioms Nock.RedTeam.Batch180.dot_offdiagonal_count
#print axioms Nock.RedTeam.Batch180.dot_offdiagonal_is_real
#print axioms Nock.RedTeam.Batch180.alphaA_order_eq_192
#print axioms Nock.RedTeam.Batch180.dot_semanticData
#print axioms Nock.RedTeam.Batch180.dot_computeTree_agrees
#print axioms Nock.RedTeam.Batch180.dot_memoryForest_agrees
