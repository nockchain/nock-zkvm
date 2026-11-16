/-
  Nock/NockVMROM/Thm54/TraceGen/GenBroadSeed.lean

  **The three counted seed/coin conditions of `genSemanticData`, at the broad program.**

  The broad program (`GenBroadProgram.lean`)
  has four `cons` rows, one `.s5` row with **distinct** operands and one `.s3` row whose call
  returns a **cell**, so at it:

  | condition | at Tier A | here |
  |---|---|---|
  | `SeedGood`'s `cons` clause | no `cons` row | four rows, each a polynomial condition on `z` |
  | `SeedGood`'s `.s5` clause | no `.s5` row | on the *right* disjunct: the operands differ |
  | `SeedGood`'s `.s3` clause | no `.s3` row | on the *cell* branch: `z ^ 2 ≠ z` |
  | `ComputeCoinsGeneric` | no `.s5` row, `∀ a b c` | live at the `.s5` row, needs `c = 1` |
  | `hbad` off-diagonal pairs | one (the OP6 branches) | one (the OP5 operands) |

  Everything here is stated at an arbitrary field with the field-level facts as named hypotheses, so
  the configuration module supplies numbers and nothing else.  What the table's right column says
  is not that the conditions are *harder* — it is that at this program they are **conditions**.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenBroadProgram
import Nock.NockVMROM.Thm54.TraceGen.GenGenericSelfPairs
import Nock.NockVMROM.Thm54.TraceGen.GenDyckBadSeed
import Nock.NockVMROM.Thm54.TraceGen.GenChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenCensus
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulSeed
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.P8Census
open ComputeTable

variable {K : Type} [Field K]

/-! ## `RowSeedGood`, state by state -/

/-- `SeedGood` from the row list.  `seedGood_of_bfsRows` (`GenDyckBadSeed.lean:417`) says the same
thing but sits inside that module's `[Fintype K] [DecidableEq K]` section, and neither instance is
available at a released carrier without `Fintype.ofFinite` / `Classical.decEq` (`ES.2`).  Nothing in
the statement or the proof needs them, so they are not taken. -/
theorem seedGood_of_rows {z : K} {t : NTree (GenComputeRow K)}
    (h : ∀ g ∈ bfsRows t, RowSeedGood z g) : SeedGood z t := by
  intro v hv
  have hmem : v ∈ bfsForest [t] := (mem_bfsForest [t] v).mpr ⟨t, by simp, hv⟩
  exact h v.label (List.mem_map.mpr ⟨v, hmem, rfl⟩)

theorem rowSeedGood_of_state_ne {z : K} {g : GenComputeRow K} {st : State}
    (hst : g.skel.state = st) (h1 : st ≠ .cons) (h2 : st ≠ .s5) (h3 : st ≠ .s3) :
    RowSeedGood z g :=
  ⟨fun h => absurd (hst.symm.trans h) h1,
   fun h => absurd (hst.symm.trans h) h2,
   fun h => absurd (hst.symm.trans h) h3⟩

theorem rowSeedGood_cons {z : K} {g : GenComputeRow K}
    (hst : g.skel.state = .cons)
    (hd : (encC z (formulaHead g.skel.formula)).dyck ≠ 0) :
    RowSeedGood z g :=
  ⟨fun _ => hd,
   fun h => absurd (hst.symm.trans h) (by decide),
   fun h => absurd (hst.symm.trans h) (by decide)⟩

theorem rowSeedGood_s5 {z : K} {g : GenComputeRow K}
    (hst : g.skel.state = .s5) (h : op5ResultsAgree z g.skel) :
    RowSeedGood z g :=
  ⟨fun hc => absurd (hst.symm.trans hc) (by decide),
   fun _ => h,
   fun hc => absurd (hst.symm.trans hc) (by decide)⟩

theorem rowSeedGood_s3 {z : K} {g : GenComputeRow K}
    (hst : g.skel.state = .s3) (h : op3CallSizeOk z g.skel) :
    RowSeedGood z g :=
  ⟨fun hc => absurd (hst.symm.trans hc) (by decide),
   fun hc => absurd (hst.symm.trans hc) (by decide),
   fun _ => h⟩

/-! ## `SeedGood` at the broad program

Four `cons` heads, one `.s5` operand pair, one `.s3` cell — six field-level facts and nothing
else. -/

/-- **`SeedGood` at the broad program.**  Contrast `Batch180.dot_seedGood`, which is proved `∀ z`
because every clause is vacuous at Tier A.  Here every clause of `RowSeedGood` fires at some row
and the six hypotheses below are what pays for them. -/
theorem bp_seedGood (z : K)
    (h7 : (encC z bp7).dyck ≠ 0)
    (h8 : (encC z bp8).dyck ≠ 0)
    (h5 : (encC z bp5).dyck ≠ 0)
    (h4 : (encC z bp4).dyck ≠ 0)
    (hop5 : encC z (.atom 1) ≠ encC z (.atom 2))
    (hop3 : (encC z bp3Call).size ≠ z) :
    SeedGood z (bpTree (K := K)) := by
  refine seedGood_of_rows ?_
  intro g hg
  rw [bp_bfsRows] at hg
  fin_cases hg
  · exact rowSeedGood_cons rfl h7
  · exact rowSeedGood_of_state_ne (st := .s7) rfl (by decide) (by decide) (by decide)
  · exact rowSeedGood_cons rfl h8
  · exact rowSeedGood_of_state_ne (st := .s1) rfl (by decide) (by decide) (by decide)
  · exact rowSeedGood_of_state_ne (st := .s0) rfl (by decide) (by decide) (by decide)
  · exact rowSeedGood_of_state_ne (st := .s8) rfl (by decide) (by decide) (by decide)
  · exact rowSeedGood_cons rfl h5
  · exact rowSeedGood_of_state_ne (st := .s1) rfl (by decide) (by decide) (by decide)
  · exact rowSeedGood_of_state_ne (st := .s0) rfl (by decide) (by decide) (by decide)
  · exact rowSeedGood_s5 rfl (Or.inr hop5)
  · exact rowSeedGood_cons rfl h4
  · exact rowSeedGood_of_state_ne (st := .s1) rfl (by decide) (by decide) (by decide)
  · exact rowSeedGood_of_state_ne (st := .s1) rfl (by decide) (by decide) (by decide)
  · exact rowSeedGood_of_state_ne (st := .s4) rfl (by decide) (by decide) (by decide)
  · exact rowSeedGood_s3 rfl hop3
  · exact rowSeedGood_of_state_ne (st := .s1) rfl (by decide) (by decide) (by decide)
  · exact rowSeedGood_of_state_ne (st := .s1) rfl (by decide) (by decide) (by decide)

/-! ## `ComputeCoinsGeneric` — live at the `.s5` row, discharged at `c = 1`

`Batch180.dot_computeCoins` is `∀ a b c` because Tier A has no `.s5` row.  Here the coin obligation
is real; `op5C1Ready` holds because the two operands are atoms, which is what
`rlc5Holds_c_one_of_atom_or_eq` needs (`GenWF.lean:278`). -/

/-- The `.s5` row's operands are the atoms `1` and `2`, so `op5C1Ready` holds by its right
disjunct. -/
theorem bp_air_op5C1 :
    ∀ v, InTree (bpTreeAir (K := K)) v → v.label.skel.state = State.s5 →
      op5C1Ready v.label.skel := by
  intro v hv hs
  have hmem : v ∈ bfsForest [bpTreeAir (K := K)] :=
    (mem_bfsForest _ v).mpr ⟨_, List.mem_singleton.mpr rfl, hv⟩
  rw [bp_air_bfsForest] at hmem
  fin_cases hmem <;> first
    | exact Or.inr ⟨1, 2, rfl, rfl⟩
    | exact Or.inl rfl
    | exact absurd hs (by
        simp [bpTreeAir, bp7TreeAir, bpR1TreeAir, bp8TreeAir, bpR2Tree, bpR3Tree,
          bp5Tree, bp4Tree, bp3Tree, bp7CTree, bp8CTree, bpOp1Tree, skelNode,
          genSkelCons, genSkelOp7, genSkelOp8, genSkelOp5, genSkelOp4, genSkelOp3,
          genSkelOp1, genSkelOp0])

/-- **The coin condition at the broad program**, at coins `(0, 0, 1)`. -/
theorem bp_computeCoins (z α : K) :
    ComputeCoinsGeneric z α 0 0 1 (airReorder (bpTree (K := K))) := by
  rw [airReorder_bpTree]
  exact computeCoinsGeneric_c_one z α _ bp_air_op5C1

/-! ## `hbad` — one off-diagonal pair over seventeen rows

`GenGenericSelfPairs` says which comparisons can be off-diagonal at all: only `.s5`'s
`equalityOperand` and `.s6`'s untaken branch.  This program has one `.s5` row and no `.s6` row, so
the whole census reduces to one pair. -/

/-- Every census comparison of every row of this program is a self-pair, except the `.s5`
`equalityOperand` pair `(1, 2)`.

`hchar` is the no-wrap condition the `.s4` row needs: the census compares the increment against
`incMod (ringChar K)` and the generator emits `Noun.lus`, and they agree because `2 < ringChar K`. -/
theorem bp_air_comparisons (hchar : 2 < ringChar K) :
    ∀ g ∈ bfsRows (bpTreeAir (K := K)),
      ∀ c ∈ skeletonComparisons (K := K) g.skel,
        c.left = c.right ∨ (c.left = .atom 1 ∧ c.right = .atom 2) := by
  have hinc : OpcodeSemantics.incMod (ringChar K) (.atom 1) = (.atom 2 : Noun) := by
    norm_num [OpcodeSemantics.incMod, Nat.mod_eq_of_lt hchar]
  intro g hg
  rw [bp_air_bfsRows] at hg
  fin_cases hg
  · exact fun c hc => Or.inl (selfPairs_genSkelCons bpSubject bp7 bpR1 (.atom 5) bpR1Result c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelOp7 bpSubject bp7B bp7C bp7Sb bp7Sb c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelCons bpSubject bp8 bpR2 bpSubject bpR2Result c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelOp0 bp7Sb bp7Sb 1 c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelOp1 bpSubject (.atom 5) c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelOp8 bpSubject bp8B bp8C bp8Sb bpSubject c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelCons bpSubject bp5 bpR3 (.atom 1) bpR3Result c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelOp0 bp8Pushed bpSubject 3 c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelOp1 bpSubject (.atom 3) c hc)
  · exact fun c hc => selfPairs_genSkelOp5 bpSubject bp5B bp5C (.atom 1) (.atom 2) c hc
  · exact fun c hc => Or.inl (selfPairs_genSkelCons bpSubject bp4 bp3 (.atom 2) (.atom 0) c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelOp1 bpSubject (.atom 1) c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelOp1 bpSubject (.atom 2) c hc)
  · exact fun c hc =>
      Or.inl (selfPairs_genSkelOp4 bpSubject bp4Tail (.atom 1) (.atom 2) hinc c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelOp3 bpSubject bp3Tail bp3Call c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelOp1 bpSubject (.atom 1) c hc)
  · exact fun c hc => Or.inl (selfPairs_genSkelOp1 bpSubject bp3Call c hc)

/-- **Separation at every census pair of the broad program**, from the single field-level fact
`SepSeed z 1 2`.  The three root/public-claim pairs are self-pairs at every skeleton
(`ES.2`); the row comparisons are `bp_air_comparisons`. -/
theorem bp_pairs_sep (z : K) (hchar : 2 < ringChar K)
    (hsep : GlobalCarryRecognizer.SepSeed z (.atom 1) (.atom 2))
    (mf : List (NTree (GenMemoryRow K))) :
    ∀ pr ∈ BoundSemanticTrace.skeletonPairs K
        (genSemanticSkeleton (bfsAssign (airReorder (bpTree (K := K)))) mf),
      GlobalCarryRecognizer.SepSeed z pr.1 pr.2 := by
  have hrows : ∀ s ∈ computeSkeletonRows
      (genSemanticSkeleton (bfsAssign (airReorder (bpTree (K := K)))) mf),
      ∀ c ∈ skeletonComparisons (K := K) s,
        GlobalCarryRecognizer.SepSeed z c.left c.right := by
    refine bfsAssign_computeSkeletonRows_of_bfsRows _ _ mf ?_
    rw [airReorder_bpTree]
    intro g hg c hc
    rcases bp_air_comparisons hchar g hg c hc with h | ⟨hl, hr⟩
    · exact sepSeed_of_eq h
    · rw [hl, hr]; exact hsep
  intro pr hpr
  simp only [BoundSemanticTrace.skeletonPairs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hpr
  rcases hpr with (rfl | rfl | rfl) | h
  · exact sepSeed_self z _
  · exact sepSeed_self z _
  · exact sepSeed_self z _
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    rw [skeletonComparisonCensus, List.mem_flatMap] at hc
    obtain ⟨s, hs, hcs⟩ := hc
    exact hrows s hs c hcs

/-- `z ∉ badSeeds` is exactly separation at every census pair. -/
theorem not_mem_badSeeds_of_pairs [Fintype K] [DecidableEq K]
    {S : SemanticSkeleton} {Λ : ℕ}
    (C : BoundSemanticTrace.SkeletonP8Census K S Λ) (z : K)
    (h : ∀ pr ∈ BoundSemanticTrace.skeletonPairs K S,
      GlobalCarryRecognizer.SepSeed z pr.1 pr.2) :
    z ∉ C.census.badSeeds (K := K) := by
  intro hmem
  obtain ⟨i, hi⟩ := (ComparisonCensus.mem_badSeeds_iff _ z).mp hmem
  exact hi (h _ (List.get_mem _ i))

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_seedGood
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_computeCoins
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_air_comparisons
#print axioms Nock.NockVMROM.Thm54.TraceGen.bp_pairs_sep
#print axioms Nock.NockVMROM.Thm54.TraceGen.not_mem_badSeeds_of_pairs
