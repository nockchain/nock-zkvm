/-
  Nock/NockVMROM/Thm54/TraceGen/GenEdgeSelfCensus.lean

  The edge sub-census carries no premise on the generated path.

  SCOPE FIRST.  This file is about the *comparison census* only.  It is
  NOT the soundness of the parent-to-child binding, which the paper
  splits across three mechanisms that live in three different places:

  1. Absent child slots.  `tab:V_comp_equality`
     writes `0`, not `⊥`, for slots above the opcode's fanout, so a
     prover cannot smuggle a phantom child.  In this tree that pinning
     is structural rather than a constraint: `skeletonSubformula` is
     `.atom 0` above `fanoutComp s.state` (`P8Census.lean:251-255`),
     `WalkSat`'s child sum ranges only over `Icc 1 (fo i)`, and
     `Walk_IOP_final_*` presents children as
     `if j < fo i then some (clab i (j+1)) else none` under
     `hfo : fo i = St.fanout (lbl i).1` (`Walk.lean:2845-2874`).

  2. The child *output* `sf_i_e`.  Mostly unconstrained in-row -- the
     "(optimistic) evaluation... checked later on in the tree" of
     the paper bound to the child's own row by the
     line-indexed multiset accumulator of `RAP_walk`
     at the recognizer setting `seed = RLC^γ(root)·α`,
     `initial_count = α`, `out_walk = 0`.  THIS is
     where the soundness of the edge binding lives, and it is closed in
     `Nock/Walk.lean`: `ln_closed`, `count_closed`, `acc_telescope`,
     `acc_closed`, `walk_out_zero_iff`, Schwartz-Zippel
     `walk_soundness_card`, and the inverse-BFS reconstruction
     `reconTree_ReconGoal` composed as `Walk_IOP_final_card/_prob`
     (= `«Thm:Walk_IOP»`), with the honest `ε_RLC` term the paper omits.  Fingerprint collisions there are bounded by `enc`
     injectivity plus `ε_RLC` -- a DIFFERENT fingerprint from the one
     the census separates.

  3. The child *inputs* `sf_i_s`, `sf_i_f`.  That bridge is the
     comparison census, and mechanism 3 is the ONLY one this file
     touches.

  What is proved here: `childrenMatchSf` is a
  *noun-level* equality that `genComputeSkeleton` satisfies by
  construction, so on the generated path every `edgeTriple` comparison
  is a self-pair, `SepSeed z P P` is vacuous, and the edge summand of
  `combinedSkeletonPairs` contributes no bad seed.  Hence `hbad` at the
  p8 census alone discharges the combined census and no edge premise is
  carried.  Note `edgeTriple` also compares the evaluation slot, which
  the paper leaves to mechanism 2; the generated path satisfies that
  definitionally too, so holding the weaker p8 premise and deriving the
  edge half is the sound direction (cf. `p8_good_of_combined_good`,
  which runs combined -> p8).

  What is NOT proved here, and cannot be: anything about a hostile
  trace.  There `childrenMatchSf` need not hold, edge pairs are genuine
  distinct pairs, and mechanism 3 must separate them.  This is a
  statement about traces the generator produced.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenAirOrderAirLinked
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.GenericHonestCommitment

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk Nock.NockVM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.EdgeComparisonCensus

variable {K : Type} [Field K]

/-! ## A pair compares against itself at every seed -/

/-- A self-pair is bad at no seed: `SepSeed`'s hypothesis becomes `x ≠ x`.

`sepSeed_self` in that bare form already exists twice — `EqualityOperandCensus.sepSeed_self`
(`:69`) and `TraceGen.sepSeed_self` (`GenGenericSelfPairs.lean:51`) — and a third named copy
briefly lived here.  Neither existing home is in this module's import closure,
and adding an import to share a one-line `absurd rfl` would be the same bad trade `HW` §4 objects
to elsewhere, so the proof is inlined here instead of re-exported under a fourth name. -/
theorem sepSeed_of_fst_eq_snd (z : K) {pair : Noun × Noun}
    (h : pair.1 = pair.2) :
    GlobalCarryRecognizer.SepSeed z pair.1 pair.2 := by
  rw [h]
  intro hne
  exact absurd rfl hne

/-! ## `childrenMatchSf` holds at every node of an AIR-linked tree -/

/-- `AirLinked` is the everywhere form; project it at an arbitrary subtree. -/
theorem childrenMatchSf_of_inTree {t s : NTree (GenComputeRow K)}
    (h : AirLinked t) (hs : InTree t s) : childrenMatchSf s := by
  induction hs with
  | here c => exact childrenMatchSf_of_AirLinked h
  | sub hmem hsub ih =>
    apply ih
    rename_i c s' _
    cases c with
    | node g cs =>
      unfold AirLinked at h
      exact h.2 _ hmem

/-! ## Generated edge comparisons are self-pairs -/

/-- At one node, `edgeTriple` reads exactly the three slots `childrenMatchSf` pins. -/
theorem rowEdgePairs_self_of_childrenMatchSf
    {t : NTree (GenComputeRow K)} (h : childrenMatchSf t)
    {pair : Noun × Noun}
    (hp : pair ∈ rowEdgePairs (mapNTree (fun g : GenComputeRow K => g.skel) t)) :
    pair.1 = pair.2 := by
  cases t with
  | node g cs =>
    rw [rowEdgePairs, List.mem_flatMap] at hp
    obtain ⟨l, hl, hpl⟩ := hp
    rw [List.mem_ofFn] at hl
    obtain ⟨i, hi⟩ := hl
    subst hi
    simp only [id] at hpl
    -- the mapped child at slot `i`, if present
    have hch :
        (mapNTree (fun g : GenComputeRow K => g.skel) (.node g cs)).childOpt i =
          (cs[(i : ℕ)]?).map (mapNTree (fun g : GenComputeRow K => g.skel)) := by
      simp [NTree.childOpt, mapNTree, NTree.children, List.getElem?_map]
    rw [hch] at hpl
    rcases hc : cs[(i : ℕ)]? with _ | c
    · rw [hc] at hpl; simp at hpl
    · rw [hc] at hpl
      simp only [Option.map_some] at hpl
      obtain ⟨hlt, hceq⟩ := List.getElem?_eq_some_iff.mp hc
      -- `children` of a node reduces to `cs`, so the slot equations are about `cs[i]`
      have hcm0 :
          (cs[(i : ℕ)]'hlt).label.skel.subject =
              P8Census.skeletonSubformula g.skel i TripleSlot.subject ∧
            (cs[(i : ℕ)]'hlt).label.skel.formula =
              P8Census.skeletonSubformula g.skel i TripleSlot.formula ∧
            (cs[(i : ℕ)]'hlt).label.skel.evaluation =
              P8Census.skeletonSubformula g.skel i TripleSlot.result :=
        h i (by simpa [NTree.children] using hlt)
      rw [hceq] at hcm0
      rw [edgeTriple, mapNTree_label, mapNTree_label] at hpl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpl
      rcases hpl with h1 | h1 | h1
      · rw [h1]; exact hcm0.1
      · rw [h1]; exact hcm0.2.1
      · rw [h1]; exact hcm0.2.2

/-- Every edge comparison of an AIR-linked tree's skeleton is a self-pair. -/
theorem edgePairs_self_of_airLinked
    {t : NTree (GenComputeRow K)} (h : AirLinked t)
    {pair : Noun × Noun}
    (hp : pair ∈ edgePairs (mapNTree (fun g : GenComputeRow K => g.skel) t)) :
    pair.1 = pair.2 := by
  rw [edgePairs, List.mem_flatMap] at hp
  obtain ⟨node, hnode, hpn⟩ := hp
  rw [show [mapNTree (fun g : GenComputeRow K => g.skel) t] =
        [t].map (mapNTree (fun g : GenComputeRow K => g.skel)) from rfl,
    bfsForest_mapNTree, List.mem_map] at hnode
  obtain ⟨s, hs, hseq⟩ := hnode
  rw [mem_bfsForest] at hs
  obtain ⟨c, hc, hin⟩ := hs
  have hct : c = t := by simp at hc; exact hc
  subst hct
  subst hseq
  exact rowEdgePairs_self_of_childrenMatchSf (childrenMatchSf_of_inTree h hin) hpn

/-! ## The combined census needs no premise beyond p8 -/

section Finite
variable [Fintype K] [DecidableEq K]

/-- With every edge comparison a self-pair, p8 goodness *is* combined goodness. -/
theorem combined_good_of_p8_good {Λ : ℕ}
    {S : SemanticStrategy.SemanticSkeleton}
    (C : CombinedSkeletonCensus K S Λ)
    (hself : ∀ pair ∈ edgePairs S.computeTree, pair.1 = pair.2)
    (z : K) (hgood : z ∉ C.p8.census.badSeeds (K := K)) :
    z ∉ C.census.badSeeds (K := K) := by
  intro hbad
  obtain ⟨i, hi⟩ := (ComparisonCensus.mem_badSeeds_iff C.census z).1 hbad
  have hmem : C.census.pair i ∈ combinedSkeletonPairs K S := by
    have hget : C.census.pair i = (combinedSkeletonPairs K S).get
        ⟨i, by exact i.isLt⟩ := rfl
    rw [hget]
    exact List.get_mem _ _
  rw [combinedSkeletonPairs, List.mem_append] at hmem
  rcases hmem with hp8 | hedge
  · obtain ⟨j, hj⟩ :=
      ComparisonCensus.exists_pair_of_mem
        (BoundSemanticTrace.skeletonPairs K S) C.p8.leaves_bounded hp8
    apply hgood
    rw [ComparisonCensus.mem_badSeeds_iff]
    refine ⟨j, ?_⟩
    show ¬ GlobalCarryRecognizer.SepSeed z
      (C.p8.census.pair j).1 (C.p8.census.pair j).2
    rw [show C.p8.census.pair j = C.census.pair i from hj]
    exact hi
  · exact hi (sepSeed_of_fst_eq_snd z (hself _ hedge))

end Finite

/-! ## At the generated semantic skeleton -/

/-- Every edge comparison of an accepted program's AIR-ordered skeleton is a self-pair. -/
theorem edgePairs_self_of_gen
    {fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (hgen : genComputeSkeleton (K := K) fuel subject formula = .ok p)
    (mf : List (NTree (GenMemoryRow K)))
    {pair : Noun × Noun}
    (hp : pair ∈ edgePairs (genSemanticSkeleton (airReorder p.1) mf).computeTree) :
    pair.1 = pair.2 :=
  edgePairs_self_of_airLinked (airLinked_airReorder_of_gen hgen) hp

section GenFinite
variable [Fintype K] [DecidableEq K]

/-- On the generated path the combined census needs no premise beyond p8. -/
theorem combined_good_of_p8_good_gen {Λ fuel : ℕ} {subject formula : Noun}
    {p : NTree (GenComputeRow K) × Noun}
    (hgen : genComputeSkeleton (K := K) fuel subject formula = .ok p)
    (mf : List (NTree (GenMemoryRow K)))
    (C : CombinedSkeletonCensus K (genSemanticSkeleton (airReorder p.1) mf) Λ)
    (z : K) (hgood : z ∉ C.p8.census.badSeeds (K := K)) :
    z ∉ C.census.badSeeds (K := K) :=
  combined_good_of_p8_good C
    (fun _ hedge => edgePairs_self_of_gen hgen mf hedge) z hgood

end GenFinite

end Nock.NockVMROM.Thm54.TraceGen
