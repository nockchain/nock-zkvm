/-
  Nock/NockVMROM/Thm54/TraceGen/GenGenericOffdiag.lean

  **Generated AIR census pairs are diagonal, or `.s5`/`.s6` off-diag.**

  `hbad` of `nockCompiles_of_grom_atTree_p62` is `z ∉ census.badSeeds`, and
  `ComparisonCensus.badSeeds` is the `SepSeed` roots of `boundPairs`
  (`JointSoundness.lean::badSeeds`, `P8Census.lean::boundPairs`).  On a generated
  trace the only nouns that can differ are OP5 equality operands and the OP6
  untaken branch (`GenGenericSelfPairs`).  This module lifts those per-constructor
  lemmas along `genComputeSkeleton`.

  Completeness, not a new bound summand: `collisionFailureEvent = liftSeed
  C.badSeeds` is already in `ProductionP8Containment.FailureUnion`, priced in
  `p8Work` as `(3+19·rows)·(2Λ−1)`.
-/
import Nock.FieldEmbedding
import Nock.NockVMROM.Thm54.TraceGen.GenGenericSelfPairs
import Nock.NockVMROM.Thm54.TraceGen.GenSkeletonFanout
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Noun Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.P8Census
open Nock.NockVMROM.Thm54.SemanticTrace
open ComputeTable

variable {K : Type} [Field K]

/-! ## The classification -/

/-- Every census comparison of this row is a self-pair, or the `.s5` operand
pair, or an `.s6` off-diagonal `recursiveFormula`. -/
def ComparisonClassified (g : GenComputeRow K) : Prop :=
  ∀ c ∈ skeletonComparisons (K := K) g.skel,
    c.left = c.right
    ∨ (g.skel.state = .s5 ∧ c.role = .equalityOperand)
    ∨ (g.skel.state = .s6 ∧ c.role = .recursiveFormula ∧ c.left ≠ c.right)

/-- OP4 wrap: `incMod (ringChar K)` agrees with the emitted evaluation. -/
def IncWrap (u : NTree (GenComputeRow K)) : Prop :=
  u.label.skel.state = .s4 →
    OpcodeSemantics.incMod (ringChar K)
      (skeletonSubformula u.label.skel 0 TripleSlot.result)
      = u.label.skel.evaluation

theorem incWrap_sub {lab : GenComputeRow K} {cs : List (NTree (GenComputeRow K))}
    {child : NTree (GenComputeRow K)}
    (hwrap : ∀ u, InTree (.node lab cs) u → IncWrap u)
    (hc : child ∈ cs) :
    ∀ u, InTree child u → IncWrap u :=
  fun u hu => hwrap u (InTree.sub hc hu)

theorem comparisonClassified_of_self {g : GenComputeRow K}
    (h : ∀ c ∈ skeletonComparisons (K := K) g.skel, c.left = c.right) :
    ComparisonClassified g :=
  fun c hc => Or.inl (h c hc)

theorem comparisonClassified_op5 {g : GenComputeRow K} {c : ComparisonUse}
    (hst : g.skel.state = .s5) (hr : c.role = .equalityOperand) :
    c.left = c.right
      ∨ (g.skel.state = .s5 ∧ c.role = .equalityOperand)
      ∨ (g.skel.state = .s6 ∧ c.role = .recursiveFormula ∧ c.left ≠ c.right) :=
  Or.inr (Or.inl ⟨hst, hr⟩)

theorem comparisonClassified_op6 {g : GenComputeRow K} {c : ComparisonUse}
    (hst : g.skel.state = .s6) (hr : c.role = .recursiveFormula)
    (hne : c.left ≠ c.right) :
    c.left = c.right
      ∨ (g.skel.state = .s5 ∧ c.role = .equalityOperand)
      ∨ (g.skel.state = .s6 ∧ c.role = .recursiveFormula ∧ c.left ≠ c.right) :=
  Or.inr (Or.inr ⟨hst, hr, hne⟩)

/-- Generated-row facts used to name the `.s6` off-diag pair. -/
structure GeneratedCmpShape (g : GenComputeRow K) : Prop where
  classified : ComparisonClassified g
  s6_taken_branch :
    g.skel.state = .s6 →
      skeletonSubformula g.skel 0 TripleSlot.formula = skeletonDec g.skel .f_tth
      ∨ skeletonSubformula g.skel 0 TripleSlot.formula = skeletonDec g.skel .f_ttt
  s6_cond_self :
    g.skel.state = .s6 →
      skeletonSubformula g.skel 1 TripleSlot.formula = skeletonDec g.skel .f_th

theorem generatedCmpShape_of_self {g : GenComputeRow K}
    (hclass : ComparisonClassified g) (hne : g.skel.state ≠ .s6) :
    GeneratedCmpShape g :=
  ⟨hclass, fun hs => absurd hs hne, fun hs => absurd hs hne⟩

/-! ## Fuel induction on the raw generator tree -/

/-- Every `InTree` node of an accepted program has classified census pairs
and the two `.s6` branch identities. -/
theorem generated_comparisons_self_or_offdiag_inTree
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hwrap : ∀ u, InTree t u → IncWrap u)
    (u : NTree (GenComputeRow K)) (hu : InTree t u) :
    GeneratedCmpShape u.label := by
  induction fuel generalizing subject formula t result u with
  | zero =>
    simp [genComputeSkeleton] at h
  | succ n ih =>
    cases formula with
    | atom _ =>
      simp [genComputeSkeleton] at h
    | cell hd tl =>
      cases hd with
      | cell lh lt =>
        cases hL : genComputeSkeleton (K := K) n subject (.cell lh lt) with
        | error _ => simp [genComputeSkeleton, hL] at h
        | ok pL =>
          cases hR : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hL, hR] at h
          | ok pR =>
            simp [genComputeSkeleton, hL, hR] at h
            obtain ⟨rfl, rfl⟩ := h
            cases hu with
            | here =>
              exact generatedCmpShape_of_self
                (comparisonClassified_of_self fun c hc =>
                  selfPairs_genSkelCons subject (.cell lh lt) tl pL.2 pR.2 c
                    (by simpa [skelNode] using hc))
                (by simp [skelNode, genSkelCons])
            | sub hs hu' =>
              simp [NTree.children] at hs
              rcases hs with rfl | rfl
              · exact ih hL (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
              · exact ih hR (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        · cases tl with
          | cell _ _ => simp [genComputeSkeleton] at h
          | atom ax =>
            cases hslot : Noun.slot ax subject with
            | none => simp [genComputeSkeleton, hslot] at h
            | some slotR =>
              simp [genComputeSkeleton, hslot] at h
              obtain ⟨rfl, rfl⟩ := h
              cases hu with
              | here =>
                exact generatedCmpShape_of_self
                  (comparisonClassified_of_self fun c hc =>
                    selfPairs_genSkelOp0 subject slotR ax c (by simpa [skelNode] using hc))
                  (by simp [skelNode, genSkelOp0])
              | sub hs _ =>
                simp [NTree.children] at hs
        · simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hu with
          | here =>
            exact generatedCmpShape_of_self
              (comparisonClassified_of_self fun c hc =>
                selfPairs_genSkelOp1 subject tl c (by simpa [skelNode] using hc))
              (by simp [skelNode, genSkelOp1])
          | sub hs _ =>
            simp [NTree.children] at hs
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                cases hM : genComputeSkeleton (K := K) n pB.2 pC.2 with
                | error _ => simp [genComputeSkeleton, hB, hC, hM] at h
                | ok pM =>
                  simp [genComputeSkeleton, hB, hC, hM] at h
                  obtain ⟨rfl, rfl⟩ := h
                  cases hu with
                  | here =>
                    exact generatedCmpShape_of_self
                      (comparisonClassified_of_self fun cmp hcmp =>
                        selfPairs_genSkelOp2 subject b c pB.2 pC.2 pM.2 cmp
                          (by simpa [skelNode] using hcmp))
                      (by simp [skelNode, genSkelOp2])
                  | sub hs hu' =>
                    simp [NTree.children] at hs
                    rcases hs with rfl | rfl | rfl
                    · exact ih hB (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
                    · exact ih hC (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
                    · exact ih hM (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            cases hu with
            | here =>
              exact generatedCmpShape_of_self
                (comparisonClassified_of_self fun c hc =>
                  selfPairs_genSkelOp3 subject tl p.2 c (by simpa [skelNode] using hc))
                (by simp [skelNode, genSkelOp3])
            | sub hs hu' =>
              simp [NTree.children] at hs
              cases hs
              exact ih hcall (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            cases hlus : Noun.lus p.2 with
            | none => simp [genComputeSkeleton, hcall, hlus] at h
            | some incR =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              cases hu with
              | here =>
                have hinc :
                    OpcodeSemantics.incMod (ringChar K) p.2 = incR := by
                  have hw := hwrap _ (InTree.here _) (by simp [skelNode, genSkelOp4])
                  simpa [skelNode, genSkelOp4, skeletonSubformula,
                    ComputeTable.fanoutComp] using hw
                exact generatedCmpShape_of_self
                  (comparisonClassified_of_self fun c hc =>
                    selfPairs_genSkelOp4 subject tl p.2 incR hinc c
                      (by simpa [skelNode] using hc))
                  (by simp [skelNode, genSkelOp4])
              | sub hs hu' =>
                simp [NTree.children] at hs
                cases hs
                exact ih hcall (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  refine generatedCmpShape_of_self ?_ (by simp [skelNode, genSkelOp5])
                  intro cmp hcmp
                  have hsp := selfPairs_genSkelOp5_off (K := K) subject b c pB.2 pC.2 cmp
                    (by simpa [skelNode] using hcmp)
                  rcases hsp with heq | ⟨hrole, _, _⟩
                  · exact Or.inl heq
                  · exact comparisonClassified_op5 (by simp [skelNode, genSkelOp5]) hrole
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
                  · exact ih hC (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ => simp [genComputeSkeleton] at h
            | cell c d =>
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ => simp [genComputeSkeleton, hcond] at h
              | ok pCond =>
                cases hval : pCond.2 with
                | cell _ _ => simp [genComputeSkeleton, hcond, hval] at h
                | atom condv =>
                  cases condv with
                  | zero =>
                    cases htaken : genComputeSkeleton (K := K) n subject c with
                    | error _ => simp [genComputeSkeleton, hcond, hval, htaken] at h
                    | ok pTaken =>
                      simp [genComputeSkeleton, hcond, hval, htaken] at h
                      obtain ⟨rfl, rfl⟩ := h
                      cases hu with
                      | here =>
                        refine ⟨?_, ?_, ?_⟩
                        · intro cmp hcmp
                          have hsp := selfPairs_genSkelOp6_then_off (K := K)
                            subject b c d pTaken.2 cmp (by simpa [skelNode] using hcmp)
                          rcases hsp with heq | ⟨hrole, _, _⟩
                          · exact Or.inl heq
                          · by_cases hne : cmp.left = cmp.right
                            · exact Or.inl hne
                            · exact comparisonClassified_op6
                                (by simp [skelNode, genSkelOp6]) hrole hne
                        · intro
                          exact Or.inl (by
                            simp [skelNode, skeletonSubformula, skeletonDec, genSkelOp6,
                              ComputeTable.fanoutComp, SemanticStrategy.decActive,
                              SemanticStrategy.hasTailDecomposition])
                        · intro
                          simp [skelNode, skeletonSubformula, skeletonDec, genSkelOp6,
                            ComputeTable.fanoutComp, SemanticStrategy.decActive,
                            SemanticStrategy.hasTailDecomposition]
                      | sub hs hu' =>
                        simp [NTree.children] at hs
                        rcases hs with rfl | rfl
                        · exact ih hcond (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
                        · exact ih htaken (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
                  | succ condv =>
                    cases condv with
                    | zero =>
                      cases htaken : genComputeSkeleton (K := K) n subject d with
                      | error _ =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                      | ok pTaken =>
                        simp [genComputeSkeleton, hcond, hval, htaken] at h
                        obtain ⟨rfl, rfl⟩ := h
                        cases hu with
                        | here =>
                          refine ⟨?_, ?_, ?_⟩
                          · intro cmp hcmp
                            have hsp := selfPairs_genSkelOp6_else_off (K := K)
                              subject b c d pTaken.2 cmp (by simpa [skelNode] using hcmp)
                            rcases hsp with heq | ⟨hrole, _, _⟩
                            · exact Or.inl heq
                            · by_cases hne : cmp.left = cmp.right
                              · exact Or.inl hne
                              · exact comparisonClassified_op6
                                  (by simp [skelNode, genSkelOp6]) hrole hne
                          · intro
                            exact Or.inr (by
                              simp [skelNode, skeletonSubformula, skeletonDec, genSkelOp6,
                                ComputeTable.fanoutComp, SemanticStrategy.decActive,
                                SemanticStrategy.hasTailDecomposition])
                          · intro
                            simp [skelNode, skeletonSubformula, skeletonDec, genSkelOp6,
                              ComputeTable.fanoutComp, SemanticStrategy.decActive,
                              SemanticStrategy.hasTailDecomposition]
                        | sub hs hu' =>
                          simp [NTree.children] at hs
                          rcases hs with rfl | rfl
                          · exact ih hcond (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
                          · exact ih htaken (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
                    | succ _ =>
                      simp [genComputeSkeleton, hcond, hval] at h
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n pB.2 c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  exact generatedCmpShape_of_self
                    (comparisonClassified_of_self fun cmp hcmp =>
                      selfPairs_genSkelOp7 subject b c pB.2 pC.2 cmp
                        (by simpa [skelNode] using hcmp))
                    (by simp [skelNode, genSkelOp7])
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
                  · exact ih hC (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hB : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hB] at h
            | ok pB =>
              cases hC : genComputeSkeleton (K := K) n (.cell pB.2 subject) c with
              | error _ => simp [genComputeSkeleton, hB, hC] at h
              | ok pC =>
                simp [genComputeSkeleton, hB, hC] at h
                obtain ⟨rfl, rfl⟩ := h
                cases hu with
                | here =>
                  exact generatedCmpShape_of_self
                    (comparisonClassified_of_self fun cmp hcmp =>
                      selfPairs_genSkelOp8 subject b c pB.2 pC.2 cmp
                        (by simpa [skelNode] using hcmp))
                    (by simp [skelNode, genSkelOp8])
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
                  · exact ih hC (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell axN c =>
            cases axN with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom ax =>
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hcore] at h
              | ok pCore =>
                cases hslot : Noun.slot ax pCore.2 with
                | none => simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pCore.2 arm with
                  | error _ => simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pInv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    obtain ⟨rfl, rfl⟩ := h
                    cases hu with
                    | here =>
                      exact generatedCmpShape_of_self
                        (comparisonClassified_of_self fun cmp hcmp =>
                          selfPairs_genSkelOp9 subject c pCore.2 arm pInv.2 ax cmp
                            (by simpa [skelNode] using hcmp))
                        (by simp [skelNode, genSkelOp9])
                    | sub hs hu' =>
                      simp [NTree.children] at hs
                      rcases hs with rfl | rfl
                      · exact ih hcore (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
                      · exact ih hinv (incWrap_sub hwrap (by simp [NTree.children])) _ hu'
        · simp [genComputeSkeleton] at h
        · simp [genComputeSkeleton] at h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

/-! ## Transport to the AIR-ordered BFS rows -/

theorem incWrap_of_air
    {t : NTree (GenComputeRow K)}
    (hwrap : ∀ g ∈ bfsRows (airReorder t),
      g.skel.state = .s4 →
        OpcodeSemantics.incMod (ringChar K)
          (skeletonSubformula g.skel 0 TripleSlot.result)
          = g.skel.evaluation) :
    ∀ u, InTree t u → IncWrap u := by
  intro u hu hs4
  obtain ⟨u', hu', hl⟩ := labelsFrom_of_airReorder t u hu
  have hg : u.label ∈ bfsRows (airReorder t) := by
    rw [hl]
    exact List.mem_map.mpr ⟨u',
      (mem_bfsForest [airReorder t] u').mpr ⟨airReorder t, List.mem_singleton.mpr rfl, hu'⟩, rfl⟩
  exact hwrap _ hg (by simpa [hl] using hs4)

/-- **Every generated AIR census pair is diagonal or `.s5`/`.s6` off-diag.**

`hwrap` is `evalGBy`'s no-overflow at OP4: the census compares against
`incMod (ringChar K)` while the generator emits `Noun.lus`. -/
theorem generated_comparisons_self_or_offdiag
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hwrap : ∀ g ∈ bfsRows (airReorder t),
      g.skel.state = .s4 →
        OpcodeSemantics.incMod (ringChar K)
          (skeletonSubformula g.skel 0 TripleSlot.result)
          = g.skel.evaluation) :
    ∀ g ∈ bfsRows (airReorder t),
      ∀ c ∈ skeletonComparisons (K := K) g.skel,
        c.left = c.right
        ∨ (g.skel.state = .s5 ∧ c.role = .equalityOperand)
        ∨ (g.skel.state = .s6 ∧ c.role = .recursiveFormula ∧ c.left ≠ c.right) := by
  intro g hg
  have hin := generated_comparisons_self_or_offdiag_inTree h (incWrap_of_air hwrap)
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hg
  obtain ⟨r, hr, hinAir⟩ := (mem_bfsForest [airReorder t] n).mp hn
  simp only [List.mem_singleton] at hr
  subst r
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t n hinAir
  intro c hc
  have hc' : c ∈ skeletonComparisons (K := K) u0.label.skel := by
    simpa [hl] using hc
  simpa [hl] using (hin u0 hu0).classified c hc'

theorem generated_cmpShape_air
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hwrap : ∀ g ∈ bfsRows (airReorder t),
      g.skel.state = .s4 →
        OpcodeSemantics.incMod (ringChar K)
          (skeletonSubformula g.skel 0 TripleSlot.result)
          = g.skel.evaluation) :
    ∀ g ∈ bfsRows (airReorder t), GeneratedCmpShape g := by
  intro g hg
  have hin := generated_comparisons_self_or_offdiag_inTree h (incWrap_of_air hwrap)
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hg
  obtain ⟨r, hr, hinAir⟩ := (mem_bfsForest [airReorder t] n).mp hn
  simp only [List.mem_singleton] at hr
  subst r
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t n hinAir
  simpa [hl] using hin u0 hu0

/-! ## `NPR.fn` / `SepSeed` transport -/

open Polynomial

theorem dyckBits_algebraMap' {F K : Type} [Field F] [Field K] [Algebra F K]
    (n : Noun) :
    NPR.dyckBits (K := K) n =
      (NPR.dyckBits (K := F) n).map (algebraMap F K) := by
  simp only [NPR.dyckBits, List.map_map]
  congr 1
  funext b
  cases b <;> simp [RingHom.map_zero, RingHom.map_one]

theorem leafF_algebraMap {F K : Type} [Field F] [Field K] [Algebra F K]
    (n : Noun) :
    NPR.leafF (K := K) n =
      (NPR.leafF (K := F) n).map (algebraMap F K) := by
  simp only [NPR.leafF, List.map_map, Function.comp]
  exact congrArg (List.map · n.leafList)
    (funext fun k => (map_natCast (algebraMap F K) k).symm)

theorem listPoly_map {F K : Type} [Field F] [Field K] (f : F →+* K) :
    ∀ l : List F, NPR.listPoly (l.map f) = (NPR.listPoly l).map f
  | [] => by simp [NPR.listPoly_nil, Polynomial.map_zero]
  | a :: l => by
    simp only [List.map_cons, NPR.listPoly_cons, listPoly_map f l,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]

/-- `fn(n; φ(z)) = φ³(fn(n; z))`. -/
theorem fn_algebraMap {F K : Type} [Field F] [Field K] [Algebra F K]
    (n : Noun) (z : F) :
    NPR.fn (K := K) n (algebraMap F K z) =
      (algebraMap F K (NPR.fn (K := F) n z).1,
        algebraMap F K (NPR.fn (K := F) n z).2.1,
        algebraMap F K (NPR.fn (K := F) n z).2.2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [NPR.fn, map_pow]
  · simp only [NPR.fn]
    rw [leafF_algebraMap (F := F) (K := K) n, listPoly_map (algebraMap F K),
      Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (algebraMap F K) z
  · simp only [NPR.fn]
    rw [dyckBits_algebraMap' (F := F) (K := K) n, listPoly_map (algebraMap F K),
      Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (algebraMap F K) z

theorem sepSeed_symm (z : K) {P Q : Noun}
    (h : GlobalCarryRecognizer.SepSeed z P Q) :
    GlobalCarryRecognizer.SepSeed z Q P := by
  intro hne hfn
  exact h (fun heq => hne heq.symm) hfn.symm

/-- `SepSeed` transports along an injective `algebraMap`. -/
theorem sepSeed_algebraMap {F K : Type} [Field F] [Field K] [Algebra F K]
    (hinj : Function.Injective (algebraMap F K))
    {z : F} {P Q : Noun}
    (h : GlobalCarryRecognizer.SepSeed z P Q) :
    GlobalCarryRecognizer.SepSeed (algebraMap F K z) P Q := by
  intro hneK
  have hneF :
      (NPR.leafF (K := F) P, NPR.dyckBits (K := F) P) ≠
        (NPR.leafF (K := F) Q, NPR.dyckBits (K := F) Q) := by
    intro heqF
    refine hneK (Prod.ext ?_ ?_)
    · simpa [leafF_algebraMap (F := F) (K := K)] using
        congrArg (List.map (algebraMap F K)) (congrArg Prod.fst heqF)
    · simpa [dyckBits_algebraMap' (F := F) (K := K)] using
        congrArg (List.map (algebraMap F K)) (congrArg Prod.snd heqF)
  have hfnF := h hneF
  intro hfnK
  apply hfnF
  have hP := fn_algebraMap (F := F) (K := K) P z
  have hQ := fn_algebraMap (F := F) (K := K) Q z
  rw [hP, hQ] at hfnK
  have h1 : algebraMap F K (NPR.fn (K := F) P z).1 =
      algebraMap F K (NPR.fn (K := F) Q z).1 := congrArg Prod.fst hfnK
  have h2 : algebraMap F K (NPR.fn (K := F) P z).2.1 =
      algebraMap F K (NPR.fn (K := F) Q z).2.1 :=
    congrArg (fun t : K × K × K => t.2.1) hfnK
  have h3 : algebraMap F K (NPR.fn (K := F) P z).2.2 =
      algebraMap F K (NPR.fn (K := F) Q z).2.2 :=
    congrArg (fun t : K × K × K => t.2.2) hfnK
  exact Prod.ext (hinj h1) (Prod.ext (hinj h2) (hinj h3))

/-! ## Off-diag `SepSeed` combinators -/

theorem sepSeed_atoms (z : K) {a b : ℕ} (hne : (a : K) ≠ (b : K)) :
    GlobalCarryRecognizer.SepSeed z (.atom a) (.atom b) := by
  intro _ hfn
  have hleaf :
      (NPR.listPoly (NPR.leafF (K := K) (.atom a))).eval z =
        (NPR.listPoly (NPR.leafF (K := K) (.atom b))).eval z :=
    congrArg (fun t => t.2.1) hfn
  have ha : NPR.leafF (K := K) (.atom a) = [(a : K)] := rfl
  have hb : NPR.leafF (K := K) (.atom b) = [(b : K)] := rfl
  simp [ha, hb, NPR.listPoly_cons, NPR.listPoly_nil, eval_C] at hleaf
  exact hne hleaf

theorem sepSeed_atoms_of_bounded {q : ℕ} (z : K) {a b : ℕ}
    (ha : a < q) (hb : b < q) (hq : q ≤ ringChar K) (hne : a ≠ b) :
    GlobalCarryRecognizer.SepSeed z (.atom a) (.atom b) := by
  refine sepSeed_atoms z ?_
  haveI : CharP K (ringChar K) := ringChar.charP K
  intro heq
  exact hne
    (CharP.natCast_injOn_Iio K (ringChar K)
      (Set.mem_Iio.mpr (lt_of_lt_of_le ha hq))
      (Set.mem_Iio.mpr (lt_of_lt_of_le hb hq)) heq)

/-- Distinct leaf counts: the first `fn` coordinate is `z^leaves`.
`orderOf z` not dividing the positive gap is the usual way to discharge
`z^λ ≠ z^μ`; do not claim `orderOf z = 2^32 → hbad`.
The gap is the *positive* difference — `n - m = 0` whenever `n ≤ m`, and
every `orderOf` divides `0`, so a two-sided `Nat.sub` conjunction is
unsatisfiable on unequal counts. -/
def leafGap (P Q : Noun) : ℕ :=
  P.leaves - Q.leaves + (Q.leaves - P.leaves)

theorem sepSeed_of_leaves_ne (z : K) (hz : z ≠ 0) {P Q : Noun}
    (hleaves : P.leaves ≠ Q.leaves)
    (hord : ¬ orderOf z ∣ leafGap P Q) :
    GlobalCarryRecognizer.SepSeed z P Q := by
  intro _ hfn
  have hpow : z ^ P.leaves = z ^ Q.leaves := congrArg Prod.fst hfn
  rcases lt_or_gt_of_ne hleaves with hlt | hgt
  · have hle : P.leaves ≤ Q.leaves := le_of_lt hlt
    have hgap : leafGap P Q = Q.leaves - P.leaves := by
      simp [leafGap, Nat.sub_eq_zero_of_le hle]
    have hsub : Q.leaves = P.leaves + leafGap P Q := by
      rw [hgap, Nat.add_sub_of_le hle]
    have hz1 : z ^ leafGap P Q = 1 := by
      have : z ^ P.leaves * z ^ leafGap P Q = z ^ P.leaves * 1 := by
        rw [← pow_add, ← hsub, ← hpow, mul_one]
      exact mul_left_cancel₀ (pow_ne_zero _ hz) this
    exact hord (orderOf_dvd_of_pow_eq_one hz1)
  · have hle : Q.leaves ≤ P.leaves := le_of_lt hgt
    have hgap : leafGap P Q = P.leaves - Q.leaves := by
      simp [leafGap, Nat.sub_eq_zero_of_le hle]
    have hsub : P.leaves = Q.leaves + leafGap P Q := by
      rw [hgap, Nat.add_sub_of_le hle]
    have hz1 : z ^ leafGap P Q = 1 := by
      have : z ^ Q.leaves * z ^ leafGap P Q = z ^ Q.leaves * 1 := by
        rw [← pow_add, ← hsub, hpow, mul_one]
      exact mul_left_cancel₀ (pow_ne_zero _ hz) this
    exact hord (orderOf_dvd_of_pow_eq_one hz1)

/-- Generated OP4 emits `Noun.lus`.  Combined with `BoundedBy q` on the
result and `q ≤ ringChar K`, this is `hwrap`. -/
theorem incMod_eq_of_lus {q : ℕ} {v r : Noun}
    (hlus : Noun.lus v = some r)
    (hr : FieldEmbedding.BoundedBy q r)
    (hle : q ≤ ringChar K) :
    OpcodeSemantics.incMod (ringChar K) v = r := by
  match v with
  | .cell _ _ => simp [Noun.lus] at hlus
  | .atom n =>
    simp only [Noun.lus, Option.some.injEq] at hlus
    subst r
    have hn : n + 1 < q := (FieldEmbedding.BoundedBy_atom).mp hr
    have hlt : n + 1 < ringChar K := lt_of_lt_of_le hn hle
    simp [OpcodeSemantics.incMod, Nat.mod_eq_of_lt hlt]

/-! ## Glue: `z ∉ badSeeds` from off-diag `SepSeed` -/

theorem equalityOperand_nouns {s : ComputeRowSkeleton}
    (hs : s.state = .s5) {c : ComparisonUse}
    (hc : c ∈ skeletonComparisons (K := K) s)
    (hr : c.role = .equalityOperand) :
    c.left = skeletonSubformula s 0 TripleSlot.result ∧
      c.right = skeletonSubformula s 1 TripleSlot.result := by
  simp only [skeletonComparisons, hs, skeletonUse, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hr
  · cases hr
  · cases hr
  · cases hr
  · cases hr
  · cases hr
  · cases hr
  · exact ⟨rfl, rfl⟩
  · cases hr

theorem s6_offdiag_is_branches {s : ComputeRowSkeleton}
    (hs : s.state = .s6)
    (htaken : skeletonSubformula s 0 TripleSlot.formula = skeletonDec s .f_tth
      ∨ skeletonSubformula s 0 TripleSlot.formula = skeletonDec s .f_ttt)
    (hcond : skeletonSubformula s 1 TripleSlot.formula = skeletonDec s .f_th)
    {c : ComparisonUse} (hc : c ∈ skeletonComparisons (K := K) s)
    (hr : c.role = .recursiveFormula) (hne : c.left ≠ c.right) :
    (c.left = skeletonDec s .f_tth ∧ c.right = skeletonDec s .f_ttt)
    ∨ (c.left = skeletonDec s .f_ttt ∧ c.right = skeletonDec s .f_tth) := by
  simp only [skeletonComparisons, hs, skeletonUse, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases hr
  · cases hr
  · cases hr
  · cases hr
  · cases hr
  · -- (sf0.formula, f_tth)
    rcases htaken with h | h
    · exact absurd (h ▸ rfl) hne
    · exact Or.inr ⟨h, rfl⟩
  · -- (sf0.formula, f_ttt)
    rcases htaken with h | h
    · exact Or.inl ⟨h, rfl⟩
    · exact absurd (h ▸ rfl) hne
  · cases hr
  · -- (sf1.formula, f_th)
    exact absurd (hcond ▸ rfl) hne
  · cases hr

theorem not_mem_badSeeds_of_pairs' [Fintype K] [DecidableEq K]
    {S : SemanticSkeleton} {Λ : ℕ}
    (C : BoundSemanticTrace.SkeletonP8Census K S Λ) (z : K)
    (h : ∀ pr ∈ BoundSemanticTrace.skeletonPairs K S,
      GlobalCarryRecognizer.SepSeed z pr.1 pr.2) :
    z ∉ C.census.badSeeds (K := K) := by
  intro hmem
  obtain ⟨i, hi⟩ := (ComparisonCensus.mem_badSeeds_iff _ z).mp hmem
  exact hi (h _ (List.get_mem _ i))

/-- Completeness: a seed that separates every generated off-diag pair is
outside `badSeeds`.  `hoff5`/`hoff6` are compiler-avoidable, not a sixth
§1 binder.  Already priced in `p8Work`. -/
theorem notMem_badSeeds_of_offdiag_sep
    {Λ : ℕ} [Fintype K] [DecidableEq K]
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (mf : List (NTree (GenMemoryRow K)))
    (hwrap : ∀ g ∈ bfsRows (airReorder t),
      g.skel.state = .s4 →
        OpcodeSemantics.incMod (ringChar K)
          (skeletonSubformula g.skel 0 TripleSlot.result)
          = g.skel.evaluation)
    (z : K)
    (hoff5 : ∀ g ∈ bfsRows (airReorder t), g.skel.state = .s5 →
      GlobalCarryRecognizer.SepSeed z
        (skeletonSubformula g.skel 0 TripleSlot.result)
        (skeletonSubformula g.skel 1 TripleSlot.result))
    (hoff6 : ∀ g ∈ bfsRows (airReorder t), g.skel.state = .s6 →
      GlobalCarryRecognizer.SepSeed z
        (skeletonDec g.skel .f_tth) (skeletonDec g.skel .f_ttt)) :
    z ∉ (genSkeletonP8Census hΛ h hconf mf).census.badSeeds := by
  refine not_mem_badSeeds_of_pairs' _ z ?_
  have hshape := generated_cmpShape_air h hwrap
  have hrows : ∀ s ∈ computeSkeletonRows
      (genSemanticSkeleton (bfsAssign (airReorder t)) mf),
      ∀ c ∈ skeletonComparisons (K := K) s,
        GlobalCarryRecognizer.SepSeed z c.left c.right := by
    refine bfsAssign_computeSkeletonRows_of_bfsRows _ _ mf ?_
    intro g hg c hc
    have hgshape := hshape g hg
    rcases hgshape.classified c hc with hself | hs5 | hs6
    · exact sepSeed_of_eq hself
    · obtain ⟨hst, hrole⟩ := hs5
      obtain ⟨hl, hr⟩ := equalityOperand_nouns hst hc hrole
      rw [hl, hr]
      exact hoff5 g hg hst
    · obtain ⟨hst, hrole, hne⟩ := hs6
      rcases s6_offdiag_is_branches hst (hgshape.s6_taken_branch hst)
          (hgshape.s6_cond_self hst) hc hrole hne with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · rw [hl, hr]; exact hoff6 g hg hst
      · rw [hl, hr]; exact sepSeed_symm z (hoff6 g hg hst)
  intro pr hpr
  simp only [BoundSemanticTrace.skeletonPairs, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hpr
  rcases hpr with (rfl | rfl | rfl) | hcmp
  · exact sepSeed_self z _
  · exact sepSeed_self z _
  · exact sepSeed_self z _
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcmp
    rw [skeletonComparisonCensus, List.mem_flatMap] at hc
    obtain ⟨s, hs, hcs⟩ := hc
    exact hrows s hs c hcs

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.selfPairs_genSkelOp6_else
#print axioms Nock.NockVMROM.Thm54.TraceGen.generated_comparisons_self_or_offdiag
#print axioms Nock.NockVMROM.Thm54.TraceGen.fn_algebraMap
#print axioms Nock.NockVMROM.Thm54.TraceGen.sepSeed_algebraMap
#print axioms Nock.NockVMROM.Thm54.TraceGen.sepSeed_atoms
#print axioms Nock.NockVMROM.Thm54.TraceGen.sepSeed_of_leaves_ne
#print axioms Nock.NockVMROM.Thm54.TraceGen.notMem_badSeeds_of_offdiag_sep
