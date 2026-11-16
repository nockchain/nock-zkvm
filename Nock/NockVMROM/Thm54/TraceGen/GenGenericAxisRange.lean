/-
  Nock/NockVMROM/Thm54/TraceGen/GenGenericAxisRange.lean

  **`SkeletonAxisRange` for every program the generator accepts.**

  `SkeletonAxisRange q S` (`GenSemanticDataParts.lean`) is the OP0/OP9 memory-record axis
  measurement.  `Batch168.dot_skeletonAxisRange` was the only witness — an
  eight-way case split at the dot fixture, of which the OP0 half is *vacuous* because Tier A has no
  `.s0` row (`Batch168.dot_no_s0_row`).

  **The observation that makes it cheap.**  The axis is not an independent datum: at every row
  `genComputeSkeleton` emits, it is an **atom of the row's own committed formula**.

  * OP0 (`Gen.lean:569-579`) matches the formula tail as `.atom ax` and emits
    `genSkelOp0 subject formula (.atom 0) tail result ax`, so
    `formula =.cell (.atom 0) (.atom ax)` and `skeletonMemoryAxis s 1 = ax`.
  * OP9 (`Gen.lean:695-707`) matches the tail as `.cell (.atom ax) c` and emits
    `genSkelOp9 subject formula (.atom 9) tail (.atom ax) c core arm result ax`, so
    `formula =.cell (.atom 9) (.cell (.atom ax) c)` and `skeletonMemoryAxis s 2 = ax`.

  So the missing object is a **shape** statement about the emitted formula — `NodeAxisInFormula`
  below — which carries **no bound and no premise**, and is therefore an induction of the same kind
  as `genComputeSkeleton_inTree_fanout` (`GenSkeletonFanout.lean:31`) and
  `genComputeSkeleton_inTree_census` (`GenMatmulSemanticData.lean:69`) rather than one that has to
  thread `subject`/`formula` bounds through twelve arms.  Composing it with
  `ComputeRowSkeleton.BoundedBy q s`, which `genComputeSkeleton_assigned_inTree_bounded`
  (`GenGenericBounded.lean`) now supplies generically, gives `SkeletonAxisRange`.

  `Batch168`'s docstring proposed the bridge `skeletonDec s.f_t =.atom (skeletonMemoryAxis s 1)`
  instead.  That is true too, but it then needs `RowCellIdentities` to reach the formula and a
  `decActive` side condition at OP9; stating the shape on the formula directly skips both.

  **Scope.**  `∀ program accepted by genComputeSkeleton`, and — for the range half — at the same
  three program-level side conditions as `GenGenericBounded`: `1 < q`, and the subject, formula and
  run bounded by `q`.  Both halves of the predicate are exercised: the OP0 half is not vacuous here
  the way it is at Tier A, because the induction covers the arm rather than a fixed row list.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericBounded

set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

/-! ## The shape statement -/

/-- **The committed memory-record axis of a generated OP0/OP9 row is an atom of its formula.**

Stated as a shape on `skel.formula`, with no bound, so that the induction below needs no premise
beyond acceptance. -/
def NodeAxisInFormula (g : GenComputeRow K) : Prop :=
  (g.skel.state = .s0 →
      ∃ hd, g.skel.formula =
        .cell hd (.atom (P8Census.skeletonMemoryAxis g.skel 1))) ∧
    (g.skel.state = .s9 →
      ∃ hd tt, g.skel.formula =
        .cell hd (.cell (.atom (P8Census.skeletonMemoryAxis g.skel 2)) tt)) ∧
    (g.skel.state = .s0 → 1 ≤ P8Census.skeletonMemoryAxis g.skel 1) ∧
    (g.skel.state = .s9 → 1 ≤ P8Census.skeletonMemoryAxis g.skel 2)

/-- Rows that are neither OP0 nor OP9 satisfy it vacuously — ten of the twelve arms. -/
theorem nodeAxisInFormula_ne_lookup (g : GenComputeRow K)
    (h0 : g.skel.state ≠ .s0) (h9 : g.skel.state ≠ .s9) :
    NodeAxisInFormula g :=
  ⟨fun h => absurd h h0, fun h => absurd h h9, fun h => absurd h h0, fun h => absurd h h9⟩

/-! ## The induction

Twelve arms, structurally identical to `genComputeSkeleton_inTree_census`
(`GenMatmulSemanticData.lean:69`): destructure the emission, discharge the root, recurse on the
children.  Only the OP0 and OP9 roots do work, and each is one `exact ⟨…, rfl⟩` after the pattern
match has already replaced the formula by its own shape. -/

/-- **The shape statement at every node of any accepted program.**  Unconditional. -/
theorem genComputeSkeleton_inTree_axisInFormula
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree t u) :
    NodeAxisInFormula u.label := by
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
              exact nodeAxisInFormula_ne_lookup _ (by simp [skelNode, genSkelCons])
                (by simp [skelNode, genSkelCons])
            | sub hs hu' =>
              simp [NTree.children] at hs
              rcases hs with rfl | rfl
              · exact ih hL _ hu'
              · exact ih hR _ hu'
      | atom op =>
        rcases nat_lt_twelve_or_ge op with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hge
        -- OP0: the axis is the formula tail.
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
                have hax : 1 ≤ ax := by
                  rcases Nat.eq_zero_or_pos ax with rfl | hpos
                  · simp [Nock.Noun.slot] at hslot
                  · exact hpos
                refine ⟨fun _ => ⟨.atom 0, ?_⟩, fun hs9 => ?_, fun _ => ?_, fun hs9 => ?_⟩
                · simp [skelNode, genSkelOp0, P8Census.skeletonMemoryAxis,
                    Nock.Framework.recordCount]
                · simp [skelNode, genSkelOp0] at hs9
                · simpa [skelNode, genSkelOp0, P8Census.skeletonMemoryAxis,
                    Nock.Framework.recordCount] using hax
                · simp [skelNode, genSkelOp0] at hs9
              | sub hs _ =>
                simp [NTree.children] at hs
        -- OP1
        · simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hu with
          | here =>
            exact nodeAxisInFormula_ne_lookup _ (by simp [skelNode, genSkelOp1])
              (by simp [skelNode, genSkelOp1])
          | sub hs _ =>
            simp [NTree.children] at hs
        -- OP2
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
                    exact nodeAxisInFormula_ne_lookup _ (by simp [skelNode, genSkelOp2])
                      (by simp [skelNode, genSkelOp2])
                  | sub hs hu' =>
                    simp [NTree.children] at hs
                    rcases hs with rfl | rfl | rfl
                    · exact ih hB _ hu'
                    · exact ih hC _ hu'
                    · exact ih hM _ hu'
        -- OP3
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            cases hu with
            | here =>
              exact nodeAxisInFormula_ne_lookup _ (by simp [skelNode, genSkelOp3])
                (by simp [skelNode, genSkelOp3])
            | sub hs hu' =>
              simp [NTree.children] at hs
              cases hs
              exact ih hcall _ hu'
        -- OP4
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            cases hlus : Noun.lus p.2 with
            | none => simp [genComputeSkeleton, hcall, hlus] at h
            | some _ =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              cases hu with
              | here =>
                exact nodeAxisInFormula_ne_lookup _ (by simp [skelNode, genSkelOp4])
                  (by simp [skelNode, genSkelOp4])
              | sub hs hu' =>
                simp [NTree.children] at hs
                cases hs
                exact ih hcall _ hu'
        -- OP5
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
                  exact nodeAxisInFormula_ne_lookup _ (by simp [skelNode, genSkelOp5])
                    (by simp [skelNode, genSkelOp5])
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
        -- OP6
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
                        exact nodeAxisInFormula_ne_lookup _
                          (by simp [skelNode, genSkelOp6]) (by simp [skelNode, genSkelOp6])
                      | sub hs hu' =>
                        simp [NTree.children] at hs
                        rcases hs with rfl | rfl
                        · exact ih hcond _ hu'
                        · exact ih htaken _ hu'
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
                          exact nodeAxisInFormula_ne_lookup _
                            (by simp [skelNode, genSkelOp6]) (by simp [skelNode, genSkelOp6])
                        | sub hs hu' =>
                          simp [NTree.children] at hs
                          rcases hs with rfl | rfl
                          · exact ih hcond _ hu'
                          · exact ih htaken _ hu'
                    | succ _ =>
                      simp [genComputeSkeleton, hcond, hval] at h
        -- OP7
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
                  exact nodeAxisInFormula_ne_lookup _ (by simp [skelNode, genSkelOp7])
                    (by simp [skelNode, genSkelOp7])
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
        -- OP8
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
                  exact nodeAxisInFormula_ne_lookup _ (by simp [skelNode, genSkelOp8])
                    (by simp [skelNode, genSkelOp8])
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
        -- OP9: the axis is the head of the formula tail.
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
                      have hax : 1 ≤ ax := by
                        rcases Nat.eq_zero_or_pos ax with rfl | hpos
                        · simp [Nock.Noun.slot] at hslot
                        · exact hpos
                      refine ⟨fun hs0 => ?_, fun _ => ⟨.atom 9, c, ?_⟩, fun hs0 => ?_, fun _ => ?_⟩
                      · simp [skelNode, genSkelOp9] at hs0
                      · simp [skelNode, genSkelOp9, P8Census.skeletonMemoryAxis,
                          Nock.Framework.recordCount]
                      · simp [skelNode, genSkelOp9] at hs0
                      · simpa [skelNode, genSkelOp9, P8Census.skeletonMemoryAxis,
                          Nock.Framework.recordCount] using hax
                    | sub hs hu' =>
                      simp [NTree.children] at hs
                      rcases hs with rfl | rfl
                      · exact ih hcore _ hu'
                      · exact ih hinv _ hu'
        -- OP10, OP11: not emitted
        · simp [genComputeSkeleton] at h
        · simp [genComputeSkeleton] at h
        -- op ≥ 12
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

/-! ## Transport to the committed tree -/

/-- The shape statement at every node of the AIR-reordered tree. -/
theorem genComputeSkeleton_airReorder_inTree_axisInFormula
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u, InTree (airReorder t) u → NodeAxisInFormula u.label := by
  intro u hu
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t u hu
  have hb := genComputeSkeleton_inTree_axisInFormula h u0 hu0
  simp only [NodeAxisInFormula] at hb ⊢
  rw [hl]
  exact hb

/-- The shape statement at every node of the BFS-assigned, AIR-reordered tree. -/
theorem genComputeSkeleton_assigned_inTree_axisInFormula
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u, InTree (bfsAssign (airReorder t)) u → NodeAxisInFormula u.label := by
  intro n hn
  have hnF : n ∈ bfsForest [bfsAssign (airReorder t)] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab : n.label ∈ (bfsForest [bfsAssign (airReorder t)]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [bfsAssign_bfsForest_labels] at hlab
  obtain ⟨i, hi, hni⟩ := List.mem_map.mp hlab
  have hi' := lt_bfsRows_of_mem_range' hi
  have hrow : (bfsRows (airReorder t))[i - 1] ∈ bfsRows (airReorder t) :=
    List.getElem_mem hi'
  unfold bfsRows at hrow
  obtain ⟨n0, hn0, hlab0⟩ := List.mem_map.mp hrow
  obtain ⟨r0, hr0, hin0⟩ := (mem_bfsForest _ n0).mp hn0
  simp only [List.mem_singleton] at hr0
  subst hr0
  have hb := genComputeSkeleton_airReorder_inTree_axisInFormula h n0 hin0
  simp only [NodeAxisInFormula] at hb ⊢
  rw [← hni, bfsLabelAt_skel (airReorder t) i hi']
  have hbeq : (bfsRows (airReorder t))[i - 1] = n0.label := by
    unfold bfsRows
    exact hlab0.symm
  rw [hbeq]
  exact hb

/-! ## `SkeletonAxisRange`, generically

The shape statement plus the noun bound.  `ComputeRowSkeleton.BoundedBy` bounds the row's committed
formula, and the shape says the axis is an atom of it. -/

/-- The per-row step: an axis that is an atom of a `q`-bounded formula is `< q`. -/
theorem axisRange_of_axisInFormula {q : ℕ} {g : GenComputeRow K}
    (hshape : NodeAxisInFormula g) (hb : g.skel.BoundedBy q) :
    (g.skel.state = .s0 → P8Census.skeletonMemoryAxis g.skel 1 < q) ∧
      (g.skel.state = .s9 → P8Census.skeletonMemoryAxis g.skel 2 < q) := by
  refine ⟨fun h0 => ?_, fun h9 => ?_⟩
  · obtain ⟨hd, hf⟩ := hshape.1 h0
    have := hb.2.1
    rw [hf] at this
    exact this.2
  · obtain ⟨hd, tt, hf⟩ := hshape.2.1 h9
    have := hb.2.1
    rw [hf] at this
    exact this.2.1

/-- **`SkeletonAxisRange` for every program the generator accepts.**

The premise `genSemanticData` (`GenSemanticData.lean:138`), `genRows`, `genCombinedBounded`,
`genServedMemoryTrace` and `genData` all take as `haxis`, derived rather than declared, at the same
three program-level side conditions as `genComputeSkeleton_skeletonBounded`. -/
theorem genComputeSkeleton_axisRange {q fuel : ℕ} (hq : 1 < q)
    {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (mf : List (NTree (GenMemoryRow K))) :
    SkeletonAxisRange q (genSemanticSkeleton (bfsAssign (airReorder t)) mf) := by
  intro s hsm
  rw [computeSkeletonRows_genSemantic, computeSkeletonRows_genCompute] at hsm
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hsm
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest _ n).mp hn
  simp only [List.mem_singleton] at hr
  subst hr
  exact axisRange_of_axisInFormula
    (genComputeSkeleton_assigned_inTree_axisInFormula h n hin)
    (genComputeSkeleton_assigned_inTree_bounded hq hs hf hG h n hin).1

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_inTree_axisInFormula
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_airReorder_inTree_axisInFormula
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_assigned_inTree_axisInFormula
#print axioms Nock.NockVMROM.Thm54.TraceGen.axisRange_of_axisInFormula
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_axisRange
