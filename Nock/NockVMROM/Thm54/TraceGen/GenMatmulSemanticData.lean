/-
  Nock/NockVMROM/Thm54/TraceGen/GenMatmulSemanticData.lean

  Per-row `ComputeRowSemanticData` and assembled
  `ExactExecutionSemanticData 65537 2048` on the AIR-ordered matmul
  carrier.  Operational extras are fuel-induction on
  `genComputeSkeleton` (OP0/OP9 slot identities, OP4/OP6 atom windows,
  no OP3 via `SeedOK`); comparisons are diagonal except unequal
  leaf-counts / atom operands, which `seedZ` separates.

  `memoryTrace` / `BuildableNockExecution` are not claimed here.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulBounded
import Nock.NockVMROM.Thm54.BelowDefs.CensusExtraClosure

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ServedLookupBridge
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.ExactExecution
open Nock.NockVMROM.Thm54.CensusExtraClosure

variable {K : Type} [Field K]

/-! ## Per-node census extras -/

def nodeCensus (g : GenComputeRow K) : Prop :=
  SkeletonSlotSemantics g.skel ∧
    SkeletonRecordEquations g.skel ∧
    (g.skel.state = .s4 →
      ∃ k, P8Census.skeletonSubformula g.skel 0 .result = .atom k) ∧
    (g.skel.state = .s6 →
      P8Census.skeletonSubformula g.skel 1 .result = .atom 0 ∨
        P8Census.skeletonSubformula g.skel 1 .result = .atom 1)

theorem nodeCensus_ne_lookup (g : GenComputeRow K)
    (h0 : g.skel.state ≠ .s0) (h9 : g.skel.state ≠ .s9)
    (h4 : g.skel.state ≠ .s4) (h6 : g.skel.state ≠ .s6) :
    nodeCensus g :=
  ⟨slotSemantics_of_ne_lookup _ h0 h9, recordEquations_of_ne_lookup _ h0 h9,
    fun h => (h4 h).elim, fun h => (h6 h).elim⟩

theorem genComputeSkeleton_inTree_census
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (u : NTree (GenComputeRow K)) (hu : InTree t u) :
    nodeCensus u.label := by
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
              simpa [skelNode, genSkelCons] using
                nodeCensus_ne_lookup _ (by simp [genSkelCons])
                  (by simp [genSkelCons]) (by simp [genSkelCons])
                  (by simp [genSkelCons])
            | sub hs hu' =>
              simp [NTree.children] at hs
              rcases hs with rfl | rfl
              · exact ih hL _ hu'
              · exact ih hR _ hu'
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
                refine ⟨genSkelOp0_slotSemantics _ _ _ _ _ _ hslot,
                  genSkelOp0_recordEquations _ _ _ _ _ _, ?_, ?_⟩
                · intro hs4; simp [skelNode, genSkelOp0] at hs4
                · intro hs6; simp [skelNode, genSkelOp0] at hs6
              | sub hs _ =>
                simp [NTree.children] at hs
        · simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          cases hu with
          | here =>
            simpa [skelNode, genSkelOp1] using
              nodeCensus_ne_lookup _ (by simp [genSkelOp1])
                (by simp [genSkelOp1]) (by simp [genSkelOp1])
                (by simp [genSkelOp1])
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
                    simpa [skelNode, genSkelOp2] using
                      nodeCensus_ne_lookup _ (by simp [genSkelOp2])
                        (by simp [genSkelOp2]) (by simp [genSkelOp2])
                        (by simp [genSkelOp2])
                  | sub hs hu' =>
                    simp [NTree.children] at hs
                    rcases hs with rfl | rfl | rfl
                    · exact ih hB _ hu'
                    · exact ih hC _ hu'
                    · exact ih hM _ hu'
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            cases hu with
            | here =>
              simpa [skelNode, genSkelOp3] using
                nodeCensus_ne_lookup _ (by simp [genSkelOp3])
                  (by simp [genSkelOp3]) (by simp [genSkelOp3])
                  (by simp [genSkelOp3])
            | sub hs hu' =>
              simp [NTree.children] at hs
              cases hs
              exact ih hcall _ hu'
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
                refine ⟨slotSemantics_of_ne_lookup _ (by simp [skelNode, genSkelOp4])
                    (by simp [skelNode, genSkelOp4]),
                  recordEquations_of_ne_lookup _ (by simp [skelNode, genSkelOp4])
                    (by simp [skelNode, genSkelOp4]), ?_, ?_⟩
                · intro _
                  obtain ⟨k, hk, _⟩ := lus_eq_some hlus
                  refine ⟨k, ?_⟩
                  simp [skelNode, genSkelOp4, P8Census.skeletonSubformula,
                    ComputeTable.fanoutComp, hk]
                · intro hs6; simp [skelNode, genSkelOp4] at hs6
              | sub hs hu' =>
                simp [NTree.children] at hs
                cases hs
                exact ih hcall _ hu'
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
                  simpa [skelNode, genSkelOp5] using
                    nodeCensus_ne_lookup _ (by simp [genSkelOp5])
                      (by simp [genSkelOp5]) (by simp [genSkelOp5])
                      (by simp [genSkelOp5])
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
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
                        refine ⟨slotSemantics_of_ne_lookup _
                            (by simp [skelNode, genSkelOp6])
                            (by simp [skelNode, genSkelOp6]),
                          recordEquations_of_ne_lookup _
                            (by simp [skelNode, genSkelOp6])
                            (by simp [skelNode, genSkelOp6]), ?_, ?_⟩
                        · intro hs4; simp [skelNode, genSkelOp6] at hs4
                        · intro _
                          simp [skelNode, genSkelOp6, P8Census.skeletonSubformula,
                            ComputeTable.fanoutComp]
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
                          refine ⟨slotSemantics_of_ne_lookup _
                              (by simp [skelNode, genSkelOp6])
                              (by simp [skelNode, genSkelOp6]),
                            recordEquations_of_ne_lookup _
                              (by simp [skelNode, genSkelOp6])
                              (by simp [skelNode, genSkelOp6]), ?_, ?_⟩
                          · intro hs4; simp [skelNode, genSkelOp6] at hs4
                          · intro _
                            simp [skelNode, genSkelOp6, P8Census.skeletonSubformula,
                              ComputeTable.fanoutComp]
                        | sub hs hu' =>
                          simp [NTree.children] at hs
                          rcases hs with rfl | rfl
                          · exact ih hcond _ hu'
                          · exact ih htaken _ hu'
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
                  simpa [skelNode, genSkelOp7] using
                    nodeCensus_ne_lookup _ (by simp [genSkelOp7])
                      (by simp [genSkelOp7]) (by simp [genSkelOp7])
                      (by simp [genSkelOp7])
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
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
                  simpa [skelNode, genSkelOp8] using
                    nodeCensus_ne_lookup _ (by simp [genSkelOp8])
                      (by simp [genSkelOp8]) (by simp [genSkelOp8])
                      (by simp [genSkelOp8])
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih hB _ hu'
                  · exact ih hC _ hu'
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
                      refine ⟨genSkelOp9_slotSemantics _ _ _ _ _ _ _ _ _ _ hslot,
                        genSkelOp9_recordEquations _ _ _ _ _ _ _ _ _ _, ?_, ?_⟩
                      · intro hs4; simp [skelNode, genSkelOp9] at hs4
                      · intro hs6; simp [skelNode, genSkelOp9] at hs6
                    | sub hs hu' =>
                      simp [NTree.children] at hs
                      rcases hs with rfl | rfl
                      · exact ih hcore _ hu'
                      · exact ih hinv _ hu'
        · simp [genComputeSkeleton] at h
        · simp [genComputeSkeleton] at h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

theorem mmTree_inTree_census (u : NTree (GenComputeRow K))
    (hu : InTree (mmTree (K := K)) u) :
    nodeCensus u.label :=
  genComputeSkeleton_inTree_census (mmTree_gen (K := K)) u hu

theorem mmTreeAir_inTree_census (u : NTree (GenComputeRow K))
    (hu : InTree (mmTreeAir (K := K)) u) :
    nodeCensus u.label := by
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label (mmTree (K := K)) u hu
  simpa [nodeCensus, hl] using mmTree_inTree_census u0 hu0

theorem bfsAssign_inTree_census {t : NTree (GenComputeRow K)}
    (H : ∀ u, InTree t u → nodeCensus u.label)
    (n : NTree (GenComputeRow K)) (hn : InTree (bfsAssign t) n) :
    nodeCensus n.label := by
  have hnF : n ∈ bfsForest [bfsAssign t] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [bfsAssign_bfsForest_labels] at hlab
  obtain ⟨i, hi, hni⟩ := List.mem_map.mp hlab
  have hi' := lt_bfsRows_of_mem_range' hi
  have hrow : (bfsRows t)[i - 1] ∈ bfsRows t := List.getElem_mem hi'
  unfold bfsRows at hrow
  obtain ⟨n0, hn0, hlab0⟩ := List.mem_map.mp hrow
  obtain ⟨u0, hu0, hin0⟩ := (mem_bfsForest _ n0).mp hn0
  simp only [List.mem_singleton] at hu0
  subst u0
  have hb := H n0 hin0
  have hbeq : (bfsRows t)[i - 1] = n0.label := by
    unfold bfsRows; exact hlab0.symm
  rw [← hni]
  have hskel : (bfsLabelAt t i).skel = n0.label.skel := by
    rw [bfsLabelAt_skel t i hi', hbeq]
  simpa [nodeCensus, hskel] using hb

theorem mmAssigned_inTree_census (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (mmTreeAir (K := K))) n) :
    nodeCensus n.label :=
  bfsAssign_inTree_census mmTreeAir_inTree_census n hn

/-! ## Cell identities and comparison classification -/

/-- Every OP6 `[6 [b [c d]]]` in a noun has distinct then/else leaf counts
    modulo `orderOf seedZ = 32`. -/
def nounOp6Sep : Noun → Bool
  | .atom _ => true
  | .cell l r =>
      (match l, r with
        | .atom 6, .cell _ (.cell c d) => decide (c.leaves % 32 ≠ d.leaves % 32)
        | _, _ => true) && nounOp6Sep l && nounOp6Sep r

theorem nounOp6Sep_atom (k : ℕ) : nounOp6Sep (.atom k) = true := rfl

theorem nounOp6Sep_left {l r : Noun} (h : nounOp6Sep (.cell l r) = true) :
    nounOp6Sep l = true := by
  simp only [nounOp6Sep] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

theorem nounOp6Sep_right {l r : Noun} (h : nounOp6Sep (.cell l r) = true) :
    nounOp6Sep r = true := by
  simp only [nounOp6Sep] at h
  rw [Bool.and_eq_true] at h
  exact h.2

theorem nounOp6Sep_op6 {b c d : Noun}
    (h : nounOp6Sep (.cell (.atom 6) (.cell b (.cell c d))) = true) :
    c.leaves % 32 ≠ d.leaves % 32 := by
  simp only [nounOp6Sep] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1

/-! `CmpKind`: a census comparison is a diagonal, an atom pair, or the
    OP6 then/else off-diagonal. -/
def CmpKind (s : ComputeRowSkeleton) (c : SemanticTrace.ComparisonUse) : Prop :=
  c.left = c.right ∨
    (∃ a b : ℕ, c.left = .atom a ∧ c.right = .atom b) ∨
    (c.left = P8Census.skeletonDec s .f_tth ∧
      c.right = P8Census.skeletonDec s .f_ttt) ∨
    (c.left = P8Census.skeletonDec s .f_ttt ∧
      c.right = P8Census.skeletonDec s .f_tth) ∨
    c.role = .equalityOperand

theorem cmpKind_diag {s : ComputeRowSkeleton} {n : Noun}
    {c : SemanticTrace.ComparisonUse} (h : c.left = n ∧ c.right = n) :
    CmpKind s c :=
  Or.inl (h.1.trans h.2.symm)

theorem cmpKind_atoms {s : ComputeRowSkeleton} {a b : ℕ}
    {c : SemanticTrace.ComparisonUse}
    (h : c.left = .atom a ∧ c.right = .atom b) :
    CmpKind s c :=
  Or.inr (Or.inl ⟨a, b, h⟩)

theorem genSkelCons_cmpKind (subject leftF rightF leftR rightR : Noun) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelCons subject leftF rightF leftR rightR),
      CmpKind (genSkelCons subject leftF rightF leftR rightR) c := by
  intro c hc
  simp [P8Census.skeletonComparisons, P8Census.skeletonDec,
    P8Census.skeletonSubformula, P8Census.skeletonUse, genSkelCons,
    ComputeTable.fanoutComp, decActive] at hc
  rcases hc with h | h | h | h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl

theorem genSkelOp1_cmpKind (subject formula result : Noun)
    (hform : formula = .cell (.atom 1) result) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp1 subject formula result (.atom 1)),
      CmpKind (genSkelOp1 subject formula result (.atom 1)) c := by
  intro c hc
  simp [P8Census.skeletonComparisons, P8Census.skeletonDec,
    P8Census.skeletonUse, genSkelOp1, decActive] at hc
  rcases hc with h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl (by simp [hform])
  · subst h; exact Or.inl rfl

theorem genSkelOp0_cmpKind (subject formula result : Noun) (axis : ℕ)
    (hform : formula = .cell (.atom 0) (.atom axis)) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp0 subject formula (.atom 0) (.atom axis) result axis),
      CmpKind (genSkelOp0 subject formula (.atom 0) (.atom axis) result axis) c := by
  intro c hc
  simp [P8Census.skeletonComparisons, P8Census.skeletonDec,
    P8Census.skeletonUse, P8Census.skeletonMemoryAxis, genSkelOp0,
    Nock.Framework.recordCount, decActive] at hc
  rcases hc with h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl (by simp [hform])
  · subst h; exact Or.inl rfl

theorem genSkelOp4_cmpKind (subject formula tail callResult result : Noun)
    (hform : formula = .cell (.atom 4) tail)
    (hk : ∃ k, callResult = .atom k)
    (hr : ∃ k, result = .atom k) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp4 subject formula (.atom 4) tail subject tail callResult result),
      CmpKind (genSkelOp4 subject formula (.atom 4) tail subject tail
        callResult result) c := by
  intro c hc
  simp [P8Census.skeletonComparisons, P8Census.skeletonDec,
    P8Census.skeletonSubformula, P8Census.skeletonUse, genSkelOp4,
    ComputeTable.fanoutComp, decActive] at hc
  rcases hc with h | h | h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl (by simp [hform])
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h
    obtain ⟨k, hk⟩ := hk
    obtain ⟨k', hr⟩ := hr
    refine Or.inr (Or.inl ⟨k', (k + 1) % ringChar K, hr, ?_⟩)
    simp [OpcodeSemantics.incMod, hk]

theorem genSkelOp2_cmpKind
    (subject formula fTail fTh fTt sf1 sf2 result : Noun)
    (hform : formula = .cell (.atom 2) fTail)
    (htail : fTail = .cell fTh fTt) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp2 subject formula (.atom 2) fTail fTh fTt sf1 sf2 result),
      CmpKind (genSkelOp2 subject formula (.atom 2) fTail fTh fTt sf1 sf2
        result) c := by
  intro c hc
  simp [P8Census.skeletonComparisons, P8Census.skeletonDec,
    P8Census.skeletonSubformula, P8Census.skeletonUse, genSkelOp2,
    ComputeTable.fanoutComp, decActive, hasTailDecomposition] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl (by simp [hform])
  · subst h; exact Or.inl (by simp [htail])
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl

theorem genSkelOp5_cmpKind
    (subject formula fTail fTh fTt sf1 sf2 result : Noun)
    (hform : formula = .cell (.atom 5) fTail)
    (htail : fTail = .cell fTh fTt)
    (hres : result = Noun.tis sf1 sf2) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp5 subject formula (.atom 5) fTail fTh fTt sf1 sf2 result),
      CmpKind (genSkelOp5 subject formula (.atom 5) fTail fTh fTt sf1 sf2
        result) c := by
  intro c hc
  simp [P8Census.skeletonComparisons, P8Census.skeletonDec,
    P8Census.skeletonSubformula, P8Census.skeletonUse, genSkelOp5,
    ComputeTable.fanoutComp, decActive, hasTailDecomposition] at hc
  rcases hc with h | h | h | h | h | h | h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl (by simp [hform])
  · subst h; exact Or.inl (by simp [htail])
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h
    by_cases heq : sf1 = sf2
    · subst heq; exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · subst h; exact Or.inl (by simp [hres])

theorem genSkelOp6_cmpKind
    (subject formula fTail fTh fTt fTth fTtt cond taken result : Noun)
    (hform : formula = .cell (.atom 6) fTail)
    (htail : fTail = .cell fTh fTt)
    (hbr : fTt = .cell fTth fTtt)
    (htaken : taken = fTth ∨ taken = fTtt) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp6 subject formula (.atom 6) fTail fTh fTt fTth fTtt cond
        taken result),
      CmpKind (genSkelOp6 subject formula (.atom 6) fTail fTh fTt fTth fTtt
        cond taken result) c := by
  intro c hc
  simp [P8Census.skeletonComparisons, P8Census.skeletonDec,
    P8Census.skeletonSubformula, P8Census.skeletonUse, genSkelOp6,
    ComputeTable.fanoutComp, decActive, hasTailDecomposition] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl (by simp [hform])
  · subst h; exact Or.inl (by simp [htail])
  · subst h; exact Or.inl (by simp [hbr])
  · subst h; exact Or.inl rfl
  · subst h
    rcases htaken with htaken | htaken
    · exact Or.inl (by simp [htaken])
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨htaken, rfl⟩)))
  · subst h
    rcases htaken with htaken | htaken
    · exact Or.inr (Or.inr (Or.inl ⟨htaken, rfl⟩))
    · exact Or.inl (by simp [htaken])
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl

theorem genSkelOp7_sf0 (subject formula fTail fTh fTt sb result : Noun)
    (slot : SemanticStrategy.TripleSlot) :
    P8Census.skeletonSubformula
      (genSkelOp7 subject formula (.atom 7) fTail fTh fTt sb result)
      ⟨0, by decide⟩ slot =
      match slot with
      | .subject => sb
      | .formula => fTt
      | .result => result := by
  unfold P8Census.skeletonSubformula
  rw [dif_pos (by simp [genSkelOp7, ComputeTable.fanoutComp])]
  rfl

theorem genSkelOp7_sf1 (subject formula fTail fTh fTt sb result : Noun)
    (slot : SemanticStrategy.TripleSlot) :
    P8Census.skeletonSubformula
      (genSkelOp7 subject formula (.atom 7) fTail fTh fTt sb result)
      ⟨1, by decide⟩ slot =
      match slot with
      | .subject => subject
      | .formula => fTh
      | .result => sb := by
  unfold P8Census.skeletonSubformula
  rw [dif_pos (by simp [genSkelOp7, ComputeTable.fanoutComp])]
  rfl

theorem genSkelOp7_cmpKind
    (subject formula fTail fTh fTt sb result : Noun)
    (hform : formula = .cell (.atom 7) fTail)
    (htail : fTail = .cell fTh fTt) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp7 subject formula (.atom 7) fTail fTh fTt sb result),
      CmpKind (genSkelOp7 subject formula (.atom 7) fTail fTh fTt sb
        result) c := by
  intro c hc
  simp [P8Census.skeletonComparisons, P8Census.skeletonDec,
    P8Census.skeletonUse, genSkelOp7, ComputeTable.fanoutComp,
    decActive, hasTailDecomposition,
    genSkelOp7_sf0, genSkelOp7_sf1] at hc
  rcases hc with h | h | h | h | h | h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl (by simp [hform])
  · subst h; exact Or.inl (by simp [htail])
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl

theorem genSkelOp8_sf0 (subject formula fTail fTh fTt sb result : Noun)
    (slot : SemanticStrategy.TripleSlot) :
    P8Census.skeletonSubformula
      (genSkelOp8 subject formula (.atom 8) fTail fTh fTt sb result)
      ⟨0, by decide⟩ slot =
      match slot with
      | .subject => .cell sb subject
      | .formula => fTt
      | .result => result := by
  unfold P8Census.skeletonSubformula
  rw [dif_pos (by simp [genSkelOp8, ComputeTable.fanoutComp])]
  rfl

theorem genSkelOp8_sf1 (subject formula fTail fTh fTt sb result : Noun)
    (slot : SemanticStrategy.TripleSlot) :
    P8Census.skeletonSubformula
      (genSkelOp8 subject formula (.atom 8) fTail fTh fTt sb result)
      ⟨1, by decide⟩ slot =
      match slot with
      | .subject => subject
      | .formula => fTh
      | .result => sb := by
  unfold P8Census.skeletonSubformula
  rw [dif_pos (by simp [genSkelOp8, ComputeTable.fanoutComp])]
  rfl

theorem genSkelOp8_cmpKind
    (subject formula fTail fTh fTt sb result : Noun)
    (hform : formula = .cell (.atom 8) fTail)
    (htail : fTail = .cell fTh fTt) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp8 subject formula (.atom 8) fTail fTh fTt sb result),
      CmpKind (genSkelOp8 subject formula (.atom 8) fTail fTh fTt sb
        result) c := by
  intro c hc
  simp [P8Census.skeletonComparisons, P8Census.skeletonDec,
    P8Census.skeletonUse, genSkelOp8, ComputeTable.fanoutComp,
    decActive, hasTailDecomposition,
    genSkelOp8_sf0, genSkelOp8_sf1] at hc
  rcases hc with h | h | h | h | h | h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl (by simp [hform])
  · subst h; exact Or.inl (by simp [htail])
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl

theorem genSkelOp9_sf0 (subject formula fTail fTh fTt core arm result : Noun)
    (axis : ℕ) (slot : SemanticStrategy.TripleSlot) :
    P8Census.skeletonSubformula
      (genSkelOp9 subject formula (.atom 9) fTail fTh fTt core arm result
        axis) ⟨0, by decide⟩ slot =
      match slot with
      | .subject => subject
      | .formula => fTt
      | .result => core := by
  unfold P8Census.skeletonSubformula
  rw [dif_pos (by simp [genSkelOp9, ComputeTable.fanoutComp])]
  rfl

theorem genSkelOp9_sf1 (subject formula fTail fTh fTt core arm result : Noun)
    (axis : ℕ) (slot : SemanticStrategy.TripleSlot) :
    P8Census.skeletonSubformula
      (genSkelOp9 subject formula (.atom 9) fTail fTh fTt core arm result
        axis) ⟨1, by decide⟩ slot =
      match slot with
      | .subject => core
      | .formula => arm
      | .result => result := by
  unfold P8Census.skeletonSubformula
  rw [dif_pos (by simp [genSkelOp9, ComputeTable.fanoutComp])]
  rfl

theorem genSkelOp9_cmpKind
    (subject formula fTail fTh fTt core arm result : Noun) (axis : ℕ)
    (hform : formula = .cell (.atom 9) fTail)
    (htail : fTail = .cell fTh fTt)
    (haxis : fTh = .atom axis) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp9 subject formula (.atom 9) fTail fTh fTt core arm result
        axis),
      CmpKind (genSkelOp9 subject formula (.atom 9) fTail fTh fTt core arm
        result axis) c := by
  intro c hc
  simp [P8Census.skeletonComparisons, P8Census.skeletonDec,
    P8Census.skeletonUse, P8Census.skeletonMemoryAxis, genSkelOp9,
    ComputeTable.fanoutComp, Nock.Framework.recordCount, decActive,
    hasTailDecomposition, genSkelOp9_sf0, genSkelOp9_sf1] at hc
  rcases hc with h | h | h | h | h | h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl (by simp [hform])
  · subst h; exact Or.inl (by simp [htail])
  · subst h; exact Or.inl (by simp [haxis])
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl

theorem genSkelOp3_cmpKind
    (subject formula tail callResult result : Noun)
    (hform : formula = .cell (.atom 3) tail)
    (hres : result = Noun.wut callResult) :
    ∀ c ∈ P8Census.skeletonComparisons (K := K)
      (genSkelOp3 subject formula (.atom 3) tail subject tail callResult
        result),
      CmpKind (genSkelOp3 subject formula (.atom 3) tail subject tail
        callResult result) c := by
  intro c hc
  simp [P8Census.skeletonComparisons, P8Census.skeletonDec,
    P8Census.skeletonSubformula, P8Census.skeletonUse, genSkelOp3,
    ComputeTable.fanoutComp, decActive] at hc
  rcases hc with h | h | h | h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl (by simp [hform])
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inl (by simp [hres])

theorem nounOp6Sep_slot {n : Noun} {ax : ℕ} {v : Noun}
    (h : nounOp6Sep n = true) (hs : Noun.slot ax n = some v) :
    nounOp6Sep v = true := by
  induction ax using Nat.strongRecOn generalizing n v with
  | ind ax ih =>
    match ax with
    | 0 => simp [Noun.slot] at hs
    | 1 =>
      simp [Noun.slot] at hs
      subst v
      exact h
    | ax + 2 =>
      have hge : 2 ≤ ax + 2 := by omega
      rw [slot_ge_two (ax + 2) n hge] at hs
      cases hmid : Noun.slot ((ax + 2) / 2) n with
      | none =>
        rw [hmid] at hs
        cases hs
      | some mid =>
        have hmid' : nounOp6Sep mid = true :=
          ih ((ax + 2) / 2) (by omega) h hmid
        rw [hmid] at hs
        cases mid with
        | atom _ => simp at hs
        | cell l r =>
          simp at hs
          by_cases hmod : ax % 2 = 0
          · simp [hmod] at hs
            subst v
            exact nounOp6Sep_left hmid'
          · simp [hmod] at hs
            subst v
            exact nounOp6Sep_right hmid'

def NoHead8 : Noun → Prop
  | .atom _ => True
  | .cell (.atom _op) tl => NoHead8 tl
  | .cell (.cell a b) c => NoHead8 (.cell a b) ∧ NoHead8 c

instance instDecidableNoHead8 : (n : Noun) → Decidable (NoHead8 n)
  | .atom _ => isTrue trivial
  | .cell (.atom _op) tl => instDecidableNoHead8 tl
  | .cell (.cell a b) c =>
    match instDecidableNoHead8 (.cell a b), instDecidableNoHead8 c with
    | isTrue hl, isTrue hr => isTrue ⟨hl, hr⟩
    | isFalse hl, _ => isFalse fun hf => hl hf.1
    | _, isFalse hr => isFalse fun hf => hr hf.2

theorem noHead8_left {a b : Noun} (h : NoHead8 (.cell a b)) : NoHead8 a := by
  cases a with
  | atom _ => exact trivial
  | cell _ _ => exact h.1

theorem noHead8_right {a b : Noun} (h : NoHead8 (.cell a b)) : NoHead8 b := by
  cases a with
  | atom _ => exact h
  | cell _ _ => exact h.2

theorem noHead8_slot {n : Noun} {ax : ℕ} {v : Noun}
    (h : NoHead8 n) (hs : Noun.slot ax n = some v) : NoHead8 v := by
  induction ax using Nat.strongRecOn generalizing n v with
  | ind ax ih =>
    match ax with
    | 0 => simp [Noun.slot] at hs
    | 1 =>
      simp [Noun.slot] at hs
      subst v
      exact h
    | ax + 2 =>
      have hge : 2 ≤ ax + 2 := by omega
      rw [slot_ge_two (ax + 2) n hge] at hs
      cases hmid : Noun.slot ((ax + 2) / 2) n with
      | none =>
        rw [hmid] at hs
        cases hs
      | some mid =>
        have hmid' : NoHead8 mid :=
          ih ((ax + 2) / 2) (by omega) h hmid
        rw [hmid] at hs
        cases mid with
        | atom _ => simp at hs
        | cell l r =>
          simp at hs
          by_cases hmod : ax % 2 = 0
          · simp [hmod] at hs
            subst v
            exact noHead8_left hmid'
          · simp [hmod] at hs
            subst v
            exact noHead8_right hmid'

theorem noHead8_pair {a b : Noun} (ha : NoHead8 a) (hb : NoHead8 b) :
    NoHead8 (.cell a b) := by
  cases a with
  | atom _ => exact hb
  | cell _ _ => exact ⟨ha, hb⟩

theorem nounOp6Sep_cell_cell {a b r : Noun}
    (hl : nounOp6Sep (.cell a b) = true) (hr : nounOp6Sep r = true) :
    nounOp6Sep (.cell (.cell a b) r) = true := by
  conv => lhs; unfold nounOp6Sep
  simp [hl, hr]

theorem nounOp6Sep_cell_atom {k : ℕ} {r : Noun} (hk : k ≠ 6)
    (hr : nounOp6Sep r = true) :
    nounOp6Sep (.cell (.atom k) r) = true := by
  conv => lhs; unfold nounOp6Sep
  simp only [nounOp6Sep_atom, hr, Bool.true_and, Bool.and_true]
  split
  · exact (hk (by injection ‹atom k = atom 6›)).elim
  · rfl

theorem nounOp6Sep_cell {l r : Noun}
    (hl : nounOp6Sep l = true) (hr : nounOp6Sep r = true)
    (h6 : ∀ b c d, l = .atom 6 → r = .cell b (.cell c d) →
      c.leaves % 32 ≠ d.leaves % 32) :
    nounOp6Sep (.cell l r) = true := by
  conv => lhs; unfold nounOp6Sep
  simp only [hl, hr, Bool.true_and, Bool.and_true]
  split
  · apply decide_eq_true
    apply h6
    · rfl
    · rfl
  · rfl

theorem genComputeSkeleton_cons_eval_is_cell
    {fuel : ℕ} {s a b c : Noun} {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) fuel s (.cell (.cell a b) c) = .ok (t, r)) :
    ∃ x y, r = .cell x y := by
  cases fuel with
  | zero => simp [genComputeSkeleton] at h
  | succ n =>
    cases hL : genComputeSkeleton (K := K) n s (.cell a b) with
    | error _ => simp [genComputeSkeleton, hL] at h
    | ok pL =>
      cases hR : genComputeSkeleton (K := K) n s c with
      | error _ => simp [genComputeSkeleton, hL, hR] at h
      | ok pR =>
        simp [genComputeSkeleton, hL, hR] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨pL.2, pR.2, rfl⟩

theorem genComputeSkeleton_op1_result
    {fuel : ℕ} {s tl : Noun} {t : NTree (GenComputeRow K)} {r : Noun}
    (h : genComputeSkeleton (K := K) fuel s (.cell (.atom 1) tl) = .ok (t, r)) :
    r = tl := by
  cases fuel with
  | zero => simp [genComputeSkeleton] at h
  | succ n =>
    simp [genComputeSkeleton] at h
    exact h.2.symm

/-- True of nouns that are literally an OP6 cell `[6 [b [c d]]]`.  Autocons can
    *synthesize* this shape from `[1 6]` and a nested quote; full `nounOp6Sep`
    is then not implied by the children. -/
def op6Shaped : Noun → Bool
  | .cell (.atom 6) (.cell _ (.cell _ _)) => true
  | _ => false

/-- Result invariant: full OP6-then/else sep, or the value itself is OP6-shaped
    (so the parent check is exactly the missing ineq).  Formulas stay full. -/
structure EvalInv (n : Noun) : Prop where
  full_or_op6 : nounOp6Sep n = true ∨ op6Shaped n = true
  no8 : NoHead8 n

theorem evalInv_full {n : Noun} (h : nounOp6Sep n = true) (h8 : NoHead8 n) :
    EvalInv n :=
  ⟨Or.inl h, h8⟩

theorem evalInv_to_full {n : Noun} (h : EvalInv n)
    (hnot : op6Shaped n = false) : nounOp6Sep n = true :=
  h.full_or_op6.elim id (fun hop => by simp [hop] at hnot)

theorem evalInv_op1 {fuel : ℕ} {s tl : Noun}
    {t : NTree (GenComputeRow K)} {r : Noun}
    (hsep : nounOp6Sep (.cell (.atom 1) tl) = true)
    (h8 : NoHead8 (.cell (.atom 1) tl))
    (h : genComputeSkeleton (K := K) fuel s (.cell (.atom 1) tl) = .ok (t, r)) :
    EvalInv r :=
  evalInv_full
    (by simpa [genComputeSkeleton_op1_result h] using nounOp6Sep_right hsep)
    (by simpa [genComputeSkeleton_op1_result h] using noHead8_right h8)

theorem evalInv_cell {l r : Noun}
    (hl : nounOp6Sep l = true) (hr : nounOp6Sep r = true)
    (h8 : NoHead8 (.cell l r)) :
    EvalInv (.cell l r) := by
  refine ⟨?_, h8⟩
  cases l with
  | atom k =>
    by_cases hk : k = 6
    · subst hk
      cases r with
      | atom _ =>
        exact Or.inl (by conv => lhs; unfold nounOp6Sep; simp [hl, hr])
      | cell b rest =>
        cases rest with
        | atom _ =>
          exact Or.inl (by conv => lhs; unfold nounOp6Sep; simp [hl, hr])
        | cell c d =>
          by_cases hineq : c.leaves % 32 ≠ d.leaves % 32
          · exact Or.inl (nounOp6Sep_cell hl hr fun _b _c _d h1 h2 => by
              cases h1
              cases h2
              exact hineq)
          · exact Or.inr (by simp [op6Shaped])
    · exact Or.inl (nounOp6Sep_cell_atom hk hr)
  | cell a b =>
    exact Or.inl (nounOp6Sep_cell_cell hl hr)

/- Autocons of `[1 6]` with a nested cell can *synthesize* an OP6-shaped
   result whose then/else leaf-counts collide, so `EvalInv` does not
   imply `nounOp6Sep` on every eval.  Formula/subject sep is therefore
   not part of the generic `NodeCmpKind` induction; matmul discharges it
   on `mmFormula` / `mmBattery` / `mmSubject` by `decide`. -/

/-! ## `RowCellIdentities` on generated skeletons -/

theorem genSkelCons_cellIdentities (subject leftF rightF leftR rightR : Noun) :
    RowCellIdentities (genSkelCons subject leftF rightF leftR rightR) where
  formula_cons := by
    simp [P8Census.skeletonDec, genSkelCons, SemanticStrategy.decActive]
  tail_cons := by
    intro h
    simp [genSkelCons, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition] at h
  branchTail_cons := by
    intro h
    simp [genSkelCons, SemanticStrategy.decActive] at h
  push_cons := by
    intro h
    simp [genSkelCons] at h
  cons_result := by
    simp [P8Census.skeletonSubformula, genSkelCons, ComputeTable.fanoutComp]

theorem genSkelOp1_cellIdentities (subject formula result : Noun)
    (hform : formula = .cell (.atom 1) result) :
    RowCellIdentities (genSkelOp1 subject formula result (.atom 1)) where
  formula_cons := by
    simp [P8Census.skeletonDec, genSkelOp1, SemanticStrategy.decActive, hform]
  tail_cons := by
    intro h
    simp [genSkelOp1, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition] at h
  branchTail_cons := by
    intro h
    simp [genSkelOp1, SemanticStrategy.decActive] at h
  push_cons := by
    intro h
    simp [genSkelOp1] at h
  cons_result := by
    intro h
    simp [genSkelOp1] at h

theorem genSkelOp0_cellIdentities (subject formula result : Noun) (axis : ℕ)
    (hform : formula = .cell (.atom 0) (.atom axis)) :
    RowCellIdentities
      (genSkelOp0 subject formula (.atom 0) (.atom axis) result axis) where
  formula_cons := by
    simp [P8Census.skeletonDec, genSkelOp0, SemanticStrategy.decActive, hform]
  tail_cons := by
    intro h
    simp [genSkelOp0, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition] at h
  branchTail_cons := by
    intro h
    simp [genSkelOp0, SemanticStrategy.decActive] at h
  push_cons := by
    intro h
    simp [genSkelOp0] at h
  cons_result := by
    intro h
    simp [genSkelOp0] at h

theorem genSkelOp2_cellIdentities (subject formula fTail fTh fTt sf1 sf2 result : Noun)
    (hform : formula = .cell (.atom 2) fTail)
    (htail : fTail = .cell fTh fTt) :
    RowCellIdentities
      (genSkelOp2 subject formula (.atom 2) fTail fTh fTt sf1 sf2 result) where
  formula_cons := by
    simp [P8Census.skeletonDec, genSkelOp2, SemanticStrategy.decActive, hform]
  tail_cons := by
    intro _
    simp [P8Census.skeletonDec, genSkelOp2, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition, htail]
  branchTail_cons := by
    intro h
    simp [genSkelOp2, SemanticStrategy.decActive] at h
  push_cons := by
    intro h
    simp [genSkelOp2] at h
  cons_result := by
    intro h
    simp [genSkelOp2] at h

theorem genSkelOp3_cellIdentities (subject formula tail callResult result : Noun)
    (hform : formula = .cell (.atom 3) tail) :
    RowCellIdentities
      (genSkelOp3 subject formula (.atom 3) tail subject tail callResult result) where
  formula_cons := by
    simp [P8Census.skeletonDec, genSkelOp3, SemanticStrategy.decActive, hform]
  tail_cons := by
    intro h
    simp [genSkelOp3, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition] at h
  branchTail_cons := by
    intro h
    simp [genSkelOp3, SemanticStrategy.decActive] at h
  push_cons := by
    intro h
    simp [genSkelOp3] at h
  cons_result := by
    intro h
    simp [genSkelOp3] at h

theorem genSkelOp4_cellIdentities (subject formula tail callResult result : Noun)
    (hform : formula = .cell (.atom 4) tail) :
    RowCellIdentities
      (genSkelOp4 subject formula (.atom 4) tail subject tail callResult result) where
  formula_cons := by
    simp [P8Census.skeletonDec, genSkelOp4, SemanticStrategy.decActive, hform]
  tail_cons := by
    intro h
    simp [genSkelOp4, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition] at h
  branchTail_cons := by
    intro h
    simp [genSkelOp4, SemanticStrategy.decActive] at h
  push_cons := by
    intro h
    simp [genSkelOp4] at h
  cons_result := by
    intro h
    simp [genSkelOp4] at h

theorem genSkelOp5_cellIdentities (subject formula fTail fTh fTt sf1 sf2 result : Noun)
    (hform : formula = .cell (.atom 5) fTail)
    (htail : fTail = .cell fTh fTt) :
    RowCellIdentities
      (genSkelOp5 subject formula (.atom 5) fTail fTh fTt sf1 sf2 result) where
  formula_cons := by
    simp [P8Census.skeletonDec, genSkelOp5, SemanticStrategy.decActive, hform]
  tail_cons := by
    intro _
    simp [P8Census.skeletonDec, genSkelOp5, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition, htail]
  branchTail_cons := by
    intro h
    simp [genSkelOp5, SemanticStrategy.decActive] at h
  push_cons := by
    intro h
    simp [genSkelOp5] at h
  cons_result := by
    intro h
    simp [genSkelOp5] at h

theorem genSkelOp6_cellIdentities
    (subject formula fTail fTh fTt fTth fTtt cond taken result : Noun)
    (hform : formula = .cell (.atom 6) fTail)
    (htail : fTail = .cell fTh fTt)
    (hbr : fTt = .cell fTth fTtt) :
    RowCellIdentities
      (genSkelOp6 subject formula (.atom 6) fTail fTh fTt fTth fTtt cond
        taken result) where
  formula_cons := by
    simp [P8Census.skeletonDec, genSkelOp6, SemanticStrategy.decActive, hform]
  tail_cons := by
    intro _
    simp [P8Census.skeletonDec, genSkelOp6, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition, htail]
  branchTail_cons := by
    intro _
    simp [P8Census.skeletonDec, genSkelOp6, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition, hbr]
  push_cons := by
    intro h
    simp [genSkelOp6] at h
  cons_result := by
    intro h
    simp [genSkelOp6] at h

theorem genSkelOp7_cellIdentities (subject formula fTail fTh fTt sb result : Noun)
    (hform : formula = .cell (.atom 7) fTail)
    (htail : fTail = .cell fTh fTt) :
    RowCellIdentities
      (genSkelOp7 subject formula (.atom 7) fTail fTh fTt sb result) where
  formula_cons := by
    simp [P8Census.skeletonDec, genSkelOp7, SemanticStrategy.decActive, hform]
  tail_cons := by
    intro _
    simp [P8Census.skeletonDec, genSkelOp7, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition, htail]
  branchTail_cons := by
    intro h
    simp [genSkelOp7, SemanticStrategy.decActive] at h
  push_cons := by
    intro h
    simp [genSkelOp7] at h
  cons_result := by
    intro h
    simp [genSkelOp7] at h

theorem genSkelOp8_cellIdentities (subject formula fTail fTh fTt sb result : Noun)
    (hform : formula = .cell (.atom 8) fTail)
    (htail : fTail = .cell fTh fTt) :
    RowCellIdentities
      (genSkelOp8 subject formula (.atom 8) fTail fTh fTt sb result) where
  formula_cons := by
    simp [P8Census.skeletonDec, genSkelOp8, SemanticStrategy.decActive, hform]
  tail_cons := by
    intro _
    simp [P8Census.skeletonDec, genSkelOp8, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition, htail]
  branchTail_cons := by
    intro h
    simp [genSkelOp8, SemanticStrategy.decActive] at h
  push_cons := by
    intro _
    unfold P8Census.skeletonSubformula
    simp [genSkelOp8, ComputeTable.fanoutComp]
  cons_result := by
    intro h
    simp [genSkelOp8] at h

theorem genSkelOp9_cellIdentities
    (subject formula fTail fTh fTt core arm result : Noun) (axis : ℕ)
    (hform : formula = .cell (.atom 9) fTail)
    (htail : fTail = .cell fTh fTt) :
    RowCellIdentities
      (genSkelOp9 subject formula (.atom 9) fTail fTh fTt core arm result
        axis) where
  formula_cons := by
    simp [P8Census.skeletonDec, genSkelOp9, SemanticStrategy.decActive, hform]
  tail_cons := by
    intro _
    simp [P8Census.skeletonDec, genSkelOp9, SemanticStrategy.decActive,
      SemanticStrategy.hasTailDecomposition, htail]
  branchTail_cons := by
    intro h
    simp [genSkelOp9, SemanticStrategy.decActive] at h
  push_cons := by
    intro h
    simp [genSkelOp9] at h
  cons_result := by
    intro h
    simp [genSkelOp9] at h

def NodeCmpKind (g : GenComputeRow K) : Prop :=
  (∀ c ∈ P8Census.skeletonComparisons (K := K) g.skel, CmpKind g.skel c) ∧
    NoHead8 g.skel.formula ∧
    NoHead8 g.skel.subject ∧
    RowCellIdentities g.skel

theorem genComputeSkeleton_inTree_cmpKind
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h8S : NoHead8 subject)
    (h8F : NoHead8 formula)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    NoHead8 result ∧ ∀ u, InTree t u → NodeCmpKind u.label := by
  induction fuel generalizing subject formula t result with
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
            have h8L := noHead8_left h8F
            have h8R := noHead8_right h8F
            have ihL := ih h8S h8L hL
            have ihR := ih h8S h8R hR
            refine ⟨noHead8_pair ihL.1 ihR.1, ?_⟩
            intro u hu
            cases hu with
            | here =>
              refine ⟨genSkelCons_cmpKind _ _ _ _ _, h8F, h8S,
                genSkelCons_cellIdentities _ _ _ _ _⟩
            | sub hs hu' =>
              simp [NTree.children] at hs
              rcases hs with rfl | rfl
              · exact ihL.2 _ hu'
              · exact ihR.2 _ hu'
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
              refine ⟨noHead8_slot h8S hslot, ?_⟩
              intro u hu
              cases hu with
              | here =>
                refine ⟨genSkelOp0_cmpKind _ _ _ _ rfl, h8F, h8S,
                  genSkelOp0_cellIdentities _ _ _ _ rfl⟩
              | sub hs _ =>
                simp [NTree.children] at hs
        · simp [genComputeSkeleton] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨noHead8_right h8F, ?_⟩
          intro u hu
          cases hu with
          | here =>
            refine ⟨genSkelOp1_cmpKind _ _ _ rfl, h8F, h8S,
              genSkelOp1_cellIdentities _ _ _ rfl⟩
          | sub hs _ =>
            simp [NTree.children] at hs
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases h1 : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, h1] at h
            | ok p1 =>
              cases h2 : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, h1, h2] at h
              | ok p2 =>
                cases h3 : genComputeSkeleton (K := K) n p1.2 p2.2 with
                | error _ => simp [genComputeSkeleton, h1, h2, h3] at h
                | ok p3 =>
                  simp [genComputeSkeleton, h1, h2, h3] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have h8B := noHead8_left (noHead8_right h8F)
                  have h8C := noHead8_right (noHead8_right h8F)
                  have ih1 := ih h8S h8B h1
                  have ih2 := ih h8S h8C h2
                  have ih3 := ih ih1.1 ih2.1 h3
                  exact ⟨ih3.1, fun u hu => by
                    cases hu with
                    | here =>
                      refine ⟨genSkelOp2_cmpKind _ _ _ _ _ _ _ _ rfl rfl,
                        h8F, h8S,
                        genSkelOp2_cellIdentities _ _ _ _ _ _ _ _ rfl rfl⟩
                    | sub hs hu' =>
                      simp [NTree.children] at hs
                      rcases hs with rfl | rfl | rfl
                      · exact ih1.2 _ hu'
                      · exact ih2.2 _ hu'
                      · exact ih3.2 _ hu'⟩
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            simp [genComputeSkeleton, hcall] at h
            obtain ⟨rfl, rfl⟩ := h
            have h8T := noHead8_right h8F
            have ihc := ih h8S h8T hcall
            refine ⟨by cases p.2 <;> trivial, ?_⟩
            intro u hu
            cases hu with
            | here =>
              refine ⟨genSkelOp3_cmpKind _ _ _ _ _ rfl rfl, h8F, h8S,
                genSkelOp3_cellIdentities _ _ _ _ _ rfl⟩
            | sub hs hu' =>
              simp [NTree.children] at hs
              subst hs
              exact ihc.2 _ hu'
        · cases hcall : genComputeSkeleton (K := K) n subject tl with
          | error _ => simp [genComputeSkeleton, hcall] at h
          | ok p =>
            cases hlus : Noun.lus p.2 with
            | none => simp [genComputeSkeleton, hcall, hlus] at h
            | some incR =>
              simp [genComputeSkeleton, hcall, hlus] at h
              obtain ⟨rfl, rfl⟩ := h
              have h8T := noHead8_right h8F
              have ihc := ih h8S h8T hcall
              refine ⟨(by
                  cases hp2 : p.2
                  · simp [Noun.lus, hp2] at hlus
                    subst incR
                    trivial
                  · simp [Noun.lus, hp2] at hlus), ?_⟩
              intro u hu
              cases hu with
              | here =>
                refine ⟨genSkelOp4_cmpKind _ _ _ _ _ rfl
                    (by
                      cases hp2 : p.2
                      · exact ⟨_, rfl⟩
                      · simp [Noun.lus, hp2] at hlus)
                    (by
                      cases hp2 : p.2
                      · simp [Noun.lus, hp2] at hlus
                        exact ⟨_, hlus.symm⟩
                      · simp [Noun.lus, hp2] at hlus),
                  h8F, h8S,
                  genSkelOp4_cellIdentities _ _ _ _ _ rfl⟩
              | sub hs hu' =>
                simp [NTree.children] at hs
                subst hs
                exact ihc.2 _ hu'
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases h1 : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, h1] at h
            | ok p1 =>
              cases h2 : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, h1, h2] at h
              | ok p2 =>
                simp [genComputeSkeleton, h1, h2] at h
                obtain ⟨rfl, rfl⟩ := h
                have h8B := noHead8_left (noHead8_right h8F)
                have h8C := noHead8_right (noHead8_right h8F)
                have ih1 := ih h8S h8B h1
                have ih2 := ih h8S h8C h2
                refine ⟨by unfold Noun.tis; split <;> trivial, ?_⟩
                intro u hu
                cases hu with
                | here =>
                  refine ⟨genSkelOp5_cmpKind _ _ _ _ _ _ _ _ rfl rfl rfl,
                    h8F, h8S,
                    genSkelOp5_cellIdentities _ _ _ _ _ _ _ _ rfl rfl⟩
                | sub hs hu' =>
                  simp [NTree.children] at hs
                  rcases hs with rfl | rfl
                  · exact ih1.2 _ hu'
                  · exact ih2.2 _ hu'
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b rest =>
            cases rest with
            | atom _ => simp [genComputeSkeleton] at h
            | cell c d =>
              cases hcond : genComputeSkeleton (K := K) n subject b with
              | error _ => simp [genComputeSkeleton, hcond] at h
              | ok pcond =>
                cases hp : pcond.2 with
                | cell _ _ => simp [genComputeSkeleton, hcond, hp] at h
                | atom cv =>
                  match cv with
                  | 0 =>
                    cases htk : genComputeSkeleton (K := K) n subject c with
                    | error _ => simp [genComputeSkeleton, hcond, hp, htk] at h
                    | ok ptk =>
                      simp [genComputeSkeleton, hcond, hp, htk] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have h8B := noHead8_left (noHead8_right h8F)
                      have h8Br := noHead8_right (noHead8_right h8F)
                      have h8C := noHead8_left h8Br
                      have ihc := ih h8S h8B hcond
                      have iht := ih h8S h8C htk
                      exact ⟨iht.1, fun u hu => by
                        cases hu with
                        | here =>
                          refine ⟨genSkelOp6_cmpKind _ _ _ _ _ _ _ _ _ _ rfl rfl rfl
                              (Or.inl rfl), h8F, h8S,
                            genSkelOp6_cellIdentities _ _ _ _ _ _ _ _ _ _ rfl rfl rfl⟩
                        | sub hs hu' =>
                          simp [NTree.children] at hs
                          rcases hs with rfl | rfl
                          · exact ihc.2 _ hu'
                          · exact iht.2 _ hu'⟩
                  | 1 =>
                    cases htk : genComputeSkeleton (K := K) n subject d with
                    | error _ => simp [genComputeSkeleton, hcond, hp, htk] at h
                    | ok ptk =>
                      simp [genComputeSkeleton, hcond, hp, htk] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have h8B := noHead8_left (noHead8_right h8F)
                      have h8Br := noHead8_right (noHead8_right h8F)
                      have h8D := noHead8_right h8Br
                      have ihc := ih h8S h8B hcond
                      have iht := ih h8S h8D htk
                      exact ⟨iht.1, fun u hu => by
                        cases hu with
                        | here =>
                          refine ⟨genSkelOp6_cmpKind _ _ _ _ _ _ _ _ _ _ rfl rfl rfl
                              (Or.inr rfl), h8F, h8S,
                            genSkelOp6_cellIdentities _ _ _ _ _ _ _ _ _ _ rfl rfl rfl⟩
                        | sub hs hu' =>
                          simp [NTree.children] at hs
                          rcases hs with rfl | rfl
                          · exact ihc.2 _ hu'
                          · exact iht.2 _ hu'⟩
                  | _ + 2 =>
                    simp [genComputeSkeleton, hcond, hp] at h
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hb : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hb] at h
            | ok pb =>
              cases hc : genComputeSkeleton (K := K) n pb.2 c with
              | error _ => simp [genComputeSkeleton, hb, hc] at h
              | ok pc =>
                simp [genComputeSkeleton, hb, hc] at h
                obtain ⟨rfl, rfl⟩ := h
                have h8B := noHead8_left (noHead8_right h8F)
                have h8C := noHead8_right (noHead8_right h8F)
                have ihb := ih h8S h8B hb
                have ihc := ih ihb.1 h8C hc
                exact ⟨ihc.1, fun u hu => by
                  cases hu with
                  | here =>
                    refine ⟨genSkelOp7_cmpKind _ _ _ _ _ _ _ rfl rfl,
                      h8F, h8S,
                      genSkelOp7_cellIdentities _ _ _ _ _ _ _ rfl rfl⟩
                  | sub hs hu' =>
                    simp [NTree.children] at hs
                    rcases hs with rfl | rfl
                    · exact ihb.2 _ hu'
                    · exact ihc.2 _ hu'⟩
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell b c =>
            cases hb : genComputeSkeleton (K := K) n subject b with
            | error _ => simp [genComputeSkeleton, hb] at h
            | ok pb =>
              cases hc : genComputeSkeleton (K := K) n (.cell pb.2 subject) c with
              | error _ => simp [genComputeSkeleton, hb, hc] at h
              | ok pc =>
                simp [genComputeSkeleton, hb, hc] at h
                obtain ⟨rfl, rfl⟩ := h
                have h8B := noHead8_left (noHead8_right h8F)
                have h8C := noHead8_right (noHead8_right h8F)
                have ihb := ih h8S h8B hb
                have h8push : NoHead8 (.cell pb.2 subject) :=
                  noHead8_pair ihb.1 h8S
                have ihc := ih h8push h8C hc
                exact ⟨ihc.1, fun u hu => by
                  cases hu with
                  | here =>
                    refine ⟨genSkelOp8_cmpKind _ _ _ _ _ _ _ rfl rfl,
                      h8F, h8S,
                      genSkelOp8_cellIdentities _ _ _ _ _ _ _ rfl rfl⟩
                  | sub hs hu' =>
                    simp [NTree.children] at hs
                    rcases hs with rfl | rfl
                    · exact ihb.2 _ hu'
                    · exact ihc.2 _ hu'⟩
        · cases tl with
          | atom _ => simp [genComputeSkeleton] at h
          | cell fTh c =>
            cases fTh with
            | cell _ _ => simp [genComputeSkeleton] at h
            | atom ax =>
              cases hcore : genComputeSkeleton (K := K) n subject c with
              | error _ => simp [genComputeSkeleton, hcore] at h
              | ok pcore =>
                cases hslot : Noun.slot ax pcore.2 with
                | none => simp [genComputeSkeleton, hcore, hslot] at h
                | some arm =>
                  cases hinv : genComputeSkeleton (K := K) n pcore.2 arm with
                  | error _ => simp [genComputeSkeleton, hcore, hslot, hinv] at h
                  | ok pinv =>
                    simp [genComputeSkeleton, hcore, hslot, hinv] at h
                    obtain ⟨rfl, rfl⟩ := h
                    have h8C := noHead8_right (noHead8_right h8F)
                    have ihcore := ih h8S h8C hcore
                    have h8Arm := noHead8_slot ihcore.1 hslot
                    have ihinv := ih ihcore.1 h8Arm hinv
                    exact ⟨ihinv.1, fun u hu => by
                      cases hu with
                      | here =>
                        refine ⟨genSkelOp9_cmpKind _ _ _ _ _ _ _ _ _ rfl rfl rfl,
                          h8F, h8S,
                          genSkelOp9_cellIdentities _ _ _ _ _ _ _ _ _ rfl rfl⟩
                      | sub hs hu' =>
                        simp [NTree.children] at hs
                        rcases hs with rfl | rfl
                        · exact ihcore.2 _ hu'
                        · exact ihinv.2 _ hu'⟩
        · simp [genComputeSkeleton] at h
        · simp [genComputeSkeleton] at h
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
          simp only [genComputeSkeleton] at h
          split at h <;> first | omega | contradiction

/-! ## Matmul instantiation -- `mmFormula` / `mmSubject` / AIR carrier -/

theorem mmFormula_noHead8 : NoHead8 mmFormula := by decide
theorem mmSubject_noHead8 : NoHead8 mmSubject := by decide
theorem mmBattery_noHead8 : NoHead8 mmBattery := by decide
theorem addArm_noHead8 : NoHead8 addArm := by decide
theorem macArm_noHead8 : NoHead8 macArm := by decide

theorem mmFormula_nounOp6Sep : nounOp6Sep mmFormula = true := by decide
theorem mmSubject_nounOp6Sep : nounOp6Sep mmSubject = true := by decide
theorem mmBattery_nounOp6Sep : nounOp6Sep mmBattery = true := by decide
theorem addArm_nounOp6Sep : nounOp6Sep addArm = true := by decide
theorem macArm_nounOp6Sep : nounOp6Sep macArm = true := by decide

theorem mmTree_inTree_cmpKind (u : NTree (GenComputeRow K))
    (hu : InTree (mmTree (K := K)) u) :
    NodeCmpKind u.label :=
  (genComputeSkeleton_inTree_cmpKind (K := K)
      mmSubject_noHead8 mmFormula_noHead8 (mmTree_gen (K := K))).2 u hu

theorem mmTreeAir_inTree_cmpKind (u : NTree (GenComputeRow K))
    (hu : InTree (mmTreeAir (K := K)) u) :
    NodeCmpKind u.label := by
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label (mmTree (K := K)) u hu
  simpa [NodeCmpKind, hl] using mmTree_inTree_cmpKind u0 hu0

theorem bfsAssign_inTree_cmpKind {t : NTree (GenComputeRow K)}
    (H : ∀ u, InTree t u → NodeCmpKind u.label)
    (n : NTree (GenComputeRow K)) (hn : InTree (bfsAssign t) n) :
    NodeCmpKind n.label := by
  have hnF : n ∈ bfsForest [bfsAssign t] :=
    (mem_bfsForest _ n).mpr ⟨_, List.mem_singleton.mpr rfl, hn⟩
  have hlab : n.label ∈ (bfsForest [bfsAssign t]).map NTree.label :=
    List.mem_map.mpr ⟨n, hnF, rfl⟩
  rw [bfsAssign_bfsForest_labels] at hlab
  obtain ⟨i, hi, hni⟩ := List.mem_map.mp hlab
  have hi' := lt_bfsRows_of_mem_range' hi
  have hrow : (bfsRows t)[i - 1] ∈ bfsRows t := List.getElem_mem hi'
  unfold bfsRows at hrow
  obtain ⟨n0, hn0, hlab0⟩ := List.mem_map.mp hrow
  obtain ⟨u0, hu0, hin0⟩ := (mem_bfsForest _ n0).mp hn0
  simp only [List.mem_singleton] at hu0
  subst u0
  have hb := H n0 hin0
  have hbeq : (bfsRows t)[i - 1] = n0.label := by
    unfold bfsRows; exact hlab0.symm
  rw [← hni]
  have hskel : (bfsLabelAt t i).skel = n0.label.skel := by
    rw [bfsLabelAt_skel t i hi', hbeq]
  simpa [NodeCmpKind, hskel] using hb

theorem mmAssigned_inTree_cmpKind (n : NTree (GenComputeRow K))
    (hn : InTree (bfsAssign (mmTreeAir (K := K))) n) :
    NodeCmpKind n.label :=
  bfsAssign_inTree_cmpKind mmTreeAir_inTree_cmpKind n hn

theorem bfsRows_of_inTree_root {t : NTree (GenComputeRow K)}
    {n : NTree (GenComputeRow K)} (hn : n ∈ bfsForest [t]) :
    n.label ∈ bfsRows t :=
  List.mem_map.mpr ⟨n, hn, rfl⟩

theorem mmTreeAir_bfsRows_census (g : GenComputeRow K)
    (hg : g ∈ bfsRows (mmTreeAir (K := K))) :
    nodeCensus g := by
  unfold bfsRows at hg
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hg
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ n).mp hn
  simp only [List.mem_singleton] at hu
  subst u
  exact mmTreeAir_inTree_census n hin

theorem mmTreeAir_bfsRows_cmpKind (g : GenComputeRow K)
    (hg : g ∈ bfsRows (mmTreeAir (K := K))) :
    NodeCmpKind g := by
  unfold bfsRows at hg
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hg
  obtain ⟨u, hu, hin⟩ := (mem_bfsForest _ n).mp hn
  simp only [List.mem_singleton] at hu
  subst u
  exact mmTreeAir_inTree_cmpKind n hin

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

open Nock Nock.Walk Nock.NockVM Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.BoundSemanticTrace
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.ExactExecution

noncomputable section

theorem eight_order : orderOf (8 : F) = 32 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hpos
  interval_cases m <;> decide

theorem seedZ_order : orderOf seedZ = 32 := by
  have h := orderOf_injective φ.toMonoidHom φ_injective (8 : F)
  rw [eight_order] at h
  simpa [seedZ] using h

theorem seedZ_order_gt_one : 1 < orderOf seedZ := by
  rw [seedZ_order]; norm_num

def Λ : ℕ := 2048

theorem pairFaithful_self (n : Noun) (h : FieldEmbedding.BoundedBy 65537 n) :
    OpcodeSemantics.PairFaithful seedZ 65537 n n where
  separates := fun hne => absurd rfl hne
  left_bounded := h
  right_bounded := h

theorem windows_of_ne_s346 {z : K} {s : ComputeRowSkeleton}
    (h3 : s.state ≠ .s3) (h4 : s.state ≠ .s4) (h6 : s.state ≠ .s6) :
    SkeletonSizeWindowPremises z s where
  s3_window h := (h3 h).elim
  s4_window h := (h4 h).elim
  s6_window h := (h6 h).elim

theorem semanticSkeleton_operationalCore :
    ∀ s ∈ computeSkeletonRows (semanticSkeleton seedZ alphaA),
      SkeletonOperationalCore s :=
  bfsAssign_operationalCore (mmTreeAir (K := K)) (assignedForest seedZ alphaA)
    (fun g hg => (mmTreeAir_bfsRows_census g hg).2.1)
    (fun g hg => (mmTreeAir_bfsRows_census g hg).1)

end

end Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_inTree_cmpKind
#print axioms Nock.NockVMROM.Thm54.TraceGen.mmAssigned_inTree_cmpKind
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.seedZ_order
#print axioms Nock.NockVMROM.Thm54.TraceGen.MatmulConfig65537.semanticSkeleton_operationalCore



