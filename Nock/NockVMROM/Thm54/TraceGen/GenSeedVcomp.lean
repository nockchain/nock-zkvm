/-
  Nock/NockVMROM/Thm54/TraceGen/GenSeedVcomp.lean

  `romSeed` (`KM`) avoids `{0} ∪ p8.badSeeds ∪ sizeWindowFailureSeeds`.  `SeedGood` is the
  complement of a different set (cons-dyck / OP5-agree / OP3-size, `GenDyckBadSeed`).

  * cons formula-head is a cell — `genComputeSkeleton_inTree_consHead` (`GenConsHead.lean`);
    its leaf window is `RowLeafWindow` of the formula (`genComputeSkeleton_bfsRows_leafWindow_air`,
    from `hconf`);
  * OP5 results have `leaves ≤ Λ` (`RowLeafWindow`) and `BoundedBy q`
    (`genComputeSkeleton_airReorder_inTree_bounded`, from `hs`/`hf`/`hG`/`hq`);
  * OP3 cell-call `leaves ≤ Λ` — the same `RowLeafWindow`.

  None of those is assumed.  The Dyck-bad set is therefore boundable, and the compiler
  avoids its union with the `KM` set.  The extra numerator `3 · rows · (2Λ−1)` is a
  compiler pigeonhole numeral of the same kind as `seedBudget` — **not** a new failure
  event or summand of the consumed soundness bound.

  `romSeedVcomp` is still `Classical.choose`.  Instantiation at a *literal* seed is a
  separate witness (`Batch289`, `seedZ`).
-/
import Nock.NockVMROM.Thm54.TraceGen.GenGenericBounded
import Nock.NockVMROM.Thm54.BelowDefs.TraceGen.GenGoodSeedExists
import Nock.NockVMROM.Thm54.TraceGen.GenChainedLanguage
import Nock.NockVMROM.Thm54.TraceGen.GenRomComplete

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.CensusExtraClosure
open ComputeTable

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## 0. `airReorder` is label-bijective

`labelsFrom_airReorder` is one direction.  The reverse lets `SeedGood` at the AIR
ordering transport back to the generator's raw tree. -/

theorem mem_swapPair_of_mem {α : Type*} {c : α} {cs : List α} (h : c ∈ cs) :
    c ∈ swapPair cs := by
  match cs with
  | [] => cases h
  | [_] => simpa [swapPair] using h
  | [a, b] =>
    have : c = a ∨ c = b := by simpa [List.mem_cons, List.mem_singleton] using h
    simpa [swapPair, List.mem_cons, List.mem_singleton] using Or.symm this
  | _ :: _ :: _ :: _ => simpa [swapPair] using h

theorem mem_children_of_airReorder {g : GenComputeRow K}
    {cs : List (NTree (GenComputeRow K))} {c : NTree (GenComputeRow K)}
    (hc : c ∈ cs) :
    airReorder c ∈ (airReorder (.node g cs)).children := by
  simp only [airReorder]
  split_ifs
  · exact mem_swapPair_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)
  · exact List.mem_map.mpr ⟨c, hc, rfl⟩

theorem labelsFrom_of_airReorder (t : NTree (GenComputeRow K)) :
    LabelsFrom t (airReorder t) := by
  let P := fun t : NTree (GenComputeRow K) => LabelsFrom t (airReorder t)
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro g cs ih u h
    cases h with
    | here =>
      exact ⟨airReorder (.node g cs), InTree.here _, (airReorder_label _).symm⟩
    | sub hs hu =>
      obtain ⟨u', hu', hl⟩ := ih _ hs _ hu
      exact ⟨u', InTree.sub (mem_children_of_airReorder hs) hu', hl⟩
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

theorem seedGood_raw_of_airReorder {z : K} {t : NTree (GenComputeRow K)}
    (h : SeedGood z (airReorder t)) : SeedGood z t :=
  seedGood_of_labelsFrom h (labelsFrom_of_airReorder t)

/-! ## 1. The three shapes, from the generator -/

theorem formulaHead_cell_leaves_le (n : Noun) {a b : Noun}
    (h : formulaHead n = Noun.cell a b) :
    (Noun.cell a b).leaves ≤ n.leaves := by
  cases n with
  | atom _ => simp [formulaHead] at h
  | cell hd tl =>
    simp [formulaHead] at h
    subst h
    exact Nat.le_add_right _ _

theorem skeletonSubformula_bounded {q : ℕ} (hq : 0 < q)
    (s : ComputeRowSkeleton) (hb : s.BoundedBy q)
    (i : Fin 3) (slot : TripleSlot) :
    FieldEmbedding.BoundedBy q (P8Census.skeletonSubformula s i slot) := by
  obtain ⟨_, _, _, _, hsf, _⟩ := hb
  unfold P8Census.skeletonSubformula
  split_ifs with hi
  · exact hsf i hi slot
  · simpa [FieldEmbedding.BoundedBy_atom] using hq

/-- **Per-row bad-seed bound for any accepted program.**  The three shape hypotheses of
`rowBad_card_le_of_shape` are supplied by the generator + `hconf`/`hs`/`hf`/`hG`. -/
theorem rowBad_card_le_of_generated [Fintype K] [DecidableEq K]
    {q Λ : ℕ} (hq : 1 < q) (hle : q ≤ ringChar K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    {g : GenComputeRow K} (hg : g ∈ bfsRows (airReorder t)) :
    (Finset.univ.filter (fun z : K => ¬ RowSeedGood z g)).card ≤ 3 * (2 * Λ - 1) := by
  have hwin : RowLeafWindow Λ g.skel :=
    genComputeSkeleton_bfsRows_leafWindow_air hΛ h hconf g hg
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
  obtain ⟨r, hr, hin⟩ := (mem_bfsForest [airReorder t] u).mp hu
  simp only [List.mem_singleton] at hr
  subst r
  obtain ⟨u0, hu0, hl⟩ := inTree_airReorder_label t u hin
  have hbnd : computeNodeBounded q u :=
    genComputeSkeleton_airReorder_inTree_bounded hq hs hf hG h u hin
  have hskel : u.label.skel.BoundedBy q := hbnd.1
  refine rowBad_card_le_of_shape (K := K) hle Λ u.label ?hcons ?h5 ?h3
  · intro hst
    have hst0 : u0.label.skel.state = State.cons := by
      rw [← hl]; exact hst
    obtain ⟨a, b, hab⟩ := genComputeSkeleton_inTree_consHead h u0 hu0 hst0
    have hhead : formulaHead u.label.skel.formula = Noun.cell a b := by
      rw [hl]; exact hab
    exact ⟨a, b, hhead, (formulaHead_cell_leaves_le _ hhead).trans hwin.2.1⟩
  · intro hst
    refine Or.inr ⟨hwin.2.2.2 ⟨0, by decide⟩ TripleSlot.result,
      hwin.2.2.2 ⟨1, by decide⟩ TripleSlot.result,
      skeletonSubformula_bounded (Nat.zero_lt_of_lt hq) u.label.skel hskel _ _,
      skeletonSubformula_bounded (Nat.zero_lt_of_lt hq) u.label.skel hskel _ _⟩
  · intro _ x y hxy
    have hleav := hwin.2.2.2 (0 : Fin 3) TripleSlot.result
    rw [hxy] at hleav
    exact hleav

/-- Trace-level Dyck-bad count, at the AIR ordering, for any accepted program. -/
theorem seedBad_card_le_of_generated [Fintype K] [DecidableEq K]
    {q Λ : ℕ} (hq : 1 < q) (hle : q ≤ ringChar K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t)) :
    (Finset.univ.filter
        (fun z : K => ∃ g ∈ bfsRows (airReorder t), ¬ RowSeedGood z g)).card
      ≤ (bfsRows (airReorder t)).length * (3 * (2 * Λ - 1)) :=
  seedBad_card_le_air (3 * (2 * Λ - 1)) t
    (fun _ hg => rowBad_card_le_of_generated hq hle hs hf hG h hΛ hconf hg)

end Nock.NockVMROM.Thm54.TraceGen

namespace Nock.NockVMROM.Thm54.TraceGen.GoodSeed

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SizeWindowCounting
open Nock.NockVMROM.Thm54.TraceGen

noncomputable section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {lmb : K}

/-! ## 2. The enlarged budget

`seedBudget` plus the Dyck-bad numerator.  Compiler pigeonhole, not a soundness summand. -/

/-- **Joint seed budget**: the `KM` three-set union plus the Dyck-bad rows. -/
def seedBudgetVcomp (Λ rows : ℕ) : ℕ :=
  seedBudget Λ rows + 3 * rows * (2 * Λ - 1)

theorem seedBudget_le_vcomp (Λ rows : ℕ) :
    seedBudget Λ rows ≤ seedBudgetVcomp Λ rows :=
  Nat.le_add_right _ _

theorem seedBudgetVcomp_gt_rows {Λ rows : ℕ} (hΛ : 1 ≤ Λ) :
    rows < seedBudgetVcomp Λ rows :=
  lt_of_lt_of_le (seedBudget_gt_rows hΛ) (seedBudget_le_vcomp Λ rows)

theorem rows_lt_card_of_seedBudgetVcomp {Λ rows : ℕ}
    (hΛ : 1 ≤ Λ) (h : seedBudgetVcomp Λ rows < Fintype.card K) :
    rows < Fintype.card K :=
  lt_trans (seedBudgetVcomp_gt_rows hΛ) h

/-! ## 3. The joint existential -/

/-- **A joint-good seed exists for every accepted program.**  The conclusion is the `KM`
triple *and* `SeedGood z t`, at the forest the chosen seed generates. -/
theorem exists_vcomp_seed_of_accepted {q Λ : ℕ} (hq : 1 < q) (hle : q ≤ ringChar K)
    {fuel : ℕ} {subject formula : Noun} {t : NTree (GenComputeRow K)} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder t))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudgetVcomp Λ (bfsForest [bfsAssign (airReorder t)]).length
        < Fintype.card K) :
    ∃ z : K, z ≠ 0
      ∧ z ∉ (genSkeletonP8Census (K := K) hΛ h hconf
              (genMemoryForest z α lmb (memInputs z) t)).census.badSeeds
      ∧ z ∉ sizeWindowFailureSeeds (K := K)
              (genSemanticSkeleton (bfsAssign (airReorder t))
                (genMemoryForest z α lmb (memInputs z) t))
      ∧ SeedGood z t := by
  classical
  let rows := (bfsForest [bfsAssign (airReorder t)]).length
  let Cempty := genSkeletonP8Census (K := K) hΛ h hconf
    ([] : List (NTree (GenMemoryRow K)))
  let Sempty := genSemanticSkeleton (bfsAssign (airReorder t))
    ([] : List (NTree (GenMemoryRow K)))
  let KM : Finset K :=
    (({0} : Finset K) ∪ Cempty.census.badSeeds (K := K)) ∪
      sizeWindowFailureSeeds (K := K) Sempty
  let D : Finset K :=
    Finset.univ.filter (fun z : K => ∃ g ∈ bfsRows (airReorder t), ¬ RowSeedGood z g)
  have hrows : (bfsRows (airReorder t)).length = rows := by
    unfold rows
    rw [bfsRows_length, bfsForest_bfsAssign_length]
  have hKMcard : KM.card ≤ seedBudget Λ rows := by
    have h1 : (({0} : Finset K) ∪ Cempty.census.badSeeds (K := K)).card
        ≤ 1 + (3 + 10 * (computeSkeletonRows Sempty).length) * (2 * Λ - 1) := by
      refine (Finset.card_union_le _ _).trans ?_
      have hcen := (Cempty.census.badSeeds_card_le (K := K)).trans
        (Nat.mul_le_mul_right (2 * Λ - 1) Cempty.count_le)
      simpa using Nat.add_le_add_left hcen 1
    have hlen : (computeSkeletonRows Sempty).length = rows := by
      unfold rows
      rw [computeSkeletonRows_length]
    rw [hlen] at h1
    refine (Finset.card_union_le _ _).trans ?_
    exact Nat.add_le_add h1 (sizeWindowFailureSeeds_card_le Sempty Λ hwin)
  have hDcard : D.card ≤ rows * (3 * (2 * Λ - 1)) := by
    have := seedBad_card_le_of_generated hq hle hs hf hG h hΛ hconf
    rwa [hrows] at this
  have hunion : (KM ∪ D).card < Fintype.card K := by
    refine lt_of_le_of_lt ?_ hcard
    refine (Finset.card_union_le KM D).trans ?_
    have : rows * (3 * (2 * Λ - 1)) = 3 * rows * (2 * Λ - 1) := by
      ring
    rw [this] at hDcard
    exact Nat.add_le_add hKMcard hDcard
  obtain ⟨z, hz⟩ := exists_notMem_of_card_lt hunion
  have hzKM : z ∉ KM := fun h => hz (Finset.mem_union_left D h)
  have hzD : z ∉ D := fun h => hz (Finset.mem_union_right KM h)
  have hz01 : z ∉ ({0} : Finset K) ∪ Cempty.census.badSeeds (K := K) :=
    fun h => hzKM (Finset.mem_union_left _ h)
  have hzWin : z ∉ sizeWindowFailureSeeds (K := K) Sempty :=
    fun h => hzKM (Finset.mem_union_right _ h)
  have hz0 : z ≠ 0 :=
    fun h => hz01 (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have hzbad : z ∉ Cempty.census.badSeeds (K := K) :=
    fun h => hz01 (Finset.mem_union_right _ h)
  refine ⟨z, hz0, ?_, ?_, ?_⟩
  · rw [badSeeds_memoryForest_irrelevant
      (genSkeletonP8Census (K := K) hΛ h hconf (genMemoryForest z α lmb (memInputs z) t))
      Cempty]
    exact hzbad
  · rw [sizeWindowFailureSeeds_memoryForest_irrelevant (bfsAssign (airReorder t))
      (genMemoryForest z α lmb (memInputs z) t) ([] : List (NTree (GenMemoryRow K)))]
    exact hzWin
  · exact seedGood_raw_of_airReorder
      (seedGood_airReorder_of_not_mem z t hzD)

theorem exists_vcomp_seed_of_rom {q Λ : ℕ} (hq : 11 < q) (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : 1 ≤ Λ)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) :
    ∃ z : K, z ≠ 0
      ∧ z ∉ (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) hrom) hconf
              (genMemoryForest z α lmb (memInputs z) (romTree (K := K) hrom))).census.badSeeds
      ∧ z ∉ sizeWindowFailureSeeds (K := K)
              (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
                (genMemoryForest z α lmb (memInputs z) (romTree (K := K) hrom)))
      ∧ SeedGood z (romTree (K := K) hrom) :=
  exists_vcomp_seed_of_accepted (Nat.lt_trans (by decide : 1 < 11) hq)
    (le_of_eq hchar) hs hf hG
    (romTree_spec (K := K) hrom) hΛ hconf α hwin hcard

/-- **The joint seed is good at every Form R `λ`.**  The `KM` union reads only the compute tree
(`badSeeds_memoryForest_irrelevant`, `sizeWindowFailureSeeds_memoryForest_irrelevant`, by `rfl`), so
one seed serves every sampled `λ`; the compiler need not, and does not, choose a `λ`.  The
existential is instantiated at `λ := 0` only inside this proof (any value works). -/
theorem exists_vcomp_seed_of_rom_allLambda {q Λ : ℕ} (hq : 11 < q) (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : 1 ≤ Λ)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) :
    ∃ z : K, z ≠ 0
      ∧ (∀ lmb' : K, z ∉ (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) hrom) hconf
              (genMemoryForest z α lmb' (memInputs z) (romTree (K := K) hrom))).census.badSeeds)
      ∧ (∀ lmb' : K, z ∉ sizeWindowFailureSeeds (K := K)
              (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
                (genMemoryForest z α lmb' (memInputs z) (romTree (K := K) hrom))))
      ∧ SeedGood z (romTree (K := K) hrom) := by
  obtain ⟨z, h0, hb, hw, hg⟩ :=
    exists_vcomp_seed_of_rom (lmb := (0 : K)) hq hchar hs hf hG hrom hΛ hconf α hwin hcard
  refine ⟨z, h0, fun lmb' => ?_, fun lmb' => ?_, hg⟩
  · rw [badSeeds_memoryForest_irrelevant _
      (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) hrom) hconf
        (genMemoryForest z α (0 : K) (memInputs z) (romTree (K := K) hrom)))]
    exact hb
  · rw [sizeWindowFailureSeeds_memoryForest_irrelevant _ _
      (genMemoryForest z α (0 : K) (memInputs z) (romTree (K := K) hrom))]
    exact hw

/-! ## 4. The joint compiler seed -/

/-- **The compiler's NPR seed, jointly avoiding the `KM` union and the Dyck-bad set.**
Still `Classical.choose`. -/
def romSeedVcomp {q Λ : ℕ} (hq : 11 < q) (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : 1 ≤ Λ)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) :
    K :=
  (exists_vcomp_seed_of_rom_allLambda hq hchar hs hf hG hrom hΛ hconf α hwin hcard).choose

theorem romSeedVcomp_ne_zero {q Λ : ℕ} (hq : 11 < q) (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : 1 ≤ Λ)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) :
    romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwin hcard ≠ 0 :=
  (exists_vcomp_seed_of_rom_allLambda hq hchar hs hf hG hrom hΛ hconf α hwin hcard).choose_spec.1

theorem romSeedVcomp_notMem_badSeeds {q Λ : ℕ} (hq : 11 < q) (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : 1 ≤ Λ)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) :
    romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwin hcard ∉
      (genSkeletonP8Census (K := K) hΛ (romTree_spec (K := K) hrom) hconf
        (genMemoryForest (romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwin hcard) α lmb
          (memInputs (romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwin hcard))
          (romTree (K := K) hrom))).census.badSeeds :=
  (exists_vcomp_seed_of_rom_allLambda hq hchar hs hf hG hrom hΛ hconf α hwin hcard).choose_spec.2.1 lmb

theorem romSeedVcomp_notMem_sizeWindowFailureSeeds {q Λ : ℕ} (hq : 11 < q)
    (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : 1 ≤ Λ)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) :
    romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwin hcard ∉
      sizeWindowFailureSeeds (K := K)
        (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
          (genMemoryForest (romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwin hcard) α lmb
            (memInputs (romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwin hcard))
            (romTree (K := K) hrom))) :=
  (exists_vcomp_seed_of_rom_allLambda hq hchar hs hf hG hrom hΛ hconf α hwin hcard).choose_spec.2.2.1 lmb

/-- **`hseed` is `choose_spec`.** -/
theorem romSeedVcomp_seedGood {q Λ : ℕ} (hq : 11 < q) (hchar : q = ringChar K)
    {fuel : ℕ} {subject formula result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (hrom : evalRom fuel subject formula = some result)
    (hΛ : 1 ≤ Λ)
    (hconf : TraceConfined Λ (airReorder (romTree (K := K) hrom)))
    (α : K)
    (hwin : SizeWindowNounsBoundedBy
      (genSemanticSkeleton (bfsAssign (airReorder (romTree (K := K) hrom)))
        ([] : List (NTree (GenMemoryRow K)))) Λ)
    (hcard : seedBudgetVcomp Λ
      (bfsForest [bfsAssign (airReorder (romTree (K := K) hrom))]).length
        < Fintype.card K) :
    SeedGood (romSeedVcomp hq hchar hs hf hG hrom hΛ hconf α hwin hcard)
      (romTree (K := K) hrom) :=
  (exists_vcomp_seed_of_rom_allLambda hq hchar hs hf hG hrom hΛ hconf α hwin hcard).choose_spec.2.2.2

end

end Nock.NockVMROM.Thm54.TraceGen.GoodSeed

#print axioms Nock.NockVMROM.Thm54.TraceGen.rowBad_card_le_of_generated
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.exists_vcomp_seed_of_rom
#print axioms Nock.NockVMROM.Thm54.TraceGen.GoodSeed.romSeedVcomp_seedGood
