import Nock.NockVMROM.Thm54.VclL.Compute.TowerAssembled
import Nock.NockVMROM.Thm54.VclL.Compute.TowerSummandsQ7
import Nock.NockVMROM.Thm54.TraceGen.GenSeedVcomp
import Nock.NockVMROM.Thm54.TraceGen.GenCoinCounting
import Nock.NockVMROM.Thm54.P8Core.SVFrame.JointSummands

/-!

Three priced summands over `frameVCL` for the honest tower strategy (completeness only):

* (a) **SeedGood**: the tower seed `z′ = (χ2, χ3)` lies in `badSeedsT t = {0} ∪ {z | ∃ row, ¬ RowSeedGood z row}`;
  coins `{2,3}`, weight `1 + R · 3(2Λ − 1)` (`seedBad_card_le_of_generated` at `𝕂′`).
* (b) **rlc5**: for some OP5 row with unequal results, `χ8 Δs + χ9 Δd + χ10 Δℓ = 0` in `𝕂′` (the coins embedded);
  coins `{8,9,10}`, read set `{2,3}` (the fingerprints depend on `z′` only: `renderNode` rlc5-data is `α`-free),
  weight `nR · |𝕂|²`.
* (c) **χ0 order**: `χ0 = 0` or `χ0^d = 1` for some `0 < d < h` (C2b's `hord`); coin `{0}`, read set `∅`,
  weight `h²` (`1 ≤ h`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace TowerD

open Nock Nock.Walk Nock.Reified Module Polynomial
open Nock.NockVMROM.Thm54.T0Tower
open Nock.NockVMROM.Thm54.SVFrame Nock.Framework
open Nock.NockVMROM.Thm54.TraceGen Nock.TableWFBounds
open Nock.ComputeTable (State Pub)
open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP (seedSpecVCL)
open Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## 0. A three-coin cylinder -/

section Triple
variable {Φ : CoinFrame} {K : Type} [Fintype K] [DecidableEq K] {Tr : Type}
  {Staged : (Coins Φ K → Tr) → Prop}

/-- **A three-coin cylinder**: coins `i j k` land in a bad set of triples that reads only the coins `D`. -/
def tripleSummand (i j k : Fin Φ.n) (D : Finset (Fin Φ.n)) (hD : Disjoint ({i, j, k} : Finset (Fin Φ.n)) D)
    (bad : Tr → Coins Φ K → Finset (K × K × K)) (w : ℕ) (hw : ∀ tr χ, (bad tr χ).card ≤ w)
    (hr : ∀ Q : Coins Φ K → Tr, Staged Q → ReadsOnC Φ D (fun χ => bad (Q χ) χ)) :
    BadSummand Φ K Tr Staged where
  coins := {i, j, k}
  dep := D
  disj := hD
  badSet tr χ := Finset.univ.filter fun f : ({i, j, k} : Finset (Fin Φ.n)) → K =>
    (f ⟨i, by simp⟩, f ⟨j, by simp⟩, f ⟨k, by simp⟩) ∈ bad tr χ
  weight := w
  card_le tr χ := by
    refine le_trans (Finset.card_le_card_of_injOn
      (fun f : ({i, j, k} : Finset (Fin Φ.n)) → K => (f ⟨i, by simp⟩, f ⟨j, by simp⟩, f ⟨k, by simp⟩)) ?_ ?_)
      (hw tr χ)
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
      exact hf
    · intro f _ f' _ h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg (fun p => p.2.1) h
      have h3 := congrArg (fun p => p.2.2) h
      simp only at h1 h2 h3
      funext ⟨x, hx⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
  readsOn Q hQ χ χ' h := by
    have e := hr Q hQ χ χ' h
    simp only at e ⊢
    rw [e]

theorem tripleSummand_mem (i j k : Fin Φ.n) (D : Finset (Fin Φ.n))
    (hD : Disjoint ({i, j, k} : Finset (Fin Φ.n)) D)
    (bad : Tr → Coins Φ K → Finset (K × K × K)) (w : ℕ) (hw : ∀ tr χ, (bad tr χ).card ≤ w)
    (hr : ∀ Q : Coins Φ K → Tr, Staged Q → ReadsOnC Φ D (fun χ => bad (Q χ) χ))
    (tr : Tr) (χ : Coins Φ K) :
    (tripleSummand i j k D hD bad w hw hr (Staged := Staged)).mem tr χ ↔ (χ i, χ j, χ k) ∈ bad tr χ := by
  unfold BadSummand.mem
  show (fun x : ({i, j, k} : Finset (Fin Φ.n)) => χ x) ∈ Finset.univ.filter _ ↔ _
  rw [Finset.mem_filter]
  simp

end Triple

/-! ## 1. (a) SeedGood -/

section Seed
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

open Classical in
/-- **The bad seeds of the generated tree at `𝕂′`**: `0` and every seed failing `RowSeedGood` at some BFS row. -/
def badSeedsT (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) : Finset (Quad (algebraMap F K δ)) :=
  insert 0 (Finset.univ.filter fun z => ∃ g ∈ bfsRows (airReorder t), ¬ RowSeedGood z g)

/-- **The `SeedGood` weight**: `1 + R · 3(2Λ − 1)`. -/
def seedWeightT (R Λ : ℕ) : ℕ := 1 + R * (3 * (2 * Λ - 1))

/-- **The count** (`seedBad_card_le_of_generated` at `𝕂′`, plus the zero seed). -/
theorem badSeedsT_card_le
    {q Λ : ℕ} (hq : 1 < q) (hle : q ≤ ringChar (Quad (algebraMap F K δ)))
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow (Quad (algebraMap F K δ)))} {result : Noun}
    (hs : FieldEmbedding.BoundedBy q subject)
    (hf : FieldEmbedding.BoundedBy q formula)
    (hG : FieldEmbedding.evalGBy q fuel subject formula = some result)
    (h : genComputeSkeleton (K := Quad (algebraMap F K δ)) fuel subject formula = .ok (t, result))
    (hΛ : 1 ≤ Λ) (hconf : TraceConfined Λ (airReorder t)) :
    (badSeedsT δ t).card ≤ seedWeightT (bfsRows (airReorder t)).length Λ := by
  classical
  have h1 := seedBad_card_le_of_generated (K := Quad (algebraMap F K δ)) hq hle hs hf hG h hΛ hconf
  unfold badSeedsT seedWeightT
  refine (Finset.card_insert_le _ _).trans ?_
  have : (Finset.univ.filter fun z : Quad (algebraMap F K δ) => ∃ g ∈ bfsRows (airReorder t), ¬ RowSeedGood z g).card
      ≤ (bfsRows (airReorder t)).length * (3 * (2 * Λ - 1)) := h1
  omega

/-- **The SeedGood summand**: coins `{2, 3}`, read set `∅`, weight `w ≥ |badSeedsT t|`. -/
def sumSeedGoodT (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (w : ℕ)
    (hw : (badSeedsT δ t).card ≤ w) : TSummand F K hC S :=
  seedSummand (F := F) (C := tableVCLT hC) (S := S) (seedSpecVCL (algebraMap F K δ))
    (fun _ => badSeedsT δ t) w (fun _ => hw)

theorem sumSeedGoodT_mem (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (w : ℕ)
    (hw : (badSeedsT δ t).card ≤ w) (tr : Traces F (tableVCLT hC) S) (χ : Coins frameVCL K) :
    (sumSeedGoodT (hC := hC) (S := S) δ t w hw).mem tr χ ↔ zQuad δ χ ∈ badSeedsT δ t :=
  seedSummand_mem (F := F) (C := tableVCLT hC) (S := S) (seedSpecVCL (algebraMap F K δ))
    (fun _ => badSeedsT δ t) w (fun _ => hw) tr χ

/-- **Decode (a)**: outside the summand, `z′ ≠ 0` and `SeedGood z′ t`. -/
theorem seedGood_of_not_mem (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (χ : Coins frameVCL K)
    (h : zQuad δ χ ∉ badSeedsT δ t) : zQuad δ χ ≠ 0 ∧ SeedGood (zQuad δ χ) t := by
  classical
  refine ⟨fun h0 => h (by rw [h0]; exact Finset.mem_insert_self _ _), ?_⟩
  exact seedGood_raw_of_airReorder
    (seedGood_airReorder_of_not_mem _ t (fun hm => h (Finset.mem_insert_of_mem hm)))

end Seed

/-! ## 2. (b) rlc5 -/

section Rlc5

open Classical in
/-- **The mixed kernel bound**: `(a, b, c) ∈ 𝕂³` with `ι a · d₁ + ι b · d₂ + ι c · d₃ = 0` in `𝕂′`, for a nonzero
`(d₁, d₂, d₃) ∈ 𝕂′³`, number at most `|𝕂|²` (two `𝕂`-linear conditions; one coin is determined by the other two). -/
theorem mixedKernel_card_le {K K' : Type} [Field K] [Fintype K] [Field K'] [Algebra K K']
    (d1 d2 d3 : K') (h : d1 ≠ 0 ∨ d2 ≠ 0 ∨ d3 ≠ 0) :
    (Finset.univ.filter fun p : K × K × K =>
        algebraMap K K' p.1 * d1 + algebraMap K K' p.2.1 * d2 + algebraMap K K' p.2.2 * d3 = 0).card
      ≤ Fintype.card K * Fintype.card K := by
  have hinj : Function.Injective (algebraMap K K') := (algebraMap K K').injective
  rcases h with h | h | h
  · refine le_trans (Finset.card_le_card_of_injOn (t := (Finset.univ : Finset (K × K)))
      (fun p : K × K × K => (p.2.1, p.2.2)) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_)
      (by simp [Finset.card_univ, Fintype.card_prod])
    intro p hp p' hp' hpp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp hp'
    have h2 : p.2.1 = p'.2.1 := congrArg Prod.fst hpp
    have h3 : p.2.2 = p'.2.2 := congrArg Prod.snd hpp
    have : algebraMap K K' p.1 * d1 = algebraMap K K' p'.1 * d1 := by
      rw [h2, h3] at hp
      linear_combination hp - hp'
    have := hinj (mul_right_cancel₀ h this)
    exact Prod.ext this (Prod.ext h2 h3)
  · refine le_trans (Finset.card_le_card_of_injOn (t := (Finset.univ : Finset (K × K)))
      (fun p : K × K × K => (p.1, p.2.2)) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_)
      (by simp [Finset.card_univ, Fintype.card_prod])
    intro p hp p' hp' hpp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp hp'
    have h1 : p.1 = p'.1 := (Prod.mk.inj hpp).1
    have h3 : p.2.2 = p'.2.2 := (Prod.mk.inj hpp).2
    have : algebraMap K K' p.2.1 * d2 = algebraMap K K' p'.2.1 * d2 := by
      rw [h1, h3] at hp
      linear_combination hp - hp'
    have := hinj (mul_right_cancel₀ h this)
    exact Prod.ext h1 (Prod.ext this h3)
  · refine le_trans (Finset.card_le_card_of_injOn (t := (Finset.univ : Finset (K × K)))
      (fun p : K × K × K => (p.1, p.2.1)) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_)
      (by simp [Finset.card_univ, Fintype.card_prod])
    intro p hp p' hp' hpp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp hp'
    have h1 : p.1 = p'.1 := (Prod.mk.inj hpp).1
    have h2 : p.2.1 = p'.2.1 := (Prod.mk.inj hpp).2
    have : algebraMap K K' p.2.2 * d3 = algebraMap K K' p'.2.2 * d3 := by
      rw [h1, h2] at hp
      linear_combination hp - hp'
    have := hinj (mul_right_cancel₀ h this)
    exact Prod.ext h1 (Prod.ext h2 this)

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] {hC : ℕ} {S : MemShape}
  (δ : F) [Fact (¬ IsSquare (algebraMap F K δ))]

/-- The rlc5-relevant rows of the AIR-ordered generated tree at seed `z` (the rendered `Pub`s; the timestamp base
is irrelevant to the rlc5 data, `rlc5Holds_renderNode_alpha`, so `0` is used). -/
def rlc5PubAt (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (z : Quad (algebraMap F K δ))
    (j : Fin (bfsForest [airReorder t]).length) : Pub (Quad (algebraMap F K δ)) :=
  treeComputePub z 0 (airReorder t) j

open Classical in
/-- **The rlc5 bad triples**: `(a, b, c) ∈ 𝕂³` with `ι a Δs + ι b Δd + ι c Δℓ = 0` at some live OP5 row with unequal
results. -/
def rlc5Bad (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (z : Quad (algebraMap F K δ)) :
    Finset (K × K × K) :=
  Finset.univ.filter fun p => ∃ j : Fin (bfsForest [airReorder t]).length,
    needsRlc5 (rlc5PubAt δ t z j) ∧
      rlc5Form (algebraMap K (Quad (algebraMap F K δ)) p.1) (algebraMap K _ p.2.1) (algebraMap K _ p.2.2)
        (rlc5PubAt δ t z j) = 0

/-- **The rlc5 count**: `≤ nR · |𝕂|²`. -/
theorem rlc5Bad_card_le (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (z : Quad (algebraMap F K δ)) :
    (rlc5Bad δ t z).card ≤ (bfsForest [airReorder t]).length * (Fintype.card K * Fintype.card K) := by
  classical
  have hsub : rlc5Bad δ t z ⊆ Finset.univ.biUnion fun j : Fin (bfsForest [airReorder t]).length =>
      Finset.univ.filter fun p : K × K × K => needsRlc5 (rlc5PubAt δ t z j) ∧
        rlc5Form (algebraMap K (Quad (algebraMap F K δ)) p.1) (algebraMap K _ p.2.1) (algebraMap K _ p.2.2)
          (rlc5PubAt δ t z j) = 0 := by
    intro p hp
    simp only [rlc5Bad, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact hp
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have hj : ∀ j : Fin (bfsForest [airReorder t]).length,
      (Finset.univ.filter fun p : K × K × K => needsRlc5 (rlc5PubAt δ t z j) ∧
        rlc5Form (algebraMap K (Quad (algebraMap F K δ)) p.1) (algebraMap K _ p.2.1) (algebraMap K _ p.2.2)
          (rlc5PubAt δ t z j) = 0).card ≤ Fintype.card K * Fintype.card K := by
    intro j
    by_cases hn : needsRlc5 (rlc5PubAt δ t z j)
    · have hδ := deltas_ne_zero_of_needsRlc5 hn
      refine le_trans (le_of_eq (congrArg Finset.card ?_)) (mixedKernel_card_le (K := K) _ _ _ hδ)
      ext p
      simp [hn, rlc5Form]
      convert Iff.rfl
      erw [Finset.mem_filter]; simp
    · have : (Finset.univ.filter fun p : K × K × K => needsRlc5 (rlc5PubAt δ t z j) ∧
          rlc5Form (algebraMap K (Quad (algebraMap F K δ)) p.1) (algebraMap K _ p.2.1) (algebraMap K _ p.2.2)
            (rlc5PubAt δ t z j) = 0) = ∅ := by
        ext p; simp [hn]
      rw [this]; simp
  calc ∑ j : Fin (bfsForest [airReorder t]).length, _ ≤
      ∑ _j : Fin (bfsForest [airReorder t]).length, Fintype.card K * Fintype.card K :=
        Finset.sum_le_sum fun j _ => hj j
    _ = _ := by simp

/-- **`rlc5Holds` is `α`-free**: it reads only the state and the `sf1_e` / `sf2_e` fingerprints. -/
theorem rlc5Holds_renderNode_alpha {L : Type} [Field L] (a b c z α : L) (g : GenComputeRow L) :
    rlc5Holds a b c (renderNode z α g).row.2.2.1 ↔ rlc5Holds a b c (renderNode z 0 g).row.2.2.1 := by
  by_cases h : g.skel.state = State.s5
  · have e1 : (renderNode z α g).row.2.2.1.sf1_e = (renderNode z 0 g).row.2.2.1.sf1_e := by
      unfold renderNode; rw [h]; rfl
    have e2 : (renderNode z α g).row.2.2.1.sf2_e = (renderNode z 0 g).row.2.2.1.sf2_e := by
      unfold renderNode; rw [h]; rfl
    have e3 : (renderNode z α g).row.2.2.1.state = (renderNode z 0 g).row.2.2.1.state := by
      rw [renderNode_pub_state, renderNode_pub_state]
    unfold rlc5Holds needsRlc5 rlc5Form deltaSize deltaDyck deltaLeaf
    rw [e1, e2, e3]
  · have n1 := rlc5Holds_of_ne_s5 a b c (renderNode z α g).row.2.2.1 (by rwa [renderNode_pub_state])
    have n2 := rlc5Holds_of_ne_s5 a b c (renderNode z 0 g).row.2.2.1 (by rwa [renderNode_pub_state])
    exact ⟨fun _ => n2, fun _ => n1⟩

/-- The read set `{2, 3}` of the rlc5 summand. -/
def depSeedT : Finset (Fin frameVCL.n) := {⟨2, by decide⟩, ⟨3, by decide⟩}

theorem disj_depSeedT : Disjoint ({⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩} : Finset (Fin frameVCL.n))
    depSeedT := by decide

/-- **The rlc5 summand**: coins `{8, 9, 10}`, read set `{2, 3}` (the seed), weight `w ≥ nR · |𝕂|²`. -/
def sumRlc5T (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (w : ℕ)
    (hw : (bfsForest [airReorder t]).length * (Fintype.card K * Fintype.card K) ≤ w) : TSummand F K hC S :=
  tripleSummand (Staged := TracesStaged frameVCL (tableVCLT hC) S)
    ⟨8, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩
    depSeedT disj_depSeedT
    (fun _ χ => rlc5Bad δ t (zQuad δ χ)) w (fun _ χ => (rlc5Bad_card_le δ t _).trans hw)
    (fun _ _ χ χ' h => by
      have h2 := h ⟨2, by decide⟩ (by simp [depSeedT])
      have h3 := h ⟨3, by decide⟩ (by simp [depSeedT])
      show rlc5Bad δ t (zQuad δ χ) = rlc5Bad δ t (zQuad δ χ')
      simp only [zQuad, h2, h3])

theorem sumRlc5T_mem (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (w : ℕ)
    (hw : (bfsForest [airReorder t]).length * (Fintype.card K * Fintype.card K) ≤ w)
    (tr : Traces F (tableVCLT hC) S) (χ : Coins frameVCL K) :
    (sumRlc5T (hC := hC) (S := S) δ t w hw).mem tr χ ↔
      (χ ⟨8, by decide⟩, χ ⟨9, by decide⟩, χ ⟨10, by decide⟩) ∈ rlc5Bad δ t (zQuad δ χ) := by
  unfold sumRlc5T
  exact tripleSummand_mem _ _ _ _ _ _ _ _ _ tr χ

/-- **Decode (b)**: outside the summand, `rlc5Holds` at the embedded coins `(χ8, χ9, χ10)` holds at every generated
BFS row, at any timestamp base `αs` (the form `gen_vcomp_wf` consumes). -/
theorem rlc5_of_not_mem (t : NTree (GenComputeRow (Quad (algebraMap F K δ)))) (χ : Coins frameVCL K)
    (h : (χ ⟨8, by decide⟩, χ ⟨9, by decide⟩, χ ⟨10, by decide⟩) ∉ rlc5Bad δ t (zQuad δ χ))
    (αs : Quad (algebraMap F K δ)) {i : ℕ} (hi : i ∈ List.range' 1 (bfsForest [airReorder t]).length) :
    rlc5Holds (algebraMap K (Quad (algebraMap F K δ)) (χ ⟨8, by decide⟩)) (algebraMap K _ (χ ⟨9, by decide⟩))
      (algebraMap K _ (χ ⟨10, by decide⟩))
      (renderNode (zQuad δ χ) αs (bfsLabelAt (airReorder t) i)).row.2.2.1 := by
  classical
  rw [rlc5Holds_renderNode_alpha]
  obtain ⟨h1, h2⟩ := List.mem_range'_1.mp hi
  have hlt : i - 1 < (bfsForest [airReorder t]).length := by omega
  have hi' : i - 1 + 1 = i := by omega
  intro hn hf
  apply h
  simp only [rlc5Bad, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨i - 1, hlt⟩, ?_, ?_⟩
  · simpa [rlc5PubAt, treeComputePub, hi'] using hn
  · simpa [rlc5PubAt, treeComputePub, hi', rlc5Form] using hf

end Rlc5

/-! ## 3. (c) the `χ0` order -/

section Ord
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [DecidableEq F]
  [Fintype K] [DecidableEq K] {hC : ℕ} {S : MemShape}

open Classical in
/-- **The low-order `χ0`**: `0`, or a root of unity of order `< h`. -/
def ordBad (h : ℕ) : Finset K :=
  insert 0 (Finset.univ.filter fun x : K => ∃ d, 0 < d ∧ d < h ∧ x ^ d = 1)

theorem ordBad_card_le (h : ℕ) (hh : 1 ≤ h) : (ordBad (K := K) h).card ≤ h * h := by
  classical
  have hsub : (Finset.univ.filter fun x : K => ∃ d, 0 < d ∧ d < h ∧ x ^ d = 1) ⊆
      (Finset.range h).biUnion fun d => (Polynomial.nthRootsFinset d (1 : K)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨d, hd0, hdh, hxd⟩ := hx
    simp only [Finset.mem_biUnion, Finset.mem_range]
    exact ⟨d, hdh, (Polynomial.mem_nthRootsFinset hd0 1).2 hxd⟩
  have hcard : ∀ d ∈ Finset.range h, (Polynomial.nthRootsFinset d (1 : K)).card ≤ d :=
    fun d _ => by
      rw [Polynomial.nthRootsFinset_def]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots d 1)
  have h1 := (Finset.card_le_card hsub).trans
    ((Finset.card_biUnion_le).trans (Finset.sum_le_sum hcard))
  refine (Finset.card_insert_le _ _).trans ?_
  have hS := Finset.sum_range_id_mul_two h
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hS
  nlinarith [h1, hS]

/-- **The `χ0`-order summand**: coin `0`, read set `∅`, weight `h²`. -/
def sumOrdT (h : ℕ) (hh : 1 ≤ h) : TSummand F K hC S :=
  coinSummand ⟨0, by decide⟩ ∅ (by simp) (fun _ _ => ordBad (K := K) h) (h * h)
    (fun _ _ => ordBad_card_le h hh) (fun _ _ _ _ _ => rfl)

theorem sumOrdT_mem (h : ℕ) (hh : 1 ≤ h) (tr : Traces F (tableVCLT hC) S) (χ : Coins frameVCL K) :
    (sumOrdT (hC := hC) (S := S) h hh).mem tr χ ↔ χ ⟨0, by decide⟩ ∈ ordBad (K := K) h :=
  coinSummand_mem _ _ _ _ _ _ _ tr χ

/-- **Decode (c)**: outside the summand, `h ≤ orderOf (ι χ0)` in any extension `𝕂′` (`hord` of C2b / C1g). -/
theorem hord_of_not_mem {K' : Type} [Field K'] [Algebra K K'] (h : ℕ) (x : K) (hx : x ∉ ordBad (K := K) h) :
    h ≤ orderOf (algebraMap K K' x) := by
  classical
  rw [show orderOf (algebraMap K K' x) = orderOf x from
    orderOf_injective (algebraMap K K').toMonoidHom (algebraMap K K').injective x]
  have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0]; exact Finset.mem_insert_self _ _)
  have hq : 0 < Fintype.card K - 1 := by
    have := Fintype.one_lt_card (α := K); omega
  have hpos : 0 < orderOf x :=
    (isOfFinOrder_iff_pow_eq_one.2 ⟨Fintype.card K - 1, hq, FiniteField.pow_card_sub_one_eq_one x hx0⟩).orderOf_pos
  by_contra hlt
  simp only [not_le] at hlt
  exact hx (Finset.mem_insert_of_mem (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨orderOf x, hpos, hlt, pow_orderOf_eq_one x⟩))

end Ord

end

end TowerD
end VclL.Compute
end Nock.NockVMROM.Thm54
