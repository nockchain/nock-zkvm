/-
  Nock/RedTeam/Batch700Thm54PreSeedCensus.lean

  **Lane `h1-3-census`: receipts for the pre-`z` census and the fixed-pair event.**

  * **(1) Step 3, positive controls at the deployed memory view** (any chip parameters):
    the size column `6` (and `7, 8`, leaf `12..14`) may read `z`; selectors `0..5`, `atom` `180`
    and `reqIdx` `181` may not.  A set reading size column `6` FAILS `PreZReads`
    (`size_set_not_preZReads`); a set reading only the `halt` selector and `atom` PASSES
    (`haltAtom_set_preZReads`).
  * **(2) Step 4**: the census and the pre-`z` nouns read only pre-`z` columns; on an accepted
    trace the decoder's `halt` atoms are census entries and every decoded node is pre-`z`.
  * **(3) Step 6 receipt, `Batch610` is priced**: the adaptive base-atom four-leaf collision lies
    INSIDE the pair event (`batch610_collision_in_pairBadSeeds`), and at production
    (`batch610_inside_pairEvent`): wherever a decoded node and its target are that pair, every
    tuple with that `z` is in `pairEvent`.  So the forgery is priced at `2Λ − 1` per pair for a
    pre-`z` pair, not excluded.
  * **(4) Step 6 receipt, the honest trace lies outside**: decoded = target ⇒ the event is empty
    (`honest_outside`), at every package and trace with the decoded forest as target.
  * **(5) The guard is load-bearing**: the same collision at window `Λ = 3 < 4` leaves is NOT
    priced (`guard_excludes_out_of_window`), so the conjunct's window premise is needed.
  * **(6) Step 7 figures** restated with axioms.
-/
import Nock.NockVMROM.Thm54.PreSeedCensus
import Nock.NockVMROM.Thm54.PreSeedCensusFigures
import Nock.RedTeam.Batch610Thm54PreseedFreshForgeries
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch700

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.Reified
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedStaging
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.PreSeedCensus

noncomputable section

/-! ## `PreZReads` positive controls at the deployed memory view -/

section Controls

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Module.Basis (Fin 3) F K)
  (chalVal pubVal : ℕ → F) (orbit : StrictExtension.StrictOrbitDomain F 3 h) (kMem : ℕ)

/-- Size / leaf `𝕂` columns may read `z`; selectors, `atom`, `reqIdx` may not. -/
theorem column_reads_z :
    (∀ c ∈ ([6, 7, 8, 12, 13, 14] : List ℕ), ∀ hc : c < 205,
      zIdx ∈ (deployedMemoryView hn nodes b chalVal pubVal orbit kMem).columnChallenges
        ⟨c, hc⟩) ∧
    (∀ c ∈ ([0, 1, 2, 3, 4, 5, 180, 181] : List ℕ), ∀ hc : c < 205,
      zIdx ∉ (deployedMemoryView hn nodes b chalVal pubVal orbit kMem).columnChallenges
        ⟨c, hc⟩) := by
  refine ⟨?_, ?_⟩
  · intro c hc hlt
    have hr : memoryColRound c ≠ 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    by_contra hz
    exact hr ((memView_preZ_iff hn nodes b chalVal pubVal orbit kMem ⟨c, hlt⟩).1 hz)
  · intro c hc hlt
    have hr : memoryColRound c = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (memView_preZ_iff hn nodes b chalVal pubVal orbit kMem ⟨c, hlt⟩).2 hr

/-- The set of traces whose size column `6` vanishes. -/
def sizeSet : Set (Fin 205 → F[X]) := {Q | Q ⟨6, by decide⟩ = 0}

/-- The set of traces on which `sel_halt · atom = 0` (reads columns `1` and `180` only). -/
def haltAtomSet : Set (Fin 205 → F[X]) := {Q | Q ⟨1, by decide⟩ * Q ⟨180, by decide⟩ = 0}

/-- **Positive control (fail)**: a set reading size column `6` is not `PreZReads`. -/
theorem size_set_not_preZReads :
    ¬ PreZReads (deployedMemoryView hn nodes b chalVal pubVal orbit kMem) (sizeSet (F := F)) := by
  refine not_preZReads_of_witness _ _ (fun _ => 0)
    (fun c => if (c : ℕ) = 6 then 1 else 0) ?_ rfl ?_
  · intro c hc
    have hne : (c : ℕ) ≠ 6 := by
      intro h6
      apply hc
      have hc' : c = ⟨6, (by norm_num : (6 : ℕ) < 205)⟩ := Fin.ext h6
      rw [hc']
      exact (column_reads_z hn nodes b chalVal pubVal orbit kMem).1 6 (by simp) _
    simp only [hne, if_false]
  · intro h
    have h1 : (if (6 : ℕ) = 6 then (1 : F[X]) else 0) = 0 := h
    simp at h1

/-- **Positive control (pass)**: a set reading only the `halt` selector and `atom` is
`PreZReads`. -/
theorem haltAtom_set_preZReads :
    PreZReads (deployedMemoryView hn nodes b chalVal pubVal orbit kMem) (haltAtomSet (F := F)) := by
  refine preZReads_of_readsOnly _
    {⟨1, (by norm_num : (1 : ℕ) < 205)⟩, ⟨180, (by norm_num : (180 : ℕ) < 205)⟩} ?_ _ ?_
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact (column_reads_z hn nodes b chalVal pubVal orbit kMem).2 1 (by simp) _
    · exact (column_reads_z hn nodes b chalVal pubVal orbit kMem).2 180 (by simp) _
  · intro Q Q' hQ
    have h1 := hQ ⟨1, (by norm_num : (1 : ℕ) < 205)⟩ (by simp)
    have h2 := hQ ⟨180, (by norm_num : (180 : ℕ) < 205)⟩ (by simp)
    show Q _ * Q _ = 0 ↔ Q' _ * Q' _ = 0
    erw [h1, h2]
    exact Iff.rfl

end Controls

/-! ## The census and the bridge, restated -/

section Census

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem census_pre_z (q : ℕ) : PreZReadsFnOn (memCC P) (preSeedCensus P q) :=
  preSeedCensus_preZReads P q

theorem nouns_pre_z (q : ℕ) : PreZReadsFnOn (memCC P) (preZNouns P q) :=
  preZNouns_preZReads P q

theorem event_pre_z (q Λ : ℕ) (tgt : ℕ → Noun) :
    PreZReadsFnOn (memCC P) (fun Qm => pairEvent (K := K) P q Λ Qm tgt) :=
  pairEvent_preZReads P q Λ tgt

theorem decoded_is_pre_z (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) (q i : ℕ) :
    HostileSkeletonDecoding.decodeNoun q
        (buildTF P.optimized.family.problem.cfg.kMem (ExecOfTraces.foM P (FamilyMemoryRows.honestQm P c Qm) c)
          (ExecOfTraces.lblM P (FamilyMemoryRows.honestQm P c Qm) c)
          P.optimized.family.problem.cfg.memRows i) =
      preZNoun P q (FamilyMemoryRows.honestQm P c Qm) i :=
  accepted_decode_eq_preZNoun P c Qm hsat q i


/-- Generic: a field-distinct pair colliding at `z` and within the window is priced. -/
theorem nest4_leaves (a : Fin 4 → ℕ) : (Batch610.nest4 a).leaves = 4 := by
  simp [Batch610.nest4, Batch578.nest4, Noun.leaves]

theorem nest4_leafList (a : Fin 4 → ℕ) :
    (Batch610.nest4 a).leafList = [a 0, a 1, a 2, a 3] := by
  simp [Batch610.nest4, Batch578.nest4, Noun.leafList]

theorem batch610_inside_pairEvent (q Λ : ℕ) (hΛ : 4 ≤ Λ) (Qm : Fin P.memoryChip.rap.w → F[X])
    (tgt : ℕ → Noun) {i : ℕ} (hi : i ∈ List.range' 1 P.optimized.family.problem.cfg.memRows)
    (z : K) (a b' : Fin 4 → ℕ) (ha : ∀ j, a j < ringChar K) (hb : ∀ j, b' j < ringChar K)
    (hne : Batch610.nest4 a ≠ Batch610.nest4 b')
    (henc : GlobalCarryRecognizer.enc z (Batch610.nest4 a) =
      GlobalCarryRecognizer.enc z (Batch610.nest4 b'))
    (hd : preZNoun P q Qm i = Batch610.nest4 a) (ht : tgt i = Batch610.nest4 b')
    (c : OptimizedProductionChallengeTuple K F) (hc : nprSeed c.1 = z) :
    c ∈ pairEvent P q Λ Qm tgt := by
  have hmem : (Batch610.nest4 a, Batch610.nest4 b') ∈ zipPairs P q Qm tgt := by
    rw [← hd, ← ht]
    exact List.mem_map.2 ⟨i, hi, rfl⟩
  have hdist : (NPR.leafF (K := K) (Batch610.nest4 a), NPR.dyckBits (K := K) (Batch610.nest4 a))
      ≠ (NPR.leafF (K := K) (Batch610.nest4 b'), NPR.dyckBits (K := K) (Batch610.nest4 b')) := by
    intro hfe
    apply hne
    refine noun_eq_of_fieldNoun_eq ?_ ?_ hfe
    · intro k hk
      rw [nest4_leafList] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact ha _
    · intro k hk
      rw [nest4_leafList] at hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact hb _
  have hz : z ∈ pairBadSeeds (K := K) Λ (zipPairs P q Qm tgt) :=
    mem_pairBadSeeds_of_collision hmem (by rw [nest4_leaves]; exact hΛ)
      (by rw [nest4_leaves]; exact hΛ) hdist
      (GlobalCarryRecognizer.enc_eq_imp_fn_eq z _ _ henc)
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hc ▸ hz⟩

/-! ## (4) The honest trace lies outside -/

/-- With the decoded forest as its own target (what an honest trace's binding gives), the event
is empty: every tuple is outside it. -/
theorem honest_outside (q Λ : ℕ) (Qm : Fin P.memoryChip.rap.w → F[X]) :
    pairEvent (K := K) P q Λ Qm (preZNoun P q Qm) = ∅ :=
  pairEvent_eq_empty_of_decoded_eq P q Λ Qm _ (fun _ _ => rfl)

end Census

theorem batch610_collision_in_pairBadSeeds {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Fintype K] [DecidableEq K] [Algebra (ZMod p) K]
    (hK : Module.finrank (ZMod p) K = 3) (z : K) (hz : z ≠ 0) {Λ : ℕ} (hΛ : 4 ≤ Λ) :
    ∃ a b : Fin 4 → ℕ, Batch610.nest4 a ≠ Batch610.nest4 b ∧
      z ∈ pairBadSeeds (K := K) Λ [(Batch610.nest4 a, Batch610.nest4 b)] := by
  obtain ⟨a, b, ha, hb, hne, henc, -, -⟩ := Batch610.adaptive_base_leaf_collision hK z hz
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hchar : ringChar K = p := ringChar.eq K p
  refine ⟨a, b, hne, mem_pairBadSeeds_of_collision (by simp) (by rw [nest4_leaves]; exact hΛ)
    (by rw [nest4_leaves]; exact hΛ) ?_ (GlobalCarryRecognizer.enc_eq_imp_fn_eq z _ _ henc)⟩
  intro hfe
  apply hne
  refine noun_eq_of_fieldNoun_eq ?_ ?_ hfe
  · intro k hk
    rw [nest4_leafList] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rw [hchar]
    rcases hk with rfl | rfl | rfl | rfl <;> exact ha _
  · intro k hk
    rw [nest4_leafList] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rw [hchar]
    rcases hk with rfl | rfl | rfl | rfl <;> exact hb _

/-! ## (5) The guard is load-bearing -/

theorem guard_excludes_out_of_window {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (z : K) (a b : Fin 4 → ℕ) :
    z ∉ pairBadSeeds (K := K) 3 [(Batch610.nest4 a, Batch610.nest4 b)] := by
  rw [mem_pairBadSeeds_iff]
  rintro ⟨p, hp, h1, -, -⟩
  simp only [List.mem_singleton] at hp
  subst hp
  rw [nest4_leaves] at h1
  omega

/-! ## Figures -/

open Nock.NockVMROM.Thm54.PreSeedCensusFigures in
theorem figures :
    (∀ R M Λ A p8Work : ℕ, R ≤ 2 ^ 31 → M ≤ 2 ^ 31 → Λ ≤ 2 ^ 31 → A ≤ 2 ^ 31 →
      p8Work ≤ RealProgramSoundness.p8Majorant R M Λ A + M * (3 * R + 130) →
      GoldilocksParameters.goldilocksHostileFailureBound p8Work
          (FiniteIO.ioFailureUnionBound 10 (3 * R) M (Fintype.card Nock.Field.K)) R M
        + (pairWork M Λ : ℚ) / (GoldilocksParameters.cardKGold : ℚ) < 1 / (2 : ℚ) ^ 122) ∧
    (1 / (2 : ℚ) ^ 98 <
      (allPairWork (2 ^ 31) (2 ^ 31) : ℚ) / (GoldilocksParameters.cardKGold : ℚ)) :=
  ⟨fun R M Λ A p8Work hR hM hΛ hA hp8 =>
    hostile_soundness_formR_pair_at_two_pow_31 R M Λ A p8Work hR hM hΛ hA hp8,
   allPairs_floor_at_two_pow_31⟩

end

end Nock.RedTeam.Batch700

#print axioms Nock.RedTeam.Batch700.size_set_not_preZReads
#print axioms Nock.RedTeam.Batch700.haltAtom_set_preZReads
#print axioms Nock.RedTeam.Batch700.census_pre_z
#print axioms Nock.RedTeam.Batch700.decoded_is_pre_z
#print axioms Nock.RedTeam.Batch700.batch610_inside_pairEvent
#print axioms Nock.RedTeam.Batch700.batch610_collision_in_pairBadSeeds
#print axioms Nock.RedTeam.Batch700.honest_outside
#print axioms Nock.RedTeam.Batch700.guard_excludes_out_of_window
#print axioms Nock.RedTeam.Batch700.figures
#print axioms Nock.NockVMROM.Thm54.PreSeedCensus.accepted_outside_pairEvent_decoded_eq
#print axioms Nock.NockVMROM.Thm54.PreSeedCensus.pairEvent_card_le
#print axioms Nock.NockVMROM.Thm54.PreSeedCensus.pairEvent_adaptive_eq
#print axioms Nock.NockVMROM.Thm54.PreSeedCensus.failure_union_pairEvent_card_le
#print axioms Nock.NockVMROM.Thm54.PreSeedCensusFigures.hostile_soundness_formR_pair_at_two_pow_32
#print axioms Nock.NockVMROM.Thm54.PreSeedCensusFigures.hostile_soundness_at_paper_configuration_pair
#print axioms Nock.NockVMROM.Thm54.PreSeedCensusFigures.hostile_soundness_formR_allPairs_at_two_pow_31
#print axioms Nock.NockVMROM.Thm54.PreSeedCensusFigures.hostile_soundness_formR_allPairs_at_two_pow_32
#print axioms Nock.NockVMROM.Thm54.PreSeedCensusFigures.allPairs_floor_at_two_pow_32
