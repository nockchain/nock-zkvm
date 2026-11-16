/-
  Nock/RedTeam/Batch601Thm54PreseedAtomMemoryGate.lean

  What is checked here, symbol by symbol against the resume note:
  * **Column.** One `𝔽` column `atom`, physical index `180` (`atomCol`), appended to the memory
    source chip (`expandChipTail … 1`) inside its single (round-0) commitment: the memory chip has
    `k = 1`, so `wRAP 0 = 181` is the whole source and the column is committed with the selectors,
    before any coin is read (`atom_column_in_round_zero`).
  * **Gates.** `sel_halt · (leaf_k − coord b 1 k · atom)`, `k = 0,1,2` (`MemoryHaltAtomDecode.haltAtomGateCoord_eq`);
    at a basis with `coord b 1 = (1,0,0)` (`FormRBasis`; `compilerBasis_formR`) these are exactly
    `sel_halt·(leaf₀ − atom)`, `sel_halt·leaf₁`, `sel_halt·leaf₂` (`gate_bodies_at_formR`,
    `gate_bodies_at_compilerBasis`); degree `2` each (`gate_degree_two`); `sel_halt` is base
    column `1` (`MState.toIdx.halt = 1`), `leaf_k` are physical `12, 13, 14` (role `2`).
  * **Honest fill.** Generated `halt` rows are atoms and their honest `atom` is `(a : F)`
    (`TraceGen.honestAtomOf_op9HaltPub`, `honest_halt_gate`, `genMemForestFromTree_halt_leaf_base`).
  * **Decode.** On every accepted trace a decoded `halt` row's leaf is the lifted atom column
    (`MemoryHaltAtomDecode.decodeMemPub_halt_leaf_eq_atom`); at `𝔽 = ZMod p` the decoded noun is
    `Noun.atom atom.val` (`decodeNoun_halt_eq_atom_zmod`).
  * **Negative control at the deployed gate.**
-/
import Nock.NockVMROM.Thm54.MemoryHaltAtomDecode
import Nock.NockVMROM.Thm54.TraceGen.GenMemAtomFill
import Nock.NockVMROM.Thm54.TraceGen.GenNockCompilesCarrier
import Nock.RedTeam.Batch579Thm54PreseedAtomGates
import Mathlib.FieldTheory.Finite.GaloisField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch601

open Nock
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.Thm54Resources
attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Gate bodies -/

section Bodies

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem gate_bodies_at_formR (b : Module.Basis (Fin 3) F K)
    (hb : OptimizedComputeFinalTrace.FormRBasis b) (env : Env F) :
    (haltAtomGateCoord b 0).eval env = env.trace 1 * (env.trace 12 - env.trace 180) ∧
      (haltAtomGateCoord b 1).eval env = env.trace 1 * env.trace 13 ∧
      (haltAtomGateCoord b 2).eval env = env.trace 1 * env.trace 14 :=
  MemoryHaltAtomDecode.haltAtomGateCoord_formR b hb.1 hb.2.1 hb.2.2 env

theorem gate_degree_two (b : Module.Basis (Fin 3) F K) (k : Fin 3) :
    (haltAtomGateCoord b k).degree = 2 := by
  rw [MemoryHaltAtomDecode.haltAtomGateCoord_eq]
  rfl

/-- The three coordinate gates are members of the committed memory gate list (`allGates`). -/
theorem gates_committed (b : Module.Basis (Fin 3) F K) (k : Fin 3) :
    haltAtomGateCoord b k ∈ (memorySourceTemplate b).allGates b := by
  have hmix : haltAtomMixed (F := F) ∈ (memorySourceTemplate b).mixedTransition := by
    simp [memorySourceTemplate, mixedTransitionGates]
  have hmem : haltAtomGateCoord b k ∈
      MixedCoordinateCompiler.mixedExpandList b ((memorySourceTemplate b).col0 3)
        (memorySourceTemplate b).mixedTransition :=
    (MixedCoordinateCompiler.mem_mixedExpandList b _ _ _).mpr ⟨_, hmix, k, rfl⟩
  simp only [ChipTemplate.allGates, ChipTemplate.transitionGates, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr hmem)))

/-- The gate's semantics: on a `halt` row (selector `1`) the leaf is the lifted atom. -/
theorem gate_semantics (eK : Env K) (eF : Env F) (hsel : eF.trace 1 = 1) :
    (haltAtomMixed (F := F)).eval eK eF = 0 ↔ eK.trace 2 = algebraMap F K (eF.trace 180) := by
  rw [haltAtomMixed_eval, hsel, map_one, one_mul, sub_eq_zero]

/-- **Negative control at the deployed gate**: a `halt` row whose leaf is not a lifted base value
fails the gate whatever the prover writes in the `atom` column. -/
theorem forged_leaf_fails_gate (eK : Env K) (eF : Env F) (hsel : eF.trace 1 = 1)
    (hleaf : ∀ a : F, eK.trace 2 ≠ algebraMap F K a) :
    (haltAtomMixed (F := F)).eval eK eF ≠ 0 := by
  rw [Ne, gate_semantics eK eF hsel]
  exact hleaf _

end Bodies

theorem gate_bodies_at_compilerBasis {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] (hK : Module.finrank F K = 3) (env : Env F) :
    (haltAtomGateCoord (TraceGen.compilerBasis (F := F) (K := K) hK) 0).eval env =
        env.trace 1 * (env.trace 12 - env.trace 180) ∧
      (haltAtomGateCoord (TraceGen.compilerBasis (F := F) (K := K) hK) 1).eval env =
        env.trace 1 * env.trace 13 ∧
      (haltAtomGateCoord (TraceGen.compilerBasis (F := F) (K := K) hK) 2).eval env =
        env.trace 1 * env.trace 14 :=
  gate_bodies_at_formR _ (TraceGen.compilerBasis_formR hK) env

/-! ## Numerals and round -/

theorem numerals :
    memoryColumns deployedExtensionDegree = 205 ∧
      memoryConstraints deployedExtensionDegree = 156 ∧
      memoryTransitionGates deployedExtensionDegree = 156 ∧
      computeColumns deployedExtensionDegree = 303 ∧
      computeConstraints deployedExtensionDegree = 418 :=
  ⟨memoryColumns_deployed, memoryConstraints_deployed, memoryTransitionGates_deployed,
    computeColumns_deployed, computeConstraints_deployed⟩

section Chip

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem source_and_final_fingerprints {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Module.Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) (kMem : ℕ) :
    (sourceMemoryRAP b chalVal pubVal orbit (rowNodeSet nodes)).w = 182 ∧
      (sourceMemoryRAP b chalVal pubVal orbit (rowNodeSet nodes)).s = 156 ∧
      (namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.w = 205 ∧
      (namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.s = 156 ∧
      (namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.d = 4 ∧
      (namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.k = 1 :=
  ⟨(sourceMemoryRAP_fingerprint b chalVal pubVal orbit _).1,
    (sourceMemoryRAP_fingerprint b chalVal pubVal orbit _).2.1,
    finalMemoryRAP_fingerprint hn nodes b chalVal pubVal orbit kMem⟩

/-- **The `atom` column is round 0.** -/
theorem atom_column_in_round_zero {h : ℕ} (b : Module.Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) (H : Finset F) :
    (sourceMemoryRAP b chalVal pubVal orbit H).k = 1 ∧
      (sourceMemoryRAP b chalVal pubVal orbit H).wRAP
        ⟨0, (memorySourceTemplate b).rounds_pos⟩ = 182 ∧
      atomCol < 182 ∧ haltSel (F := F) = CoordinateCompiler.CoeffExpr.var .traceCur 1 := by
  refine ⟨rfl, ?_, by decide, rfl⟩
  simp [sourceMemoryRAP, expandChipTail, ChipTemplate.roundWidthTail, ChipTemplate.roundWidth,
    memorySourceTemplate]

end Chip


theorem forged_root_seeds_le_two {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] (atom : F) (x : K) (h2 : (2 : K) ≠ 0) :
    (Finset.univ.filter fun z : K =>
      z ≠ 0 ∧ Batch579.fixedLeafFormula z (algebraMap F K atom) =
        Batch578.publicFormula z x).card ≤ 2 :=
  Batch579.fixed_leaf_collisions_card_le_two x (algebraMap F K atom) h2

theorem batch578_leaf_base_seeds_card_le {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [Fintype K] [DecidableEq K] (x0 : F) (h2 : (2 : K) ≠ 0) :
    (Finset.univ.filter fun z : K =>
      ∃ a : F, Batch578.forgedLeaf z (algebraMap F K x0) = algebraMap F K a).card ≤
      2 * Fintype.card F := by
  classical
  -- `x + 2 w² = a` with `w = z⁻¹`: `w ∈ nthRoots 2 ((a − x)/2)`, so `z = w⁻¹`.
  let roots : F → Finset K := fun a =>
    ((Polynomial.nthRoots 2 ((algebraMap F K a - algebraMap F K x0) / 2)).toFinset).image
      (fun w => w⁻¹)
  have hsub : (Finset.univ.filter fun z : K =>
      ∃ a : F, Batch578.forgedLeaf z (algebraMap F K x0) = algebraMap F K a) ⊆
      Finset.univ.biUnion roots := by
    intro z hz
    obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hz).2
    refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, ?_⟩
    refine Finset.mem_image.mpr ⟨z⁻¹, ?_, inv_inv z⟩
    refine Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots (by decide)).mpr ?_)
    unfold Batch578.forgedLeaf at ha
    rw [eq_div_iff h2]
    linear_combination ha
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le).trans ?_
  have hroots : ∀ a : F, (roots a).card ≤ 2 := fun a =>
    Finset.card_image_le.trans
      ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 2 _))
  calc ∑ a, (roots a).card ≤ ∑ _a : F, 2 := Finset.sum_le_sum fun a _ => hroots a
    _ = 2 * Fintype.card F := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

theorem batch578_leaf_rejected_31 :
    ∃ z : Batch578.K31, ∀ a : Batch578.F31,
      Batch578.forgedLeaf z (algebraMap Batch578.F31 Batch578.K31 1) ≠
        algebraMap Batch578.F31 Batch578.K31 a := by
  classical
  letI : Fintype Batch578.K31 := Fintype.ofFinite _
  by_contra hall
  push Not at hall
  have h2 : (2 : Batch578.K31) ≠ 0 := by
    have h : (2 : Batch578.K31) = algebraMap Batch578.F31 Batch578.K31 2 :=
      (map_ofNat (algebraMap Batch578.F31 Batch578.K31) 2).symm
    rw [h]
    exact (map_ne_zero_iff _ (algebraMap Batch578.F31 Batch578.K31).injective).mpr (by decide)
  have hfull : (Finset.univ.filter fun z : Batch578.K31 =>
      ∃ a : Batch578.F31, Batch578.forgedLeaf z (algebraMap Batch578.F31 Batch578.K31 1) =
        algebraMap Batch578.F31 Batch578.K31 a) = Finset.univ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact hall z
  have hle := batch578_leaf_base_seeds_card_le (F := Batch578.F31) (K := Batch578.K31) 1 h2
  rw [hfull, Finset.card_univ] at hle
  have hK : Fintype.card Batch578.K31 = 31 ^ 3 := by
    rw [@Module.card_eq_pow_finrank (K := Batch578.F31) (V := Batch578.K31), ZMod.card,
      GaloisField.finrank 31 (by norm_num : (3 : ℕ) ≠ 0)]
  rw [hK, ZMod.card] at hle
  norm_num at hle

end

end Nock.RedTeam.Batch601

#print axioms Nock.RedTeam.Batch601.gate_bodies_at_formR
#print axioms Nock.RedTeam.Batch601.gate_bodies_at_compilerBasis
#print axioms Nock.RedTeam.Batch601.gate_degree_two
#print axioms Nock.RedTeam.Batch601.gates_committed
#print axioms Nock.RedTeam.Batch601.forged_leaf_fails_gate
#print axioms Nock.RedTeam.Batch601.numerals
#print axioms Nock.RedTeam.Batch601.source_and_final_fingerprints
#print axioms Nock.RedTeam.Batch601.atom_column_in_round_zero
#print axioms Nock.RedTeam.Batch601.forged_root_seeds_le_two
#print axioms Nock.RedTeam.Batch601.batch578_leaf_base_seeds_card_le
#print axioms Nock.RedTeam.Batch601.batch578_leaf_rejected_31
#print axioms Nock.NockVMROM.Thm54.MemoryHaltAtomDecode.decodeMemPub_halt_leaf_eq_atom
#print axioms Nock.NockVMROM.Thm54.MemoryHaltAtomDecode.decodeNoun_halt_eq_atom
#print axioms Nock.NockVMROM.Thm54.MemoryHaltAtomDecode.decodeNoun_halt_eq_atom_zmod
#print axioms Nock.NockVMROM.Thm54.TraceGen.honest_halt_gate
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_haltAtomMixed
