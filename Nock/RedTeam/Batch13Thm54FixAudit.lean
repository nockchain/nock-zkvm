/-
  Nock/RedTeam/Batch13Thm54FixAudit.lean

  This batch does NOT dispute that the repairs are real as far as they go.  It measures how far
  they go, by compiling the residue.  Each result below is either a countermodel against a claim
  the repair could be read as making, or a machine-checked statement of the remaining cap.

  Paper authority: Theorem 5.4, the paper cost figures the paper.
-/
import Nock.RedTeam.Batch12Thm54Independent

namespace Nock.RedTeam

open Nock Nock.Framework Nock.NockVMROM Nock.Reified

/-! ## F8a residue (i): `SecurityFamily` is a phantom parameter of the asymptotic class

    `HasAsymptoticSoundness (Fam : SecurityFamily) (bad : ℕ → ℝ)` has exactly one field,
    `negligible : Negligible bad`.  `Fam` occurs nowhere in the class body, and `SecurityFamily`
    itself bundles no `Field` instance — it is `FieldAt : ℕ → Type*` and nothing else.  So swapping
    the family from `GF(2^{n+1})` to `GF(13^{n+1})` cannot change any `HasAsymptoticSoundness`
    obligation: the repair makes a standalone lemma true, but the asymptotic clause does not consume
    the family. -/

/-- The family parameter is inert: asymptotic soundness transfers across arbitrary families. -/
theorem b13_asymptotic_family_is_phantom (Fam Fam' : SecurityFamily) (bad : ℕ → ℝ) :
    HasAsymptoticSoundness Fam bad ↔ HasAsymptoticSoundness Fam' bad :=
  ⟨fun h => ⟨h.negligible⟩, fun h => ⟨h.negligible⟩⟩

/-- A degenerate "security family" of one-element types. -/
def b13_trivialFamily : SecurityFamily := ⟨fun _ => Unit⟩

/-- **Countermodel.**  The zero-hypothesis asymptotic witness holds verbatim over the one-element
    family, so the repaired `GF(13^{n+1})` family is not load-bearing in the clause that is supposed
    to be about it.  Tying the two together is the disclosed F8b bridge. -/
theorem b13_zero_hyp_witness_over_trivial_family :
    HasAsymptoticSoundness b13_trivialFamily
      (fun n => ((n : ℝ) + 1) ^ 5 / (13 : ℝ) ^ (n + 1)) :=
  ⟨nockVMROM_asymptotic_zero_hyp⟩

/-! ## F8a residue (ii): the repaired family is AIR-compatible but FIXED-characteristic

    But the
    operational capstone's structural hypotheses are stated in the CHARACTERISTIC `p`, not the
    cardinality:

      `V_NockVMROM_forest`      : `hwrapc : 1 + hc * 3 < p`, `hwrapm : kroots_m + hm * 2 < p`,
                                  `hKp : Ksz < p`
      `fullAIR_entails_forest'` : the same three bounds
      `IO.io_result_LIO`        : `hKp : K < p`

    The family's characteristic is the constant `13` at every security parameter, so those bounds
    are the SAME constants for every `n`.  Cardinality growth `13^(n+1)` does not relax them. -/

/-- The family's field at `n` is `GF(13^{n+1})` definitionally.  (`SecurityFamily` carries no
    `Field` instance, so characteristic facts must be stated on this side of the equation.) -/
theorem b13_familyAt_eq (n : ℕ) :
    nockConcreteSecurityFamily.FieldAt n = GaloisField 13 (n + 1) := rfl

/-- Every field of the repaired concrete family has characteristic `13`. -/
theorem b13_family_char_13 (n : ℕ) : CharP (GaloisField 13 (n + 1)) 13 := inferInstance

/-- There is no escape via a different `p`: the characteristic is unique, so any `CharP` instance
    used to instantiate the capstone's `p`-bounds at a family field is `13`. -/
theorem b13_family_char_unique (n p : ℕ) [hp : CharP (GaloisField 13 (n + 1)) p] : p = 13 :=
  CharP.eq _ hp (b13_family_char_13 n)

/-- **F8a residue (countermodel to a growing-workload reading).**  At every security parameter `n`,
    instantiating the capstone over `𝔽_n` forces `p = 13`, hence a compute walk of at most `3` rows,
    a memory forest of at most `5` aggregate rows (given the real `1 ≤ kroots_m`), and `Ksz ≤ 12`.
    These caps are independent of `n`, so the family cannot carry a workload that grows with the
    security parameter — which is exactly what an asymptotic-soundness bridge (F8b) must do.  A
    varying-prime family is required; a fixed characteristic, including `13`, is insufficient. -/
theorem b13_asymptotic_family_caps_workload :
    (∀ n : ℕ, CharP (GaloisField 13 (n + 1)) 13) ∧
    (∀ hc kroots_m hm Ksz : ℕ,
      1 ≤ kroots_m → 1 + hc * 3 < 13 → kroots_m + hm * 2 < 13 → Ksz < 13 →
      hc ≤ 3 ∧ hm ≤ 5 ∧ Ksz ≤ 12) := by
  refine ⟨b13_family_char_13, ?_⟩
  intro hc kroots_m hm Ksz hk h1 h2 h3
  exact ⟨by omega, by omega, by omega⟩

/-! ## F9 controls after the exact-cost cutover -/

@[reducible] noncomputable def b13_bundle_cost_slot_unchanged (F K : Type) [Field F] [Field K]
    [Algebra F K]
    [Fintype K] [DecidableEq K] (α β : K) (Ksz : ℕ) [NeZero Ksz] :
    VerifiableVMCompilation (Tag F K α β Ksz) (nmrMEF F K) K 10 3
      (Nock.NockVMROM.Thm54.ProductionP8Containment.ExactProductionFixedFieldSoundness F K)
      (Nock.NockVMROM.Thm54.ProductionP8Containment.exactProductionFixedFieldSoundness F K)
      (Nock.NockVMROM.Thm54.ExactSegmentedCostVerification F K)
      (Nock.NockVMROM.Thm54.exactSegmentedCostVerification F K)
      (Nock.NockVMROM.Thm54.ExactChainedHasPerfectCompleteness F K)
      (Nock.NockVMROM.Thm54.exactChainedHasPerfectCompleteness F K)
      (Nock.NockVMROM.Thm54.ExactTwoRAPVerification F K)
      (Nock.NockVMROM.Thm54.exactTwoRAPVerification F K)
      (nock_uniqueMES F K α β Ksz)
      (Nock.NockVMROM.Thm54.ExactChainedHasCanonicalRAP2 F K)
      (Nock.NockVMROM.Thm54.exactChainedHasCanonicalRAP2 F K)
      (Nock.NockVMROM.Thm54.ExactChainedOneHot F K)
      (Nock.NockVMROM.Thm54.exactChainedOneHot F K)
      (Nock.NockVMROM.Thm54.ExactDefTraversable F K)
      (Nock.NockVMROM.Thm54.exactDefTraversable F K)
      (nock_languageInhabited F K α β Ksz) :=
  NockVMROM_Thm54_structural F K α β Ksz

/-- **The rejecting VM inhabits the NEW parametric class too.**  `HasParamCostModel` is `ι`-agnostic
    exactly as `HasCostModel` was, so the parametric refinement does not by itself defeat
    `b12_s8_reject_vm_costed`.  (The repair discloses this; here it is compiled.) -/
@[reducible] def b13_reject_vm_param_costed :
    HasParamCostModel B12RejectVM reifiedNockParamCost where
  compMaxDeg_le := by decide
  memMaxDeg_le := by decide
  mem_deg4_lt_comp := by intro e _; show 0 * e + 2 < 0 * e + 13; omega

theorem b13_legacy_cost_models_do_not_fill_exact_slot :
    Nock.NockVMROM.Thm54.ExactSegmentedCostVerification (ZMod 7) (ZMod 7) := by
  fail_if_success exact b12_s8_reject_vm_costed
  fail_if_success exact b13_reject_vm_param_costed
  exact Nock.NockVMROM.Thm54.exactSegmentedCostVerification (ZMod 7) (ZMod 7)

/-- A decoy parametric cost whose 𝕂/𝔽 split is entirely different from the documented
    `⟨80,14⟩`/`⟨20,15⟩` derivation: every count is placed on the `e`-coefficient side. -/
def b13_decoyParamCost : ParamCostModel :=
  { compCols := ⟨94, 0⟩, compDeg4 := ⟨13, 0⟩,     memCols := ⟨36, 0⟩, memDeg4 := ⟨2, 0⟩,
    compIOCols := ⟨94, 0⟩, compIODeg4 := ⟨13, 0⟩, memIOCols := ⟨36, 0⟩, memIODeg4 := ⟨2, 0⟩,
    compMaxDeg := 4, memMaxDeg := 4 }

/-- **F9(b) residue (countermodel).**  `reifiedNockParamCost_faithful` evaluates only at `e = 1`,
    where `AffineE.eval ⟨a,b⟩ 1 = a + b`.  It therefore pins the SUM `coeffE + const` and says
    nothing about the split.  The decoy above satisfies the identical faithfulness statement, so
    the AIR reference does not certify the `e`-parametric structure that is the point of the
    refinement — the 𝕂/𝔽 attribution remains a docstring claim. -/
theorem b13_decoy_split_passes_faithfulness {K : Type*} [Field K] :
    b13_decoyParamCost.compCols.eval 1 = computeAIR.numTraceCols ∧
    b13_decoyParamCost.compDeg4.eval 1 = computeAIR.constraints.countP (fun c => c.degree == 4) ∧
    b13_decoyParamCost.memCols.eval 1 = (memoryAIR (K := K)).numTraceCols ∧
    b13_decoyParamCost.memDeg4.eval 1 =
      (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 4) :=
  ⟨computeAIR_numTraceCols.symm, computeAIR_deg4.symm,
   memoryAIR_numTraceCols.symm, memoryAIR_deg4.symm⟩

/-- The decoy and the shipped model genuinely differ as `e`-parametric objects: they agree at
    `e = 1` (the only point faithfulness tests) and disagree everywhere else. -/
theorem b13_decoy_differs_off_one :
    b13_decoyParamCost.compCols.eval 1 = reifiedNockParamCost.compCols.eval 1 ∧
    b13_decoyParamCost.compCols.eval 2 ≠ reifiedNockParamCost.compCols.eval 2 :=
  ⟨by decide, by decide⟩

/-! ## F4 residue: the relabel is accurate, and the countermodel still stands

    Recorded here as a
    dependency so a future edit that silently re-strengthens the S4 label breaks this batch. -/
theorem b13_s4_countermodel_still_stands :
    ∃ (ps : (nock_uniqueMES ℚ ℚ 0 1 1).ProgStatement)
      (pw : (nock_uniqueMES ℚ ℚ 0 1 1).ProgWitness)
      (io : (nock_uniqueMES ℚ ℚ 0 1 1).ProgIO),
      (nock_uniqueMES ℚ ℚ 0 1 1).computeAccepts ps pw io ∧
      ∀ lbl : (nock_traversalModel ℚ ℚ 0 1 1).ComputeLabel,
        ((nock_isTraversable ℚ ℚ 0 1 1).computeReadout lbl).1 ≠ ps :=
  b12_s4_accepted_not_in_readout


#print axioms b13_asymptotic_family_is_phantom
#print axioms b13_zero_hyp_witness_over_trivial_family
#print axioms b13_familyAt_eq
#print axioms b13_family_char_13
#print axioms b13_family_char_unique
#print axioms b13_asymptotic_family_caps_workload
#print axioms b13_bundle_cost_slot_unchanged
#print axioms b13_reject_vm_param_costed
#print axioms b13_legacy_cost_models_do_not_fill_exact_slot
#print axioms b13_decoy_split_passes_faithfulness
#print axioms b13_decoy_differs_off_one
#print axioms b13_s4_countermodel_still_stands

end Nock.RedTeam
