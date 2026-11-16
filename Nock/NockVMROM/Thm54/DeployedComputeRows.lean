import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
import Nock.NockVMROM.Thm54.P8Core.DeployedComputeRows
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# Deployed compute rows are Nock steps (fingerprint `V_comp`)

From `RAP.SatisfiesWithPreprocessing P.computeChip Qc`
and the chip's SV gates:

1. `deployed_row_one_hot` — the eleven selector columns are the one-hot of a state,
   **from the gates** (`selector_gates_at` / `rowSelector_oneHot` /
   `ComputePaperPacking.oneHot_of_svBaseGates`).  Needs the characteristic hypothesis
   `StateTagChar` already on the package (`freeSelectorChar_of_stateTagChar`; fails
   in characteristics `2,3,5,7`).
2. `deployed_row_vcomp` — the row decodes to a `V_comp` triple via `paperPackingRowLocal_eval_zero` +
   `paperPacking_iff_atomic` + `computeAIR_sound` + `equiv_compute_sound`.
   `z ≠ 0` is the F-E-3 coin pin (`zZinv_at_rowEnv`): the chip no longer commits
   `z · z⁻¹ = 1`.

3. `deployed_row_operational_core` is **not stated**.  `SkeletonOperationalCore`
   (`BoundSemanticTrace.lean`) reads the *nouns* `s.subject`, `s.evaluation`,
   `s.memoryRecord`, and `P8Census.skeletonSubformula`, plus
   `GlobalCarryAxis.ServedLookup` at those nouns.  A deployed row carries
   fingerprints, not nouns.

Paper: the paper (SV2/SV3), `:1726-1742` (`V_comp`), `:1697-1699`
(`Lem:equiv_compute`).
-/

namespace Nock.NockVMROM.Thm54
namespace DeployedComputeRows

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.ComputeTable
open Nock.Framework
open Nock.Framework.Reify
open OptimizedStrictFullPackage
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open OptimizedComputeGateBasis
open OptimizedComputeSubstitution
open OptimizedComputeSemanticRealization
open OptimizedComputeCorrectedFinal
open ComputePaperPacking
open Module

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

variable (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

variable (Qc : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
include hsat

/-- The selector columns of every accepted row are the one-hot of a
state, proved from the committed SV gates. -/
theorem deployed_row_one_hot (i : Fin (rows P)) :
    ∃ st : State, OneHotSelector (rowEnv P Qc i).toSourceEnv st := by
  obtain ⟨s, hs⟩ := source_selector P Qc hsat (pkgHchar P) i
  refine ⟨s, fun t => ?_⟩
  simpa [OneHotSelector, opSel] using hs t

/-- Packed row-local gates vanish on every accepted row. -/
theorem packed_rowLocal_zero (i : Fin (rows P)) :
    ∀ g ∈ ComputePaperPacking.paperPackingRowLocal,
      g.eval (rowEnv P Qc i).toSourceEnv = 0 :=
  paperPackingRowLocal_eval_zero (row_obligations P Qc hsat i)

/-- The 66 packed classes vanish (subset of the row-local list). -/
theorem packedTable_zero (i : Fin (rows P)) :
    ∀ g ∈ ComputePaperPacking.packedTableOptimized,
      g.eval (rowEnv P Qc i).toSourceEnv = 0 :=
  fun g hg => packed_rowLocal_zero P Qc hsat i g (List.mem_append.mpr (Or.inl hg))

/-- Always-on prefix (SV4–SV6 + formula cons) vanishes on every accepted row. -/
theorem alwaysOn_zero (i : Fin (rows P)) :
    ∀ g ∈ ComputePaperPacking.alwaysOnOptimized,
      g.eval (rowEnv P Qc i).toSourceEnv = 0 :=
  fun g hg => packed_rowLocal_zero P Qc hsat i g (alwaysOn_mem_rowLocal hg)

variable (hz0 : P.optimized.family.problem.cfg.challenges.z ≠ 0)
include hz0

/-- Every accepted compute row is a `V_comp` step at the fingerprints
the row decodes to. -/
theorem deployed_row_vcomp (i : Fin (rows P)) :
    VcompAt (rowEnv P Qc i) := by
  obtain ⟨st, hone⟩ := deployed_row_one_hot P Qc hsat i
  refine ⟨st, hone, ?_⟩
  set env := (rowEnv P Qc i).toSourceEnv
  set E := decodeSource (rowEnv P Qc i)
  have hz : (zZinvExpr.subst computeSubst).eval env = 0 :=
    zZinv_at_rowEnv P Qc i hz0
  have hpk := packedTable_zero P Qc hsat i
  have hsrc := row_obligations P Qc hsat i
  have hatomic :=
    (paperPacking_iff_atomic env st hone hz).1 hpk
  have hrefold : ∀ e ∈ refoldedPerStateGates, e.eval env = 0 := by
    intro e he
    have hsb : e ∈ stateBlocks := by
      simpa [stateBlocks_eq_refolded] using he
    simp only [stateBlocks, List.mem_flatten, List.mem_map] at hsb
    obtain ⟨_, ⟨s, -, rfl⟩, he'⟩ := hsb
    exact hatomic s e he'
  have hgated : ∀ e ∈ perStateGated, e.eval E = 0 :=
    (refolded_iff_perStateGated env st hone).1 hrefold
  have hsvBase := svBaseGates_of_oneHot (env := env) (st := st) hone
  have hon := alwaysOn_zero P Qc hsat i
  have hsubst_id_sv : ∀ e ∈ svBaseGates, e.subst computeSubst = e := by
    intro e he
    simp only [svBaseGates, svBoolExprs, List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨t, -, rfl⟩ | rfl
    · cases t <;> rfl
    · rfl
  have hsvE : ∀ e ∈ svExprs, e.eval E = 0 := by
    intro e he
    simp only [svExprs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with hbool | rfl | rfl | rfl | rfl
    · have hmem : e ∈ svBaseGates := List.mem_append.mpr (Or.inl hbool)
      rw [show e.eval E = (e.subst computeSubst).eval env from
        (Expr.eval_subst computeSubst e env).symm, hsubst_id_sv e hmem]
      exact hsvBase e hmem
    · have hmem : svOneHotExprF ∈ svBaseGates := by simp [svBaseGates]
      rw [show svOneHotExprF.eval E = (svOneHotExprF.subst computeSubst).eval env from
        (Expr.eval_subst computeSubst svOneHotExprF env).symm, hsubst_id_sv _ hmem]
      exact hsvBase _ hmem
    · have hmem : sv4Expr.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
        simp [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized]
      exact (Expr.eval_subst computeSubst sv4Expr env).symm.trans (hon _ hmem)
    · have hmem : sv5Expr.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
        simp [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized]
      exact (Expr.eval_subst computeSubst sv5Expr env).symm.trans (hon _ hmem)
    · have hmem : sv6Expr.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
        simp [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized]
      exact (Expr.eval_subst computeSubst sv6Expr env).symm.trans (hon _ hmem)
  have hformE : ∀ e ∈ formulaExprs, e.eval E = 0 := by
    intro e he
    have hmem : e.subst computeSubst ∈ ComputePaperPacking.alwaysOnOptimized := by
      simp only [ComputePaperPacking.alwaysOnOptimized, OptimizedComputeGateBasis.alwaysOnOptimized,
        List.mem_append, List.mem_cons, List.mem_map]
      exact Or.inr ⟨e, he, rfl⟩
    exact (Expr.eval_subst computeSubst e env).symm.trans (hon _ hmem)
  have hmr1E : ∀ e ∈ mr1Exprs, e.eval E = 0 := by
    intro e he
    exact (Expr.eval_subst computeSubst e env).symm.trans (mr1Exprs_subst_vanish env e he)
  have hzE : zZinvExpr.eval E = 0 :=
    (Expr.eval_subst computeSubst zZinvExpr env).symm.trans hz
  have hallE : ∀ c ∈ computeAIR.constraints, c.expr.eval E = 0 := by
    intro c hc
    have hc' : c ∈
        (svExprs.map (fun e => ⟨.row, e⟩) ++
          formulaExprs.map (fun e => ⟨.row, e⟩) ++
          mr1Exprs.map (fun e => ⟨.row, e⟩) ++
          [⟨.row, zZinvExpr⟩] ++
          perStateGated.map (fun e => ⟨.row, e⟩)) := hc
    rcases List.mem_append.mp hc' with hL | hD
    · rcases List.mem_append.mp hL with hL2 | hzmem
      · rcases List.mem_append.mp hL2 with hL3 | hC
        · rcases List.mem_append.mp hL3 with hA | hB
          · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hA; exact hsvE e he
          · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hB; exact hformE e he
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hC; exact hmr1E e he
      · simp only [List.mem_singleton] at hzmem; subst c; exact hzE
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hD; exact hgated e he
  have hz93 : E.trace 93 = (E.chal 1)⁻¹ := trace93_eq_inv_of_zZinv E hzE
  have hop : opOf E = opSel st := by
    funext t
    have honeE : OneHotSelector E st := oneHot_ofSubst env st hone
    simpa [opOf, opSel] using honeE t
  have hre' : ∀ c ∈ computeAIR.constraints,
      c.expr.eval (computeEnvFull (inpOf E) (opSel (pubOfState E st).state)
        (pubOfState E st) (decOf E) (exOf E)) = 0 := by
    intro c hc
    have hkind : c.kind = .row := by
      have := List.all_eq_true.mp computeAIR_all_row c hc
      simpa [beq_iff_eq] using this
    have hchained : c ∈ Trans.computeAIRchained.constraints :=
      List.mem_append.mpr (Or.inl hc)
    have hagree := row_constraint_eval_agree E st hz93 c hchained hkind
    have hopub : opSel (pubOfState E st).state = opOf E := by
      simpa [pubOfState] using hop.symm
    rw [hopub, ← hagree]
    exact hallE c hc
  have hrap :=
    (computeAIR_sound (inp := inpOf E) (pub := pubOfState E st)
      (dec := decOf E) (ex := exOf E)).mp hre'
  exact equiv_compute_sound _ _ _ ⟨decodeEx (rowEnv P Qc i), hrap.1⟩

end DeployedComputeRows
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.DeployedComputeRows.deployed_row_one_hot
#print axioms Nock.NockVMROM.Thm54.DeployedComputeRows.deployed_row_vcomp
