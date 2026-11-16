import Nock.NockVMROM.Thm54.VclL.Compute.CompChipVCL
import Nock.NockVMROM.Thm54.VclL.Compute.SummandsQ7

/-!
# CF-A : the tree is ρ-free; the root label; `node_records` / `root_binds` at the CF chip

.

The frame's `tree : V → Msg0 → Q → Coins → NTree` takes no `ρ`, while the CF chip's publics carry
`ρ 1`, `ρ 2` at limbs `42..47` (`pubCF`).  Row labels read the environment only through
`toSourceEnv`, whose `pub` is `extensionPublic i` (limbs `< 9`) and `scalarPublic` (limbs `20..41`):
so `treeV` at `pubCF` is `treeV` at `pubVQ7` (`treeV_pub_irrel`).
-/

namespace Nock.NockVMROM.Thm54
namespace VclL.Compute
namespace CompTreeVCL

open Nock Nock.Walk Nock.Reified Nock.Framework Nock.Framework.Reify Module Nock.ComputeTable
open Nock.NockVMROM.Thm54.SVFrame
open Nock.NockVMROM.Thm54.SVWalk
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.VclL.Compute.CompChipVCL
open Nock.NockVMROM.Thm54.VclL.Compute.WalkQ7
open Nock.NockVMROM.Thm54.VclL.Compute.CoreQ7
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.VclL.Compute.TopoQ7 (lnPatch_pub_sfe)
open scoped Polynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 300000

noncomputable section

section pubirrel
variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [Fintype F] [DecidableEq F] {hC : ℕ} {S : MemShape}

theorem pubCF_lt (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K)
    (j : ℕ) (hj : j < 42) : pubCF V x ρ χ j = pubVQ7 V.basis V.claim x χ j := by
  unfold pubCF
  rw [dif_neg (by unfold rhoExportPub; omega), dif_neg (by unfold rhoPathPub; omega)]

theorem toSourceEnv_envsP_pub (V : VerifierData F K hC S) (c p p' : ℕ → F) (Q : Fin 232 → F[X])
    (i : Fin V.N) (hp : ∀ j < 42, p j = p' j) :
    (envsP V c p Q i).toSourceEnv = (envsP V c p' Q i).toSourceEnv := by
  unfold envsP envsV
  simp only [CorrectedFinalTypedEnv.toSourceEnv, lnPatch, gatherCorrectedFinalTypedEnv, pullEnv,
    envOfTrace]
  congr 1
  funext n
  split_ifs with h1 h2
  · exact Finset.sum_congr rfl fun k _ => by
      have := k.isLt
      rw [hp _ (by omega)]
  · rw [hp _ (by omega)]
  · rfl

theorem treeV_pub_irrel (V : VerifierData F K hC S) (c p p' : ℕ → F) (Q : Fin 232 → F[X])
    (hp : ∀ j < 42, p j = p' j) : treeV V c p Q = treeV V c p' Q := by
  have hl : ∀ i, rowLabel (envsP V c p Q i) = rowLabel (envsP V c p' Q i) := by
    intro i
    simp only [rowLabel, StrategyOfTracesLift.decodeSource, StrategyOfTracesLift.decodeInputs,
      StrategyOfTracesLift.decodePub, StrategyOfTracesLift.decodeDec,
      toSourceEnv_envsP_pub V c p p' Q i hp]
  have hc : ∀ i, rowCarrier (envsP V c p Q i) = rowCarrier (envsP V c p' Q i) := fun i => rfl
  simp only [treeV, treeV1, computeTree, hl, hc]

/-- The tree of the CF chip's publics is the tree at the ρ-free publics. -/
theorem treeV_pubCF (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K)
    (Q : Fin 232 → F[X]) :
    treeV V (chalVQ7 V.basis χ) (pubCF V x ρ χ) Q =
      treeV V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim x χ) Q :=
  treeV_pub_irrel V _ _ _ Q (fun j hj => pubCF_lt V x ρ χ j hj)

theorem label_mapNTree {A B : Type} (f : A → B) (t : NTree A) : (mapNTree f t).label = f t.label := by
  cases t; simp [mapNTree]

/-- **The root label of `treeV` is row `0`'s** (carrier doubled). -/
theorem treeV_label_root (V : VerifierData F K hC S) (c p : ℕ → F) (Q : Fin 232 → F[X]) :
    (treeV V c p Q).label = (rowLabel (envsP V c p Q ⟨0, V.hN⟩),
      2 * rowCarrier (envsP V c p Q ⟨0, V.hN⟩)) := by
  unfold treeV treeV1 computeTree treeOfRows reconTree
  rw [label_mapNTree, buildT_label]
  simp only [at1]
  rw [dif_pos (show 1 - 1 < V.N from by have := V.hN; omega), dif_pos (show 1 - 1 < V.N from by have := V.hN; omega),
    dif_pos (show 1 - 1 < V.N from by have := V.hN; omega)]

/-! ## 2. `node_records` at the CF chip -/

theorem slotK_congr (b : Basis (Fin 3) F K) (p p' : ℕ → F) (q : ℕ) (hq : 3 * q + 2 < 42)
    (hp : ∀ j < 42, p j = p' j) : slotK b p q = slotK b p' q := by
  unfold slotK
  exact Finset.sum_congr rfl fun k _ => by
    have := k.isLt
    rw [hp _ (by omega)]

/-- The frame coin facts at the CF chip's publics. -/
theorem coins_pubCF (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K) :
    alphaQ (cdOfG V (chalVQ7 V.basis χ) (pubCF V x ρ χ)) (chalVQ7 V.basis χ) = χ ⟨0, by decide⟩ ∧
      gammaQ (cdOfG V (chalVQ7 V.basis χ) (pubCF V x ρ χ)) (chalVQ7 V.basis χ) = χ ⟨1, by decide⟩ ∧
      zQ (cdOfG V (chalVQ7 V.basis χ) (pubCF V x ρ χ)) (chalVQ7 V.basis χ) = χ ⟨2, by decide⟩ ∧
      slotK V.basis (chalVQ7 V.basis χ) 5 = (χ ⟨2, by decide⟩)⁻¹ ∧
      initQ (cdOfG V (chalVQ7 V.basis χ) (pubCF V x ρ χ)) (pubCF V x ρ χ) = χ ⟨0, by decide⟩ ∧
      seedQ (cdOfG V (chalVQ7 V.basis χ) (pubCF V x ρ χ)) (pubCF V x ρ χ) = seedVCL V.claim χ := by
  obtain ⟨h0, h1, h2, h3, -, -⟩ := frame_coins (cdOf V (chalVQ7 V.basis χ) x) χ
  have hp := fun j (hj : j < 42) => pubCF_lt V x ρ χ j hj
  refine ⟨h0, h1, h2, h3, ?_, ?_⟩
  · show slotK V.basis (pubCF V x ρ χ) 0 = _
    rw [slotK_congr V.basis _ (pubVQ7 V.basis V.claim x χ) 0 (by norm_num) hp]
    exact slotK_pubVQ7_zero _ _ _ _
  · show slotK V.basis (pubCF V x ρ χ) 1 = _
    rw [slotK_congr V.basis _ (pubVQ7 V.basis V.claim x χ) 1 (by norm_num) hp]
    exact slotK_pubVQ7_one _ _ _ _

/-- **`node_records` at the CF chip** (the frame field's shape, `inlineRecords = 0`). -/
theorem node_records_CF (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K)
    (Q : Fin 232 → F[X])
    (h : RAP.SatisfiesWithPreprocessing (chipCF V x ρ χ) (fun j => Q (Fin.cast (chipCF_width V x ρ χ) j)))
    (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X])
    (hout : ∀ s ∈ SummandsQ7.summandsQ7 (F := F) (K := K) (S := S) V, ¬ s.mem (Q, Qm) χ)
    (u : NTree ((State × DTcomp K) × ℕ))
    (hu : InTree (treeV V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim x χ) Q) u)
    (j : ℕ) (hj : j < Nock.Framework.recordCount u.label.1.1) :
    (∃ a : Fin 3, ∃ r ∈ (reqFactsCF V x ρ χ Q h a).records,
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).root a r = (SVFrame.traceRecOf u.label j).root ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).child a r = (SVFrame.traceRecOf u.label j).child ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).key a r =
        recKeyQ7' V (b0 (T := tableVCLE hC) Q) u.label.1.1 u.label.2 j ∧
      (RV.recordViewVCL F K K (tableVCLE hC) S hC).axis a V (b0 (T := tableVCLE hC) Q)
          (fun t => b0 (Qm t)) r =
        SVFrame.joinRecordAxis u.label.1.1 (axB0Q7 V (b0 (T := tableVCLE hC) Q)) u.label.2 j) ∨
    (((u.label.1.1 = .s0 ∧ j = 1) ∨ (u.label.1.1 = .s9 ∧ j = 2)) ∧
      SVFrame.joinRecordAxis u.label.1.1 (axB0Q7 V (b0 (T := tableVCLE hC) Q)) u.label.2 j = 1 ∧
      (SVFrame.traceRecOf u.label j).child = (SVFrame.traceRecOf u.label j).root) := by
  have hg := chipCF_good V x ρ χ Q h
  have hs := chipCF_sat V x ρ χ Q h
  obtain ⟨hα0, hγ1, hz2, hzi5, hinit, hseed⟩ := coins_pubCF V x ρ χ
  obtain ⟨hz, hzi, -⟩ := SummandsQ7.rowFacts_outside_core V 21 24 χ Q (chalVQ7 V.basis χ)
    (pubCF V x ρ χ) hg.1 hg.2.1 hg.2.2.1 hs hg.2.2.2.1 hα0 hγ1 hz2 hzi5 hinit hseed Qm hout
  rw [← treeV_pubCF V x ρ χ Q] at hu
  rcases NodeRecQ7.node_records_Q7 V 21 24 (chalVQ7 V.basis χ)
    (pubCF V x ρ χ) Q hg.1 hg.2.1 hg.2.2.1 hs hg.2.2.2.1 hz hzi (fun t => b0 (Qm t)) u hu j hj with
    ⟨a, r, hr, h1, h2, h3, h4⟩ | hid
  swap
  · exact Or.inr hid
  refine Or.inl ⟨a, r, ?_, h1, h2, h3, h4⟩
  rw [reqFactsCF_records]
  unfold reqRecordsCF
  rw [← reqRecsQ7_round1 V (chalVQ7 V.basis χ) (pubCF V x ρ χ) (fun _ => 0) (fun _ => 0) Q Q
    (fun _ _ => rfl) a]
  exact hr

/-! ## 3. `root_binds` at the CF chip -/

theorem rowStateOf_toSourceEnv (env : CorrectedFinalTypedEnv F K) :
    ComputeWalkRootEvents.rowStateOf env.toSourceEnv =
      stateOfBase (fun k => if h : k < 13 then env.baseTrace ⟨k, h⟩ else 0) := by
  have ht : ∀ k (hk : k < 11), env.toSourceEnv.trace k = algebraMap F K (env.baseTrace ⟨k, by omega⟩) := by
    intro k hk
    simp [CorrectedFinalTypedEnv.toSourceEnv, show k < 13 by omega]
  unfold ComputeWalkRootEvents.rowStateOf stateOfBase
  simp only [ht 1 (by norm_num), ht 2 (by norm_num), ht 3 (by norm_num), ht 4 (by norm_num),
    ht 5 (by norm_num), ht 6 (by norm_num), ht 7 (by norm_num), ht 8 (by norm_num),
    ht 9 (by norm_num), ht 10 (by norm_num), algebraMap_eq_one_iff]
  simp only [show (1 : ℕ) < 13 by norm_num, show (2 : ℕ) < 13 by norm_num,
    show (3 : ℕ) < 13 by norm_num, show (4 : ℕ) < 13 by norm_num, show (5 : ℕ) < 13 by norm_num,
    show (6 : ℕ) < 13 by norm_num, show (7 : ℕ) < 13 by norm_num, show (8 : ℕ) < 13 by norm_num,
    show (9 : ℕ) < 13 by norm_num, show (10 : ℕ) < 13 by norm_num, dite_true]

/-- **`root_binds` at the CF chip** (the frame field's conclusion at `Z.seed χ = χ 2`). -/
theorem root_binds_CF (V : VerifierData F K hC S) (x : ℕ → F) (ρ : Fin 3 → K) (χ : Coins frameVCL K)
    (Q : Fin 232 → F[X])
    (h : RAP.SatisfiesWithPreprocessing (chipCF V x ρ χ) (fun j => Q (Fin.cast (chipCF_width V x ρ χ) j)))
    (Qm : ∀ t : Fin S.k, Fin (S.table t).width → F[X])
    (hout : ∀ s ∈ SummandsQ7.summandsQ7 (F := F) (K := K) (S := S) V, ¬ s.mem (Q, Qm) χ) :
    SemanticStrategy.bindFP (χ ⟨2, by decide⟩) V.claim.subject
        (treeV V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim x χ) Q).label.1.2.2.1.s ∧
      SemanticStrategy.bindFP (χ ⟨2, by decide⟩) V.claim.formula
        (treeV V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim x χ) Q).label.1.2.2.1.f ∧
      SemanticStrategy.bindFP (χ ⟨2, by decide⟩) V.claim.result
        (treeV V (chalVQ7 V.basis χ) (pubVQ7 V.basis V.claim x χ) Q).label.1.2.2.1.e := by
  have hg := chipCF_good V x ρ χ Q h
  have hs := chipCF_sat V x ρ χ Q h
  obtain ⟨hα0, hγ1, -, -, hinit, hseed⟩ := coins_pubCF V x ρ χ
  obtain ⟨st0, hst0, b1, b2, b3⟩ := SummandsQ7.root_binds_outside_core V 21 24 χ Q (chalVQ7 V.basis χ)
    (pubCF V x ρ χ) hg.1 hg.2.1 hg.2.2.1 hs hα0 hγ1 hinit hseed Qm hout
  rw [← treeV_pubCF V x ρ χ Q, treeV_label_root]
  have hst : (rowLabel (envsP V (chalVQ7 V.basis χ) (pubCF V x ρ χ) Q ⟨0, V.hN⟩)).1 = st0 := by
    rw [rowLabel_envsP_fst]
    have := SummandsQ7.rowStateOf_of_oneHot hst0
    rw [rowLabel_fst, ← rowStateOf_toSourceEnv]
    exact this
  have key := lnPatch_pub_sfe (envsV V (chalVQ7 V.basis χ) (pubCF V x ρ χ) Q ⟨0, V.hN⟩) st0
  obtain ⟨-, hs', hf', he', -⟩ := key
  have hP : (rowLabel (envsP V (chalVQ7 V.basis χ) (pubCF V x ρ χ) Q ⟨0, V.hN⟩)).2.2.1 =
      StrategyOfTracesLift.decodePub (lnPatch (envsV V (chalVQ7 V.basis χ) (pubCF V x ρ χ) Q ⟨0, V.hN⟩)) st0 := by
    show StrategyOfTracesLift.decodePub _ (StrategyOfTracesLift.computeStateOf _) = _
    rw [show StrategyOfTracesLift.computeStateOf (StrategyOfTracesLift.decodeSource
      (envsP V (chalVQ7 V.basis χ) (pubCF V x ρ χ) Q ⟨0, V.hN⟩)) = st0 from hst]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · show SemanticStrategy.bindFP _ _ (rowLabel (envsP V (chalVQ7 V.basis χ) (pubCF V x ρ χ) Q ⟨0, V.hN⟩)).2.2.1.s
    rw [hP, hs']; exact b1
  · show SemanticStrategy.bindFP _ _ (rowLabel (envsP V (chalVQ7 V.basis χ) (pubCF V x ρ χ) Q ⟨0, V.hN⟩)).2.2.1.f
    rw [hP, hf']; exact b2
  · show SemanticStrategy.bindFP _ _ (rowLabel (envsP V (chalVQ7 V.basis χ) (pubCF V x ρ χ) Q ⟨0, V.hN⟩)).2.2.1.e
    rw [hP, he']; exact b3

end pubirrel

end

end CompTreeVCL
end VclL.Compute
end Nock.NockVMROM.Thm54
