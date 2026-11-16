/-
  Nock/NockVMROM/Thm54/P8Core/Batch1024Thm54C2BindsAtCoin.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch1024Thm54C2BindsAtCoin`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch1024Thm54C2BindsAtCoin.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1011Thm54AxisViewBindsAtCoin
import Nock.NockVMROM.Thm54.P8Core.Batch1021Thm54C2JoinAssembly
import Nock.NockVMROM.Thm54.P8Core.ForestExponentWindow
import Nock.NockVMROM.Thm54.P8Core.Batch530Thm54ComputeTreeBindsDeployed
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1024

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.RedTeam.Batch1021

noncomputable section

section Transport

variable {K : Type} [Field K] [DecidableEq K]

/-- **`BindComputeRow` transports through the compute specialization.**  Every field it reads is
unchanged except the record slots, where the active ones keep root / child / axis and the inactive
ones become `MemRec.zero` — exactly `BindComputeRow`'s demand. -/
theorem bindComputeRow_specialize {z : K} (α : K) (s : ComputeRowSkeleton)
    (row : State × DTcomp K) (h : BindComputeRow z s row) :
    BindComputeRow z s ((StrategyOfTracesLift.wrapComputeLabel row).specialize α) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h1, h4, h5, h6, h7, h8, ?_⟩
  intro i
  have hi := h9 i
  by_cases hlt : (i : ℕ) < Nock.Framework.recordCount s.state
  · rw [dif_pos hlt] at hi ⊢
    have hact : computeMemRecKind row.1 i = .active := by
      simp [computeMemRecKind, h1, hlt]
    obtain ⟨hr, hc, ha⟩ := hi
    fin_cases i
    · simp only [computeMemRec, ComputeRowTemplate.specialize, StrategyOfTracesLift.wrapComputeLabel,
        specializeMemRecScaled]
      split
      · exact ⟨hr, hc, ha⟩
      · exact absurd (decide_eq_true hact) ‹_›
    · simp only [computeMemRec, ComputeRowTemplate.specialize, StrategyOfTracesLift.wrapComputeLabel,
        specializeMemRecScaled]
      split
      · exact ⟨hr, hc, ha⟩
      · exact absurd (decide_eq_true hact) ‹_›
    · simp only [computeMemRec, ComputeRowTemplate.specialize, StrategyOfTracesLift.wrapComputeLabel,
        specializeMemRecScaled]
      split
      · exact ⟨hr, hc, ha⟩
      · exact absurd (decide_eq_true hact) ‹_›
  · rw [dif_neg hlt] at hi ⊢
    have hpad : computeMemRecKind row.1 i = .padding := by
      simp [computeMemRecKind, h1, hlt]
    have hna : ¬ computeMemRecKind row.1 i = .active := by rw [hpad]; decide
    fin_cases i
    · simp only [computeMemRec, ComputeRowTemplate.specialize, StrategyOfTracesLift.wrapComputeLabel,
        specializeMemRecScaled]
      split
      · exact absurd (of_decide_eq_true ‹_›) hna
      · rfl
    · simp only [computeMemRec, ComputeRowTemplate.specialize, StrategyOfTracesLift.wrapComputeLabel,
        specializeMemRecScaled]
      split
      · exact absurd (of_decide_eq_true ‹_›) hna
      · rfl
    · simp only [computeMemRec, ComputeRowTemplate.specialize, StrategyOfTracesLift.wrapComputeLabel,
        specializeMemRecScaled]
      split
      · exact absurd (of_decide_eq_true ‹_›) hna
      · rfl

theorem forall₂_map_of_sizes {z : K} (φ : State × DTcomp K → State × DTcomp K) (n : ℕ)
    (ih : ∀ (s : NTree ComputeRowSkeleton) (t : NTree (State × DTcomp K)), t.size ≤ n →
      ComputeTreeBinds z s t → ComputeTreeBinds z s (mapNTree φ t)) :
    ∀ (sc : List (NTree ComputeRowSkeleton)) (rc : List (NTree (State × DTcomp K))),
      (∀ c ∈ rc, c.size ≤ n) → List.Forall₂ (ComputeTreeBinds z) sc rc →
      List.Forall₂ (ComputeTreeBinds z) sc (rc.map (mapNTree φ))
  | _, _, _, .nil => .nil
  | _, _, hsz, .cons hb hrest =>
      .cons (ih _ _ (hsz _ List.mem_cons_self) hb)
        (forall₂_map_of_sizes φ n ih _ _ (fun c hc => hsz c (List.mem_cons_of_mem _ hc)) hrest)

/-- **`ComputeTreeBinds` transports through `mapNTree`** of any row map that transports
`BindComputeRow`. -/
theorem computeTreeBinds_mapNTree {z : K} (φ : State × DTcomp K → State × DTcomp K)
    (hφ : ∀ (s : ComputeRowSkeleton) (row : State × DTcomp K),
      BindComputeRow z s row → BindComputeRow z s (φ row)) :
    ∀ (n : ℕ) (s : NTree ComputeRowSkeleton) (t : NTree (State × DTcomp K)), t.size ≤ n →
      ComputeTreeBinds z s t → ComputeTreeBinds z s (mapNTree φ t) := by
  intro n
  induction n with
  | zero =>
      intro s t ht
      have := Batch530.ntree_size_pos t
      omega
  | succ n ih =>
      intro s t ht h
      cases h with
      | @node s sc row rc shape rowB children =>
          have hch : ∀ c ∈ rc, c.size ≤ n := fun c hc => Batch530.child_size_le_of_node ht hc
          simp only [mapNTree]
          exact ComputeTreeBinds.node shape (hφ _ _ rowB)
            (forall₂_map_of_sizes φ n ih sc rc hch children)

end Transport

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
  (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)

/-- The C2 strategy at the family traces. -/
abbrev TC := strategyOfTracesR0AC2 P.optimized P.stateTagChar (honestQc P c Qc)
  (honestQm P c Qm) c h

/-- The S-carrying exec tree of the family traces. -/
abbrev treeS := c2TreeOfTraces P.optimized (honestQc P c Qc) c

/-- The served lookup and the certificate axes of the family traces. -/
abbrev svF := c2ServedOf P.optimized (honestQm P c Qm) c

abbrev axF := c2AxOf P.optimized (honestQc P c Qc) c

/-- **The specialized compute tree is the `mapNTree` of the decoded exec tree** (`mapNTree_comp`). -/
theorem specialized_computeTree_C2 (z : K) (hz : z ≠ 0) (α lmb : K) :
    ((TC P c Qc Qm h).specializedExec z hz α lmb).computeTree =
      mapNTree (fun row => (StrategyOfTracesLift.wrapComputeLabel row).specialize α)
        (StrategyOfTracesLift.execOfTraces P.optimized (honestQc P c Qc) (honestQm P c Qm) c h).computeTree := by
  rw [specializedExec_C2_eq, specializedExec_R0A_eq, specializedExec_R0_eq]
  exact ForestExponentWindow.mapNTree_comp _ _ _

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hacc hgood hax hbasis hwidth

theorem memoryForestBinds_C2 (hz : nprSeed c.1 ≠ 0)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x)
    (hα0 : alphaM c.1 ≠ 0) :
    List.Forall₂ (MemoryTreeBinds (nprSeed c.1))
      (TC P c Qc Qm h).skeleton.memoryForest
      ((TC P c Qc Qm h).specializedExec (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryForest :=
  Batch1011.memoryForestBinds_R0A P c Qc Qm hacc hgood hax hbasis hwidth h hz hF hα0

end

end Nock.RedTeam.Batch1024
