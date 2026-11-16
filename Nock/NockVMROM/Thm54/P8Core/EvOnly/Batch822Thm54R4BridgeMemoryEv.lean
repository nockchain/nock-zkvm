/-
  Nock/NockVMROM/Thm54/P8Core/EvOnly/Batch822Thm54R4BridgeMemoryEv.lean

  The originals are untouched.  Imports P8Core only; never the statement file.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch822Thm54R4BridgeMemory
import Nock.NockVMROM.Thm54.P8Core.PlacementABridge
import Nock.NockVMROM.Thm54.P8Core.EvOnly.OptimizedHostileTimestampsEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch465Thm54DeployedRootLabelEqClaimEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch489Thm54FoOfEqFoWEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch490Thm54TopologyAssemblyEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch500Thm54GammaTransportEv
import Nock.NockVMROM.Thm54.P8Core.EvOnly.Batch501Thm54MemoryTopologyEv
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch822

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.AxisBatching
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.FormRBridge
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.Framework
open Nock.Framework.Reify
open Nock.RedTeam.Batch490
open Nock.RedTeam.Batch501

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

section Accepted

variable (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)
  (hgood : c ∉ Nock.NockVMROM.Thm54.OptimizedFailureEventEv.optimizedFailureEventEv P Qc₀ Qm₀)
include hsatM hchar

include hgood in
theorem tiling_foM_ev :
    P.optimized.family.problem.cfg.kMem + Sf (foM P Qm₀ c) P.optimized.family.problem.cfg.memRows =
      P.optimized.family.problem.cfg.memRows := by
  rw [← foW_eq_foM' P c Qm₀ hsatM hchar]
  exact deployed_tiling_memory P c (familyQm P c Qm₀) hsatM hchar
    (htileαM_of_good_ev P c Qc₀ Qm₀ hsatM hchar hgood)

include hgood in
/-- Children sit strictly later, inside the table (`BFSValidF` + tiling). -/
theorem order_of_deployed_ev (i : ℕ) (h : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ foOfMem (P.memoryBaseEnv Qm₀) i) :
    i < childIdx (P.memoryBaseEnv Qm₀) P.optimized.family.problem.cfg.kMem i ℓ ∧
      childIdx (P.memoryBaseEnv Qm₀) P.optimized.family.problem.cfg.kMem i ℓ ≤
        P.optimized.family.problem.cfg.memRows := by
  have hv := bfsValid_foM P c Qm₀ hsatM hchar i h.1 h.2
  have ht := tiling_foM_ev P c Qm₀ Qc₀ hsatM hchar hgood
  have hfo := foOfMem_eq_foM P c Qm₀ i h.1 h.2
  have hsplit := Sf_split (foM P Qm₀ c) h.1
  have hmono := Walk.Sf_mono (foM P Qm₀ c) h.2
  have hcong := Sf_congr_le (fo := foOfMem (P.memoryBaseEnv Qm₀)) (fo' := foM P Qm₀ c)
    (M := P.optimized.family.problem.cfg.memRows) (n := i - 1) (by omega)
    (fun k hk1 hk2 => foOfMem_eq_foM P c Qm₀ k hk1 hk2)
  unfold childIdx
  rw [hcong]
  constructor <;> omega

include hgood hsatC hz in
/-- **The child link**: the followed slot `ℓ ∈ {1, 2}` of row `i` holds row `childIdx i ℓ`'s
`pt` in its `lc` / `rc` cell. -/
theorem link_of_deployed_ev (i : ℕ) (h : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows)
    (ℓ : ℕ) (hℓ : ℓ < foOfMem (P.memoryBaseEnv Qm₀) i) :
    memCell (lblM P Qm₀ c i) ⟨ℓ % 2, Nat.mod_lt _ (by norm_num)⟩ =
      (pubR P c Qm₀ (childIdx (P.memoryBaseEnv Qm₀) P.optimized.family.problem.cfg.kMem i
        (ℓ + 1))).pt := by
  have hγ : gamma c.1 ∉ forestPrefixBadGammas (VdM P c Qm₀) (CvdM P c Qm₀)
      (foM P Qm₀ c) (kMemP P) (memRowsP P) := by
    rw [← forestPrefixBadGammas_VdM_eq_committed P c Qm₀]
    exact hγM_of_good_ev P c Qc₀ Qm₀ hgood
  have hb' := deployed_forestVecBFT_pt P c Qm₀ hsatM hchar hγ
    (hαM_of_good_ev P c Qc₀ Qm₀ hsatC hsatM hchar hz hgood) (htileαM_of_good_ev P c Qc₀ Qm₀ hsatM hchar hgood)
  have ht := tiling_foM_ev P c Qm₀ Qc₀ hsatM hchar hgood
  have hfo := foOfMem_eq_foM P c Qm₀ i h.1 h.2
  have hℓ' : ℓ < foM P Qm₀ c i := by rw [← hfo]; exact hℓ
  have hkey := ForestVecBFT_layout
    (fun i => encPT (lblM P Qm₀ c i))
    (fun i l => encPT (clabOfMem (lblM P Qm₀ c) i l))
    (foM P Qm₀ c) ht hb' h.1 h.2 hℓ'
  have hpt := encPT_label _ _ hkey
  have hcell : ptOf (clabOfMem (lblM P Qm₀ c) i (ℓ + 1)) =
      memCell (lblM P Qm₀ c i) ⟨ℓ % 2, Nat.mod_lt _ (by norm_num)⟩ := by
    simp only [ptOf, clabOfMem, Nat.add_sub_cancel]
  rw [childIdx_eq_firstCF P c Qm₀ i ℓ h.2, ← hcell, hpt]
  rfl

include hgood hsatC hz in
theorem link1_of_deployed_ev (i : ℕ) (h : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows)
    (h1 : 1 ≤ foOfMem (P.memoryBaseEnv Qm₀) i) :
    (pubR P c Qm₀ i).lc =
      (pubR P c Qm₀ (childIdx (P.memoryBaseEnv Qm₀) P.optimized.family.problem.cfg.kMem i 1)).pt :=
  link_of_deployed_ev P c Qm₀ Qc₀ hsatC hsatM hchar hz hgood i h 0 (by omega)

include hgood hsatC hz in
theorem link2_of_deployed_ev (i : ℕ) (h : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows)
    (h2 : 2 ≤ foOfMem (P.memoryBaseEnv Qm₀) i) :
    (pubR P c Qm₀ i).rc =
      (pubR P c Qm₀ (childIdx (P.memoryBaseEnv Qm₀) P.optimized.family.problem.cfg.kMem i 2)).pt :=
  link_of_deployed_ev P c Qm₀ Qc₀ hsatC hsatM hchar hz hgood i h 1 (by omega)

include hz hgood hsatC in
theorem telescopeRows_of_memory_ev (n : ℕ) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool)
    (hn : MemoryTable.pwScaleExp K = n - 1)
    (hts : ∀ i (h : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows),
      (FormRBridge.stAt (P.memoryBaseEnv Qm₀) i h = .read_root ∨
        FormRBridge.stAt (P.memoryBaseEnv Qm₀) i h = .verify_child) →
      (pubR P c Qm₀ i).mem.ts = alphaM c.1 ^ FormRBridge.expAt (P.memoryBaseEnv Qm₀) i h)
    (haxis : ∀ i (h : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows),
      FormRBridge.stAt (P.memoryBaseEnv Qm₀) i h = .read_root →
      (pubR P c Qm₀ i).mem.axis = c.2.2.2.lambda ^ mm (FormRBridge.expAt (P.memoryBaseEnv Qm₀) i h))
    (hcp : ∀ i (h : 1 ≤ i ∧ i ≤ P.optimized.family.problem.cfg.memRows),
      FormRBridge.stAt (P.memoryBaseEnv Qm₀) i h = .read_root →
      (pubR P c Qm₀ i).cprime =
        (Batch575.C'poly (K := K) n (cc (FormRBridge.expAt (P.memoryBaseEnv Qm₀) i h))).eval c.2.2.2.lambda) :
    TelescopeRows (P.memoryBaseEnv Qm₀) P.optimized.family.problem.cfg.kMem (pubR P c Qm₀)
      (inpR P c Qm₀) (alphaM c.1) c.2.2.2.lambda n mm cc where
  st := pub_st P c Qm₀
  eqBlk := eqBlk_of_deployed P c Qm₀ hsatM hchar hz
  lam := pub_lam P c Qm₀
  link1 := link1_of_deployed_ev P c Qm₀ Qc₀ hsatC hsatM hchar hz hgood
  link2 := link2_of_deployed_ev P c Qm₀ Qc₀ hsatC hsatM hchar hz hgood
  order := order_of_deployed_ev P c Qm₀ Qc₀ hsatM hchar hgood
  ts := hts
  axis := haxis
  cprime := hcp
  scale := hn

end Accepted

end

end Nock.RedTeam.Batch822

