/-
  Nock/NockVMROM/Thm54/P8Core/Batch501Thm54MemoryTopology.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch501Thm54MemoryTopology`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch501Thm54MemoryTopology.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch500Thm54GammaTransport
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace Nock.RedTeam.Batch501

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.WalkQueueDeployed
open Nock.NockVMROM.Thm54.MemoryWalkDeployed
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.HostilePoleAlignment
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryHostileAccumulator
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open Nock.RedTeam.Batch489
open Nock.RedTeam.Batch490
open Nock.RedTeam.Batch500
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree (FmemTopo mem_stateSep_topo respects_pt_topo memPtOf)

noncomputable section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem forestPrefixBadGammas_congr_on {n : ℕ}
    {V V' : ℕ → Fin n → K} {Cv Cv' : ℕ → ℕ → Fin n → K}
    {fo fo' : ℕ → ℕ} {kroots h : ℕ} (hkh : kroots ≤ h)
    (hV : ∀ i, 1 ≤ i → i ≤ h → V i = V' i)
    (hCv : ∀ i l, 1 ≤ i → i ≤ h → Cv i l = Cv' i l)
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = fo' i) :
    forestPrefixBadGammas V Cv fo kroots h =
      forestPrefixBadGammas V' Cv' fo' kroots h := by
  unfold forestPrefixBadGammas
  congr 1
  · exact curValsV_congr_on hV
  · have hcur : curValsV V kroots = curValsV V' kroots :=
      curValsV_congr_on (fun i h1 h2 => hV i h1 (le_trans h2 hkh))
    have hflat : flatBlksV Cv fo h = flatBlksV Cv' fo' h :=
      flatBlksV_congr_on hfo hCv
    simp only [hcur, hflat]

section PricedForestGamma

variable {F : Type} [Field F] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

/-- Priced `memoryPrefixGammaEventOf` is `forestPrefixBadGammas` of the
    committed `memorySourceEnv` / `memoryBaseEnv` vectors. -/
theorem hγM_of_priced
    (hγM : c.1 ∉ P.memoryPrefixGammaEventOf Qm₀) :
    gamma c.1 ∉
      forestPrefixBadGammas
        (committedMemoryV (P.memorySourceEnv Qm₀) (P.memoryBaseEnv Qm₀))
        (committedMemoryCv (P.memorySourceEnv Qm₀))
        (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm₀))
        P.optimized.family.problem.cfg.kMem
        P.optimized.family.problem.cfg.memRows :=
  (memoryPrefixGammaEventOfEnvs_eq_prefix (P.memorySourceEnv Qm₀)
    (P.memoryBaseEnv Qm₀) P.optimized.family.problem.cfg.kMem c.1).mpr.mt hγM

/-- `c ∉ optimizedFailureEvent` discharges the memory forest `hγ`. -/
theorem hγM_of_good
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    gamma c.1 ∉
      forestPrefixBadGammas
        (committedMemoryV (P.memorySourceEnv Qm₀) (P.memoryBaseEnv Qm₀))
        (committedMemoryCv (P.memorySourceEnv Qm₀))
        (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm₀))
        P.optimized.family.problem.cfg.kMem
        P.optimized.family.problem.cfg.memRows :=
  hγM_of_priced P c Qm₀
    (P.optimizedFailureEvent_good_components Qc₀ Qm₀ c hgood).2.2.2.2.2.2.2.2.1

end PricedForestGamma

section Projection

variable {K : Type} [Field K]

/-- Drop coordinate `0` (the state tag) of an `x^mem` label vector. -/
def ptProj (v : Fin 6 → K) : Fin 5 → K := fun k => v k.succ

/-- The child-link projection `childLinkMem` reads. -/
def ptOf (l : MState × DTmem K) : Cell K := l.2.2.pt

/-- The projected encoder: coordinates `1..5` of `memoryLabelVec`. -/
def encPT (l : MState × DTmem K) : Fin 5 → K := ptProj (memoryLabelVec l.2.2)

/-- After projecting away the tag, the `clabM`-shaped label IS the declared
    child vector, for ANY hosted tags. -/
theorem encPT_clab (pub : MemoryTable.Pub K) (tags : Fin 2 → K) (j : Fin 2) :
    ptProj (memoryLabelVec { pub with pt := childCell pub j }) =
      ptProj (childVec pub tags j) := by
  funext k
  fin_cases k <;> rfl

theorem cell_eq_of_coords {a b : Cell K}
    (hs : a.noun.size = b.noun.size) (hd : a.noun.dyck = b.noun.dyck)
    (hl : a.noun.leaf = b.noun.leaf)
    (hi : a.indicator = b.indicator) (hc : a.counts = b.counts) : a = b := by
  rcases a with ⟨⟨sz, dy, lf⟩, ind, cnt⟩
  rcases b with ⟨⟨sz', dy', lf'⟩, ind', cnt'⟩
  simp_all

/-- The projected encoder determines the child-link projection. -/
theorem encPT_label (a b : MState × DTmem K) (h : encPT a = encPT b) :
    ptOf a = ptOf b := by
  have hcoord (k : Fin 5) :
      memoryLabelVec a.2.2 k.succ = memoryLabelVec b.2.2 k.succ :=
    congrFun h k
  have hs : a.2.2.pt.noun.size = b.2.2.pt.noun.size := by
    simpa [memoryLabelVec] using hcoord 0
  have hd : a.2.2.pt.noun.dyck = b.2.2.pt.noun.dyck := by
    simpa [memoryLabelVec] using hcoord 1
  have hl : a.2.2.pt.noun.leaf = b.2.2.pt.noun.leaf := by
    simpa [memoryLabelVec] using hcoord 2
  have hc : a.2.2.pt.counts = b.2.2.pt.counts := by
    simpa [memoryLabelVec] using hcoord 3
  have hi : a.2.2.pt.indicator = b.2.2.pt.indicator := by
    simpa [memoryLabelVec] using hcoord 4
  simp only [ptOf]
  exact cell_eq_of_coords hs hd hl hi hc

end Projection

section ForestMap

variable {K : Type*} [Field K] {n m : ℕ}

theorem forestVecBFT_map (π : (Fin n → K) → (Fin m → K)) {V : ℕ → Fin n → K}
    {Cv : ℕ → ℕ → Fin n → K} {fo : ℕ → ℕ} {kroots h : ℕ}
    (hb : ForestVecBFT V Cv fo kroots h) :
    ForestVecBFT (fun i => π (V i)) (fun i l => π (Cv i l)) fo kroots h := by
  unfold ForestVecBFT at hb ⊢
  have := congrArg (List.map π) hb
  simpa [curValsV, flatBlksV, blkValsV, List.map_append, List.map_flatMap,
    List.map_map, Function.comp_def] using this

theorem forestVecBFT_congr_children {V : ℕ → Fin n → K} {Cv Cv' : ℕ → ℕ → Fin n → K}
    {fo : ℕ → ℕ} {kroots h : ℕ}
    (hC : ∀ i l, l < fo i → Cv i (l + 1) = Cv' i (l + 1))
    (hb : ForestVecBFT V Cv fo kroots h) :
    ForestVecBFT V Cv' fo kroots h := by
  unfold ForestVecBFT at hb ⊢
  rw [hb]
  congr 1
  unfold flatBlksV
  apply List.flatMap_congr
  intro i _
  unfold blkValsV
  apply List.map_congr_left
  intro l hl
  exact hC (i + 1) l (List.mem_range.mp hl)

end ForestMap

section MemoryVectors

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)

abbrev memRowsP : ℕ := P.optimized.family.problem.cfg.memRows

abbrev kMemP : ℕ := P.optimized.family.problem.cfg.kMem

/-- Hosted `x^mem` at walk index `i`. -/
def VdM (i : ℕ) : Fin 6 → K :=
  memoryLabelVec (pubAt P c (familyQm P c Qm₀) (rowOf P i))

/-- Hosted declared child at walk index `i`, slot `l` (1-indexed). -/
def CvdM (i l : ℕ) : Fin 6 → K :=
  childVecN (pubAt P c (familyQm P c Qm₀) (rowOf P i))
    (tagsAt P c (familyQm P c Qm₀) (rowOf P i)) (l - 1)

omit hsatM hchar hz in
theorem memorySourceEnv_trace_eq (i : Fin (memRowsP P)) :
    (P.memorySourceEnv Qm₀ i).trace =
      (memorySourceEnvAt P c Qm₀ i).trace := by
  have hF := memoryBaseEnv_trace_eq P c Qm₀ i
  funext idx
  simp only [OptimizedFullStrictNockVMROMPackage.memorySourceEnv,
    memorySourceEnvAt, gatherEnv, hF]

omit hsatM hchar hz in
theorem memRowLabelVec_eq_pub (i : Fin (memRowsP P)) :
    memRowLabelVec (memorySourceEnvAt P c Qm₀ i) (memoryBaseEnvAt P c Qm₀ i) =
      memoryLabelVec (decodeMemPub P Qm₀ c i) := by
  have hst : WalkTilingEvents.memRowStateOf (memoryBaseEnvAt P c Qm₀ i) =
      memoryStateOf (memoryBaseEnvAt P c Qm₀ i) := by
    unfold WalkTilingEvents.memRowStateOf memoryStateOf
    rfl
  funext k
  fin_cases k <;>
    simp [memRowLabelVec, memoryLabelVec, decodeMemPub, memoryPtNoun, hst]

omit hsatM hchar hz in
theorem memRowChildVec_eq_childVec_decode (i : Fin (memRowsP P)) (j : Fin 2) :
    memRowChildVec (memorySourceEnvAt P c Qm₀ i) j =
      childVec (decodeMemPub P Qm₀ c i)
        (fun j => (memorySourceEnvAt P c Qm₀ i).trace (childTagHostRole j)) j := by
  funext t
  fin_cases j <;> fin_cases t <;>
    simp [memRowChildVec, childVec, childCell, decodeMemPub, childTagHostRole]

omit hsatM hchar hz in
theorem VdM_eq_committed (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ memRowsP P) :
    committedMemoryV (P.memorySourceEnv Qm₀) (P.memoryBaseEnv Qm₀) i =
      VdM P c Qm₀ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < memRowsP P := by omega
  have hpos : 1 ≤ k + 1 ∧ k < memRowsP P := ⟨by omega, hk⟩
  have hQ : honestQm P c (familyQm P c Qm₀) = Qm₀ :=
    WalkQueueDeployed.honestQm_familyQm P c Qm₀
  have htr := memorySourceEnv_trace_eq P c Qm₀ ⟨k, hk⟩
  have hF := memoryBaseEnv_trace_eq P c Qm₀ ⟨k, hk⟩
  simp only [committedMemoryV, VdM, dif_pos hpos, Nat.add_sub_cancel]
  rw [rowOf_succ P k hk]
  simp only [pubAt, MemoryWalkDeployed.Qmh, hQ]
  have hlab := memRowLabelVec_eq_pub P c Qm₀ ⟨k, hk⟩
  rw [← hlab]
  exact memRowLabelVec_congr htr.symm hF.symm

omit hsatM hchar hz in
theorem CvdM_eq_committed (i l : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ memRowsP P) :
    committedMemoryCv (P.memorySourceEnv Qm₀) i l = CvdM P c Qm₀ i l := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < memRowsP P := by omega
  have hpos : 1 ≤ k + 1 ∧ k < memRowsP P := ⟨by omega, hk⟩
  have hQ : honestQm P c (familyQm P c Qm₀) = Qm₀ :=
    WalkQueueDeployed.honestQm_familyQm P c Qm₀
  have htr := memorySourceEnv_trace_eq P c Qm₀ ⟨k, hk⟩
  simp only [committedMemoryCv, CvdM, dif_pos hpos, Nat.add_sub_cancel]
  rw [rowOf_succ P k hk]
  by_cases hl : l - 1 < 2
  · rw [dif_pos hl]
    have hfin : childVecN (pubAt P c (familyQm P c Qm₀) ⟨k, hk⟩)
        (tagsAt P c (familyQm P c Qm₀) ⟨k, hk⟩) (l - 1) =
        childVec (pubAt P c (familyQm P c Qm₀) ⟨k, hk⟩)
          (tagsAt P c (familyQm P c Qm₀) ⟨k, hk⟩) ⟨l - 1, hl⟩ :=
      childVecN_fin _ _ ⟨l - 1, hl⟩
    rw [hfin]
    simp only [pubAt, MemoryWalkDeployed.Qmh, hQ]
    have htags : tagsAt P c (familyQm P c Qm₀) ⟨k, hk⟩ =
        fun j => (memorySourceEnvAt P c Qm₀ ⟨k, hk⟩).trace (childTagHostRole j) := by
      funext j
      simp [tagsAt, MemoryWalkDeployed.envK, MemoryWalkDeployed.Qmh, hQ]
    rw [htags]
    have hch := memRowChildVec_eq_childVec_decode P c Qm₀ ⟨k, hk⟩ ⟨l - 1, hl⟩
    rw [← hch]
    exact memRowChildVec_congr htr.symm ⟨l - 1, hl⟩
  · rw [dif_neg hl]
    change (0 : Fin 6 → K) =
      childVecN (pubAt P c (familyQm P c Qm₀) ⟨k, hk⟩)
        (tagsAt P c (familyQm P c Qm₀) ⟨k, hk⟩) (l - 1)
    simp only [childVecN]
    split <;> first | omega | rfl

omit hsatM hchar hz in
theorem encPT_clab_active (i l : ℕ) (hl : l < foM P Qm₀ c i) :
    ptProj (CvdM P c Qm₀ i (l + 1)) =
      encPT (clabOfMem (lblM P Qm₀ c) i (l + 1)) := by
  have hl2 : l < 2 :=
    lt_of_lt_of_le hl (fanoutMem_le_two (lblM P Qm₀ c i).1)
  have hQ : honestQm P c (familyQm P c Qm₀) = Qm₀ :=
    WalkQueueDeployed.honestQm_familyQm P c Qm₀
  have hpub : pubAt P c (familyQm P c Qm₀) (rowOf P i) = (lblM P Qm₀ c i).2.2 := by
    simp only [pubAt, lblM, Qmh, hQ, rowOf]
    split_ifs <;> rfl
  have hL : CvdM P c Qm₀ i (l + 1) =
      childVec (lblM P Qm₀ c i).2.2
        (tagsAt P c (familyQm P c Qm₀) (rowOf P i)) ⟨l, hl2⟩ := by
    simp only [CvdM, Nat.add_sub_cancel]
    rw [hpub]
    exact childVecN_fin _ _ ⟨l, hl2⟩
  have hslot : (⟨l % 2, Nat.mod_lt l (by norm_num)⟩ : Fin 2) = ⟨l, hl2⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hl2)
  have hR : encPT (clabOfMem (lblM P Qm₀ c) i (l + 1)) =
      ptProj (memoryLabelVec
        { (lblM P Qm₀ c i).2.2 with
          pt := childCell (lblM P Qm₀ c i).2.2 ⟨l, hl2⟩ }) := by
    simp only [encPT, clabOfMem, Nat.add_sub_cancel]
    rw [hslot, ← childCell_eq_memCell (lblM P Qm₀ c i) ⟨l, hl2⟩]
  rw [hL, hR]
  exact (encPT_clab (lblM P Qm₀ c i).2.2
    (tagsAt P c (familyQm P c Qm₀) (rowOf P i)) ⟨l, hl2⟩).symm

omit hsatM hchar hz in
theorem pubAt_eq_lblM_pub (i : ℕ) :
    pubAt P c (familyQm P c Qm₀) (rowOf P i) = (lblM P Qm₀ c i).2.2 := by
  have hQ : honestQm P c (familyQm P c Qm₀) = Qm₀ :=
    WalkQueueDeployed.honestQm_familyQm P c Qm₀
  simp only [pubAt, lblM, Qmh, hQ, rowOf, lblMAt]
  split_ifs <;> rfl

omit hchar hz hsatM in
theorem foM_eq_committed (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ memRowsP P) :
    WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm₀) i = foM P Qm₀ c i := by
  have hfoW := foOfMem_eq_foWmem P c Qm₀ i hi1 hih
  have hAll := foW_eq_foM_all P c (familyQm P c Qm₀) i
  have hQ : honestQm P c (familyQm P c Qm₀) = Qm₀ :=
    WalkQueueDeployed.honestQm_familyQm P c Qm₀
  rw [hfoW, hAll]
  simp [MemoryWalkDeployed.Qmh, hQ]

omit hchar hz hsatM in
theorem kMem_le_memRows : kMemP P ≤ memRowsP P :=
  MemoryWalkDeployed.kMem_le P

omit hz in
/-- Package/family K-traces agree, so the priced `hγ` is the hosted-vector event. -/
theorem forestPrefixBadGammas_VdM_eq_committed :
    forestPrefixBadGammas
        (committedMemoryV (P.memorySourceEnv Qm₀) (P.memoryBaseEnv Qm₀))
        (committedMemoryCv (P.memorySourceEnv Qm₀))
        (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm₀))
        (kMemP P) (memRowsP P) =
      forestPrefixBadGammas (VdM P c Qm₀) (CvdM P c Qm₀)
        (foM P Qm₀ c) (kMemP P) (memRowsP P) :=
  forestPrefixBadGammas_congr_on (kMem_le_memRows P)
    (fun i h1 h2 => VdM_eq_committed P c Qm₀ i h1 h2)
    (fun i l h1 h2 => CvdM_eq_committed P c Qm₀ i l h1 h2)
    (fun i h1 h2 => foM_eq_committed P c Qm₀ i h1 h2)

include hz
include hsatM hchar

/-- `hFcommit` at every memory row (M′, `m-prime-topo`): the β-free `FmemTopo` from the chip's
acceptance, `MemStateTagChar` and `z ≠ 0` (`Batch490.hFcommit_memory`). -/
theorem hFcommit_memory_of_good
    (i : ℕ) (hi1 : 1 ≤ i) (hih : i ≤ memRowsP P) :
    FmemTopo (lblM P Qm₀ c i)
      (fun j : Fin 2 =>
        if (j : ℕ) < foM P Qm₀ c i then
          some (clabOfMem (lblM P Qm₀ c) i ((j : ℕ) + 1))
        else none) :=
  hFcommit_memory P c Qm₀ hsatM hchar hz i hi1 hih

end MemoryVectors

section ForestVecBFT

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
include hsatM hchar

/-- Tiling exclusion the chip theorem takes, from the priced event. -/
theorem htileαM_of_good
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    c.1 ∉ WalkTilingEvents.memoryTilingEvent
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P) := by
  have htileM : c.1 ∉ P.memoryTilingEventOf Qm₀ :=
    (P.optimizedFailureEvent_good_components Qc₀ Qm₀ c hgood).2.2.2.2.2.2.1
  rwa [← memoryTilingEventOf_eq_foWmem P c Qm₀]

/-- Whole-table `ForestVecBFT` at the hosted vectors.  `hseed` is
    definitional (`exists_walkSat_agree_ge` at `nodeListP kMem`). -/
theorem deployed_forestVecBFT
    (hγ : gamma c.1 ∉ forestPrefixBadGammas (VdM P c Qm₀) (CvdM P c Qm₀)
      (foM P Qm₀ c) (kMemP P) (memRowsP P))
    (hα : alphaM c.1 ∉ walkForestPrefixAlphaEvent
      (curW P c (familyQm P c Qm₀)) (chldW P c (familyQm P c Qm₀))
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P))
    (htileα : c.1 ∉ WalkTilingEvents.memoryTilingEvent
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P)) :
    ForestVecBFT (VdM P c Qm₀) (CvdM P c Qm₀) (foM P Qm₀ c)
      (kMemP P) (memRowsP P) := by
  have hw := deployed_walkSat P c (familyQm P c Qm₀) hsatM hchar
  have hout : accW P c (familyQm P c Qm₀) (memRowsP P) = 0 :=
    deployed_walk_out P c (familyQm P c Qm₀) hsatM
  obtain ⟨acc', hws, hagree⟩ := WalkSatInGate.exists_walkSat_agree_ge hw
  have hout' : acc' (memRowsP P) = 0 := by
    rw [← hagree (memRowsP P) (memRows_pos P) le_rfl (kMem_le P)]
    exact hout
  have hfo : foW P c (familyQm P c Qm₀) = foM P Qm₀ c := by
    funext i
    have h := foW_eq_foM_all P c (familyQm P c Qm₀) i
    rw [MemoryWalkDeployed.Qmh, WalkQueueDeployed.honestQm_familyQm P c Qm₀] at h
    exact h
  have hcur : (fun i => rlc (gamma c.1) (VdM P c Qm₀ i)) =
      curW P c (familyQm P c Qm₀) := rfl
  have hch : (fun i l => rlc (gamma c.1) (CvdM P c Qm₀ i l)) =
      chldW P c (familyQm P c Qm₀) := rfl
  rcases isForestFullBFT_or_mem_alphaEvent hws rfl rfl hout' with hbft | hmem
  · have hγ' : gamma c.1 ∉ forestPrefixBadGammas (VdM P c Qm₀) (CvdM P c Qm₀)
        (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P) := by
      rw [hfo]; exact hγ
    have hbft' : IsForestFullBFT
        (fun i => rlc (gamma c.1) (VdM P c Qm₀ i))
        (fun i l => rlc (gamma c.1) (CvdM P c Qm₀ i l))
        (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P) := by
      rw [hcur, hch]; exact hbft
    have hpre := forestPrefixBFT_of_isForestFullBFT (VdM P c Qm₀) (CvdM P c Qm₀)
      (foW P c (familyQm P c Qm₀)) (MemoryWalkDeployed.kMem_pos P)
      (MemoryWalkDeployed.kMem_le P) hγ' hbft'
    have hv : BFSValidF (kMemP P) (foW P c (familyQm P c Qm₀)) (memRowsP P) :=
      deployed_bfsValid_memory P c (familyQm P c Qm₀) hsatM hchar
    have hlen : prefixLenF (kMemP P) (foW P c (familyQm P c Qm₀)) (memRowsP P) =
        memRowsP P :=
      prefixLenF_eq_of_bfsValidF (kMemP P) (foW P c (familyQm P c Qm₀)) hv
    have htile : kMemP P + Sf (foW P c (familyQm P c Qm₀)) (memRowsP P) =
        memRowsP P :=
      deployed_tiling_memory P c (familyQm P c Qm₀) hsatM hchar htileα
    obtain ⟨_, hcase⟩ := hpre
    rw [hlen] at hcase
    rcases hcase with ⟨_, hb⟩ | ⟨_, hgt, _⟩
    · rw [← hfo]; exact hb
    · have hgt' : memRowsP P < kMemP P + Sf (foW P c (familyQm P c Qm₀)) (memRowsP P) :=
        hgt
      rw [htile] at hgt'
      exact (lt_irrefl _ hgt').elim
  · exact absurd hmem hα

/-- Projected whole-table `ForestVecBFT` at `encPT` / `clabOfMem`. -/
theorem deployed_forestVecBFT_pt
    (hγ : gamma c.1 ∉ forestPrefixBadGammas (VdM P c Qm₀) (CvdM P c Qm₀)
      (foM P Qm₀ c) (kMemP P) (memRowsP P))
    (hα : alphaM c.1 ∉ walkForestPrefixAlphaEvent
      (curW P c (familyQm P c Qm₀)) (chldW P c (familyQm P c Qm₀))
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P))
    (htileα : c.1 ∉ WalkTilingEvents.memoryTilingEvent
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P)) :
    ForestVecBFT (fun i => encPT (lblM P Qm₀ c i))
      (fun i l => encPT (clabOfMem (lblM P Qm₀ c) i l))
      (foM P Qm₀ c) (kMemP P) (memRowsP P) := by
  have hbft := deployed_forestVecBFT P c Qm₀ hsatM hchar hγ hα htileα
  have hproj := forestVecBFT_map ptProj hbft
  have hV : (fun i => ptProj (VdM P c Qm₀ i)) =
      (fun i => encPT (lblM P Qm₀ c i)) := by
    funext i
    simp only [VdM, encPT]
    rw [pubAt_eq_lblM_pub]
  have hC := forestVecBFT_congr_children
      (V := fun i => ptProj (VdM P c Qm₀ i))
      (Cv := fun i l => ptProj (CvdM P c Qm₀ i l))
      (Cv' := fun i l => encPT (clabOfMem (lblM P Qm₀ c) i l))
      (fun i l hl => encPT_clab_active P c Qm₀ i l hl) hproj
  rw [← hV]; exact hC

end ForestVecBFT

section MemoryTopology

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hsatM hchar hz
include hsatC
include hax hbasis hwidth

/-- **The β-free memory topology of `execOfTraces`** (M′, `m-prime-topo`): every reconstructed
memory tree is in `L_RVT^{FmemTopo,2}`.  Restated: the former conclusion was the production
`MemoryExactTopology` (`RVTWithArity Fmem`, uniform-β `V_mem`) under `hexp0`, unsatisfiable on record rows whenever `γ ≠ 0`;
the production `MemoryExactTopology` is NOT concluded here. -/
theorem execOfTraces_memoryTopology
    (h : TracesWalkHyps P Qc₀ Qm₀ c)
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hα : alphaM c.1 ∉ walkForestPrefixAlphaEvent
      (curW P c (familyQm P c Qm₀)) (chldW P c (familyQm P c Qm₀))
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P)) :
    ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest, RVTWithArity (FmemTopo (K := K)) t := by
  have hfo : foW P c (familyQm P c Qm₀) = foM P Qm₀ c := by
    funext i
    have hw := foW_eq_foM_all P c (familyQm P c Qm₀) i
    rw [MemoryWalkDeployed.Qmh, WalkQueueDeployed.honestQm_familyQm P c Qm₀] at hw
    exact hw
  have hv : BFSValidF (kMemP P) (foM P Qm₀ c) (memRowsP P) := by
    rw [← hfo]
    exact deployed_bfsValid_memory P c (familyQm P c Qm₀) hsatM hchar
  have htile : kMemP P + Sf (foM P Qm₀ c) (memRowsP P) = memRowsP P := by
    rw [← hfo]
    exact deployed_tiling_memory P c (familyQm P c Qm₀) hsatM hchar
      (htileαM_of_good P c Qc₀ Qm₀ hsatM hchar hgood)
  have hγ : gamma c.1 ∉ forestPrefixBadGammas (VdM P c Qm₀) (CvdM P c Qm₀)
      (foM P Qm₀ c) (kMemP P) (memRowsP P) := by
    rw [← forestPrefixBadGammas_VdM_eq_committed P c Qm₀]
    exact hγM_of_good P c Qc₀ Qm₀ hgood
  have hb' := deployed_forestVecBFT_pt P c Qm₀ hsatM hchar hγ hα
    (htileαM_of_good P c Qc₀ Qm₀ hsatM hchar hgood)
  have harity : ∀ i, foM P Qm₀ c i ≤ 2 :=
    fun i => fanoutMem_le_two (lblM P Qm₀ c i).1
  have hF : ∀ i, 1 ≤ i → i ≤ memRowsP P →
      FmemTopo (lblM P Qm₀ c i)
        (fun j : Fin 2 =>
          if (j : ℕ) < foM P Qm₀ c i then
            some (lblM P Qm₀ c (firstCF (kMemP P) (foM P Qm₀ c) i + j))
          else none) := by
    intro i hi1 hih
    refine respects_pt_topo (lblM P Qm₀ c i) _ _ ?_
      (hFcommit_memory_of_good P c Qm₀ hsatM hchar hz i hi1 hih)
    intro j
    by_cases hj : (j : ℕ) < foM P Qm₀ c i
    · have hkey := ForestVecBFT_layout
        (fun i => encPT (lblM P Qm₀ c i))
        (fun i l => encPT (clabOfMem (lblM P Qm₀ c) i l))
        (foM P Qm₀ c) htile hb' hi1 hih hj
      rw [if_pos hj, if_pos hj]
      simp only [Option.map_some]
      exact congrArg some (encPT_label _ _ hkey)
    · rw [if_neg hj, if_neg hj]
  have hrvt := reconForest_RVT (mem_stateSep_topo (K := K)) (kMemP P)
    (foM P Qm₀ c) (lblM P Qm₀ c) (memRowsP P)
    (MemoryWalkDeployed.kMem_pos P) htile hv harity
    (fun i _ _ => rfl) hF
  have hpa := reconForest_properArity (kMemP P) (foM P Qm₀ c)
    (lblM P Qm₀ c) (memRowsP P) (MemoryWalkDeployed.kMem_pos P) htile hv harity
  intro t ht
  exact RVTWithArity.mk' (hrvt t (by
      change t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest
      exact ht))
    (hpa t (by
      change t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest
      exact ht))

omit hax hbasis hwidth in
theorem hαM_of_good
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    alphaM c.1 ∉ walkForestPrefixAlphaEvent
      (curW P c (familyQm P c Qm₀)) (chldW P c (familyQm P c Qm₀))
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P) := by
  have hαM : c.1 ∉ P.memoryForestAlphaEventOf Qm₀ :=
    (P.optimizedFailureEvent_good_components Qc₀ Qm₀ c hgood).2.2.2.2.2.2.2.2.2.1
  have htileα := htileαM_of_good P c Qc₀ Qm₀ hsatM hchar hgood
  have htile : kMemP P + Sf (foW P c (familyQm P c Qm₀)) (memRowsP P) =
      memRowsP P :=
    deployed_tiling_memory P c (familyQm P c Qm₀) hsatM hchar htileα
  have htile' : kMemP P + Sf (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm₀))
      (memRowsP P) = memRowsP P := by
    rw [Sf_foOfMem_eq_foWmem P c Qm₀]; exact htile
  have hmem : alphaM c.1 ∉ walkForestPrefixAlphaEvent
      (curOfMem (committedMemoryV (P.memorySourceEnv Qm₀) (P.memoryBaseEnv Qm₀))
        (gamma c.1))
      (chldOfMem (committedMemoryCv (P.memorySourceEnv Qm₀)) (gamma c.1))
      (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm₀)) (kMemP P) (memRowsP P) :=
    (mem_memoryForestAlphaEventOfEnvs_of_tiling
      (P.memorySourceEnv Qm₀) (P.memoryBaseEnv Qm₀) (kMemP P) htile' c.1).mpr.mt
      (by simpa [OptimizedFullStrictNockVMROMPackage.memoryForestAlphaEventOf] using hαM)
  have heq : walkForestPrefixAlphaEvent
      (curOfMem (committedMemoryV (P.memorySourceEnv Qm₀) (P.memoryBaseEnv Qm₀))
        (gamma c.1))
      (chldOfMem (committedMemoryCv (P.memorySourceEnv Qm₀)) (gamma c.1))
      (WalkTilingEvents.foOfMem (P.memoryBaseEnv Qm₀)) (kMemP P) (memRowsP P) =
      walkForestPrefixAlphaEvent
        (curW P c (familyQm P c Qm₀)) (chldW P c (familyQm P c Qm₀))
        (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P) := by
    refine WalkForestPrefixAlphaEvents.walkForestPrefixAlphaEvent_congr_on
      (kMem_le_memRows P) ?_ ?_ ?_
    · intro i h1 h2
      simp only [curOfMem]
      have hV := VdM_eq_committed P c Qm₀ i h1 h2
      have hcur : curW P c (familyQm P c Qm₀) i =
          rlc (gamma c.1) (VdM P c Qm₀ i) := rfl
      rw [hV, hcur]
    · intro i l h1 h2
      simp only [chldOfMem]
      have hC := CvdM_eq_committed P c Qm₀ i l h1 h2
      have hch : chldW P c (familyQm P c Qm₀) i l =
          rlc (gamma c.1) (CvdM P c Qm₀ i l) := rfl
      rw [hC, hch]
    · intro i h1 h2
      exact foOfMem_eq_foWmem P c Qm₀ i h1 h2
  rwa [heq] at hmem

/-- **Exact remaining hyp.**  `DeployedAcceptanceAt` + priced events give the β-free memory
    topology of `execOfTraces` (M′: `∀ t ∈ memoryForest, RVTWithArity FmemTopo t`, no `hexp0`)
    once `α ∉ walkForestPrefixAlphaEvent`.  That event is the paper's `:1008` `h/|K|`. -/
theorem memoryTopology_of_deployed
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hα : alphaM c.1 ∉ walkForestPrefixAlphaEvent
      (curW P c (familyQm P c Qm₀)) (chldW P c (familyQm P c Qm₀))
      (foW P c (familyQm P c Qm₀)) (kMemP P) (memRowsP P)) :
    ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c
      (tracesWalkHyps_of_deployed P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)).memoryForest,
      RVTWithArity (FmemTopo (K := K)) t :=
  execOfTraces_memoryTopology P c Qc₀ Qm₀ hsatC hsatM hchar hz hax hbasis hwidth
    (tracesWalkHyps_of_deployed P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)
    hgood hα

theorem memoryTopology_of_deployed_of_good
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀) :
    ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c
      (tracesWalkHyps_of_deployed P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth hacc hgood)).memoryForest,
      RVTWithArity (FmemTopo (K := K)) t :=
  memoryTopology_of_deployed P c Qc₀ Qm₀ hsatC hsatM hchar hz hax hbasis hwidth hacc hgood
    (hαM_of_good P c Qc₀ Qm₀ hsatC hsatM hchar hz hgood)

end MemoryTopology

end

end Nock.RedTeam.Batch501
