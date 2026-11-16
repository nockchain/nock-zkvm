/-
  Nock/RedTeam/Batch960Thm54HonestMemoryForestVec.lean

  Both events are functions of the committed memory node vectors `V = committedMemoryV`, child
  vectors `Cv = committedMemoryCv` and fanout column `fo = foOfMem`:
  * prefix-γ: `γ ∈ BadRLCList (curValsV V M) ((curValsV V kMem ++ flatBlksV Cv fo M).take M)`;
  * forest-α: under tiling, `αM` a root of `nodeListP cur M − forestQueueP cur chld fo kMem M` at
    `cur = RLC^γ ∘ V`, `chld = RLC^γ ∘ Cv`, guarded by `¬ IsForestFullBFT`.
  Both are EMPTY for every coin once the VECTOR forest identity
  `curValsV V M = curValsV V kMem ++ flatBlksV Cv fo M` holds (`ForestVecBFT`).

  This file proves that identity at the canonical memory trace of EVERY package:
  * §A, generic: the vector BFS identity of any BFS forest (`forest_vec_identity`), coordinatewise
    from `WalkForest.curVals_curCol_full` / `flatBlks_chldCol`;
  * §B: at the canonical trace, `V (i+1) = x^mem(row i)` (`committedMemoryV_honest`) and, on
    active child slots, `Cv (i+1) l = x^mem(child)` (`committedMemoryCv_honest`), from the
    canonical role lemmas of `MemoryWalkLabelCanonical` and the package's own
    `MemoryWalkLabelObligations` (`childLinkMem`);
  * §C: the two components.

  Status: **proved** (honest-trace identity), for every coin, at every package (no hypothesis).
-/
import Nock.RedTeam.Batch959Thm54HonestMemoryTiling
import Nock.WalkForest
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch960

open Nock
open Nock.Walk

noncomputable section

/-! ## A. The vector BFS identity of a BFS forest -/

section Generic

variable {LT : Type*} {K : Type*} [Field K] {n : ℕ}

/-- Two lists of vectors agree when every coordinate projection agrees (`n > 0`). -/
theorem vec_list_ext (hn : 0 < n) {L₁ L₂ : List (Fin n → K)}
    (h : ∀ k : Fin n, L₁.map (fun v => v k) = L₂.map (fun v => v k)) : L₁ = L₂ := by
  have hlen : L₁.length = L₂.length := by
    simpa using congrArg List.length (h ⟨0, hn⟩)
  apply List.ext_getElem hlen
  intro m h1 h2
  funext k
  have := congrArg (fun L => L[m]?) (h k)
  simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.map_some, Option.some.injEq] at this
  exact this

theorem curValsV_coord (V : ℕ → Fin n → K) (h : ℕ) (k : Fin n) :
    (curValsV V h).map (fun v => v k) = curVals (fun i => V i k) h := by
  simp [curValsV, curVals, List.map_map]

theorem flatBlksV_coord (Cv : ℕ → ℕ → Fin n → K) (fo : ℕ → ℕ) (h : ℕ) (k : Fin n) :
    (flatBlksV Cv fo h).map (fun v => v k) = flatBlks (fun i l => Cv i l k) fo h := by
  induction h with
  | zero => simp [flatBlksV, flatBlks]
  | succ m ih =>
    rw [flatBlksV_succ, flatBlks_succ, List.map_append, ih]
    simp [blkValsV, blkVals, List.map_map]

/-- The vector node column of a BFS row list. -/
def vcur (g : NTree LT → Fin n → K) (W : List (NTree LT)) (i : ℕ) : Fin n → K :=
  ((W[i - 1]?).map g).getD 0

/-- The vector child column of a BFS row list. -/
def vchld (g : NTree LT → Fin n → K) (W : List (NTree LT)) (i l : ℕ) : Fin n → K :=
  (((W[i - 1]?).bind (fun t => t.children[l - 1]?)).map g).getD 0

theorem vcur_coord (g : NTree LT → Fin n → K) (W : List (NTree LT)) (k : Fin n) :
    (fun i => vcur g W i k) = curCol (fun t => g t k) W := by
  funext i
  unfold vcur curCol
  cases W[i - 1]? <;> rfl

theorem vchld_coord (g : NTree LT → Fin n → K) (W : List (NTree LT)) (k : Fin n) :
    (fun i l => vchld g W i l k) = chldCol (fun t => g t k) W := by
  funext i l
  unfold vchld chldCol
  cases (W[i - 1]?).bind (fun t => t.children[l - 1]?) <;> rfl

/-- **The vector forest BFS identity** of `bfsForest l`. -/
theorem forest_vec_identity (hn : 0 < n) (g : NTree LT → Fin n → K) (l : List (NTree LT))
    (hne : l ≠ []) :
    curValsV (vcur g (bfsForest l)) (bfsForest l).length =
      curValsV (vcur g (bfsForest l)) l.length ++
        flatBlksV (vchld g (bfsForest l)) (foCol (bfsForest l)) (bfsForest l).length := by
  apply vec_list_ext hn
  intro k
  rw [List.map_append, curValsV_coord, curValsV_coord, flatBlksV_coord, vcur_coord, vchld_coord,
    curVals_curCol_full, flatBlks_chldCol, List.take_length]
  have hsplit : bfsForest l = l ++ (bfsForest l).flatMap NTree.children :=
    bfsForest_eq_append_flatMap l hne
  have hpre : curVals (curCol (fun t => g t k) (bfsForest l)) l.length =
      l.map (fun t => g t k) := by
    conv_lhs => rw [hsplit]
    exact curVals_curCol_prefix _ l _
  rw [hpre]
  conv_lhs => rw [hsplit]
  rw [List.map_append]

theorem curValsV_congr_on {V V' : ℕ → Fin n → K} {h : ℕ}
    (hV : ∀ i, 1 ≤ i → i ≤ h → V i = V' i) : curValsV V h = curValsV V' h := by
  unfold curValsV
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact hV (i + 1) (by omega) (by omega)

theorem flatBlksV_congr_on {Cv Cv' : ℕ → ℕ → Fin n → K} {fo fo' : ℕ → ℕ} {h : ℕ}
    (hfo : ∀ i, 1 ≤ i → i ≤ h → fo i = fo' i)
    (hCv : ∀ i l, 1 ≤ i → i ≤ h → 1 ≤ l → l ≤ fo i → Cv i l = Cv' i l) :
    flatBlksV Cv fo h = flatBlksV Cv' fo' h := by
  unfold flatBlksV
  apply List.flatMap_congr
  intro i hi
  rw [List.mem_range] at hi
  unfold blkValsV
  rw [← hfo (i + 1) (by omega) (by omega)]
  apply List.map_congr_left
  intro l hl
  rw [List.mem_range] at hl
  exact hCv (i + 1) (l + 1) (by omega) (by omega) (by omega) (by omega)

end Generic

/-! ## B. The committed memory vectors at the canonical trace -/

section Canonical

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.MemoryWalkLabelCanonical
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.MemoryTable

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The `x^mem` label of a walk node. -/
def gMem (t : NTree (MState × DTmem K)) : Fin 6 → K := MemoryTable.memoryLabelVec t.label.2.2

/-- Source role `r < 15` of the canonical row is table column `4 + r` of the exact row. -/
theorem src_role (i : Fin P.optimized.family.problem.cfg.memRows) (r : ℕ) (hr : r < 15) :
    (P.memorySourceEnv (canonicalMemoryTrace P) i).trace r =
      (OptimizedMemorySemanticRealization.exactMemoryRowEnv P.optimized.sampled i).trace (4 + r) := by
  rw [canonical_memorySourceEnv]
  exact canonical_cellRole_cur P.optimized.sampled P.optimized.memoryNodes
    P.optimized.memoryNodes_injective P.optimized.basis P.optimized.memoryChallenge
    P.optimized.memoryPublic P.optimized.orbit P.optimized.memoryCoordinatePins i r hr

theorem src_host (i : Fin P.optimized.family.problem.cfg.memRows) (j : Fin 2) :
    (P.memorySourceEnv (canonicalMemoryTrace P) i).trace (45 + (j : ℕ)) =
      memChildStateTagCol P.optimized.family.memoryWalkRows ((i : ℕ) + 1) j := by
  rw [canonical_memorySourceEnv]
  have h := canonical_host_cur P.optimized.sampled P.optimized.memoryNodes
    P.optimized.memoryNodes_injective P.optimized.basis P.optimized.memoryChallenge
    P.optimized.memoryPublic P.optimized.orbit i j
  fin_cases j <;> simpa [childTagHostRole] using h

/-- **`V (i+1)` at the canonical trace is the row's `x^mem` label.** -/
theorem memRowLabelVec_honest (i : Fin P.optimized.family.problem.cfg.memRows) :
    memRowLabelVec (P.memorySourceEnv (canonicalMemoryTrace P) i)
        (P.memoryBaseEnv (canonicalMemoryTrace P) i) =
      MemoryTable.memoryLabelVec (P.optimized.family.problem.exec.memoryPubAt i) := by
  have hc : ∀ k : Fin 5, (P.memorySourceEnv (canonicalMemoryTrace P) i).trace k =
      cellCoord (P.optimized.family.problem.exec.memoryPubAt i).pt k := by
    intro k
    rw [src_role P i k (by omega)]
    exact exactRow_cellCoord P.optimized.sampled i k
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  have h4 := hc 4
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  have h3' : (P.memorySourceEnv (canonicalMemoryTrace P) i).trace 3 =
      (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator := h3
  have h4' : (P.memorySourceEnv (canonicalMemoryTrace P) i).trace 4 =
      (P.optimized.family.problem.exec.memoryPubAt i).pt.counts := h4
  funext k
  fin_cases k <;>
    simp [memRowLabelVec, MemoryTable.memoryLabelVec, Batch959.memRowState_honest, h0, h1, h2,
      h3', h4', cellCoord]

/-- `Cv (i+1)` slot `j` at the canonical trace is the declared child vector. -/
theorem memRowChildVec_honest (i : Fin P.optimized.family.problem.cfg.memRows) (j : Fin 2) :
    memRowChildVec (P.memorySourceEnv (canonicalMemoryTrace P) i) j =
      childVec (P.optimized.family.problem.exec.memoryPubAt i)
        (fun j => memChildStateTagCol P.optimized.family.memoryWalkRows ((i : ℕ) + 1) j) j := by
  have hc : ∀ k : Fin 5, (P.memorySourceEnv (canonicalMemoryTrace P) i).trace
      (cellBase j + (k : ℕ)) =
      cellCoord (childCell (P.optimized.family.problem.exec.memoryPubAt i) j) k := by
    intro k
    have hr : cellBase j + (k : ℕ) < 15 := by fin_cases j <;> simp [cellBase] <;> omega
    rw [src_role P i _ hr]
    exact exactRow_childCellCoord P.optimized.sampled i j k
  have ht := src_host P i j
  funext k
  fin_cases j <;> fin_cases k
  all_goals
    first
    | simpa [memRowChildVec, childVec] using ht
    | (have := hc 0; simpa [memRowChildVec, childVec, cellBase, cellCoord] using this)
    | (have := hc 1; simpa [memRowChildVec, childVec, cellBase, cellCoord] using this)
    | (have := hc 2; simpa [memRowChildVec, childVec, cellBase, cellCoord] using this)
    | (have := hc 4; simpa [memRowChildVec, childVec, cellBase, cellCoord] using this)
    | (have := hc 3; simpa [memRowChildVec, childVec, cellBase, cellCoord] using this)

end Canonical

/-! ## C. The forest vector identity and the two components -/

section Components

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.MemoryWalkLabel
open Nock.NockVMROM.Thm54.MemoryWalkLabelCanonical
open Nock.NockVMROM.Thm54.WalkPrefixGammaEvents
open Nock.NockVMROM.Thm54.WalkForestPrefixAlphaEvents
open Nock.MemoryTable

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem committedMemoryV_honest (i : ℕ) (hi1 : 1 ≤ i)
    (hiM : i ≤ P.optimized.family.problem.cfg.memRows) :
    committedMemoryV (P.memorySourceEnv (canonicalMemoryTrace P))
        (P.memoryBaseEnv (canonicalMemoryTrace P)) i =
      vcur gMem P.optimized.family.memoryWalkRows i := by
  have hlt : i - 1 < P.optimized.family.problem.cfg.memRows := by omega
  unfold committedMemoryV vcur
  rw [dif_pos ⟨hi1, hlt⟩, memRowLabelVec_honest]
  obtain ⟨t, ht, hl⟩ := memoryWalkRows_getElem?_row (R := P.optimized.family) ⟨i - 1, hlt⟩
  simp only at ht
  rw [ht]
  simp only [Option.map_some, Option.getD_some, gMem, hl]
  rfl

theorem committedMemoryCv_honest (i l : ℕ) (hi1 : 1 ≤ i)
    (hiM : i ≤ P.optimized.family.problem.cfg.memRows) (hl1 : 1 ≤ l)
    (hlfo : l ≤ Walk.foCol P.optimized.family.memoryWalkRows i) :
    committedMemoryCv (P.memorySourceEnv (canonicalMemoryTrace P)) i l =
      vchld gMem P.optimized.family.memoryWalkRows i l := by
  have hlt : i - 1 < P.optimized.family.problem.cfg.memRows := by omega
  set ii : Fin P.optimized.family.problem.cfg.memRows := ⟨i - 1, hlt⟩ with hii
  have htopo := P.optimized.memoryProduction.obligations.2.2.2.2
  obtain ⟨t, ht, hlbl⟩ := memoryWalkRows_getElem?_row (R := P.optimized.family) ii
  obtain ⟨hst, hfan, hlink⟩ := htopo t (List.mem_of_getElem? ht)
  have hpub : P.optimized.family.problem.exec.memoryPubAt ii = t.label.2.2 := by
    show (P.optimized.family.problem.exec.memoryRowAt ii).2.2 = _
    rw [hlbl]
  have hfoi : Walk.foCol P.optimized.family.memoryWalkRows i = t.children.length := by
    unfold Walk.foCol
    have : (ii : ℕ) = i - 1 := rfl
    rw [← this, ht]; rfl
  have hlt2 : l - 1 < t.children.length := by omega
  have hle2 : l - 1 < 2 := by
    have := fanoutMem_le_two t.label.1
    omega
  obtain ⟨c, hc⟩ : ∃ c, t.children[l - 1]? = some c :=
    ⟨t.children[l - 1], List.getElem?_eq_getElem hlt2⟩
  have hcell : c.label.2.2.pt = memCell t.label ⟨l - 1, hle2⟩ := by
    have hlinkj := hlink ⟨l - 1, hle2⟩ (by
      show l - 1 < fanoutMem t.label.1
      rw [hfan]; exact hlt2)
    simp only [Walk.NTree.childLabel, Walk.NTree.childOpt, hc, Option.map_some] at hlinkj
    exact Option.some.inj hlinkj
  have hi' : (ii : ℕ) + 1 = i := by simp [hii]; omega
  have htag : memChildStateTagCol P.optimized.family.memoryWalkRows ((ii : ℕ) + 1) (l - 1) =
      mstateTagField c.label.2.2.st := by
    have : ((ii : ℕ) + 1) - 1 = (ii : ℕ) := by omega
    simp [memChildStateTagCol, this, ht, hc]
  unfold committedMemoryCv vchld
  rw [dif_pos ⟨hi1, hlt⟩, dif_pos hle2]
  rw [show (⟨i - 1, hlt⟩ : Fin _) = ii from rfl, memRowChildVec_honest P ii]
  have hii1 : i - 1 = (ii : ℕ) := rfl
  rw [hii1, ht]
  simp only [Option.bind_some, hc, Option.map_some, Option.getD_some, gMem]
  apply childVec_eq_labelVec
  · exact htag
  · rw [hpub, childCell_eq_memCell, hcell]

/-- **The committed vector forest identity at the canonical memory trace** (every package). -/
theorem committed_forestVec_honest :
    curValsV (committedMemoryV (P.memorySourceEnv (canonicalMemoryTrace P))
        (P.memoryBaseEnv (canonicalMemoryTrace P))) P.optimized.family.problem.cfg.memRows =
      curValsV (committedMemoryV (P.memorySourceEnv (canonicalMemoryTrace P))
          (P.memoryBaseEnv (canonicalMemoryTrace P))) P.optimized.family.problem.cfg.kMem ++
        flatBlksV (committedMemoryCv (P.memorySourceEnv (canonicalMemoryTrace P)))
          (WalkTilingEvents.foOfMem (P.memoryBaseEnv (canonicalMemoryTrace P)))
          P.optimized.family.problem.cfg.memRows := by
  have hkM : P.optimized.family.problem.cfg.kMem ≤ P.optimized.family.problem.cfg.memRows := by
    have h := exact_memory_tiling (R := P.optimized.family)
    omega
  have hV : ∀ h, h ≤ P.optimized.family.problem.cfg.memRows →
      curValsV (committedMemoryV (P.memorySourceEnv (canonicalMemoryTrace P))
        (P.memoryBaseEnv (canonicalMemoryTrace P))) h =
      curValsV (vcur gMem P.optimized.family.memoryWalkRows) h := fun h hh =>
    curValsV_congr_on (fun i h1 h2 => committedMemoryV_honest P i h1 (le_trans h2 hh))
  have hC : flatBlksV (committedMemoryCv (P.memorySourceEnv (canonicalMemoryTrace P)))
        (WalkTilingEvents.foOfMem (P.memoryBaseEnv (canonicalMemoryTrace P)))
        P.optimized.family.problem.cfg.memRows =
      flatBlksV (vchld gMem P.optimized.family.memoryWalkRows)
        (Walk.foCol P.optimized.family.memoryWalkRows) P.optimized.family.problem.cfg.memRows :=
    flatBlksV_congr_on (fun i h1 h2 => Batch959.foOfMem_honest P i h1 h2)
      (fun i l h1 h2 hl1 hl2 => committedMemoryCv_honest P i l h1 h2 hl1
        (by rw [← Batch959.foOfMem_honest P i h1 h2]; exact hl2))
  rw [hV _ le_rfl, hV _ hkM, hC]
  have hW : P.optimized.family.memoryWalkRows =
      bfsForest P.optimized.family.problem.exec.memoryForest := rfl
  have hlenW := exact_memory_walkRows_length (R := P.optimized.family)
  have hk := P.optimized.family.problem.exec.memory_root_count
  have := forest_vec_identity (by norm_num : 0 < 6) gMem
    P.optimized.family.problem.exec.memoryForest
    P.optimized.family.problem.exec.memoryForest_nonempty
  rw [← hW, hlenW, hk] at this
  exact this

theorem badRLCList_self {n : ℕ} (L : List (Fin n → K)) : BadRLCList L L = ∅ := by
  ext γ
  simp [BadRLCList]

/-- **Component 9 at the honest instance**: the memory prefix-γ event is empty at the canonical
trace, for every coin, at every package. -/
theorem memoryPrefixGamma_empty_honest :
    P.memoryPrefixGammaEventOf (canonicalMemoryTrace P) = ∅ := by
  ext ω
  simp only [Finset.notMem_empty, iff_false]
  intro hω
  have h := (memoryPrefixGammaEventOfEnvs_eq_prefix _ _ _ ω).1 hω
  unfold forestPrefixBadGammas at h
  rw [← committed_forestVec_honest P, List.take_of_length_le (by rw [curValsV_length])] at h
  rw [badRLCList_self] at h
  exact Finset.notMem_empty _ h

/-- **Component 10 at the honest instance**: the memory forest α-event is empty at the canonical
trace, for every coin, at every package. -/
theorem memoryForestAlpha_empty_honest :
    P.memoryForestAlphaEventOf (canonicalMemoryTrace P) = ∅ := by
  ext ω
  simp only [Finset.notMem_empty, iff_false]
  intro hω
  unfold OptimizedFullStrictNockVMROMPackage.memoryForestAlphaEventOf
    memoryForestAlphaEventOfEnvs memoryForestAlphaEventConsumed at hω
  split_ifs at hω with htile
  · rw [mem_memoryForestAlphaEvent_iff] at hω
    have hfull : IsForestFullBFT
        (curOfMem (committedMemoryV (P.memorySourceEnv (canonicalMemoryTrace P))
          (P.memoryBaseEnv (canonicalMemoryTrace P))) (gamma ω))
        (chldOfMem (committedMemoryCv (P.memorySourceEnv (canonicalMemoryTrace P))) (gamma ω))
        (WalkTilingEvents.foOfMem (P.memoryBaseEnv (canonicalMemoryTrace P)))
        P.optimized.family.problem.cfg.kMem P.optimized.family.problem.cfg.memRows := by
      unfold IsForestFullBFT
      rw [nodeListP_eq_lpoly_gen, forestQueueP_eq_lpoly]
      unfold curOfMem chldOfMem
      rw [curVals_rlc, curVals_rlc, flatBlks_rlc, ← List.map_append,
        ← committed_forestVec_honest P]
    unfold walkForestPrefixAlphaEvent at hω
    rw [if_pos hfull] at hω
    exact Finset.notMem_empty _ hω
  · exact Finset.notMem_empty _ hω

end Components

end

end Nock.RedTeam.Batch960

#print axioms Nock.RedTeam.Batch960.forest_vec_identity
#print axioms Nock.RedTeam.Batch960.committed_forestVec_honest
#print axioms Nock.RedTeam.Batch960.memoryPrefixGamma_empty_honest
#print axioms Nock.RedTeam.Batch960.memoryForestAlpha_empty_honest
