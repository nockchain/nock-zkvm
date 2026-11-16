/-
  Nock/NockVMROM/Thm54/ExecOfTracesPrefix.lean

  A TRUNCATION constructor beside
  `ExecOfTraces.execOfTraces` (not a redefinition).

  `execOfTraces` builds the compute tree over the WHOLE decoded table
  (`compRows = N`) and needs `TracesWalkHyps` — whole-table tiling
  `Sf foC N + 1 = N` and queue-validity `BFSValid foC N`.  The prefix route (`Nock/WalkPrefix.lean`) forces
  them at `k = Walk.prefixLen (foC) N` instead: `BFSValid foC k` always
  (`Walk.bfsValid_prefixLen`), and the tiling `Sf foC k + 1 = k` whenever the
  prefix is proper (`Walk.prefixLen_tiling_of_lt`).

  This module builds the execution on rows `1..k` only:
  * `cfgOfTracesPrefix` — `cfgOfTraces` with `compRows := k`;
  * `PrefixWalkHyps` — the compute tiling at `k` plus the UNCHANGED memory half of
    `TracesWalkHyps`;
  * `execOfTracesPrefix` — `reconTree foC lblC k`, the memory forest as before;
  * `prefixWalkHyps_of_tracesWalkHyps` / `execOfTracesPrefix_rows_eq_of_hyps` —
    conservative: where `TracesWalkHyps` holds the prefix IS the whole table.

  Paper: the paper (`Thm:Walk_IOP`), `:2263`, `:2276-2281`.
-/
import Nock.WalkPrefix
import Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.ExecOfTracesPrefix

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The queue-empty prefix length of the decoded compute table. -/
def prefixRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : ℕ :=
  prefixLen (foC P Qc c) P.optimized.family.problem.cfg.compRows

theorem prefixRows_le
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    prefixRows P Qc c ≤ P.optimized.family.problem.cfg.compRows :=
  prefixLen_le _ _

theorem prefixRows_pos
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    0 < prefixRows P Qc c :=
  one_le_prefixLen _ P.optimized.family.problem.cfg.compRows_pos

theorem bfsValid_prefixRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    BFSValid (foC P Qc c) (prefixRows P Qc c) :=
  bfsValid_prefixLen _ _

/-- `cfgOfTraces` with the compute table truncated to its queue-empty prefix. -/
def cfgOfTracesPrefix
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ExactConfig F K where
  challenges := (cfgOfTraces P Qc Qm c).challenges
  Ksz := (cfgOfTraces P Qc Qm c).Ksz
  kMem := (cfgOfTraces P Qc Qm c).kMem
  orbit := (cfgOfTraces P Qc Qm c).orbit
  orbit_h_pos := (cfgOfTraces P Qc Qm c).orbit_h_pos
  compRows := prefixRows P Qc c
  memRows := (cfgOfTraces P Qc Qm c).memRows
  compRows_pos := prefixRows_pos P Qc c
  memRows_pos := (cfgOfTraces P Qc Qm c).memRows_pos
  compRows_le :=
    le_trans (prefixRows_le P Qc c) P.optimized.family.problem.cfg.compRows_le
  memRows_le := (cfgOfTraces P Qc Qm c).memRows_le
  eDeg := (cfgOfTraces P Qc Qm c).eDeg
  eDeg_eq_one := (cfgOfTraces P Qc Qm c).eDeg_eq_one
  compNodes := fun i =>
    P.optimized.family.problem.cfg.orbit.βcoset *
      P.optimized.family.problem.cfg.orbit.ω ^ (i : ℕ)
  compNodes_spec := fun _ => rfl
  memNodes := (cfgOfTraces P Qc Qm c).memNodes
  memNodes_spec := (cfgOfTraces P Qc Qm c).memNodes_spec

theorem cfgOfTracesPrefix_compRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (cfgOfTracesPrefix P Qc Qm c).compRows = prefixRows P Qc c := rfl

/-- The prefix analogue of `TracesWalkHyps`: compute tiling at the PREFIX (queue-validity at
the prefix is a theorem, `bfsValid_prefixRows`), memory half unchanged. -/
structure PrefixWalkHyps
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Prop where
  sfPrefix : Sf (foC P Qc c) (prefixRows P Qc c) + 1 = prefixRows P Qc c
  sfMemory :
    P.optimized.family.problem.cfg.kMem +
        Sf (foM P Qm c) P.optimized.family.problem.cfg.memRows =
      P.optimized.family.problem.cfg.memRows
  validMemory :
    BFSValidF P.optimized.family.problem.cfg.kMem (foM P Qm c)
      P.optimized.family.problem.cfg.memRows

/-- **The compute tiling at the prefix is DERIVED whenever the prefix is proper.** -/
theorem sfPrefix_of_lt
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hlt : prefixRows P Qc c < P.optimized.family.problem.cfg.compRows) :
    Sf (foC P Qc c) (prefixRows P Qc c) + 1 = prefixRows P Qc c :=
  prefixLen_tiling_of_lt _ P.optimized.family.problem.cfg.compRows_pos hlt

/-- The dichotomy: the tiling at the prefix holds unless the prefix is the whole table and the
whole table overflows (`1 + Sf foC N > N`, the zero-label case of `Walk.PrefixBFT`). -/
theorem sfPrefix_or_overflow
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    Sf (foC P Qc c) (prefixRows P Qc c) + 1 = prefixRows P Qc c ∨
      (prefixRows P Qc c = P.optimized.family.problem.cfg.compRows ∧
        P.optimized.family.problem.cfg.compRows <
          Sf (foC P Qc c) P.optimized.family.problem.cfg.compRows + 1) := by
  rcases lt_or_eq_of_le (prefixRows_le P Qc c) with hlt | heq
  · exact Or.inl (sfPrefix_of_lt P Qc c hlt)
  · by_cases ht : Sf (foC P Qc c) (prefixRows P Qc c) + 1 = prefixRows P Qc c
    · exact Or.inl ht
    · right
      refine ⟨heq, ?_⟩
      have hv := bfsValid_prefixRows P Qc c
      rw [heq] at hv ht
      have hN : 1 ≤ P.optimized.family.problem.cfg.compRows :=
        P.optimized.family.problem.cfg.compRows_pos
      have hge := hv P.optimized.family.problem.cfg.compRows hN le_rfl
      -- `BFSValid` at `N` gives `N ≤ Sf foC (N − 1) + 1 ≤ Sf foC N + 1`; not equal, so `<`.
      have hmono : Sf (foC P Qc c) (P.optimized.family.problem.cfg.compRows - 1) ≤
          Sf (foC P Qc c) P.optimized.family.problem.cfg.compRows :=
        Sf_mono _ (Nat.sub_le _ _)
      omega

/-- **Truncation constructor.**  The compute tree is `reconTree foC lblC k` over the prefix; the
memory forest is `execOfTraces`' own. -/
def execOfTracesPrefix
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : PrefixWalkHyps P Qc Qm c) :
    ExactExecution (cfgOfTracesPrefix P Qc Qm c) where
  computeTree := reconTree (foC P Qc c) (lblC P Qc c) (prefixRows P Qc c)
  memoryForest :=
    reconForest P.optimized.family.problem.cfg.kMem (foM P Qm c) (lblM P Qm c)
      P.optimized.family.problem.cfg.memRows
  memoryForest_nonempty := by
    have hk := tracesKMem_pos P Qc Qm c
    rw [cfgOfTraces_kMem] at hk
    intro hempty
    have hlen := congrArg List.length hempty
    simp [reconForest, List.length_map, List.length_range'] at hlen
    exact (Nat.ne_of_gt (Nat.succ_le_iff.mp hk) hlen)
  memory_root_count := by
    simpa [reconForest, List.length_map, List.length_range'] using
      (cfgOfTraces_kMem P Qc Qm c).symm.trans (rfl : _ = (cfgOfTracesPrefix P Qc Qm c).kMem)
  compute_bfs_length := by
    rw [bfsForest_reconTree (foC P Qc c) (lblC P Qc c) (prefixRows P Qc c) h.sfPrefix
      (bfsValid_prefixRows P Qc c)]
    simp [List.length_map, List.length_range']
    rfl
  memory_bfs_length := by
    have hk := tracesKMem_pos P Qc Qm c
    rw [cfgOfTraces_kMem] at hk
    rw [bfsForest_reconForest P.optimized.family.problem.cfg.kMem (foM P Qm c)
      (lblM P Qm c) P.optimized.family.problem.cfg.memRows hk h.sfMemory h.validMemory]
    simp [List.length_map, List.length_range']
    exact (cfgOfTraces_memRows P Qc Qm c).symm

/-- The prefix execution's compute rows are the decoded labels of rows `1..k`. -/
theorem execOfTracesPrefix_computeRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : PrefixWalkHyps P Qc Qm c) :
    (execOfTracesPrefix P Qc Qm c h).computeRows =
      (List.range' 1 (prefixRows P Qc c)).map (lblC P Qc c) := by
  unfold ExactExecution.computeRows execOfTracesPrefix
  exact reconTree_labels (foC P Qc c) (lblC P Qc c) (prefixRows P Qc c) h.sfPrefix
    (bfsValid_prefixRows P Qc c)

/-- **Conservative:** whole-table hypotheses force the prefix to be the whole table. -/
theorem prefixRows_eq_of_tracesWalkHyps
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    prefixRows P Qc c = P.optimized.family.problem.cfg.compRows :=
  prefixLen_eq_of_bfsValid _ h.validCompute

theorem prefixWalkHyps_of_tracesWalkHyps
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    PrefixWalkHyps P Qc Qm c where
  sfPrefix := by rw [prefixRows_eq_of_tracesWalkHyps P Qc Qm c h]; exact h.sfCompute
  sfMemory := h.sfMemory
  validMemory := h.validMemory

/-- Where `TracesWalkHyps` holds, the prefix execution's compute rows are `execOfTraces`'. -/
theorem execOfTracesPrefix_rows_eq_of_hyps
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    (execOfTracesPrefix P Qc Qm c (prefixWalkHyps_of_tracesWalkHyps P Qc Qm c h)).computeRows =
      (execOfTraces P Qc Qm c h).computeRows := by
  rw [execOfTracesPrefix_computeRows, execOfTraces_computeRows,
    prefixRows_eq_of_tracesWalkHyps P Qc Qm c h, cfgOfTraces_compRows]

/-- **Whole-table hypotheses are FALSE on a proper prefix** — the garbage case
(`Batch469`'s `fo = (0,0,2,0,2)` shape has `prefixLen = 1 < 5`): `execOfTraces` is not
constructible there, while `execOfTracesPrefix` is. -/
theorem not_tracesWalkHyps_of_prefix_lt
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hlt : prefixRows P Qc c < P.optimized.family.problem.cfg.compRows) :
    ¬ TracesWalkHyps P Qc Qm c := by
  intro h
  have := prefixRows_eq_of_tracesWalkHyps P Qc Qm c h
  omega

/-- On a proper prefix the truncated configuration has strictly fewer compute rows than the one
`AcceptedContent` is stated over (`cfgOfTraces_compRows`). -/
theorem cfgOfTracesPrefix_compRows_lt
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (hlt : prefixRows P Qc c < P.optimized.family.problem.cfg.compRows) :
    (cfgOfTracesPrefix P Qc Qm c).compRows < (cfgOfTraces P Qc Qm c).compRows := by
  rw [cfgOfTracesPrefix_compRows, cfgOfTraces_compRows]; exact hlt

end

end Nock.NockVMROM.Thm54.ExecOfTracesPrefix
