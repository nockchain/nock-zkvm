/-
  Nock/NockVMROM/Thm54/P8Core/ExecOfTraces.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.ExecOfTraces`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/ExecOfTraces.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.FamilyComputeRows
import Nock.NockVMROM.Thm54.P8Core.StrategyOfTraces
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.ExecOfTraces

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- 0-indexed compute label: state + `(decodeInputs, decodePub, decodeDec)`
at `rowEnvAt P c (familyQc P c Qc) i` — the family chip that reads `c`.
Mentions `Qc`. -/
def lblCAt
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    State × DTcomp K :=
  let env := rowEnvAt P c (familyQc P c Qc) i
  let st := computeStateOf (decodeSource env)
  (st, (decodeInputs env, decodePub env st, decodeDec env))

/-- 1-indexed compute label (`Walk.lean` BFS positions start at 1).
Out of range reads row 0 of `Qc`. Mentions `Qc`. -/
def lblC
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ℕ → State × DTcomp K :=
  fun i =>
    if h : i - 1 < P.optimized.family.problem.cfg.compRows then
      lblCAt P Qc c ⟨i - 1, h⟩
    else
      lblCAt P Qc c ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩

/-- Memory public decoded from `memorySourceEnvAt` (family chip at `c`).
Deployed `6/55` source layout:
* `pt.noun` roles `0..2`; `pt.indicator` / `pt.counts` roles `3` / `4`
* `lc` roles `5..9`; `rc` roles `10..14`
* `mem.root` / `mem.child` roles `19..21` / `22..24` (`memRowRecord` / `recordRLCExpr`)
* `mem.axis` / `mem.ts` roles `25` / `26` (`encRec` / `memRowRecord`)
* `ipre` / `icur` roles `27` / `28` (`intermediateInitGate` / `TerminalGate`)
* `ver` role `39` — selects `IO_mem` rows
`lcSt` is the parent state on `read_root` / `verify_child`; otherwise `halt`.
Mentions `Qm`. -/
def decodeMemPub
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    MemoryTable.Pub K :=
  let envF := memoryBaseEnvAt P c Qm i
  let envK := memorySourceEnvAt P c Qm i
  let st := memoryStateOf envF
  { st := st
    pt := ⟨memoryPtNoun envK, envK.trace 3, envK.trace 4⟩
    lc := ⟨⟨envK.trace 5, envK.trace 6, envK.trace 7⟩, envK.trace 8, envK.trace 9⟩
    rc := ⟨⟨envK.trace 10, envK.trace 11, envK.trace 12⟩, envK.trace 13, envK.trace 14⟩
    lcSt :=
      match st with
      | .read_root | .verify_child => st
      | _ => .halt
    rcSt := .halt
    mem := ⟨memoryMemRoot envK, memoryMemChild envK, envK.trace 25, envK.trace 26⟩
    ipre := envK.trace 27
    icur := envK.trace 28
    ver := decide (envK.trace 39 = 1)
    cprime? := some (envK.trace 57)
    lambda? := some (envK.chal 8) }

/-- A6: decoded `λ` is challenge slot 8 (`lamE`), not the `Pub.lambda` default `1`. -/
theorem decodeMemPub_lambda
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (decodeMemPub P Qm c i).lambda = (memorySourceEnvAt P c Qm i).chal 8 := by
  simp [decodeMemPub, Pub.lambda]

/-- A6: decoded `C'` is 𝕂-role 57 (`recC'`), not the `Pub.cprime` default `1`. -/
theorem decodeMemPub_cprime
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (decodeMemPub P Qm c i).cprime = (memorySourceEnvAt P c Qm i).trace 57 := by
  simp [decodeMemPub, Pub.cprime]

/-- 0-indexed memory label.  Mentions `Qm`.  Inputs are the coins of `c`
so they match `cfgOfTraces.challenges.memoryInputs`.
`β := −interPole` so `MemoryTable.pole = RLC − β` agrees with chip
`poleSource = interPole + RLC`. -/
def lblMAt
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    MState × DTmem K :=
  let st := memoryStateOf (memoryBaseEnvAt P c Qm i)
  (st, ({ z := nprSeed c.1, β := -(c.2.2.2.interPole), γ := c.2.1.1 },
    decodeMemPub P Qm c i))

/-- 1-indexed memory label.  Mentions `Qm`. -/
def lblM
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ℕ → MState × DTmem K :=
  fun i =>
    if h : i - 1 < P.optimized.family.problem.cfg.memRows then
      lblMAt P Qm c ⟨i - 1, h⟩
    else
      lblMAt P Qm c ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩

/-- Compute fanout from the decoded state's `StateSep` (`fanoutComp`). Mentions `Qc`. -/
def foC
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ℕ → ℕ :=
  fun i => fanoutComp (lblC P Qc c i).1

/-- Memory fanout from the decoded state's `StateSep` (`fanoutMem`). Mentions `Qm`. -/
def foM
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ℕ → ℕ :=
  fun i => fanoutMem (lblM P Qm c i).1

/-- Active compute labels, in AIR order, read off `Qc`. -/
def computeLabelList
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    List (State × DTcomp K) :=
  (List.finRange P.optimized.family.problem.cfg.compRows).map (lblCAt P Qc c)

/-- Active memory labels, in AIR order, read off `Qm`. -/
def memoryLabelList
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    List (MState × DTmem K) :=
  (List.finRange P.optimized.family.problem.cfg.memRows).map (lblMAt P Qm c)

theorem computeLabelList_length
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (computeLabelList P Qc c).length = P.optimized.family.problem.cfg.compRows := by
  simp [computeLabelList]

theorem memoryLabelList_length
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (memoryLabelList P Qm c).length = P.optimized.family.problem.cfg.memRows := by
  simp [memoryLabelList]

theorem lblM_succ
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    lblM P Qm c (i.val + 1) = lblMAt P Qm c i := by
  have h : (i.val + 1) - 1 < P.optimized.family.problem.cfg.memRows := by
    simpa [Nat.add_sub_cancel] using i.isLt
  simp [lblM, h]

/-- Family decode: `lblCAt` is the `rowEnvAt` triple. -/
theorem lblCAt_eq_rowEnvAt
    (Qc : Fin P.computeChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    lblCAt P Qc c i =
      (computeStateOf (decodeSource (rowEnvAt P c (familyQc P c Qc) i)),
        (decodeInputs (rowEnvAt P c (familyQc P c Qc) i),
          decodePub (rowEnvAt P c (familyQc P c Qc) i)
            (computeStateOf (decodeSource (rowEnvAt P c (familyQc P c Qc) i))),
          decodeDec (rowEnvAt P c (familyQc P c Qc) i))) :=
  rfl

/-- Config whose row counts are the decoded `Qc`/`Qm` lists (equal to the
chips' `H.card` / package budgets) and whose coins are `c` (`a,b,c` after
NN; `α = alphaM`; `z = nprSeed`; `γ` is the IO/record-RLC coin;
`β := −interPole` so table `pole = RLC − β` matches chip `poleSource`.  Honest generate-path
configs may keep `β = 0` with a separate `memoryExtensionFold`; the hostile
decode path follows the paper/chip convention. -/
def cfgOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ExactConfig F K where
  challenges :=
    { a := c.2.2.1.eqA
      b := c.2.2.1.eqB
      c := c.2.2.1.eqC
      α := alphaM c.1
      z := nprSeed c.1
      β := -(c.2.2.2.interPole)
      γ := c.2.1.1
      -- Form R `λ`: the sampled coin (memory chip slot `8` / compute slot `9`,
      -- `DeployedChipFamily.memoryKOfTuple_lambda`), which `decodeMemPub` writes as every
      -- row's `lambda?`
      lam := c.2.2.2.lambda }
  Ksz := P.optimized.family.problem.cfg.Ksz
  kMem := P.optimized.family.problem.cfg.kMem
  orbit := P.optimized.family.problem.cfg.orbit
  orbit_h_pos := P.optimized.family.problem.cfg.orbit_h_pos
  compRows := (computeLabelList P Qc c).length
  memRows := (memoryLabelList P Qm c).length
  compRows_pos := by
    rw [computeLabelList_length]
    exact P.optimized.family.problem.cfg.compRows_pos
  memRows_pos := by
    rw [memoryLabelList_length]
    exact P.optimized.family.problem.cfg.memRows_pos
  compRows_le := by
    rw [computeLabelList_length]
    exact P.optimized.family.problem.cfg.compRows_le
  memRows_le := by
    rw [memoryLabelList_length]
    exact P.optimized.family.problem.cfg.memRows_le
  eDeg := P.optimized.family.problem.cfg.eDeg
  eDeg_eq_one := P.optimized.family.problem.cfg.eDeg_eq_one
  compNodes := fun i =>
    P.optimized.family.problem.cfg.orbit.βcoset *
      P.optimized.family.problem.cfg.orbit.ω ^ (i : ℕ)
  compNodes_spec := fun i => rfl
  memNodes := fun i =>
    P.optimized.family.problem.cfg.orbit.βcoset *
      P.optimized.family.problem.cfg.orbit.ω ^ (i : ℕ)
  memNodes_spec := fun i => rfl

theorem cfgOfTraces_compRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (cfgOfTraces P Qc Qm c).compRows = P.optimized.family.problem.cfg.compRows :=
  computeLabelList_length P Qc c

theorem cfgOfTraces_memRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (cfgOfTraces P Qc Qm c).memRows = P.optimized.family.problem.cfg.memRows :=
  memoryLabelList_length P Qm c

theorem cfgOfTraces_kMem
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    (cfgOfTraces P Qc Qm c).kMem = P.optimized.family.problem.cfg.kMem :=
  rfl

/-- Walk-tiling facts needed by `bfsForest_reconTree` / `bfsForest_reconForest`.
These are walk-gate obligations; carried until step 5.  Mentions `Qc` and `Qm`. -/
structure TracesWalkHyps
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) : Prop where
  sfCompute :
    Sf (foC P Qc c) P.optimized.family.problem.cfg.compRows + 1 =
      P.optimized.family.problem.cfg.compRows
  validCompute :
    BFSValid (foC P Qc c) P.optimized.family.problem.cfg.compRows
  sfMemory :
    P.optimized.family.problem.cfg.kMem +
        Sf (foM P Qm c) P.optimized.family.problem.cfg.memRows =
      P.optimized.family.problem.cfg.memRows
  validMemory :
    BFSValidF P.optimized.family.problem.cfg.kMem (foM P Qm c)
      P.optimized.family.problem.cfg.memRows

private theorem family_kMem_pos :
    1 ≤ P.optimized.family.problem.cfg.kMem := by
  have hpos : 0 < P.objects.cfg.kMem := P.objects.exec.memoryRootCount_pos
  have hk := congrArg ExactConfig.kMem P.optimized.family_cfg
  rw [← hk] at hpos
  exact hpos

theorem tracesKMem_pos
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    1 ≤ (cfgOfTraces P Qc Qm c).kMem := by
  rw [cfgOfTraces_kMem]
  exact family_kMem_pos P

/-- Inverse-BFS execution: compute tree from `Qc` (package `N` rows),
memory forest from `Qm`.  Length fields transport along
`cfgOfTraces_compRows` / `_memRows`. -/
def execOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    ExactExecution (cfgOfTraces P Qc Qm c) where
  computeTree :=
    reconTree (foC P Qc c) (lblC P Qc c)
      P.optimized.family.problem.cfg.compRows
  memoryForest :=
    reconForest P.optimized.family.problem.cfg.kMem (foM P Qm c) (lblM P Qm c)
      P.optimized.family.problem.cfg.memRows
  memoryForest_nonempty := by
    have hk := family_kMem_pos P
    intro hempty
    have hlen := congrArg List.length hempty
    simp [reconForest, List.length_map, List.length_range'] at hlen
    exact (Nat.ne_of_gt (Nat.succ_le_iff.mp hk) hlen)
  memory_root_count := by
    simpa [reconForest, List.length_map, List.length_range'] using
      (cfgOfTraces_kMem P Qc Qm c).symm
  compute_bfs_length := by
    rw [bfsForest_reconTree (foC P Qc c) (lblC P Qc c)
      P.optimized.family.problem.cfg.compRows h.sfCompute h.validCompute]
    simp [List.length_map, List.length_range']
    exact (cfgOfTraces_compRows P Qc Qm c).symm
  memory_bfs_length := by
    have hk := family_kMem_pos P
    rw [bfsForest_reconForest P.optimized.family.problem.cfg.kMem (foM P Qm c)
      (lblM P Qm c) P.optimized.family.problem.cfg.memRows hk h.sfMemory
      h.validMemory]
    simp [List.length_map, List.length_range']
    exact (cfgOfTraces_memRows P Qc Qm c).symm

theorem execOfTraces_memoryRows
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    (execOfTraces P Qc Qm c h).memoryRows =
      (List.range' 1 (cfgOfTraces P Qc Qm c).memRows).map (lblM P Qm c) := by
  have hM := cfgOfTraces_memRows P Qc Qm c
  have hk := family_kMem_pos P
  unfold ExactExecution.memoryRows execOfTraces
  rw [reconForest_labels P.optimized.family.problem.cfg.kMem (foM P Qm c)
    (lblM P Qm c) P.optimized.family.problem.cfg.memRows hk h.sfMemory
    h.validMemory]
  rw [hM]

end

end Nock.NockVMROM.Thm54.ExecOfTraces
