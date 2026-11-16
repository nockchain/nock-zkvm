/-
  Nock/NockVMROM/Thm54/P8Core/Batch1011Thm54AxisViewBindsAtCoin.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch1011Thm54AxisViewBindsAtCoin`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch1011Thm54AxisViewBindsAtCoin.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1010Thm54AxisViewMemoryTreeBinds
import Nock.NockVMROM.Thm54.P8Core.Batch974Thm54Round0WrapJoinForest
import Nock.NockVMROM.Thm54.P8Core.MemoryHaltAtomDecode
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch1011

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.MemoryTable
open Nock.ComputeTable (MemRec)
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0A
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.NockVMROM.Thm54.WalkTilingEvents (memRowStateOf)
open Nock.RedTeam.Batch516 (ServedFingerprint)
open Nock.RedTeam.Batch973 (expR)

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-- The 0-indexed decoded memory label (the original `ExecOfTraces.lblMAt`; the lifted one is `rfl`
to it, `Batch940.lblMAt_eq`). -/
abbrev L (k : Fin P.optimized.family.problem.cfg.memRows) : MState × DTmem K :=
  ExecOfTraces.lblMAt P (honestQm P c Qm) c k

/-- The decoded forest of the lifted `execOfTraces` — the round-0 strategy's specialized memory
forest on accepted traces outside the event (`Batch974.specialized_memoryForest_R0_eq`). -/
abbrev Fdec (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c) :
    List (NTree (MState × DTmem K)) :=
  (StrategyOfTracesLift.execOfTraces P.optimized (honestQc P c Qc) (honestQm P c Qm) c h).memoryForest

/-- The round-0 recovered axis of a row of the traces. -/
abbrev axR0 : MState × DTmem K → ℕ :=
  axOfRowsR0 P.optimized (honestQc P c Qc) (honestQm P c Qm) c

/-- The `k`-th reconstructed tree (root at row `k + 1`). -/
abbrev treeAt (k : Fin P.optimized.family.problem.cfg.memRows) : NTree (MState × DTmem K) :=
  buildTF P.optimized.family.problem.cfg.kMem
    (StrategyOfTracesLift.foM P.optimized (honestQm P c Qm) c)
    (StrategyOfTracesLift.lblM P.optimized (honestQm P c Qm) c)
    P.optimized.family.problem.cfg.memRows (k.val + 1)

theorem treeAt_label (k : Fin P.optimized.family.problem.cfg.memRows) :
    (treeAt P c Qm k).label = L P c Qm k := by
  rw [buildTF_label]
  exact ExecOfTraces.lblM_succ P (honestQm P c Qm) c k

/-- The `k`-th tree is a node of the decoded forest. -/
theorem treeAt_mem
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (k : Fin P.optimized.family.problem.cfg.memRows) :
    treeAt P c Qm k ∈ bfsForest (Fdec P c Qc Qm h) := by
  have hk := StrategyOfTracesLift.family_kMem_pos P.optimized
  show _ ∈ bfsForest (reconForest P.optimized.family.problem.cfg.kMem
    (StrategyOfTracesLift.foM P.optimized (honestQm P c Qm) c)
    (StrategyOfTracesLift.lblM P.optimized (honestQm P c Qm) c)
    P.optimized.family.problem.cfg.memRows)
  rw [bfsForest_reconForest _ _ _ _ hk h.sfMemory h.validMemory]
  exact List.mem_map.2 ⟨k.val + 1, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩

/-- **Every node of the decoded forest is some `lblMAt k`.** -/
theorem label_of_inTree
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {t node : NTree (MState × DTmem K)} (ht : t ∈ Fdec P c Qc Qm h) (hin : InTree t node) :
    ∃ k : Fin P.optimized.family.problem.cfg.memRows, node.label = L P c Qm k := by
  have hmem : node ∈ bfsForest (Fdec P c Qc Qm h) := (mem_bfsForest _ _).2 ⟨t, ht, hin⟩
  have hk := StrategyOfTracesLift.family_kMem_pos P.optimized
  change node ∈ bfsForest (reconForest P.optimized.family.problem.cfg.kMem
    (StrategyOfTracesLift.foM P.optimized (honestQm P c Qm) c)
    (StrategyOfTracesLift.lblM P.optimized (honestQm P c Qm) c)
    P.optimized.family.problem.cfg.memRows) at hmem
  rw [bfsForest_reconForest _ _ _ _ hk h.sfMemory h.validMemory] at hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hmem
  obtain ⟨hi1, hi2⟩ := List.mem_range'_1.1 hi
  refine ⟨⟨i - 1, by omega⟩, ?_⟩
  rw [buildTF_label]
  have := ExecOfTraces.lblM_succ P (honestQm P c Qm) c ⟨i - 1, by omega⟩
  simp only at this
  rw [show i - 1 + 1 = i by omega] at this
  exact this

theorem L_state (k : Fin P.optimized.family.problem.cfg.memRows) :
    (L P c Qm k).1 = memRowStateOf (memEnvF P c Qm k) :=
  Batch844.memoryStateOf_eq_memRowStateOf _

theorem L_st (k : Fin P.optimized.family.problem.cfg.memRows) :
    (L P c Qm k).2.2.st = memRowStateOf (memEnvF P c Qm k) :=
  Batch844.memoryStateOf_eq_memRowStateOf _

theorem L_lambda (k : Fin P.optimized.family.problem.cfg.memRows) :
    (L P c Qm k).2.2.lambda = c.2.2.2.lambda :=
  HostilePoleAlignment.memorySourceEnvAt_chal8 P c (honestQm P c Qm) k

theorem L_seed (k : Fin P.optimized.family.problem.cfg.memRows) :
    (L P c Qm k).2.1.z = nprSeed c.1 := rfl

theorem L_ver (k : Fin P.optimized.family.problem.cfg.memRows) :
    (L P c Qm k).2.2.ver = decide ((memEnvK P c Qm k).trace 39 = 1) := rfl

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hacc hgood hax hbasis hwidth

theorem eqBlk_at (k : Fin P.optimized.family.problem.cfg.memRows) :
    (L P c Qm k).2.2.st = (L P c Qm k).1 ∧ eqBlk (L P c Qm k).2.1 (L P c Qm k).2.2 := by
  have htop := Batch974.decoded_topology P c Qc Qm hacc hgood hax hbasis hwidth
  have hF := Batch509.fmem_of_topology P c (honestQc P c Qc) (honestQm P c Qm) _ htop
    (k.val + 1) (by omega) k.isLt
  rw [ExecOfTraces.lblM_succ] at hF
  exact ⟨hF.1, hF.2.1⟩

omit hacc hgood hax hbasis hwidth in
theorem eqBlk_readRoot_root {inp : Inputs K} {p : Pub K}
    (heq : eqBlk inp p) (hst : p.st = .read_root) : p.mem.root = p.pt.noun := by
  unfold eqBlk at heq
  rw [hst] at heq
  exact heq.2.2.2.2.1

omit hacc hgood hax hbasis hwidth in
theorem eqBlk_verifyChild_child {inp : Inputs K} {p : Pub K}
    (heq : eqBlk inp p) (hst : p.st = .verify_child) : p.mem.child = p.pt.noun := by
  unfold eqBlk at heq
  rw [hst] at heq
  exact heq.2.2.2.2.1

/-- **The stored `(T, C')` of an active decoded row are the Form R encode of `axR0` at the row's
`λ`** — `Batch973.read_row_facts` / `verify_row_facts` at the position `axOfRowsR0` chose. -/
theorem axisFacts_at (k : Fin P.optimized.family.problem.cfg.memRows)
    (hact : memoryMemRecKind (L P c Qm k).1 = .active) :
    (L P c Qm k).2.2.mem.axis =
        formRT (L P c Qm k).2.2.lambda (nockAxisOf ((axR0 P c Qc Qm (L P c Qm k) : ℕ) : K)) ∧
      (L P c Qm k).2.2.cprime =
        formRC (L P c Qm k).2.2.lambda (nockAxisOf ((axR0 P c Qc Qm (L P c Qm k) : ℕ) : K)) := by
  have hio := Batch974.hio_of_hgood P c Qc Qm hgood
  have hrb := P.rowsBound
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  obtain ⟨k', hk', hax'⟩ := axOfRowsR0_spec P.optimized (honestQc P c Qc) (honestQm P c Qm) c
    (L P c Qm k) ⟨k, rfl⟩
  have hE : memRowExpOfEnvs (memoryEnvsR0 P.optimized (honestQm P c Qm) c)
      P.optimized.family.problem.cfg.memRows_pos (k'.val + 1) = expR P c Qm k' := by
    unfold memRowExpOfEnvs
    rw [dif_pos (by simp)]
    rfl
  have hfam : FamilyEnvCore.familyQc P.optimized c (honestQc P c Qc) = Qc :=
    Batch824.familyQc_honestQc P c Qc
  have hC : certAxisOfEnvs (computeEnvsR0 P.optimized (honestQc P c Qc) c) =
      certAxisOfEnvs (Batch824.envsCR P c Qc) := by
    refine Batch970.certAxisOfEnvs_congr fun i col _ => ?_
    have htr : (computeEnvsR0 P.optimized (honestQc P c Qc) c i).trace =
        (Batch824.envsCR P c Qc i).trace := by
      unfold computeEnvsR0
      rw [hfam]
      exact (Batch823.envsC_trace P c Qc i).symm
    rw [htr]
  have hax'' : axR0 P c Qc Qm (L P c Qm k) =
      certAxisOfEnvs (computeEnvsR0 P.optimized (honestQc P c Qc) c)
        (memRowExpOfEnvs (memoryEnvsR0 P.optimized (honestQm P c Qm) c)
          P.optimized.family.problem.cfg.memRows_pos (k'.val + 1)) := hax'
  rw [L_lambda, hax'', hE, hC]
  have hk'' : L P c Qm k' = L P c Qm k := hk'
  rw [← hk''] at hact ⊢
  rw [L_state] at hact
  rcases hs : memRowStateOf (memEnvF P c Qm k') with _ | _ | _ | _
  · rw [hs] at hact; exact absurd hact (by decide)
  · rw [hs] at hact; exact absurd hact (by decide)
  · obtain ⟨h25, h57, _⟩ :=
      Batch973.read_row_facts P c Qc Qm hacc hgood hio hrb hb1 hwidth k' hs
    exact ⟨h25, h57⟩
  · obtain ⟨h25, h57, _⟩ :=
      Batch973.verify_row_facts P c Qc Qm hacc hgood hio hrb hb1 hwidth k' hs
    exact ⟨h25, h57⟩

/-- A selector-`3` family row decodes to `verify_child` (base one-hot; mirror of
`Batch973.read_state_of_sel2`). -/
theorem verify_state_of_sel3 (k : Fin P.optimized.family.problem.cfg.memRows)
    (hsel : (memEnvF P c Qm k).trace 3 = 1) :
    memRowStateOf (memEnvF P c Qm k) = .verify_child := by
  have hchar := Batch824.memStateTagChar_of_package P
  obtain ⟨st, hone⟩ := FamilyMemoryRows.baseOneHot_at_family P c Qm hacc.memory_satisfies k hchar
  have h3 := hone .verify_child
  have hst : st = .verify_child := by
    by_contra hne
    have : (memEnvF P c Qm k).trace (Nock.Reified.mopCol MState.verify_child) = 0 := by
      simpa [Ne.symm hne] using h3
    rw [show Nock.Reified.mopCol MState.verify_child = 3 from rfl] at this
    rw [this] at hsel
    exact zero_ne_one hsel
  rw [← Batch844.memoryStateOf_eq_memRowStateOf]
  exact (FamilyMemoryRows.memoryStateOf_eq_of_baseOneHot _ st hone).trans hst

/-- **A `verify_child` row has `ver ≠ 1`**: otherwise it and its `intermediate` partner are two
`ver = 1` rows with one `reqIdx`, hence one row (`ver_reqIdx_injective_at`), carrying selectors
`2` and `3` at once. -/
theorem verify_ver_ne_one (k : Fin P.optimized.family.problem.cfg.memRows)
    (hst : memRowStateOf (memEnvF P c Qm k) = .verify_child) :
    (memEnvK P c Qm k).trace 39 ≠ 1 := by
  intro hver
  have hio := Batch974.hio_of_hgood P c Qc Qm hgood
  have hrb := P.rowsBound
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  have hchar := OptimizedHostileConfiguration.hchar_of_package P
  have h3 := verify_sel_at P c Qm hacc.memory_satisfies k hst
  obtain ⟨k'', hsel2, hrec⟩ := verify_partner_at P c Qc Qm hacc hgood hrb k h3
  have hv'' := readSel_ver_at P c Qm hacc.memory_satisfies hb1 k'' hsel2
  have heq : (memEnvF P c Qm k).trace reqIdxCol = (memEnvF P c Qm k'').trace reqIdxCol := by
    have h9 := congrFun hrec 9
    apply (algebraMap F K).injective
    simpa [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord,
      reqIdxCol] using h9
  have hkk := ver_reqIdx_injective_at P c Qc Qm hacc hgood hio hchar
    (hKp_of_rowsBound_at P hrb) (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm)
    k k'' hver hv'' heq
  subst hkk
  exact (not_sel_of_verify hst).2.2 hsel2

/-- **A padding row has `ver ≠ 1`** when `α ≠ 0`: its record is zero (`eqBlk`), so its `ts = 0`,
while a `ver = 1` row's `ts` is `α^e`. -/
theorem padding_ver_ne_one (hα0 : alphaM c.1 ≠ 0)
    (k : Fin P.optimized.family.problem.cfg.memRows)
    (hpad : memoryMemRecKind (memRowStateOf (memEnvF P c Qm k)) = .padding) :
    (memEnvK P c Qm k).trace 39 ≠ 1 := by
  intro hver
  have hio := Batch974.hio_of_hgood P c Qc Qm hgood
  have hrb := P.rowsBound
  have hchar := OptimizedHostileConfiguration.hchar_of_package P
  have hts := ts_eq_alpha_pow_natLift_at P c Qc Qm hacc hgood hio hchar
    (hKp_of_rowsBound_at P hrb) (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm)
    k hver
  obtain ⟨hst, heq⟩ := eqBlk_at P c Qc Qm hacc hgood hax hbasis hwidth k
  have hpad' : memoryMemRecKind (L P c Qm k).2.2.st = .padding := by
    rw [hst, L_state]; exact hpad
  have hmem := Batch509.eqBlk_padding_mem_zero heq hpad'
  have h26 : (memEnvK P c Qm k).trace 26 = 0 := congrArg MemRec.ts hmem
  rw [h26] at hts
  exact pow_ne_zero _ hα0 hts.symm

/-- **`hver` at every row.** -/
theorem ver_at (hα0 : alphaM c.1 ≠ 0) (k : Fin P.optimized.family.problem.cfg.memRows) :
    (L P c Qm k).2.2.ver = decide ((L P c Qm k).1 = .read_root) := by
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  rw [L_ver, L_state]
  rcases hs : memRowStateOf (memEnvF P c Qm k) with _ | _ | _ | _
  · have hne := padding_ver_ne_one P c Qc Qm hacc hgood hax hbasis hwidth hα0 k
      (by rw [hs]; rfl)
    simp [hne]
  · have hne := padding_ver_ne_one P c Qc Qm hacc hgood hax hbasis hwidth hα0 k
      (by rw [hs]; rfl)
    simp [hne]
  · have h39 := readSel_ver_at P c Qm hacc.memory_satisfies hb1 k (sel2_of_read hs)
    simp [h39]
  · have hne := verify_ver_ne_one P c Qc Qm hacc hgood hax hbasis hwidth k hs
    simp [hne]

/-- **A `read_root` row's `intermediate` partner**: a selector-`3` row with the same ten-slot record
(`paired_records_of_rowsBound_at` read the other way round from `verify_partner_at`). -/
theorem read_partner_at (k : Fin P.optimized.family.problem.cfg.memRows)
    (hsel : (memEnvF P c Qm k).trace 2 = 1) :
    ∃ k' : Fin P.optimized.family.problem.cfg.memRows, (memEnvF P c Qm k').trace 3 = 1 ∧
      MemoryInternalPole.rowRecord (memEnvK P c Qm k) (memEnvF P c Qm k) =
        MemoryInternalPole.rowRecord (memEnvK P c Qm k') (memEnvF P c Qm k') := by
  have hperm := paired_records_of_rowsBound_at P c Qc Qm hacc hgood P.rowsBound
  have hmem : MemoryInternalPole.rowRecord (memEnvK P c Qm k) (memEnvF P c Qm k) ∈
      hostileReadsAt P c Qm := by
    simp only [hostileReadsAt, List.mem_flatten, List.mem_ofFn]
    refine ⟨_, ⟨k, rfl⟩, ?_⟩
    simp [MemoryInternalPole.rowReadsOf, hsel]
  have hv := (List.Perm.mem_iff hperm).1 hmem
  simp only [hostileVerifiesAt, List.mem_flatten, List.mem_ofFn] at hv
  obtain ⟨l, ⟨k', rfl⟩, hl⟩ := hv
  unfold MemoryInternalPole.rowVerifiesOf at hl
  split_ifs at hl with h3
  · simp only [List.mem_singleton] at hl
    exact ⟨k', h3, hl⟩
  · simp at hl

/-- `hservedChild`: a `read_root` row's record child is its partner `verify_child` row's own noun. -/
theorem servedChild_at
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (k : Fin P.optimized.family.problem.cfg.memRows) (hst : (L P c Qm k).1 = .read_root) :
    ServedFingerprint (Fdec P c Qc Qm h) (L P c Qm k).2.2.mem.child := by
  rw [L_state] at hst
  obtain ⟨k', h3, hrec⟩ := read_partner_at P c Qc Qm hacc hgood hax hbasis hwidth k (sel2_of_read hst)
  have hs' := verify_state_of_sel3 P c Qc Qm hacc hgood hax hbasis hwidth k' h3
  have hchild : (L P c Qm k).2.2.mem.child = (L P c Qm k').2.2.mem.child := by
    have h3' := congrFun hrec 3
    have h4 := congrFun hrec 4
    have h5 := congrFun hrec 5
    simp only [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord] at h3' h4 h5
    exact ComputeTable.FP.ext h3' h4 h5
  obtain ⟨hst', heq'⟩ := eqBlk_at P c Qc Qm hacc hgood hax hbasis hwidth k'
  have hs'' : (L P c Qm k').2.2.st = .verify_child := by rw [L_st]; exact hs'
  have hpt := eqBlk_verifyChild_child heq' hs''
  refine ⟨treeAt P c Qm k', treeAt_mem P c Qc Qm h k', ?_⟩
  rw [treeAt_label, ← hpt, ← hchild]

/-- `hservedRoot`: a `verify_child` row's record root is its partner `read_root` row's own noun. -/
theorem servedRoot_at
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (k : Fin P.optimized.family.problem.cfg.memRows) (hst : (L P c Qm k).1 = .verify_child) :
    ServedFingerprint (Fdec P c Qc Qm h) (L P c Qm k).2.2.mem.root := by
  rw [L_state] at hst
  have h3 := verify_sel_at P c Qm hacc.memory_satisfies k hst
  obtain ⟨k', hsel2, hrec⟩ := verify_partner_at P c Qc Qm hacc hgood P.rowsBound k h3
  have hs' := Batch973.read_state_of_sel2 P c Qc Qm hacc hgood P.rowsBound k' hsel2
  have hroot : (L P c Qm k).2.2.mem.root = (L P c Qm k').2.2.mem.root := by
    have h0 := congrFun hrec 0
    have h1 := congrFun hrec 1
    have h2 := congrFun hrec 2
    simp only [MemoryInternalPole.rowRecord, OptimizedMemoryHostileAccumulator.rowRecord] at h0 h1 h2
    exact ComputeTable.FP.ext h0 h1 h2
  obtain ⟨hst', heq'⟩ := eqBlk_at P c Qc Qm hacc hgood hax hbasis hwidth k'
  have hs'' : (L P c Qm k').2.2.st = .read_root := by rw [L_st]; exact hs'
  have hpt := eqBlk_readRoot_root heq' hs''
  refine ⟨treeAt P c Qm k', treeAt_mem P c Qc Qm h k', ?_⟩
  rw [treeAt_label, ← hpt, ← hroot]

theorem haltLeaf_at (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x)
    (k : Fin P.optimized.family.problem.cfg.memRows) (hst : (L P c Qm k).1 = .halt) :
    ∃ n : ℕ, n < ringChar K ∧ (n : K) = (L P c Qm k).2.2.pt.noun.leaf := by
  have hst' : (ExecOfTraces.decodeMemPub P (honestQm P c Qm) c k).st = .halt := hst
  have hleaf := MemoryHaltAtomDecode.decodeMemPub_halt_leaf_eq_atom P c Qm hacc.memory_satisfies k hst'
  obtain ⟨n, hn, hnx⟩ := hF (MemoryHaltAtomDecode.memoryAtomAt P c (honestQm P c Qm) k)
  refine ⟨n, by rw [← Algebra.ringChar_eq F K]; exact hn, ?_⟩
  show (n : K) = (ExecOfTraces.decodeMemPub P (honestQm P c Qm) c k).pt.noun.leaf
  rw [hleaf, ← hnx, map_natCast]

/-- **The memory conjunct of `BindsAt` on the round-0 forest** (what `BindsAtCoin` reads at
`(nprSeed c.1, alphaM c.1, c.λ)`), at the a-bearing skeleton. -/
theorem memoryForestBinds_R0A
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (hz : nprSeed c.1 ≠ 0)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x)
    (hα0 : alphaM c.1 ≠ 0) :
    List.Forall₂ (MemoryTreeBinds (nprSeed c.1))
      (strategyOfTracesR0A P.optimized P.stateTagChar (honestQc P c Qc) (honestQm P c Qm) c h).skeleton.memoryForest
      ((strategyOfTracesR0A P.optimized P.stateTagChar (honestQc P c Qc) (honestQm P c Qm) c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryForest := by
  rw [specializedExec_R0A_eq,
    Batch974.specialized_memoryForest_R0_eq P c Qc Qm hacc hgood hax hbasis hwidth h hz]
  have htop : ∀ t ∈ Fdec P c Qc Qm h, RVTWithArity (FmemTopo (K := K)) t := by
    have := Batch974.wrapJoin P c Qc Qm hacc hgood hax hbasis hwidth h hz
    rwa [Batch974.specialized_memoryForest_R0_eq P c Qc Qm hacc hgood hax hbasis hwidth h hz] at this
  have hseed : ∀ t ∈ Fdec P c Qc Qm h, ∀ node, InTree t node → node.label.2.1.z = nprSeed c.1 := by
    intro t ht node hin
    obtain ⟨k, hk⟩ := label_of_inTree P c Qc Qm h ht hin
    rw [hk]
    exact L_seed P c Qm k
  have hhalt : ∀ t ∈ Fdec P c Qc Qm h, ∀ node, InTree t node → node.label.1 = .halt →
      ∃ n : ℕ, n < ringChar K ∧ (n : K) = node.label.2.2.pt.noun.leaf := by
    intro t ht node hin hst
    obtain ⟨k, hk⟩ := label_of_inTree P c Qc Qm h ht hin
    rw [hk] at hst ⊢
    exact haltLeaf_at P c Qc Qm hacc hgood hax hbasis hwidth hF k hst
  show List.Forall₂ _ (decodedMemoryForestAx (ringChar K) (Fdec P c Qc Qm h) (axR0 P c Qc Qm))
    (Fdec P c Qc Qm h)
  refine Batch1010.memoryForestBinds_of_topologyA hz (Fdec P c Qc Qm h) (axR0 P c Qc Qm) htop hseed
    ?_ ?_ ?_ ?_ ?_ (Batch1010.forestFPFacts_of_topology _ htop hseed hhalt)
  · intro t ht
    exact Batch1010.leafAtomsRealized_of_structure
      (memoryFingerprintStructure_of_rvtWithArity_topo _ t (htop t ht) (hseed t ht))
      (hhalt t ht)
  · intro t ht node hin
    obtain ⟨k, hk⟩ := label_of_inTree P c Qc Qm h ht hin
    rw [hk]
    exact ver_at P c Qc Qm hacc hgood hax hbasis hwidth hα0 k
  · intro t ht node hin hst
    obtain ⟨k, hk⟩ := label_of_inTree P c Qc Qm h ht hin
    rw [hk] at hst ⊢
    exact servedChild_at P c Qc Qm hacc hgood hax hbasis hwidth h k hst
  · intro t ht node hin hst
    obtain ⟨k, hk⟩ := label_of_inTree P c Qc Qm h ht hin
    rw [hk] at hst ⊢
    exact servedRoot_at P c Qc Qm hacc hgood hax hbasis hwidth h k hst
  · intro t ht node hin hact
    obtain ⟨k, hk⟩ := label_of_inTree P c Qc Qm h ht hin
    rw [hk] at hact ⊢
    exact axisFacts_at P c Qc Qm hacc hgood hax hbasis hwidth k hact

end

end Nock.RedTeam.Batch1011
