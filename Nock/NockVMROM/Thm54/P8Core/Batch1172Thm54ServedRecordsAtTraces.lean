/-
  Nock/NockVMROM/Thm54/P8Core/Batch1172Thm54ServedRecordsAtTraces.lean

  Relocated below the statement file: declarations of
  `Nock.RedTeam.Batch1172Thm54ServedRecordsAtTraces`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/RedTeam/Batch1172Thm54ServedRecordsAtTraces.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.P8Core.Batch1140Thm54CertAxesAtTraces
import Nock.NockVMROM.Thm54.P8Core.Batch1142Thm54C2CombinedCertAxes0
import Nock.NockVMROM.Thm54.P8Core.Batch1170Thm54ServedPathSlot
import Nock.NockVMROM.Thm54.P8Core.Batch773Thm54ExpOfRequestList
import Nock.NockVMROM.Thm54.P8Core.PreSeedCensus
import Nock.NockVMROM.Thm54.P8Core.Batch971Thm54Round0WrapForestCover
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace Nock.RedTeam.Batch1172

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0
open Nock.NockVMROM.Thm54.StrategyOfTracesR0AC2
open Nock.NockVMROM.Thm54.StrategyOfTracesEv
open Nock.NockVMROM.Thm54.OptimizedFailureEventEv
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyIOChain
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.PreSeedCensus
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.UniqueExponentsBridge
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis (reqIdxCol)
open Nock.NockVMROM.Thm54.WalkTilingEvents (memRowStateOf foOfMem)
open Nock.RedTeam.Batch1024 (treeS axF svF)
open Nock.RedTeam.Batch973 (expR)
open Nock.GlobalCarryRecognizer
open Nock.AxisBatching.MTree (readCount verifyCount)
open Nock.RedTeam.Batch575 (UniqueExponents)
open Nock.FieldEmbedding

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
set_option quotPrecheck false
local notation "NN" => preZNounOfEnvs K (ringChar K) P.optimized.family.problem.cfg.kMem
  (Batch824.envsFR P c Qm) P.optimized.family.problem.cfg.memRows_pos

omit [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K] in
/-- **The served lookup's candidate rows are exactly the rows of that state and exponent.** -/
theorem mem_servedRows_iff {M : ℕ} (envs : Fin M → Env F) (hM : 0 < M) (st : MState) (e y : ℕ) :
    y ∈ PreZComputeCore.Served.servedRowsOfEnvs envs hM st e ↔ RowAt envs st e y := by
  unfold PreZComputeCore.Served.servedRowsOfEnvs RowAt
  simp only [List.mem_filter, List.mem_range'_1, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, hs, he⟩
    have hy : y - 1 < M := by omega
    refine ⟨hy, h1, ?_, ?_⟩
    · rw [← Batch1170.preLbl_fst envs hM y h1 (by omega)]; exact hs
    · unfold preReqIdxOfEnvs at he; rw [dif_pos hy] at he; exact he
  · rintro ⟨hy, h1, hs, he⟩
    refine ⟨⟨h1, by omega⟩, ?_, ?_⟩
    · rw [Batch1170.preLbl_fst envs hM y h1 (by omega)]; exact hs
    · unfold preReqIdxOfEnvs; rw [dif_pos hy]; exact he

omit [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K] in
/-- **The served lookup at an exponent-injective state** is the pre-`z` noun of the row. -/
theorem servedNoun_eq {M : ℕ} (envs : Fin M → Env F) (hM : 0 < M) (q kroots : ℕ) (st : MState)
    (e y : ℕ) (hinj : ExpInjOn envs st) (hy : RowAt envs st e y) :
    PreZComputeCore.Served.servedNounOfEnvs K q kroots envs hM st e =
      preZNounOfEnvs K q kroots envs hM y := by
  have hmem := (mem_servedRows_iff envs hM st e y).2 hy
  unfold PreZComputeCore.Served.servedNounOfEnvs
  rcases hL : PreZComputeCore.Served.servedRowsOfEnvs envs hM st e with _ | ⟨y', ys⟩
  · rw [hL] at hmem; simp at hmem
  · have hy' := (mem_servedRows_iff envs hM st e y').1 (by rw [hL]; exact List.mem_cons_self ..)
    simp only
    rw [rowAt_unique envs hinj hy' hy]

section Memory

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
include hacc hgood hax hbasis hwidth

/-- **The decoded fingerprint of a memory row**: the pre-`z` noun of row `k + 1` encodes to the
row's committed `pt.noun` (QJ's `decode_fingerprint` on the round-0 forest; halt leaves through
`hF`). -/
theorem enc_NN (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (hz : nprSeed c.1 ≠ 0)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x)
    (k : Fin P.optimized.family.problem.cfg.memRows) :
    enc (nprSeed c.1) (NN (k.val + 1)) = (Batch1011.L P c Qm k).2.2.pt.noun := by
  have htop : ∀ t ∈ Batch1011.Fdec P c Qc Qm h,
      RVTWithArity (MemoryTopoBetaFree.FmemTopo (K := K)) t := by
    have := Batch974.wrapJoin P c Qc Qm hacc hgood hax hbasis hwidth h hz
    rwa [Batch974.specialized_memoryForest_R0_eq P c Qc Qm hacc hgood hax hbasis hwidth h hz] at this
  have hseed : ∀ t ∈ Batch1011.Fdec P c Qc Qm h, ∀ node, InTree t node →
      node.label.2.1.z = nprSeed c.1 := by
    intro t ht node hin
    obtain ⟨k, hk⟩ := Batch1011.label_of_inTree P c Qc Qm h ht hin
    rw [hk]
    exact Batch1011.L_seed P c Qm k
  have hhalt : ∀ t ∈ Batch1011.Fdec P c Qc Qm h, ∀ node, InTree t node → node.label.1 = .halt →
      ∃ n : ℕ, n < ringChar K ∧ (n : K) = node.label.2.2.pt.noun.leaf := by
    intro t ht node hin hst
    obtain ⟨k, hk⟩ := Batch1011.label_of_inTree P c Qc Qm h ht hin
    rw [hk] at hst ⊢
    exact Batch1011.haltLeaf_at P c Qc Qm hacc hgood hax hbasis hwidth hF k hst
  have hFF := Batch1010.forestFPFacts_of_topology (q := ringChar K) _ htop hseed hhalt
  have hmem := Batch1011.treeAt_mem P c Qc Qm h k
  have hdec := decode_fingerprint hz (hFF.1 _ hmem) (hFF.2 _ hmem)
  have hpre := accepted_decode_eq_preZNoun P c Qm hacc.memory_satisfies (ringChar K) (k.val + 1)
  have e1 : decodeNoun (ringChar K) (Batch1011.treeAt P c Qm k) = NN (k.val + 1) := hpre
  rw [e1] at hdec
  rw [hdec]
  show (Batch1011.treeAt P c Qm k).label.2.2.pt.noun = _
  rw [Batch1011.treeAt_label]

omit hax hbasis hwidth in
/-- **The two memory rows serving an active request** `(a, j)`: a `read_root` row `k` and a
`verify_child` row `k'`, both at exponent `expOfAt a j`, both storing the request's full ten-slot
record (`request_named_by_row_at`, the `intermediate` partner either way round). -/
theorem served_rows (hα0 : alphaM c.1 ≠ 0)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1) :
    ∃ k k' : Fin P.optimized.family.problem.cfg.memRows,
      memRowStateOf (memEnvF P c Qm k) = .read_root ∧
      memRowStateOf (memEnvF P c Qm k') = .verify_child ∧
      OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm k) (memEnvF P c Qm k) =
        rowRecord (rowEnvAt P c Qc a) j ∧
      OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm k') (memEnvF P c Qm k') =
        rowRecord (rowEnvAt P c Qc a) j ∧
      expR P c Qm k = expOfAt P c Qc a j ∧ expR P c Qm k' = expOfAt P c Qc a j := by
  have hio := Batch974.hio_of_hgood P c Qc Qm hgood
  have hrb := P.rowsBound
  have hchar' := OptimizedHostileConfiguration.hchar_of_package P
  have hsatC := hacc.compute_satisfies
  obtain ⟨i, hver, hrec, hidx⟩ := request_named_by_row_at P c Qc Qm hacc hgood hio hchar'
    (hKp_of_rowsBound_at P hrb) (hKreq_of_rowsBound_at P c Qc) (hKresp_of_rowsBound_at P c Qm)
    a j hact
  have hlt := expOfAt_lt_ringChar P c Qc hsatC hchar' (hKp_of_rowsBound_at P hrb)
    (hKreq_of_rowsBound_at P c Qc) hact
  have hexpOf : ∀ k : Fin P.optimized.family.problem.cfg.memRows,
      OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm k) (memEnvF P c Qm k) =
        rowRecord (rowEnvAt P c Qc a) j →
      expR P c Qm k = expOfAt P c Qc a j := by
    intro k hk
    have h9 := congrFun (hk.trans hrec.symm) 9
    simp only [OptimizedMemoryHostileAccumulator.rowRecord] at h9
    have hr : (memEnvF P c Qm k).trace reqIdxCol = (memEnvF P c Qm i).trace reqIdxCol := by
      apply (algebraMap F K).injective
      simpa [reqIdxCol] using h9
    show RecordCarrier.natLift _ = _
    rw [hr, hidx]; exact RecordCarrier.natLift_natCast hlt
  have hts : (memEnvK P c Qm i).trace 26 ≠ 0 := by
    have h7 := congrFun hrec 7
    rw [rowRecord_ts_at_at P c Qc hsatC hchar' (nprSeed_ne_of_good_at P c Qc Qm hgood) a j hact,
      hostile_ln0_eq_one_at P c Qc hsatC, one_mul] at h7
    simp only [OptimizedMemoryHostileAccumulator.rowRecord] at h7
    intro h0
    apply pow_ne_zero (expOfAt P c Qc a j) hα0
    rw [← h7]; simpa using h0
  have hpadz : memoryMemRecKind (memRowStateOf (memEnvF P c Qm i)) = .padding →
      (memEnvK P c Qm i).trace 26 = 0 := by
    intro hk
    have htop := Batch974.decoded_topology P c Qc Qm hacc hgood hax hbasis hwidth
    have hF := Batch509.fmem_of_topology P c (honestQc P c Qc) (honestQm P c Qm) _ htop
      (i.val + 1) (by omega) i.isLt
    rw [ExecOfTraces.lblM_succ] at hF
    have hst : (ExecOfTraces.lblMAt P (honestQm P c Qm) c i).2.2.st =
        (ExecOfTraces.lblMAt P (honestQm P c Qm) c i).1 := hF.1
    have hstate : (ExecOfTraces.lblMAt P (honestQm P c Qm) c i).1 =
        memRowStateOf (memEnvF P c Qm i) := Batch844.memoryStateOf_eq_memRowStateOf _
    have hm := Batch509.eqBlk_padding_mem_zero hF.2.1 (by rw [hst, hstate]; exact hk)
    have := congrArg MemRec.ts hm
    exact this
  rcases hs : memRowStateOf (memEnvF P c Qm i) with _ | _ | _ | _
  · exact absurd (hpadz (by rw [hs]; rfl)) hts
  · exact absurd (hpadz (by rw [hs]; rfl)) hts
  · obtain ⟨k', h3, hrec'⟩ := Batch1011.read_partner_at P c Qc Qm hacc hgood hax hbasis hwidth i
      (sel2_of_read hs)
    have hs' := Batch1011.verify_state_of_sel3 P c Qc Qm hacc hgood hax hbasis hwidth k' h3
    have hr' : OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm k') (memEnvF P c Qm k') =
        rowRecord (rowEnvAt P c Qc a) j := hrec'.symm.trans hrec
    exact ⟨i, k', hs, hs', hrec, hr', hexpOf i hrec, hexpOf k' hr'⟩
  · have h3 := verify_sel_at P c Qm hacc.memory_satisfies i hs
    obtain ⟨k, hsel', hrec'⟩ := verify_partner_at P c Qc Qm hacc hgood hrb i h3
    have hst' := Batch973.read_state_of_sel2 P c Qc Qm hacc hgood hrb k hsel'
    have hr' : OptimizedMemoryHostileAccumulator.rowRecord (memEnvK P c Qm k) (memEnvF P c Qm k) =
        rowRecord (rowEnvAt P c Qc a) j := hrec'.symm.trans hrec
    exact ⟨k, i, hst', hs, hr', hrec, hexpOf k hr', hexpOf i hrec⟩

end Memory

section Bridges

/-- The request record's fingerprint slots `0..5` are the decoded source's record columns. -/
theorem rowRecord_eq_src (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K)
    (j : Fin 3) (k : Fin 10) (hk : (k : ℕ) < 6) :
    rowRecord env j k = (StrategyOfTracesLift.decodeSource env).trace (67 + 8 * (j : ℕ) + k) := by
  unfold rowRecord
  have h9 : ¬ (k : ℕ) = 9 := by omega
  have h6 : ¬ (k : ℕ) = 6 := by omega
  have h8 : ¬ (k : ℕ) = 8 := by omega
  simp only [if_neg h9, if_neg h6, if_neg h8]
  rw [Expr.eval_subst]
  show _ = (OptimizedComputeSubstitution.computeTraceSubst .traceCur
    (67 + 8 * (j : ℕ) + k)).eval env.toSourceEnv
  refine FamilyChipTwins.eval_congr_of_traceOnly _ ?_ ?_
  · funext i; rfl
  · fin_cases j <;> fin_cases k <;> first | decide | exact absurd hk (by decide)

/-- **The trace record `j` of a decoded compute label, in the request record's slots.** -/
theorem traceRec_fp (env : OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv F K)
    (st : State) (x : ComputeTable.Inputs K) (d : ComputeTable.Dec K) (S : ℕ) (j : Fin 3) :
    (Batch1171.traceRec (((st, (x, StrategyOfTracesLift.decodePub env st, d)) :
        (State × DTcomp K)) , S) (j : ℕ)).root =
        ⟨rowRecord env j 0, rowRecord env j 1, rowRecord env j 2⟩ ∧
      (Batch1171.traceRec (((st, (x, StrategyOfTracesLift.decodePub env st, d)) :
        (State × DTcomp K)), S) (j : ℕ)).child =
        ⟨rowRecord env j 3, rowRecord env j 4, rowRecord env j 5⟩ := by
  rw [rowRecord_eq_src env j 0 (by decide), rowRecord_eq_src env j 1 (by decide),
    rowRecord_eq_src env j 2 (by decide), rowRecord_eq_src env j 3 (by decide),
    rowRecord_eq_src env j 4 (by decide), rowRecord_eq_src env j 5 (by decide)]
  fin_cases j <;> exact ⟨rfl, rfl⟩

/-- `decodePre` is bounded by its modulus. -/
theorem decodePre_bounded (q : ℕ) (hq : 0 < q) :
    ∀ t : NTree (MState × F), BoundedBy q (decodePre K q t) := by
  intro t
  induction t using decodePre.induct with
  | case1 a => simp [decodePre, leafAtomOf_lt_of_pos hq]
  | case2 _ l r ihl ihr => simp only [decodePre]; exact ⟨ihl, ihr⟩
  | case3 _ ch ih => simp only [decodePre]; exact ih
  | case4 _ ch ih => simp only [decodePre]; exact ih
  | case5 t h1 h2 h3 h4 =>
      rw [decodePre.eq_def]
      split <;> first | (simp [hq]; done) | (exfalso; simp_all)

end Bridges

section Compute

/-- The C2 join on the family traces at `c`, rooted at the package claim. -/
local notation "JT" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
  (treeS P c Qc).size (treeS P c Qc)
  P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula
local notation "SK" => skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)
local notation "NC" => P.optimized.family.problem.cfg.compRows

theorem bfs_treeS (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c) :
    bfsForest [treeS P c Qc] =
      (List.range' 1 NC).map (buildT (foC P.optimized (honestQc P c Qc) c)
        (lblCS P.optimized (honestQc P c Qc) c) NC) := by
  change bfsForest [reconTree (foC P.optimized (honestQc P c Qc) c)
    (lblCS P.optimized (honestQc P c Qc) c) NC] = _
  exact bfsForest_reconTree _ _ _ h.sfCompute h.validCompute

theorem rows_eq : computeSkeletonRows SK = (bfsForest [JT]).map NTree.label := by
  unfold computeSkeletonRows
  rw [Batch1111.skeletonEv_computeTree_eq P c Qc Qm]

/-- **A positional pair sits at BFS row `a`**: the trace node is `lblCS (a + 1)`, the join node
is row `a` of the event skeleton. -/
theorem pos_of_pr (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    {u : NTree ((State × DTcomp K) × ℕ)} {w : NTree ComputeRowSkeleton}
    (hpr : Batch1171.PR (treeS P c Qc) JT u w) :
    ∃ a : Fin NC, InTree (treeS P c Qc) u ∧
      u.label = lblCS P.optimized (honestQc P c Qc) c (a.val + 1) ∧
      (computeSkeletonRows SK)[a.val]? = some w.label := by
  obtain ⟨a, h1, h2⟩ := Batch1170.pr_pos
    (Batch1170.J_shape (sv := svF P c Qm) (ax := axF P c Qc) (treeS P c Qc) _ _) hpr
  have hin : InTree (treeS P c Qc) u := by
    have hm := List.mem_of_getElem? h1
    obtain ⟨t0, ht0, hit⟩ := (mem_bfsForest _ _).1 hm
    rw [List.mem_singleton] at ht0
    rw [← ht0]; exact hit
  rw [bfs_treeS P c Qc Qm h] at h1
  have ha : a < NC := by
    have := (List.getElem?_eq_some_iff.1 h1).1
    simpa using this
  rw [List.getElem?_map, List.getElem?_range' ha] at h1
  simp only [Option.map_some, Option.some.injEq] at h1
  refine ⟨⟨a, ha⟩, hin, ?_, ?_⟩
  · rw [← h1, buildT_label]; congr 1; simp only; omega
  · rw [rows_eq P c Qc Qm, List.getElem?_map, h2]; rfl

/-- **The event skeleton's BFS states are the traces' decoded states.** -/
theorem states_eq (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c) :
    (computeSkeletonRows SK).map ComputeRowSkeleton.state =
      (List.range' 1 NC).map (fun i => (lblCS P.optimized (honestQc P c Qc) c i).1.1) := by
  rw [rows_eq P c Qc Qm]
  have hs := Batch1170.J_state_shape (sv := svF P c Qm) (ax := axF P c Qc) (treeS P c Qc).size
    (treeS P c Qc) P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula le_rfl
  have h1 := Batch773.bfs_labels_mapNTree ComputeRowSkeleton.state JT
  have h2 := Batch773.bfs_labels_mapNTree (fun l : (State × DTcomp K) × ℕ => l.1.1) (treeS P c Qc)
  rw [hs, h2, bfs_treeS P c Qc Qm h] at h1
  rw [← h1]
  simp [List.map_map, Function.comp_def, buildT_label]

theorem lblCS_succ_fst (m : ℕ) (hm : m < NC) :
    (lblCS P.optimized (honestQc P c Qc) c (m + 1)).1.1 =
      StrategyOfTracesLift.computeStateOf
        (StrategyOfTracesLift.decodeSource (rowEnvAt P c Qc ⟨m, hm⟩)) := by
  rw [Batch1140.lblCS_eq, Batch1140.lblCAt_eq]
  have : Batch1140.rowIdx P (m + 1) = ⟨m, hm⟩ := by
    unfold Batch1140.rowIdx; rw [dif_pos (by omega)]; rfl
  rw [this]

variable (hsat : Framework.RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
include hsat

/-- **The activity mask is the state's record count** (one-hot selector of an accepted row). -/
theorem activeMask_eq (r : Fin NC) (st : State)
    (h : rowSelector (rowEnvAt P c Qc r) = Nock.ComputeTable.opSel st) (j : Fin 3) :
    activeMask (rowEnvAt P c Qc r) j =
      if (j : ℕ) < Nock.Framework.recordCount st then 1 else 0 := by
  have hv : ∀ t : State, algebraMap F K ((rowEnvAt P c Qc r).baseTrace
      ⟨Nock.Reified.opCol t, by cases t <;> decide⟩) = Nock.ComputeTable.opSel st t :=
    fun t => congrFun h t
  have v0 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 0) = _ := hv .s0
  have v2 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 2) = _ := hv .s2
  have v5 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 5) = _ := hv .s5
  have v6 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 6) = _ := hv .s6
  have v7 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 7) = _ := hv .s7
  have v8 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 8) = _ := hv .s8
  have v9 : algebraMap F K ((rowEnvAt P c Qc r).baseTrace 9) = _ := hv .s9
  fin_cases j <;> cases st <;>
    simp [activeMask, OptimizedComputeSubstitution.sampledActive, Nock.Reified.Expr.eval,
      OptimizedComputeCorrectedFinal.CorrectedFinalTypedEnv.toSourceEnv,
      v0, v2, v5, v6, v7, v8, v9, Nock.ComputeTable.opSel, Nock.Framework.recordCount]

theorem rowArity_eq (r : Fin NC) :
    OptimizedHostileTimestamps.rowArity (rowEnvAt P c Qc r) = Nock.Framework.recordCount
      (StrategyOfTracesLift.computeStateOf (StrategyOfTracesLift.decodeSource (rowEnvAt P c Qc r))) := by
  have hsel := Batch1140.rowSelector_of_state P c Qc hsat r _ rfl
  have h1 := activeMask_eq P c Qc hsat r _ hsel 1
  have h2 := activeMask_eq P c Qc hsat r _ hsel 2
  unfold OptimizedHostileTimestamps.rowArity
  rw [h1, h2]
  generalize StrategyOfTracesLift.computeStateOf
    (StrategyOfTracesLift.decodeSource (rowEnvAt P c Qc r)) = st
  cases st <;> simp [Nock.Framework.recordCount]

/-- **The prefix of record counts over the event skeleton's rows is `prefixExpAt`.** -/
theorem prefix_eq (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c) :
    ∀ a, a ≤ NC → (((computeSkeletonRows SK).take a).map
      (fun r => Nock.Framework.recordCount r.state)).sum = prefixExpAt P c Qc a := by
  have hst := states_eq P c Qc Qm h
  have key : ∀ a, (((computeSkeletonRows SK).take a).map
      (fun r => Nock.Framework.recordCount r.state)) =
      (((List.range' 1 NC).map (fun i => (lblCS P.optimized (honestQc P c Qc) c i).1.1)).take a).map
        Nock.Framework.recordCount := by
    intro a
    rw [← hst, List.map_take, List.map_take, List.map_map]
    rfl
  intro a
  induction a with
  | zero => intro _; simp [prefixExpAt]
  | succ m ih =>
    intro hm
    rw [key] at ih ⊢
    rw [prefixExpAt_succ P c Qc m (by unfold rows; omega), ← ih (by omega), List.take_add_one]
    simp only [List.map_append, List.sum_append]
    congr 1
    rw [List.getElem?_map, List.getElem?_range' (by omega)]
    simp only [Option.map_some, Option.toList_some, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [show 1 + 1 * m = m + 1 by omega, lblCS_succ_fst P c Qc m (by omega), rowArity_eq P c Qc hsat]

/-- **The exponent names the request** (link (ii)): at an active slot `j` of BFS row `a`,
`requestTargets` of the event skeleton at `expOfAt a j` are the root / child of row `a`'s record
`j`. -/
theorem requestTargets_at (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (a : Fin NC) {row : ComputeRowSkeleton} (ha : (computeSkeletonRows SK)[a.val]? = some row)
    (j : Fin 3) (hj : (j : ℕ) < Nock.Framework.recordCount row.state) :
    requestTargets SK .read_root (expOfAt P c Qc a j) = (row.memoryRecord j hj).root ∧
      requestTargets SK .verify_child (expOfAt P c Qc a j) = (row.memoryRecord j hj).child := by
  obtain ⟨haR, hrow⟩ := List.getElem?_eq_some_iff.1 ha
  subst hrow
  have h0 := Batch772.requestList_getElem? SK a haR j hj
  rw [prefix_eq P c Qc Qm hsat h a (by omega)] at h0
  have hk : expOfAt P c Qc a j = (prefixExpAt P c Qc a + (j : ℕ)) + 1 := rfl
  rw [hk]
  have hrec : (computeSkeletonRows SK)[(a : ℕ)].memoryRecord
      ⟨j, lt_of_lt_of_le hj (Nock.Framework.recordCount_le _)⟩ hj =
      (computeSkeletonRows SK)[(a : ℕ)].memoryRecord j hj := rfl
  rw [hrec] at h0
  exact ⟨by simp [requestTargets, h0], by simp [requestTargets, h0]⟩

end Compute

section AtTraces

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hwidth : FormRWidth F)
  (hbasis : FormRBasis P.optimized.basis)
include hacc hgood

theorem envsFR_trace (k : Fin P.optimized.family.problem.cfg.memRows) :
    ∀ j, (Batch824.envsFR P c Qm k).trace j = (memEnvF P c Qm k).trace j :=
  fun j => (memEnvF_trace P c Qm k j).symm

omit hacc hgood in
theorem rowAt_of {st : MState} {e : ℕ} (k : Fin P.optimized.family.problem.cfg.memRows)
    (hs : memRowStateOf (memEnvF P c Qm k) = st) (he : expR P c Qm k = e) :
    RowAt (Batch824.envsFR P c Qm) st e (k.val + 1) := by
  have htr : ∀ j, (Batch824.envsFR P c Qm k).trace j = (memEnvF P c Qm k).trace j :=
    fun j => (memEnvF_trace P c Qm k j).symm
  have hk : (⟨k.val + 1 - 1, by omega⟩ : Fin P.optimized.family.problem.cfg.memRows) = k :=
    Fin.ext (by simp)
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hk, ← hs]; exact Batch733.memRowStateOf_congr (fun j _ => htr j)
  · rw [hk, ← he]; unfold rowExp; rw [htr]; rfl

/-- The BFS tiling and validity of the memory fanout at the package base envs. -/
theorem tiling_at :
    P.optimized.family.problem.cfg.kMem +
        Sf (foOfMem (Batch824.envsFR P c Qm)) P.optimized.family.problem.cfg.memRows =
      P.optimized.family.problem.cfg.memRows ∧
    BFSValidF P.optimized.family.problem.cfg.kMem (foOfMem (Batch824.envsFR P c Qm))
      P.optimized.family.problem.cfg.memRows := by
  have hchar := Batch824.memStateTagChar_of_package P
  have hsatM := hacc.memory_satisfies
  have hfQm := Batch824.familyQm_honestQm P c Qm
  have hfo : ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      foOfMem (Batch824.envsFR P c Qm) i = MemoryWalkDeployed.foW P c Qm i := by
    intro i h1 h2
    have := Batch489.foOfMem_eq_foWmem P c (honestQm P c Qm) i h1 h2
    rwa [hfQm] at this
  have hα := Batch501.htileαM_of_good P c (honestQc P c Qc) (honestQm P c Qm)
    (by rw [hfQm]; exact hsatM) hchar hgood
  rw [hfQm] at hα
  have ht := WalkQueueDeployed.deployed_tiling_memory P c Qm hsatM hchar hα
  refine ⟨?_, ?_⟩
  · rw [Batch973.Sf_congr_le _ _ _ hfo]; exact ht
  · have hv0 := WalkQueueDeployed.deployed_bfsValid_memory P c Qm hsatM hchar
    intro i h1 h2
    rw [Batch973.Sf_congr_le _ _ _ (fun j hj1 hj2 => hfo j hj1 (by omega))]
    exact hv0 i h1 h2

include hwidth hbasis in
/-- **Link (iv) at the traces**: the pre-`z` noun of the `verify_child` row at exponent `e` is
the Nock `slot`, at the recovered certificate axis of `e`, of the pre-`z` noun of the `read_root`
row at `e` (R4's path equation `V = R ++ bitsOf` at the root that pairs `e`, `Batch1170`). -/
theorem slot_at (k k' : Fin P.optimized.family.problem.cfg.memRows) {e : ℕ}
    (hk : memRowStateOf (memEnvF P c Qm k) = .read_root)
    (hk' : memRowStateOf (memEnvF P c Qm k') = .verify_child)
    (he : expR P c Qm k = e) (he' : expR P c Qm k' = e) :
    Noun.slot (certAxisOfEnvs (Batch824.envsCR P c Qc) e) (NN (k.val + 1)) =
      some (NN (k'.val + 1)) := by
  have hio := Batch974.hio_of_hgood P c Qc Qm hgood
  have hrb := P.rowsBound
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  have hb := Batch823.certBitsBoolean_of_sat P c Qc hacc.compute_satisfies
  have hn : 2 ≤ OptimizedComputeRangeCertificate.formRN F := by
    obtain ⟨_, _, h3⟩ := hwidth
    unfold OptimizedComputeRangeCertificate.formRN
    exact Nat.lt_size.mpr (by omega)
  have hA := Batch908.hA_of_acceptance P c Qc hacc.compute_satisfies hn
  have hU : ∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem,
      UniqueExponents (decodedMTreeOfEnvs (Batch824.envsKR P c Qm) (Batch824.envsFR P c Qm)
        P.optimized.family.problem.cfg.kMem r) :=
    fun r _ => UniqueExponentsBridge.uniqueExponents_decoded_pkg P c Qc Qm hacc hgood hio hrb hb1 _ r
  have hpath := Batch824.r4_path_valid_at P c Qc Qm hacc hgood hio hrb hb hb1 hU hA
  obtain ⟨htile, hv⟩ := tiling_at P c Qc Qm hacc hgood
  have hbal : ∀ r ∈ Finset.Icc 1 P.optimized.family.problem.cfg.kMem, ∀ e,
      readCount e (decodedMTreeOfEnvs (Batch824.envsKR P c Qm) (Batch824.envsFR P c Qm)
        P.optimized.family.problem.cfg.kMem r) =
      verifyCount e (decodedMTreeOfEnvs (Batch824.envsKR P c Qm) (Batch824.envsFR P c Qm)
        P.optimized.family.problem.cfg.kMem r) :=
    fun r hr e => (hpath r hr).1 e
  have hst' : memRowStateOf (Batch824.envsFR P c Qm k) = .read_root := by
    rw [← hk]; exact Batch733.memRowStateOf_congr (fun j _ => envsFR_trace P c Qc Qm hacc hgood k j)
  obtain ⟨r, hr, hpair⟩ := Batch971.paired_of_read_row (Batch824.envsKR P c Qm)
    (Batch824.envsFR P c Qm) P.optimized.family.problem.cfg.kMem htile hv hU hbal k hst'
  have hexp : rowExp (Batch824.envsFR P c Qm) k = e := by
    rw [← he]; unfold rowExp; rw [envsFR_trace P c Qc Qm hacc hgood k]; rfl
  rw [hexp] at hpair
  obtain ⟨-, qq, hrp, hvp⟩ := (hpath r hr).2 _ hpair
  have hr' := Finset.mem_Icc.mp hr
  have hkM := MemoryWalkDeployed.kMem_le P
  have hR : ExpInjOn (Batch824.envsFR P c Qm) .read_root :=
    expInjOn_congr _ (fun r => funext fun j => (envsFR_trace P c Qc Qm hacc hgood r j).symm)
      (expInj_read_at P c Qc Qm hacc hgood hio hrb hb1)
  have hV : ExpInjOn (Batch824.envsFR P c Qm) .verify_child :=
    expInjOn_congr _ (fun r => funext fun j => (envsFR_trace P c Qc Qm hacc hgood r j).symm)
      (expInj_verify_at P c Qc Qm hacc hgood hio hrb hb1)
  unfold certAxisOfEnvs
  exact Batch1170.slot_of_paths (Batch824.envsKR P c Qm) (Batch824.envsFR P c Qm)
    P.optimized.family.problem.cfg.memRows_pos P.optimized.family.problem.cfg.kMem (ringChar K)
    htile hv e _ _ r hr'.1 (by change P.optimized.family.problem.cfg.kMem ≤
      P.optimized.family.problem.cfg.memRows at hkM; omega) hR hV hrp hvp
    (rowAt_of P c Qm k hk he) (rowAt_of P c Qm k' hk' he')

include hbasis in
theorem expInj_verify_FR :
    ExpInjOn (Batch824.envsFR P c Qm) .verify_child := by
  have hio := Batch974.hio_of_hgood P c Qc Qm hgood
  have hb1 := Batch824.coord_one_ne_zero_of_formRBasis P hbasis
  exact expInjOn_congr _ (fun r => funext fun j => (envsFR_trace P c Qc Qm hacc hgood r j).symm)
    (expInj_verify_at P c Qc Qm hacc hgood hio P.rowsBound hb1)

include hbasis in
/-- **The served lookup `svF` at exponent `e` is the pre-`z` noun of the `verify_child` row at
`e`.** -/
theorem svF_eq (k' : Fin P.optimized.family.problem.cfg.memRows) {e : ℕ}
    (hk' : memRowStateOf (memEnvF P c Qm k') = .verify_child) (he' : expR P c Qm k' = e) :
    svF P c Qm .verify_child e = NN (k'.val + 1) := by
  show PreZComputeCore.Served.servedNounOfEnvs K (ringChar K) P.optimized.family.problem.cfg.kMem
    (memoryEnvsR0 P.optimized (honestQm P c Qm) c) P.optimized.family.problem.cfg.memRows_pos
    .verify_child e = _
  rw [PreZComputeCore.Served.servedNounOfEnvs_congr K (ringChar K) P.optimized.family.problem.cfg.kMem
    (envs := memoryEnvsR0 P.optimized (honestQm P c Qm) c) (envs' := Batch824.envsFR P c Qm)
    (fun i col _ => by rw [OptimizedFailureEventEv.memoryBaseEnv_trace P (honestQm P c Qm) c i])
    P.optimized.family.problem.cfg.memRows_pos]
  exact servedNoun_eq _ _ _ _ _ _ _ (expInj_verify_FR P c Qc Qm hacc hgood hbasis)
    (rowAt_of P c Qm k' hk' he')

theorem sep_eq (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (k : Fin P.optimized.family.problem.cfg.memRows) {e : ℕ}
    (hk : memRowStateOf (memEnvF P c Qm k) = .read_root) (he : expR P c Qm k = e) {t : Noun}
    (ht : requestTargets (skeletonEv P.optimized (honestQc P c Qc) (honestQm P c Qm)) .read_root e = t)
    (hl : t.leaves ≤ P.optimized.Λ) (hbt : BoundedBy (ringChar K) t)
    (henc : enc (nprSeed c.1) (NN (k.val + 1)) = enc (nprSeed c.1) t) :
    NN (k.val + 1) = t := by
  have hpair := (optimizedFailureEventEv_good_components P _ _ c hgoodEv).2.2.2.2.2.2.2.2.2.2.2.1
  unfold reqPairEv PreSeedCensus.reqPairEventOfEnvs at hpair
  rw [mem_liftSeed_iff, mem_pairBadSeeds_iff] at hpair
  push_neg at hpair
  obtain ⟨htile, hv⟩ := tiling_at P c Qc Qm hacc hgood
  have hv' : BFSValidF P.optimized.family.problem.cfg.kMem
      (preFoOfEnvs (Batch824.envsFR P c Qm) P.optimized.family.problem.cfg.memRows_pos)
      P.optimized.family.problem.cfg.memRows := by
    intro j hj1 hj2
    rw [Batch1170.Sf_pre (Batch824.envsFR P c Qm) P.optimized.family.problem.cfg.memRows_pos
      P.optimized.family.problem.cfg.kMem htile hv (j - 1) (by omega)]
    exact hv j hj1 hj2
  have hNl : (NN (k.val + 1)).leaves ≤ P.optimized.family.problem.cfg.memRows :=
    preZNounOfEnvs_leaves_le K _ _ _ _ hv' (by omega) k.isLt
  have hmem : (NN (k.val + 1), t) ∈ reqPairsOfEnvs K P.q P.optimized.family.problem.cfg.kMem
      (P.memoryBaseEnv (honestQm P c Qm)) P.optimized.family.problem.cfg.memRows_pos
      (builtRequestTargets P (honestQc P c Qc) (honestQm P c Qm)) := by
    unfold reqPairsOfEnvs
    refine List.mem_map.2 ⟨k.val + 1, List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
    have hrow := rowAt_of P c Qm k hk he
    obtain ⟨hy, -, hs, hex⟩ := hrow
    rw [P.q_eq_ringChar]
    refine Prod.ext rfl ?_
    show builtRequestTargets P (honestQc P c Qc) (honestQm P c Qm)
      (preLblOfEnvs (Batch824.envsFR P c Qm) P.optimized.family.problem.cfg.memRows_pos (k.val + 1)).1
      (RecordCarrier.natLift (preReqIdxOfEnvs (Batch824.envsFR P c Qm)
        P.optimized.family.problem.cfg.memRows_pos (k.val + 1))) = t
    rw [Batch1170.preLbl_fst _ _ _ (by omega) (by omega), hs]
    unfold preReqIdxOfEnvs
    rw [dif_pos hy]
    exact (congrArg _ hex).trans ht
  have hsep := hpair _ hmem (hNl.trans le_sup_left) (hl.trans le_sup_right)
  exact noun_eq_of_enc_eq _ _ _ hsep (CharP.natCast_injOn_Iio K (ringChar K))
    (decodePre_bounded (K := K) (ringChar K) (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite K)) _)
    hbt henc

end AtTraces

section Main

/-- The C2 join on the family traces at `c` (generic fuel / node / inputs). -/
local notation "JJ" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
/-- The C2 join on the family traces at `c`, rooted at the package claim. -/
local notation "JT" => c2JoinFuel (fun l : (State × DTcomp K) × ℕ => l.1.1)
  (fun l : (State × DTcomp K) × ℕ => l.2) (svF P c Qm) (axF P c Qc)
  (treeS P c Qc).size (treeS P c Qc)
  P.optimized.verifier.raw.claim.subject P.optimized.verifier.raw.claim.formula

/-- **The served-record oracle at positional pairs** — what `Batch1171.Ctx.recs` reads. -/
def ServedRecordsPos : Prop :=
  ∀ (u : NTree ((State × DTcomp K) × ℕ)) (s f : Noun),
    Batch1171.PR (treeS P c Qc) JT u (JJ u.size u s f) →
    Batch1171.RecOK (nprSeed c.1) (ringChar K) P.optimized.Λ u.label (JJ u.size u s f).label

theorem slot3_some {x y : Noun} (h : Noun.slot 3 x = some y) : nounTail x = y := by
  cases x with
  | atom n => simp [Noun.slot] at h
  | cell l r => simp [Noun.slot] at h; simp [nounTail, h]

theorem slot2_some {x y : Noun} (h : Noun.slot 2 x = some y) : nounHead x = y := by
  cases x with
  | atom n => simp [Noun.slot] at h
  | cell l r => simp [Noun.slot] at h; simp [nounHead, h]

/-- The OP9 join's second kid's formula is the served arm. -/
theorem kid1_formula_s9 (u : NTree ((State × DTcomp K) × ℕ)) (hst : u.label.1.1 = .s9)
    (har : u.children.length = 2) (s f : Noun) :
    (kidSkel ((JJ u.size u s f).children.map NTree.label) 1).formula =
      svF P c Qm .verify_child (u.label.2 + 3) := by
  obtain ⟨row, ch⟩ := u
  rcases ch with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, ch⟩⟩⟩ <;> simp [NTree.children] at har
  obtain ⟨m, hm, -⟩ := Batch1171.size_succ row [c0, c1]
  rw [hm, Batch1021.J_s9 (sv := svF P c Qm) (ax := axF P c Qc) _ _ row c0 c1 hst]
  simp only [NTree.children, List.map_cons, List.map_nil, kidSkel, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]
  exact c2JoinFuel_formula _ _ _ _ _ _ _ _

variable (hacc : DeployedAcceptanceAt P c Qc Qm)
  (hgood : c ∉ P.optimizedFailureEvent (honestQc P c Qc) (honestQm P c Qm))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)
  (hα0 : alphaM c.1 ≠ 0)

include hacc hgood hax hbasis hwidth hα0 in
/-- **The record's axis is the recovered certificate axis of its exponent, and its child is the
served noun** — structural records by `slot 2` / `slot 3`, the OP0 / OP9 served records by the
served lookup. -/
theorem axis_child (a : Fin P.optimized.family.problem.cfg.compRows) (j : Fin 3) (st : State)
    (hstdef : StrategyOfTracesLift.computeStateOf
      (StrategyOfTracesLift.decodeSource (rowEnvAt P c Qc a)) = st)
    (hj : (j : ℕ) < Nock.Framework.recordCount st)
    (hact : activeMask (rowEnvAt P c Qc a) j = 1)
    (kids : List ComputeRowSkeleton) (s f C : Noun)
    (hkid : st = .s9 → (kidSkel kids 1).formula = svF P c Qm .verify_child (prefixExpAt P c Qc a + 3))
    (hsv : svF P c Qm .verify_child (expOfAt P c Qc a j) = C)
    (hslot : Noun.slot (certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc a j))
      (Batch1171.c2Rec (svF P c Qm) (axF P c Qc) st (prefixExpAt P c Qc a) s f kids j).root = some C) :
    (Batch1171.c2Rec (svF P c Qm) (axF P c Qc) st (prefixExpAt P c Qc a) s f kids j).axis =
        certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc a j) ∧
      (Batch1171.c2Rec (svF P c Qm) (axF P c Qc) st (prefixExpAt P c Qc a) s f kids j).child = C := by
  have hsatC := hacc.compute_satisfies
  have hsel := Batch1140.rowSelector_of_state P c Qc hsatC a st hstdef
  have hcert := (Batch1140.request_axis P c Qc Qm hacc hgood hax hbasis hwidth hα0 a j hact).1
  have haxF := Batch1140.axF_eq P c Qc Qm hacc hgood hax hbasis hwidth hα0
  have hE := Batch908.envsCR_embeds P c Qc
  have hcol : ∀ col t, col = Nock.Reified.opCol t → (col = 0 ∨ col = 9) →
      (Batch824.envsCR P c Qc a).trace col = if t = st then 1 else 0 := by
    intro col t hct hc
    rw [hE a col (by unfold Batch908.ReadCols; omega), hct,
      Batch1140.base_sel_of P c Qc hsatC a st t hsel]
    split_ifs <;> simp
  have h0 : st ≠ .s0 → (Batch824.envsCR P c Qc a).trace 0 ≠ 1 := by
    intro hne
    rw [hcol 0 .s0 rfl (Or.inl rfl), if_neg (Ne.symm hne)]; exact zero_ne_one
  have h9 : st ≠ .s9 → (Batch824.envsCR P c Qc a).trace 9 ≠ 1 := by
    intro hne
    rw [hcol 9 .s9 rfl (Or.inr rfl), if_neg (Ne.symm hne)]; exact zero_ne_one
  obtain ⟨jv, hjv⟩ := j
  rcases jv with _ | _ | _ | jv
  · -- record 0: `(f, ft, 3)`
    rw [Batch1171.c2Rec_0] at hslot ⊢
    have h3 : certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc a ⟨0, hjv⟩) = 3 := by
      rw [hcert]; simp [slotCert, certAxis]
    rw [h3] at hslot ⊢
    exact ⟨rfl, slot3_some hslot⟩
  · -- record 1
    have hstruct : st ≠ .s0 → certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc a ⟨1, hjv⟩) = 2 := by
      intro hne
      rw [hcert]; simp [slotCert, h0 hne, certAxis]
    cases st <;> simp [Nock.Framework.recordCount] at hj
    · -- s0: served
      rw [Batch1171.c2Rec_s0_1] at hslot ⊢
      refine ⟨by rw [haxF]; rfl, ?_⟩
      rw [← hsv]; rfl
    all_goals first
      | (rw [Batch1171.c2Rec_s2_1] at hslot ⊢)
      | (rw [Batch1171.c2Rec_s5_1] at hslot ⊢)
      | (rw [Batch1171.c2Rec_s6_1] at hslot ⊢)
      | (rw [Batch1171.c2Rec_s7_1] at hslot ⊢)
      | (rw [Batch1171.c2Rec_s8_1] at hslot ⊢)
      | (rw [Batch1171.c2Rec_s9_1] at hslot ⊢)
    all_goals
      rw [hstruct (by decide)] at hslot ⊢
      exact ⟨rfl, slot2_some hslot⟩
  · -- record 2
    cases st <;> simp [Nock.Framework.recordCount] at hj
    · -- s6: structural
      rw [Batch1171.c2Rec_s6_2] at hslot ⊢
      have h2 : certAxisOfEnvs (Batch824.envsCR P c Qc) (expOfAt P c Qc a ⟨2, hjv⟩) = 2 := by
        rw [hcert]; simp [slotCert, h9 (by decide), certAxis]
      rw [h2] at hslot ⊢
      exact ⟨rfl, slot2_some hslot⟩
    · -- s9: served
      rw [Batch1171.c2Rec_s9_2] at hslot ⊢
      refine ⟨by rw [haxF]; rfl, ?_⟩
      rw [hkid rfl, ← hsv]; rfl
  · omega

include hacc hgood hax hbasis hwidth in
theorem servedRecordsPos_of_traces
    (hgoodEv : c ∉ optimizedFailureEventEv P (honestQc P c Qc) (honestQm P c Qm))
    (h : StrategyOfTracesLift.TracesWalkHyps P.optimized (honestQc P c Qc) (honestQm P c Qm) c)
    (hF : ∀ x : F, ∃ n : ℕ, n < ringChar F ∧ (n : F) = x) :
    ServedRecordsPos P c Qc Qm := by
  intro u s f hpr j hj henc hl hbnd
  have hsatC := hacc.compute_satisfies
  have hα0 := Batch1142.hα0_of_goodEv P c Qc Qm hgoodEv
  have hz := FamilyIOChain.nprSeed_ne_of_good_at P c Qc Qm hgood
  obtain ⟨a, huT, hu, hrow⟩ := pos_of_pr P c Qc Qm h hpr
  obtain ⟨st, hstdef⟩ : ∃ st, StrategyOfTracesLift.computeStateOf
      (StrategyOfTracesLift.decodeSource (rowEnvAt P c Qc a)) = st := ⟨_, rfl⟩
  have hlab : u.label = ((st, (StrategyOfTracesLift.decodeInputs (rowEnvAt P c Qc a),
      StrategyOfTracesLift.decodePub (rowEnvAt P c Qc a) st,
      StrategyOfTracesLift.decodeDec (rowEnvAt P c Qc a))), prefixExpAt P c Qc a) := by
    rw [hu, Batch1140.lblCS_eq, Batch1140.lblCAt_eq]
    have hr : Batch1140.rowIdx P (a.val + 1) = a := by
      unfold Batch1140.rowIdx; rw [dif_pos (by omega)]; rfl
    rw [hr, Batch1140.c2SAt_eq P c Qc Qm hacc hgood hax hbasis hwidth hα0 a, hstdef]
  have hwst : (JJ u.size u s f).label.state = st := by
    rw [c2JoinFuel_state, hlab]
  have hj' : (j : ℕ) < Nock.Framework.recordCount st := hwst ▸ hj
  have hsel := Batch1140.rowSelector_of_state P c Qc hsatC a st hstdef
  have hact : activeMask (rowEnvAt P c Qc a) j = 1 := by
    rw [activeMask_eq P c Qc hsatC a st hsel j, if_pos hj']
  obtain ⟨hTR, hTV⟩ := requestTargets_at P c Qc Qm hsatC h a hrow j hj
  obtain ⟨k, k', hk, hk', hrk, hrk', hek, hek'⟩ :=
    served_rows P c Qc Qm hacc hgood hα0 hax hbasis hwidth a j hact
  have hT := traceRec_fp (rowEnvAt P c Qc a) st (StrategyOfTracesLift.decodeInputs (rowEnvAt P c Qc a))
    (StrategyOfTracesLift.decodeDec (rowEnvAt P c Qc a)) (prefixExpAt P c Qc a) j
  rw [← hlab] at hT
  have hmroot : (Batch1011.L P c Qm k).2.2.mem.root =
      ⟨rowRecord (rowEnvAt P c Qc a) j 0, rowRecord (rowEnvAt P c Qc a) j 1,
        rowRecord (rowEnvAt P c Qc a) j 2⟩ := by
    have e0 := congrFun hrk 0
    have e1 := congrFun hrk 1
    have e2 := congrFun hrk 2
    simp only [OptimizedMemoryHostileAccumulator.rowRecord] at e0 e1 e2
    exact ComputeTable.FP.ext e0 e1 e2
  have hmchild : (Batch1011.L P c Qm k').2.2.mem.child =
      ⟨rowRecord (rowEnvAt P c Qc a) j 3, rowRecord (rowEnvAt P c Qc a) j 4,
        rowRecord (rowEnvAt P c Qc a) j 5⟩ := by
    have e3 := congrFun hrk' 3
    have e4 := congrFun hrk' 4
    have e5 := congrFun hrk' 5
    simp only [OptimizedMemoryHostileAccumulator.rowRecord] at e3 e4 e5
    exact ComputeTable.FP.ext e3 e4 e5
  obtain ⟨-, heqk⟩ := Batch1011.eqBlk_at P c Qc Qm hacc hgood hax hbasis hwidth k
  have hptk := Batch1011.eqBlk_readRoot_root heqk (by rw [Batch1011.L_st]; exact hk)
  obtain ⟨-, heqk'⟩ := Batch1011.eqBlk_at P c Qc Qm hacc hgood hax hbasis hwidth k'
  have hptk' := Batch1011.eqBlk_verifyChild_child heqk' (by rw [Batch1011.L_st]; exact hk')
  have hNk := enc_NN P c Qc Qm hacc hgood hax hbasis hwidth h hz hF k
  have hNk' := enc_NN P c Qc Qm hacc hgood hax hbasis hwidth h hz hF k'
  have hencR : enc (nprSeed c.1) (NN (k.val + 1)) =
      enc (nprSeed c.1) ((JJ u.size u s f).label.memoryRecord j hj).root := by
    rw [hNk, ← hptk, hmroot, ← hT.1, henc]
  have hroot := sep_eq P c Qc Qm hacc hgood hgoodEv k hk hek hTR hl hbnd hencR
  have hslot := slot_at P c Qc Qm hacc hgood hwidth hbasis k k' hk hk' hek hek'
  rw [hroot] at hslot
  have hsv := svF_eq P c Qc Qm hacc hgood hbasis k' hk' hek'
  have hJr := Batch1171.J_rec (sv := svF P c Qm) (ax := axF P c Qc) u.size u s f j hj
  rw [hJr] at hslot ⊢
  have hkid : st = .s9 → (kidSkel ((JJ u.size u s f).children.map NTree.label) 1).formula =
      svF P c Qm .verify_child (prefixExpAt P c Qc a + 3) := by
    intro h9
    have har := (Batch1111.rowFacts_core P c Qc Qm hacc hgood hax hbasis hwidth h u huT).2.2.2.1
    have hst9 : u.label.1.1 = .s9 := by rw [hlab]; exact h9
    rw [hst9] at har
    have := kid1_formula_s9 P c Qc Qm u hst9 (by simpa [fanoutComp] using har) s f
    rw [this, hlab]
  have hl1 : u.label.1.1 = st := by rw [hlab]
  have hl2 : u.label.2 = prefixExpAt P c Qc a := by rw [hlab]
  rw [hl1, hl2] at hslot ⊢
  obtain ⟨hAx, hCh⟩ := axis_child P c Qc Qm hacc hgood hax hbasis hwidth hα0 a j st hstdef hj' hact
    _ s f _ hkid hsv hslot
  refine ⟨?_, ?_⟩
  · rw [hAx, hCh]; exact hslot
  · rw [hCh, hNk', ← hptk', hmchild, ← hT.2]

end Main

end

end Nock.RedTeam.Batch1172
