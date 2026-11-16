/-
  Nock/RedTeam/Batch999Thm54HonestPathValidity.lean

At `P := buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF` (the shape of the generated
  package; `E` a buildable carrier, generic in the program), canonical traces:

  1. **`decoded_eq_axisTree`** -- the decoded tree of root `r` is the carrier's a-bearing axis tree
     of root `r - 1` (`exactAxisTree E.cfg E.execA`, the honest template's axis tree:
     `D.honest_execA`), exponents renamed by `gExp` and the verify `a` erased.
  2. **`honest_uniqueExponents`**, **`honest_formRPathValid`** -- the decoded tree has unique
     exponents and is `FormRPathValid` at the honest certificate-axis map `certAxis E` (the axis of
     the forest's service at each decoded exponent), and the decoded compute certificate IS that
     map's certificate on the tree's exponents (`decodedCert_eq`).
  3. **`honest_lam`** -- component 11: the honest tuple is outside the decoded λ-event, through
     `Batch961.lam_of_rootPolys_zero`.

  Premises beyond the package's own arguments, each a generator obligation:
  `hax : FormRAxisBound` (`genComputeRows_rowsFormRAxisBound`), `hwidth : FormRWidth F`
  (`FormRWidth_of_hp64`), `hC : E.exec.CprimeCoherent` (`genExactExecution_cprimeCoherent`), and
  `hsvc` -- every service axis of the served trace is below `ringChar K`.

  -- the paper
-/
import Nock.RedTeam.Batch998Thm54HonestExponentCoherence

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch999

open scoped Classical
open Nock
open Nock.Walk
open Nock.Reified
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.OptimizedComputeFormRDenoms
open Nock.NockVMROM.Thm54.OptimizedComputeSampledTrace
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.BuildableChips
open Nock.NockVMROM.Thm54.BuildablePackage
open Nock.NockVMROM.Thm54.WalkTilingEvents
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.FormRAxisEvent
open Nock.RedTeam.Batch575
open Nock.RedTeam.Batch995
open Nock.RedTeam.Batch996
open Nock.RedTeam.Batch998

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)] [FiniteDimensional F K]

/-! ## A. Global injectivity of `gExp` on service exponents, the honest certificate axis -/

section Carrier

variable (E : BuildableNockExecution F K)

theorem gExp_inj_svc {s1 s2 : Service E.cfg E.execA} (hs1 : s1 ∈ allSvc E)
    (hs2 : s2 ∈ allSvc E) (hg : gExp E s1.exponent = gExp E s2.exponent) : s1 = s2 := by
  unfold gExp at hg
  rw [recOf_eq E hs1, recOf_eq E hs2] at hg
  have hm1 := svc_enc_mem E hs1
  have hm2 := svc_enc_mem E hs2
  unfold RecordCarrier.honestExp at hg
  have hidx : (reqList E).idxOf (NockVM.encRecFormR s1.record E.cfg.challenges.lam) =
      (reqList E).idxOf (NockVM.encRecFormR s2.record E.cfg.challenges.lam) := by omega
  have henc : NockVM.encRecFormR s1.record E.cfg.challenges.lam =
      NockVM.encRecFormR s2.record E.cfg.challenges.lam := by
    have a1 := List.idxOf_lt_length_of_mem hm1
    have a2 := List.idxOf_lt_length_of_mem hm2
    rw [← List.getElem_idxOf a1, ← List.getElem_idxOf a2]
    simp only [hidx]
  have hts := congrArg (fun v => v 7) henc
  simp only [encRecFormR_ts] at hts
  rw [s1.timestamp, s2.timestamp] at hts
  exact svc_eq_of_pow E hs1 hs2 hts

/-- **The honest certificate-axis map**: at a decoded exponent, the axis of the forest's service
whose exponent it decodes. -/
def certAxis (x : ℕ) : ℕ :=
  if h : ∃ s ∈ allSvc E, gExp E s.exponent = x then (Classical.choose h).axis else 0

theorem certAxis_eq {s : Service E.cfg E.execA} (hs : s ∈ allSvc E) :
    certAxis E (gExp E s.exponent) = s.axis := by
  have h : ∃ s' ∈ allSvc E, gExp E s'.exponent = gExp E s.exponent := ⟨s, hs, rfl⟩
  unfold certAxis
  rw [dif_pos h]
  obtain ⟨hmem, hg⟩ := Classical.choose_spec h
  rw [gExp_inj_svc E hmem hs hg]

theorem certAxis_lt (hsvc : ∀ i, ∀ s ∈ (E.memoryTrace.roots i).services, s.axis < ringChar K)
    (x : ℕ) : certAxis E x < ringChar K := by
  unfold certAxis
  split
  · rename_i h
    obtain ⟨hmem, -⟩ := Classical.choose_spec h
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hmem
    exact hsvc i _ hi
  · exact (CharP.char_is_prime K (ringChar K)).pos

/-- Unique exponents of a renamed tree (from `Nodup` exponent lists). -/
theorem uniqueExponents_rn (g : ℕ → ℕ) (t : MTree K) (hg : InjOnExps g (fun x => x ∈ exps t))
    (hR : (readExps t).Nodup) (hV : (verifyExps t).Nodup) : UniqueExponents (rn g t) := by
  intro x
  by_cases h : ∃ e ∈ exps t, g e = x
  · obtain ⟨e, he, rfl⟩ := h
    rw [readCount_rn g (fun x => x ∈ exps t) hg e he t (fun _ h => h),
      verifyCount_rn g (fun x => x ∈ exps t) hg e he t (fun _ h => h)]
    exact ⟨readCount_le_one e t hR, verifyCount_le_one e t hV⟩
  · push Not at h
    rw [readCount_rn_out g x t h, verifyCount_rn_out g x t h]
    omega

end Carrier

theorem slotActive_of_lt (Rf : PlusIOSegmentedFamily F K) (i : Fin Rf.problem.cfg.compRows)
    (j : ℕ) (hj : j < (NockVM.activeRequestRecords (Rf.problem.exec.computePubAt i)).length) :
    slotActive Rf i ⟨j, by
      have : (NockVM.activeRequestRecords (Rf.problem.exec.computePubAt i)).length ≤ 3 := by
        unfold NockVM.activeRequestRecords; split <;> simp
      omega⟩ = 1 := by
  have hle : (NockVM.activeRequestRecords (Rf.problem.exec.computePubAt i)).length ≤ 3 := by
    unfold NockVM.activeRequestRecords; split <;> simp
  rcases j with _ | _ | _ | j
  · rfl
  · unfold NockVM.activeRequestRecords at hj
    simp only [slotActive]
    cases hs : (Rf.problem.exec.computePubAt i).state <;> simp_all [secondRequestMask]
  · unfold NockVM.activeRequestRecords at hj
    simp only [slotActive]
    cases hs : (Rf.problem.exec.computePubAt i).state <;> simp_all [thirdRequestMask]
  · exfalso; omega

/-! ## B. The generated package -/

section Package

variable (E : BuildableNockExecution F K) (I : BuildableChips.Inputs E) (R : CommitmentResidual E)
  (hzero : I.computeChallenges =
    (default : OptimizedComputeCollisionBound.FinalComputeChallengeTuple K))
  (hprl : RowLayout.PairedRecordLayout E.exec)
  (hmore : BuildableAxisWitness.LaterSeedZeros E)
  (hord : 2 ≤ E.cfg.compRows → E.cfg.compRows ≤ orderOf I.computeWalkAlpha)
  (hordM : 2 ≤ E.cfg.memRows → E.cfg.memRows ≤ orderOf I.memoryWalkAlpha)
  (hrows : 3 * E.cfg.compRows < ringChar K ∧ E.cfg.memRows < ringChar K)
  (hgenF : GeneratedField.ClaimGenerated K R.verifier.raw.claim R.Λ)
  (hF : GeneratedField.PrimeFieldElems F)

/-- The generated package (the shape `nockCompiles` builds). -/
abbrev Pkg : OptimizedFullStrictNockVMROMPackage F K I.hOrb :=
  buildFullPackage E I R hzero hprl hmore hord hordM hrows hgenF hF

/-- Canonical memory base environments of the package. -/
abbrev envsF : Fin E.cfg.memRows → Env F :=
  (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).memoryBaseEnv
    (MultiRootOptimizedAcceptance.canonicalMemoryTrace (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF))

/-- Canonical memory source environments of the package. -/
abbrev envsK : Fin E.cfg.memRows → Env K :=
  (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).memorySourceEnv
    (MultiRootOptimizedAcceptance.canonicalMemoryTrace (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF))

include I R hzero hprl hmore hord hordM hrows hgenF hF in
theorem honestVer_pkg : ∀ row ∈ E.exec.memoryRows,
    row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root) :=
  (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.sampled.honestVer

/-- The memory row of the executed list at index `r`. -/
theorem memoryPubAt_eq (r : Fin E.cfg.memRows) (t : NTree (MLT K))
    (ht : (bfsForest E.exec.memoryForest)[(r : ℕ)]? = some t) :
    E.exec.memoryPubAt r = t.label.2.2 ∧ t.label ∈ E.exec.memoryRows := by
  have hmem : t.label ∈ E.exec.memoryRows :=
    List.mem_map.mpr ⟨t, List.mem_of_getElem? ht, rfl⟩
  refine ⟨?_, hmem⟩
  unfold ExactExecution.memoryPubAt ExactExecution.memoryRowAt
  simp only [List.get_eq_getElem, Fin.val_cast]
  have h := congrArg (Option.map NTree.label) ht
  simp only [Option.map_some] at h
  have hr : (r : ℕ) < E.exec.memoryRows.length := by
    rw [E.exec.memoryRows_length]; exact r.isLt
  have : E.exec.memoryRows[(r : ℕ)]? = some t.label := by
    unfold ExactExecution.memoryRows; rw [List.getElem?_map, ht]; rfl
  rw [List.getElem?_eq_getElem hr] at this
  rw [Option.some.inj this]

theorem hst_pkg : ∀ (r : Fin E.cfg.memRows) (t : NTree (MLT K)),
    (bfsForest E.exec.memoryForest)[(r : ℕ)]? = some t →
      memRowStateOf (envsF E I R hzero hprl hmore hord hordM hrows hgenF hF r) = t.label.1 := by
  intro r t ht
  have h := Batch959.memRowState_honest (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF) r
  obtain ⟨hpub, hmem⟩ := memoryPubAt_eq E r t ht
  rw [h]
  change (E.exec.memoryPubAt r).st = _
  rw [hpub, exec_row_st E _ hmem]

theorem hex_pkg : ∀ (r : Fin E.cfg.memRows) (t : NTree (MLT K)),
    (bfsForest E.exec.memoryForest)[(r : ℕ)]? = some t →
      rowExp (envsF E I R hzero hprl hmore hord hordM hrows hgenF hF) r = exE E t.label := by
  intro r t ht
  obtain ⟨hpub, -⟩ := memoryPubAt_eq E r t ht
  unfold rowExp
  rw [show envsF E I R hzero hprl hmore hord hordM hrows hgenF hF r =
      OptimizedCanonicalHostileLists.honestMemBase (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF) r
    from rfl]
  unfold OptimizedCanonicalHostileLists.honestMemBase
  erw [OptimizedCanonicalHostileLists.canonical_memoryBaseEnv,
    OptimizedMemoryCanonicalSatisfaction.canonical_physical_reqIdx _ _
      (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.memoryNodes_injective]
  unfold OptimizedMemorySemanticRealization.honestReqIdx
    OptimizedMemorySemanticRealization.reqIdxNat exE
  change RecordCarrier.natLift ((((if (E.exec.memoryPubAt r).st = .read_root ∨
      (E.exec.memoryPubAt r).st = .verify_child then
      RecordCarrier.honestExp E.exec.derivedRequestIO
        (NockVM.encRecC (E.exec.memoryPubAt r).mem (E.exec.memoryPubAt r).cprime) else 0 : ℕ)) :
      F)) = _
  rw [hpub]

theorem htopo_pkg : ∀ t ∈ bfsForest E.exec.memoryForest,
    MemoryTable.fanoutMem t.label.1 = t.children.length := by
  intro t ht
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp ht
  rw [E.exec.memoryForest_eq_ofFn_memoryTreeAt] at hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact (E.language.traversable.exactAxisBridgeLocal i).fanout t hin

/-- The roots occupy the BFS prefix. -/
theorem bfs_root (i : Fin E.cfg.kMem) :
    (bfsForest E.exec.memoryForest)[(i : ℕ)]? = some (E.exec.memoryTreeAt i) := by
  rw [bfsForest_eq_append_flatMap _ E.exec.memoryForest_nonempty]
  have hi : (i : ℕ) < E.exec.memoryForest.length := by
    rw [E.exec.memory_root_count]; exact i.isLt
  rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  unfold ExactExecution.memoryTreeAt
  simp [List.get_eq_getElem]

/-- **T1. The decoded tree is the carrier's (honest template's) axis tree**, exponents renamed
by `gExp`, verify `a` erased. -/
theorem decoded_eq_axisTree (hC : E.exec.CprimeCoherent) (i : Fin E.cfg.kMem) :
    decodedMTreeOfEnvs (envsK E I R hzero hprl hmore hord hordM hrows hgenF hF)
        (envsF E I R hzero hprl hmore hord hordM hrows hgenF hF) E.cfg.kMem ((i : ℕ) + 1) =
      rn (gExp E) (exactAxisTree E.cfg E.execA i) := by
  have hroots : E.exec.memoryForest.length = E.cfg.kMem := E.exec.memory_root_count
  have h := decoded_eq_mt E.exec.memoryForest E.exec.memoryForest_nonempty
    E.exec.memory_bfs_length (envsK E I R hzero hprl hmore hord hordM hrows hgenF hF)
    (envsF E I R hzero hprl hmore hord hordM hrows hgenF hF) (exE E)
    (hst_pkg E I R hzero hprl hmore hord hordM hrows hgenF hF)
    (hex_pkg E I R hzero hprl hmore hord hordM hrows hgenF hF) (htopo_pkg E)
    ((i : ℕ) + 1) (E.exec.memoryTreeAt i) (by omega) (by simpa using bfs_root E i)
  rw [hroots] at h
  rw [h, exec_memoryTreeAt]
  unfold exactAxisTree
  exact mt_mapNTree_eq_rn (exE E) (MemoryRowTemplate.encodeRow E.cfg.challenges.lam)
    (fun a => MemoryRowTemplate.encodeRow_fst _ a) (timestampExpAt E.cfg.challenges.α) (gExp E)
    _ (topoA E i) (fun x hx hlive =>
      exE_live E hrows.1 (honestVer_pkg E I R hzero hprl hmore hord hordM hrows hgenF hF) hprl hC i hx
        hlive)

/-! ### The decoded certificate at a service's decoded exponent -/

/-- **The decoded certificate at a service's decoded exponent is the service axis's
certificate** (canonical compute trace, no acceptance). -/
theorem decoded_svc (hax : FormRAxisBound
      (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F)
    (hsvc : ∀ i, ∀ s ∈ (E.memoryTrace.roots i).services, s.axis < ringChar K)
    (i : Fin E.cfg.kMem) {s : Service E.cfg E.execA} (hs : s ∈ (E.memoryTrace.roots i).services) :
    decodedShift (Batch997.envsC (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF))
        (gExp E s.exponent) = MemoryTable.formRCertShift s.axis ∧
      ∀ k, 1 ≤ k → decodedBits (Batch997.envsC (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF))
        (gExp E s.exponent) k = MemoryTable.formRCertBit s.axis (k - 1) := by
  set P := Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF with hP
  have hsA := mem_allSvc E hs
  -- locate the service record among the active requests
  have hreq : s.record ∈ E.exec.rawRequests := by rw [exec_rawRequests]; exact s.request_mem
  unfold ExactExecution.rawRequests at hreq
  obtain ⟨row, hrow, hin⟩ := List.mem_flatMap.mp hreq
  obtain ⟨⟨i', hi'⟩, hrow'⟩ := List.mem_iff_get.mp hrow
  have hi'c : i' < E.cfg.compRows := by rw [← E.exec.computeRows_length]; exact hi'
  let ic : Fin P.optimized.family.problem.cfg.compRows := ⟨i', hi'c⟩
  have hpub : P.optimized.family.problem.exec.computePubAt ic = row.2.2.1 := by
    change (E.exec.computeRowAt ⟨i', hi'c⟩).2.2.1 = _
    unfold ExactExecution.computeRowAt
    rw [← hrow']; rfl
  rw [← hpub] at hin
  obtain ⟨j, hj, hjrec⟩ := List.mem_iff_getElem.mp hin
  have hact := slotActive_of_lt P.optimized.family ic j hj
  set jj : Fin 3 := ⟨j, _⟩ with hjj
  have hslot : slotRecord P.optimized.family ic jj = s.record := by
    obtain ⟨hj', hrec⟩ := slotRecord_active P.optimized.family ic jj hact
    rw [hrec]; exact hjrec
  -- its decoded exponent
  have hexp : gExp E s.exponent = honestS P.optimized.family ic + (jj : ℕ) + 1 := by
    unfold gExp
    rw [recOf_eq E hsA]
    have h := honestExp_activeRequest P.optimized.sampled ic j hj
    rw [hjrec] at h
    exact h
  -- the axis
  have hax' : MemoryTable.nockAxisOf (slotRecord P.optimized.family ic jj).axis = s.axis := by
    rw [hslot, s.realization.axis_realizes]
    exact MemoryTable.nockAxisOf_natCast (hsvc i s hs)
  have hd := Batch997.decoded_canon P hax hwidth ic jj hact
  rw [hax'] at hd
  rw [hexp]
  exact hd

/-! ### The paths -/

/-- The path premise of `formRCounts_rn_zero` at root `i`, for the certificate maps `(mm, cc)`
agreeing with the service axis's certificate at every service's decoded exponent. -/
theorem hpath_root (hsvc : ∀ i, ∀ s ∈ (E.memoryTrace.roots i).services, s.axis < ringChar K)
    (i : Fin E.cfg.kMem) (mm : ℕ → ℕ) (cc : ℕ → ℕ → Bool)
    (hmm : ∀ s ∈ (E.memoryTrace.roots i).services,
      mm (gExp E s.exponent) = MemoryTable.formRCertShift s.axis ∧
        ∀ k, 1 ≤ k → cc (gExp E s.exponent) k = MemoryTable.formRCertBit s.axis (k - 1)) :
    ∀ e ∈ readExps (exactAxisTree E.cfg E.execA i), ∃ a q, 1 ≤ a ∧ a.log2 ≤ formRN K - 1 ∧
      Batch554.rpaths e (exactAxisTree E.cfg E.execA i) = [q] ∧
      Batch554.vpaths e (exactAxisTree E.cfg E.execA i) = [q ++ axisPath a] ∧
      mm (gExp E e) = MemoryTable.formRCertShift a ∧
      ∀ k, 1 ≤ k → cc (gExp E e) k = MemoryTable.formRCertBit a (k - 1) := by
  intro e he
  have hts := E.memoryTrace.rootTimestampPowersNodup i
  obtain ⟨s, hs, hse, q, hq, hv⟩ := ServiceWalk.paths (E.memoryTrace.roots i).traversal
    ((E.memoryTrace.roots i).readExps_nodup hts) ((E.memoryTrace.roots i).verifyExps_nodup hts) e he
  subst hse
  refine ⟨s.axis, q, s.axis_pos, ?_, hq, hv, (hmm s hs).1, (hmm s hs).2⟩
  have h := certInRange_of_lt (K := K) (fun _ => s.axis) (fun _ => hsvc i s hs) 0
  unfold certShiftOf at h
  rwa [MemoryTable.formRCertShift_eq_log2] at h

/-- **T2a. Unique exponents of the decoded tree.** -/
theorem honest_uniqueExponents (hC : E.exec.CprimeCoherent) (i : Fin E.cfg.kMem) :
    UniqueExponents (decodedMTreeOfEnvs (envsK E I R hzero hprl hmore hord hordM hrows hgenF hF)
      (envsF E I R hzero hprl hmore hord hordM hrows hgenF hF) E.cfg.kMem ((i : ℕ) + 1)) := by
  rw [decoded_eq_axisTree E I R hzero hprl hmore hord hordM hrows hgenF hF hC i]
  have hts := E.memoryTrace.rootTimestampPowersNodup i
  exact uniqueExponents_rn (gExp E) _ (gExp_inj E i)
    ((E.memoryTrace.roots i).readExps_nodup hts) ((E.memoryTrace.roots i).verifyExps_nodup hts)

/-- **T2b. Honest Form R path validity of the decoded tree**, at the honest certificate-axis
map. -/
theorem honest_formRPathValid (hC : E.exec.CprimeCoherent)
    (hsvc : ∀ i, ∀ s ∈ (E.memoryTrace.roots i).services, s.axis < ringChar K)
    (i : Fin E.cfg.kMem) :
    FormRPathValid (certAxis E)
      (decodedMTreeOfEnvs (envsK E I R hzero hprl hmore hord hordM hrows hgenF hF)
        (envsF E I R hzero hprl hmore hord hordM hrows hgenF hF) E.cfg.kMem ((i : ℕ) + 1)) := by
  have hU := honest_uniqueExponents E I R hzero hprl hmore hord hordM hrows hgenF hF hC i
  rw [decoded_eq_axisTree E I R hzero hprl hmore hord hordM hrows hgenF hF hC i] at hU ⊢
  have hts := E.memoryTrace.rootTimestampPowersNodup i
  refine (formR_identity_iff_path (certAxis E) _ hU
    (certInRange_of_lt _ (certAxis_lt E hsvc))).mp ?_
  unfold FormRRootIdentity formRPolyOfCert
  refine formRCounts_rn_zero (formRN K) (certShiftOf (certAxis E)) (certBitsOf (certAxis E))
    (gExp E) _ (gExp_inj E i) ((E.memoryTrace.roots i).readExps_nodup hts)
    ((E.memoryTrace.roots i).verifyExps_nodup hts) ((E.memoryTrace.roots i).support)
    (hpath_root E hsvc i _ _ fun s hs => ⟨?_, fun k _ => ?_⟩)
  · unfold certShiftOf; rw [certAxis_eq E (mem_allSvc E hs)]
  · unfold certBitsOf; rw [certAxis_eq E (mem_allSvc E hs)]

/-- **The decoded compute certificate is the honest certificate-axis map's certificate** on the
decoded tree's exponents. -/
theorem decodedCert_eq (hax : FormRAxisBound
      (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) (hC : E.exec.CprimeCoherent)
    (hsvc : ∀ i, ∀ s ∈ (E.memoryTrace.roots i).services, s.axis < ringChar K)
    (i : Fin E.cfg.kMem) (x : ℕ)
    (hx : x ∈ exps (decodedMTreeOfEnvs (envsK E I R hzero hprl hmore hord hordM hrows hgenF hF)
        (envsF E I R hzero hprl hmore hord hordM hrows hgenF hF) E.cfg.kMem ((i : ℕ) + 1))) :
    decodedShift (Batch997.envsC (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF)) x =
        certShiftOf (certAxis E) x ∧
      ∀ k, 1 ≤ k → decodedBits (Batch997.envsC (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF)) x k =
        certBitsOf (certAxis E) x k := by
  rw [decoded_eq_axisTree E I R hzero hprl hmore hord hordM hrows hgenF hF hC i, exps_rn] at hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨s, hs, rfl⟩ := exps_svc E i he
  have hd := decoded_svc E I R hzero hprl hmore hord hordM hrows hgenF hF hax hwidth hsvc i hs
  refine ⟨?_, fun k hk => ?_⟩
  · rw [hd.1]; unfold certShiftOf; rw [certAxis_eq E (mem_allSvc E hs)]
  · rw [hd.2 k hk]; unfold certBitsOf; rw [certAxis_eq E (mem_allSvc E hs)]

/-- **The decoded root polynomial of every root vanishes identically.** -/
theorem rootPoly_zero (hax : FormRAxisBound
      (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) (hC : E.exec.CprimeCoherent)
    (hsvc : ∀ i, ∀ s ∈ (E.memoryTrace.roots i).services, s.axis < ringChar K)
    (r : ℕ) (hr : r ∈ Finset.Icc 1 E.cfg.kMem) :
    decodedRootPoly (Batch997.envsC (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF))
      (envsK E I R hzero hprl hmore hord hordM hrows hgenF hF)
      (envsF E I R hzero hprl hmore hord hordM hrows hgenF hF) E.cfg.kMem r = 0 := by
  obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
  obtain ⟨i, rfl⟩ : ∃ i : Fin E.cfg.kMem, r = (i : ℕ) + 1 := ⟨⟨r - 1, by omega⟩, by simp; omega⟩
  unfold decodedRootPoly
  rw [decoded_eq_axisTree E I R hzero hprl hmore hord hordM hrows hgenF hF hC i]
  have hts := E.memoryTrace.rootTimestampPowersNodup i
  exact formRCounts_rn_zero (formRN K) _ _ (gExp E) _ (gExp_inj E i)
    ((E.memoryTrace.roots i).readExps_nodup hts) ((E.memoryTrace.roots i).verifyExps_nodup hts)
    ((E.memoryTrace.roots i).support)
    (hpath_root E hsvc i _ _ fun s hs =>
      decoded_svc E I R hzero hprl hmore hord hordM hrows hgenF hF hax hwidth hsvc i hs)

/-- Component 11 at the generated package**: the honest tuple is outside the decoded
λ-event at the canonical traces. No `hgood`, no event premise. -/
theorem honest_lam (hax : FormRAxisBound
      (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.sampled
      (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) (hC : E.exec.CprimeCoherent)
    (hsvc : ∀ i, ∀ s ∈ (E.memoryTrace.roots i).services, s.axis < ringChar K) :
    (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).honestTuple ∉
      (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF).decodedLambdaEventOf
        (MultiRootOptimizedAcceptance.canonicalComputeTrace (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF))
        (MultiRootOptimizedAcceptance.canonicalMemoryTrace (Pkg E I R hzero hprl hmore hord hordM hrows hgenF hF)) :=
  Batch961.lam_of_rootPolys_zero _
    (rootPoly_zero E I R hzero hprl hmore hord hordM hrows hgenF hF hax hwidth hC hsvc)

end Package

end

end Nock.RedTeam.Batch999

#print axioms Nock.RedTeam.Batch999.decoded_eq_axisTree
#print axioms Nock.RedTeam.Batch999.honest_uniqueExponents
#print axioms Nock.RedTeam.Batch999.honest_formRPathValid
#print axioms Nock.RedTeam.Batch999.decodedCert_eq
#print axioms Nock.RedTeam.Batch999.honest_lam
