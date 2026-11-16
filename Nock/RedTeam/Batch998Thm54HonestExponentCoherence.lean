/-
  Nock/RedTeam/Batch998Thm54HonestExponentCoherence.lean

  No `hgood`, no event, no acceptance of a trace.

  This module
  shows, at a buildable carrier `E` (generic in the program), that on every `read_root` /
  `verify_child` node of the a-bearing forest the decoded exponent of the row-encoded label is
  `g (timestampExpAt α node)`, with

    `g e := honestExp L (encRecFormR (recOf e) λ)`,  `recOf e` the record of the forest's service
    at exponent `e`,

  and that `g` is injective on each root's exponents.  The sources, all generator facts:

  * read rows emit their record (`honestVer` of the package's sampled assignment) and the emitted
    records of a root are its services' records (`RootTrace.recordPartition`);
  * every tree exponent is a service exponent (`readPartition` / `verifyPartition`), services have
    pairwise distinct timestamps forest-wide (`ExactServedMemoryTrace.timestampPowersNodup`);
  * a `verify_child` row consumes a record some `read_root` row adds (`PairedRecordLayout E.exec`,
    an argument of `buildFullPackage`), and equal records carry equal `C'`
    (`ExactExecution.CprimeCoherent`, the carrier's `genExactExecution_cprimeCoherent` at the
    generated execution);
  * the request list is duplicate-free (`BuildableNockExecution.requestNodup`).
-/
import Nock.RedTeam.Batch997Thm54HonestComputeCertDecode

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch998

open scoped Classical
open Nock
open Nock.Walk
open Nock.AxisBatching
open Nock.AxisBatching.MTree
open Nock.AxisBridge
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.RedTeam.Batch995
open Nock.RedTeam.Batch996

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)] [FiniteDimensional F K]
variable (E : BuildableNockExecution F K)

/-! ## A. Generic tree facts -/

theorem inTree_mapNTree_of {α β : Type*} (f : α → β) {t s : NTree α} (h : InTree t s) :
    InTree (mapNTree f t) (mapNTree f s) := by
  induction h with
  | here c => exact InTree.here _
  | @sub c s t hs _ ih =>
      obtain ⟨a, ch⟩ := c
      refine InTree.sub (s := mapNTree f s) ?_ ih
      simp only [mapNTree, NTree.children]
      exact List.mem_map.mpr ⟨s, hs, rfl⟩

theorem mapNTree_children_length {α β : Type*} (f : α → β) (t : NTree α) :
    (mapNTree f t).children.length = t.children.length := by
  obtain ⟨a, ch⟩ := t; simp [mapNTree]

theorem mapNTree_label' {α β : Type*} (f : α → β) (t : NTree α) :
    (mapNTree f t).label = f t.label := mapNTree_label f t

/-- A read / verify node of a topologically exact tree occurs in the axis tree's exponent lists. -/
theorem exp_mem_of_inTree (Ex : NTree (MLT K) → ℕ) :
    ∀ t : NTree (MLT K),
      AllNodes (fun s => MemoryTable.fanoutMem s.label.1 = s.children.length) t →
      ∀ x, InTree t x →
        (x.label.1 = .read_root → Ex x ∈ readExps (ofNTree Ex t).toMTree) ∧
        (x.label.1 = .verify_child → Ex x ∈ verifyExps (ofNTree Ex t).toMTree) := by
  suffices key : ∀ n (t : NTree (MLT K)), t.size ≤ n →
      AllNodes (fun s => MemoryTable.fanoutMem s.label.1 = s.children.length) t →
      ∀ x, InTree t x →
        (x.label.1 = .read_root → Ex x ∈ readExps (ofNTree Ex t).toMTree) ∧
        (x.label.1 = .verify_child → Ex x ∈ verifyExps (ofNTree Ex t).toMTree) from
    fun t => key _ t le_rfl
  intro n
  induction n with
  | zero => intro t ht; obtain ⟨a, ch⟩ := t; simp [NTree.size] at ht
  | succ n ih =>
    intro t hsz htopo x hx
    obtain ⟨a, ch⟩ := t
    have hrec : ∀ c ∈ ch, ∀ x, InTree c x →
        (x.label.1 = .read_root → Ex x ∈ readExps (ofNTree Ex c).toMTree) ∧
        (x.label.1 = .verify_child → Ex x ∈ verifyExps (ofNTree Ex c).toMTree) := fun c hc =>
      ih c (by have := size_lt_of_mem (a := a) hc; omega) (allNodes_child htopo hc)
    have hT := allNodes_self htopo
    simp only [NTree.label, NTree.children] at hT
    obtain ⟨s, d⟩ := a
    cases hx with
    | here =>
        cases s with
        | halt => exact ⟨fun h => by simp [NTree.label] at h, fun h => by simp [NTree.label] at h⟩
        | decompose => exact ⟨fun h => by simp [NTree.label] at h, fun h => by simp [NTree.label] at h⟩
        | read_root =>
            simp only [MemoryTable.fanoutMem] at hT
            obtain ⟨c, rfl⟩ : ∃ c, ch = [c] := by
              match ch, hT with | [c], _ => exact ⟨c, rfl⟩
            refine ⟨fun _ => ?_, fun h => by simp [NTree.label] at h⟩
            rw [ofNTree.eq_def]
            simp [MemWalk.toMTree, readExps]
        | verify_child =>
            simp only [MemoryTable.fanoutMem] at hT
            obtain ⟨c, rfl⟩ : ∃ c, ch = [c] := by
              match ch, hT with | [c], _ => exact ⟨c, rfl⟩
            refine ⟨fun h => by simp [NTree.label] at h, fun _ => ?_⟩
            rw [ofNTree.eq_def]
            simp [MemWalk.toMTree, verifyExps]
    | sub hs hsub =>
        rename_i c
        have hc := hrec c hs x hsub
        cases s with
        | halt =>
            simp only [MemoryTable.fanoutMem] at hT
            have : ch = [] := List.eq_nil_of_length_eq_zero hT.symm
            subst this; simp at hs
        | decompose =>
            simp only [MemoryTable.fanoutMem] at hT
            obtain ⟨l, r, rfl⟩ : ∃ l r, ch = [l, r] := by
              match ch, hT with | [l, r], _ => exact ⟨l, r, rfl⟩
            rw [ofNTree_decompose]
            simp only [MemWalk.toMTree, readExps, verifyExps, List.mem_append]
            simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs
            rcases hs with rfl | rfl
            · exact ⟨fun h => Or.inl (hc.1 h), fun h => Or.inl (hc.2 h)⟩
            · exact ⟨fun h => Or.inr (hc.1 h), fun h => Or.inr (hc.2 h)⟩
        | read_root =>
            simp only [MemoryTable.fanoutMem] at hT
            obtain ⟨c', rfl⟩ : ∃ c', ch = [c'] := by
              match ch, hT with | [c'], _ => exact ⟨c', rfl⟩
            simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs
            subst hs
            rw [ofNTree.eq_def]
            simp only [MemWalk.toMTree, readExps, verifyExps, List.mem_cons]
            exact ⟨fun h => Or.inr (hc.1 h), fun h => hc.2 h⟩
        | verify_child =>
            simp only [MemoryTable.fanoutMem] at hT
            obtain ⟨c', rfl⟩ : ∃ c', ch = [c'] := by
              match ch, hT with | [c'], _ => exact ⟨c', rfl⟩
            simp only [NTree.children, List.mem_cons, List.not_mem_nil, or_false] at hs
            subst hs
            rw [ofNTree.eq_def]
            simp only [MemWalk.toMTree, readExps, verifyExps, List.mem_cons]
            exact ⟨fun h => hc.1 h, fun h => Or.inr (hc.2 h)⟩

/-! ## B. The carrier's forest -/

/-- The a-bearing forest's roots, row-encoded, are the executed forest's roots. -/
theorem exec_memoryForest :
    E.exec.memoryForest =
      E.execA.memoryForest.map (mapNTree (MemoryRowTemplate.encodeRow E.cfg.challenges.lam)) := by
  rw [E.exec_encode]; rfl

theorem exec_memoryRows :
    E.exec.memoryRows =
      E.execA.memoryRows.map (MemoryRowTemplate.encodeRow E.cfg.challenges.lam) := by
  rw [E.exec_encode]; exact ExactExecution.encodeMem_memoryRows _

theorem exec_computeRows : E.exec.computeRows = E.execA.computeRows := by
  rw [E.exec_encode]; rfl

theorem exec_rawRequests : E.exec.rawRequests = E.execA.rawRequests := by
  simp only [ExactExecution.rawRequests, exec_computeRows]

/-- Executed-row acceptance gives `label.1 = pub.st` on every executed row. -/
theorem exec_row_st (row : MLT K) (h : row ∈ E.exec.memoryRows) : row.1 = row.2.2.st := by
  have hacc := BuildablePackage.memoryRowsAccepted E
  exact (List.forall_iff_forall_mem.mp hacc row h).1

/-- A node of an a-bearing root is a row of the a-bearing BFS list. -/
theorem node_mem_rowsA (i : Fin E.cfg.kMem) {x : NTree (MLT K)}
    (hx : InTree (E.execA.memoryTreeAt i) x) : x.label ∈ E.execA.memoryRows := by
  have hroot : E.execA.memoryTreeAt i ∈ E.execA.memoryForest := E.execA.memoryTreeAt_mem i
  have hb : x ∈ bfsForest E.execA.memoryForest :=
    (mem_bfsForest _ _).mpr ⟨_, hroot, hx⟩
  exact List.mem_map.mpr ⟨x, hb, rfl⟩

/-- The encoded label of an a-bearing node is an executed row. -/
theorem enc_mem_rows (i : Fin E.cfg.kMem) {x : NTree (MLT K)}
    (hx : InTree (E.execA.memoryTreeAt i) x) :
    MemoryRowTemplate.encodeRow E.cfg.challenges.lam x.label ∈ E.exec.memoryRows := by
  rw [exec_memoryRows]; exact List.mem_map.mpr ⟨_, node_mem_rowsA E i hx, rfl⟩

/-- On every a-bearing node `label.1 = pub.st`. -/
theorem nodeA_st (i : Fin E.cfg.kMem) {x : NTree (MLT K)}
    (hx : InTree (E.execA.memoryTreeAt i) x) : x.label.1 = x.label.2.2.st := by
  have h := exec_row_st E _ (enc_mem_rows E i hx)
  simpa using h

/-- The executed root is the encoded a-bearing root. -/
theorem exec_memoryTreeAt (i : Fin E.cfg.kMem) :
    E.exec.memoryTreeAt i =
      mapNTree (MemoryRowTemplate.encodeRow E.cfg.challenges.lam) (E.execA.memoryTreeAt i) := by
  unfold ExactExecution.memoryTreeAt
  simp only [List.get_eq_getElem, Fin.val_cast]
  have := congrArg (fun l => l[(i : ℕ)]?) (exec_memoryForest E)
  simp only [List.getElem?_map] at this
  have hi : (i : ℕ) < E.execA.memoryForest.length := by
    rw [E.execA.memory_root_count]; exact i.isLt
  have hi' : (i : ℕ) < E.exec.memoryForest.length := by
    rw [E.exec.memory_root_count]; exact i.isLt
  rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at this
  simpa using this

/-- **Topology on the a-bearing roots** (from the executed roots' exact topology). -/
theorem topoA (i : Fin E.cfg.kMem) :
    AllNodes (fun s => MemoryTable.fanoutMem s.label.1 = s.children.length)
      (E.execA.memoryTreeAt i) := by
  intro s hs
  have hb := (E.language.traversable.exactAxisBridgeLocal i).fanout
  have h := hb _ (by rw [exec_memoryTreeAt]; exact inTree_mapNTree_of _ hs)
  rw [mapNTree_label', mapNTree_children_length] at h
  simpa using h

/-! ## C. The forest's services -/

/-- All services of the forest. -/
def allSvc : List (Service E.cfg E.execA) :=
  (List.finRange E.cfg.kMem).flatMap fun i => (E.memoryTrace.roots i).services

theorem mem_allSvc {i : Fin E.cfg.kMem} {s : Service E.cfg E.execA}
    (h : s ∈ (E.memoryTrace.roots i).services) : s ∈ allSvc E :=
  List.mem_flatMap.mpr ⟨i, List.mem_finRange i, h⟩

theorem allSvc_ts_nodup :
    ((allSvc E).map fun s => E.cfg.challenges.α ^ s.exponent).Nodup := by
  have h := E.memoryTrace.timestampPowersNodup
  unfold allSvc
  rw [List.map_flatMap]
  simpa [RootTrace.timestampPowers, RootTrace.exponents, List.map_map, Function.comp_def] using h

/-- Services of the forest with equal timestamps are equal. -/
theorem svc_eq_of_pow {s s' : Service E.cfg E.execA} (hs : s ∈ allSvc E) (hs' : s' ∈ allSvc E)
    (h : E.cfg.challenges.α ^ s.exponent = E.cfg.challenges.α ^ s'.exponent) : s = s' :=
  List.inj_on_of_nodup_map (allSvc_ts_nodup E) hs hs' h

/-- The record of the forest's service at exponent `e`. -/
def recOf (e : ℕ) : ComputeTable.MemRec K :=
  if h : ∃ s ∈ allSvc E, s.exponent = e then (Classical.choose h).record else ComputeTable.MemRec.zero

theorem recOf_eq {s : Service E.cfg E.execA} (hs : s ∈ allSvc E) : recOf E s.exponent = s.record := by
  have h : ∃ s' ∈ allSvc E, s'.exponent = s.exponent := ⟨s, hs, rfl⟩
  unfold recOf
  rw [dif_pos h]
  obtain ⟨hmem, hexp⟩ := Classical.choose_spec h
  have := svc_eq_of_pow E hmem hs (by rw [hexp])
  rw [this]

/-- Every exponent of a root's axis tree is a service exponent of that root. -/
theorem exps_svc (i : Fin E.cfg.kMem) {e : ℕ}
    (he : e ∈ exps (exactAxisTree E.cfg E.execA i)) :
    ∃ s ∈ (E.memoryTrace.roots i).services, s.exponent = e := by
  simp only [exps, List.mem_append] at he
  rcases he with h | h
  · have := ((E.memoryTrace.roots i).readPartition.mem_iff).mp h
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp this
    exact ⟨s, hs, rfl⟩
  · have := ((E.memoryTrace.roots i).verifyPartition.mem_iff).mp h
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp this
    exact ⟨s, hs, rfl⟩

/-- The timestamp exponent of a read / verify node is a service exponent of its root. -/
theorem node_svc (i : Fin E.cfg.kMem) {x : NTree (MLT K)}
    (hx : InTree (E.execA.memoryTreeAt i) x)
    (hst : x.label.1 = .read_root ∨ x.label.1 = .verify_child) :
    ∃ s ∈ (E.memoryTrace.roots i).services,
      s.exponent = timestampExpAt E.cfg.challenges.α x := by
  have h := exp_mem_of_inTree (timestampExpAt E.cfg.challenges.α) _ (topoA E i) x hx
  apply exps_svc E i
  unfold exactAxisTree
  simp only [exps, List.mem_append]
  rcases hst with hr | hv
  · exact Or.inl (h.1 hr)
  · exact Or.inr (h.2 hv)

/-! ## D. The record of a live node -/

variable {I : BuildableChips.Inputs E}

/-- A `read_root` node's record is the record of one of its root's services. -/
theorem read_svc_record (i : Fin E.cfg.kMem) {x : NTree (MLT K)}
    (hx : InTree (E.execA.memoryTreeAt i) x) (hr : x.label.1 = .read_root)
    (hver : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    ∃ s ∈ (E.memoryTrace.roots i).services, s.record = x.label.2.2.mem := by
  have hv := hver _ (enc_mem_rows E i hx)
  simp only [MemoryRowTemplate.encodeRow_ver, MemoryRowTemplate.encodeRow_st] at hv
  have hst := nodeA_st E i hx
  rw [hr] at hst
  rw [← hst] at hv
  simp only [decide_true] at hv
  have hmem : x.label.2.2.mem ∈ rootResponseRecords E.execA i := by
    unfold rootResponseRecords
    refine List.mem_flatMap.mpr ⟨x, (mem_bfsForest _ _).mpr ⟨_, List.mem_singleton_self _, hx⟩, ?_⟩
    simp [MemoryTable.responseRecords, hv]
  rw [(E.memoryTrace.roots i).recordPartition] at hmem
  obtain ⟨s, hs, hrec⟩ := List.mem_map.mp hmem
  exact ⟨s, hs, hrec⟩

/-- The timestamp exponent's service of a `read_root` node carries the node's record. -/
theorem read_recOf (i : Fin E.cfg.kMem) {x : NTree (MLT K)}
    (hx : InTree (E.execA.memoryTreeAt i) x) (hr : x.label.1 = .read_root)
    (hver : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root)) :
    recOf E (timestampExpAt E.cfg.challenges.α x) = x.label.2.2.mem := by
  obtain ⟨sx, hsx, hrec⟩ := read_svc_record E i hx hr hver
  obtain ⟨s, hs, hexp⟩ := node_svc E i hx (Or.inl hr)
  have hclosed : TimestampClosedAt E.cfg.challenges.α x.label.2.2.mem.ts :=
    ⟨sx.exponent, by rw [← hrec]; exact sx.timestamp⟩
  have hpow : E.cfg.challenges.α ^ s.exponent = E.cfg.challenges.α ^ sx.exponent := by
    rw [hexp, ← sx.timestamp, hrec]
    exact (timestampExp_spec hclosed).symm
  have heq := svc_eq_of_pow E (mem_allSvc E hs) (mem_allSvc E hsx) hpow
  rw [← hexp, recOf_eq E (mem_allSvc E hs), heq, hrec]


/-- On a live (`read_root` / `verify_child`) label the row encode stores `C' = formRCprime`. -/
theorem encodeRow_cprime_active (lmb : K) (r : MLT K)
    (h : memoryMemRecKind r.1 = .active) :
    (MemoryRowTemplate.encodeRow lmb r).2.2.cprime = NockVM.formRCprime r.2.2.mem lmb := by
  unfold MemoryRowTemplate.encodeRow; rw [if_pos h]; rfl

theorem live_active {r : MLT K} (h : r.1 = .read_root ∨ r.1 = .verify_child) :
    memoryMemRecKind r.1 = .active := by
  rcases h with h | h <;> rw [h] <;> rfl

/-- The executed encoded record of a live node. -/
theorem enc_record_live (r : MLT K) (h : r.1 = .read_root ∨ r.1 = .verify_child) :
    NockVM.encRecC (MemoryRowTemplate.encodeRow E.cfg.challenges.lam r).2.2.mem
        (MemoryRowTemplate.encodeRow E.cfg.challenges.lam r).2.2.cprime =
      NockVM.encRecFormR r.2.2.mem E.cfg.challenges.lam := by
  rw [MemoryRowTemplate.encodeRow_mem_active _ _ (live_active h),
    encodeRow_cprime_active _ _ (live_active h)]
  rfl

/-- A row of the executed list is the encode of a node of some a-bearing root. -/
theorem exec_row_node {w : MLT K} (hw : w ∈ E.exec.memoryRows) :
    ∃ (iw : Fin E.cfg.kMem) (xw : NTree (MLT K)), InTree (E.execA.memoryTreeAt iw) xw ∧
      w = MemoryRowTemplate.encodeRow E.cfg.challenges.lam xw.label := by
  rw [exec_memoryRows] at hw
  obtain ⟨wA, hwA, rfl⟩ := List.mem_map.mp hw
  obtain ⟨xw, hxw, rfl⟩ := List.mem_map.mp hwA
  obtain ⟨c, hc, hin⟩ := (mem_bfsForest _ _).mp hxw
  rw [E.execA.memoryForest_eq_ofFn_memoryTreeAt] at hc
  obtain ⟨iw, rfl⟩ := List.mem_ofFn.mp hc
  exact ⟨iw, xw, hin, rfl⟩

/-- **The record of a live node, through its timestamp exponent.**  On every `read_root` /
`verify_child` node the executed encoded record is the Form R encode of the record of the
forest's service at the node's timestamp exponent. -/
theorem live_enc_recOf
    (hver : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout E.exec) (hC : E.exec.CprimeCoherent)
    (i : Fin E.cfg.kMem) {x : NTree (MLT K)}
    (hx : InTree (E.execA.memoryTreeAt i) x)
    (hlive : x.label.1 = .read_root ∨ x.label.1 = .verify_child) :
    NockVM.encRecC (MemoryRowTemplate.encodeRow E.cfg.challenges.lam x.label).2.2.mem
        (MemoryRowTemplate.encodeRow E.cfg.challenges.lam x.label).2.2.cprime =
      NockVM.encRecFormR (recOf E (timestampExpAt E.cfg.challenges.α x)) E.cfg.challenges.lam := by
  rw [enc_record_live E _ hlive]
  rcases hlive with hr | hv
  · rw [read_recOf E i hx hr hver]
  · -- the verify row's record is consumed, hence added by some read row
    set y := MemoryRowTemplate.encodeRow E.cfg.challenges.lam x.label with hy
    have hyrow : y ∈ E.exec.memoryRows := enc_mem_rows E i hx
    have hst := nodeA_st E i hx
    have hyst : y.2.2.st = .verify_child := by
      rw [hy, MemoryRowTemplate.encodeRow_st, ← hst, hv]
    have hcons : y.2.2.mem ∈ RowLayout.consumedRecordList E.exec := by
      unfold RowLayout.consumedRecordList
      refine List.mem_flatMap.mpr ⟨y, hyrow, ?_⟩
      simp [RowLayout.consumedRecords, hyst]
    have hadd := hprl.mem_iff.mp hcons
    unfold RowLayout.addedRecordList at hadd
    obtain ⟨w, hw, hwmem⟩ := List.mem_flatMap.mp hadd
    have hwst : w.2.2.st = .read_root ∧ y.2.2.mem = w.2.2.mem := by
      cases hs : w.2.2.st <;> simp [hs] at hwmem
      exact ⟨rfl, hwmem⟩
    obtain ⟨iw, xw, hxw, rfl⟩ := exec_row_node E hw
    have hxwst := nodeA_st E iw hxw
    have hxwr : xw.label.1 = .read_root := by
      rw [hxwst]; simpa using hwst.1
    obtain ⟨sw, hsw, hswrec⟩ := read_svc_record E iw hxw hxwr hver
    -- timestamps
    have hts : x.label.2.2.mem.ts = E.cfg.challenges.α ^ sw.exponent := by
      have h1 := congrArg ComputeTable.MemRec.ts hwst.2
      simp only [hy, MemoryRowTemplate.encodeRow_mem_ts] at h1
      rw [h1, ← hswrec, sw.timestamp]
    obtain ⟨s, hs, hexp⟩ := node_svc E i hx (Or.inr hv)
    have hclosed : TimestampClosedAt E.cfg.challenges.α x.label.2.2.mem.ts := ⟨_, hts⟩
    have hpow : E.cfg.challenges.α ^ s.exponent = E.cfg.challenges.α ^ sw.exponent := by
      rw [hexp, ← hts]; exact (timestampExp_spec hclosed).symm
    have heq := svc_eq_of_pow E (mem_allSvc E hs) (mem_allSvc E hsw) hpow
    rw [← hexp, recOf_eq E (mem_allSvc E hs), heq, hswrec]
    -- the records agree as encodes: same mem (formRRow) and, by coherence, same C'
    have hcp : y.2.2.cprime =
        (MemoryRowTemplate.encodeRow E.cfg.challenges.lam xw.label).2.2.cprime :=
      hC y hyrow _ hw hwst.2
    have hlivew : xw.label.1 = .read_root ∨ xw.label.1 = .verify_child := Or.inl hxwr
    have hlivex : x.label.1 = .read_root ∨ x.label.1 = .verify_child := Or.inr hv
    rw [← enc_record_live E _ hlivew, ← enc_record_live E _ hlivex]
    rw [← hy, hwst.2, hcp]

/-! ## E. The exponent map and its injectivity -/

/-- The request list. -/
abbrev reqList : List (Fin 9 → K) := E.exec.derivedRequestIO

/-- **The exponent map**: a timestamp exponent `e` goes to the honest exponent (position in the
request list, `honestExp`) of the record of the forest's service at `e`. -/
def gExp (e : ℕ) : ℕ :=
  RecordCarrier.honestExp (reqList E) (NockVM.encRecFormR (recOf E e) E.cfg.challenges.lam)

/-- The decoded exponent of a label: `natLift` of the honest `reqIdx` (`reqIdxNat` spelled at
`E`). -/
def exE (a : MLT K) : ℕ :=
  RecordCarrier.natLift
    (((if a.2.2.st = .read_root ∨ a.2.2.st = .verify_child then
        RecordCarrier.honestExp (reqList E) (NockVM.encRecC a.2.2.mem a.2.2.cprime)
      else 0 : ℕ)) : F)

theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := h a (by simp)
      have h2 := ih fun b hb => h b (by simp [hb])
      rw [Nat.succ_mul]; omega

theorem reqList_length_le : (reqList E).length ≤ 3 * E.cfg.compRows := by
  unfold reqList
  rw [ExactExecution.derivedRequestIO_eq_computeRows, List.length_map]
  have := length_flatMap_le E.exec.computeRows
    (fun row => NockVM.activeRequestRecords row.2.2.1) 3 (fun row _ => by
      unfold NockVM.activeRequestRecords; split <;> simp)
  rw [E.exec.computeRows_length] at this
  omega

theorem svc_enc_mem {s : Service E.cfg E.execA} (hs : s ∈ allSvc E) :
    NockVM.encRecFormR s.record E.cfg.challenges.lam ∈ reqList E := by
  unfold reqList ExactExecution.derivedRequestIO
  rw [exec_rawRequests]
  exact List.mem_map.mpr ⟨s.record, s.request_mem, rfl⟩

theorem honestExp_le_of_mem {L : List (Fin 9 → K)} {r : Fin 9 → K} (h : r ∈ L) :
    RecordCarrier.honestExp L r ≤ L.length := by
  unfold RecordCarrier.honestExp
  have := List.idxOf_lt_length_of_mem h
  omega

/-- **The decoded exponent of every live node is `gExp` of its timestamp exponent.** -/
theorem exE_live (hrows : 3 * E.cfg.compRows < ringChar K)
    (hver : ∀ row ∈ E.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hprl : RowLayout.PairedRecordLayout E.exec) (hC : E.exec.CprimeCoherent)
    (i : Fin E.cfg.kMem) {x : NTree (MLT K)}
    (hx : InTree (E.execA.memoryTreeAt i) x)
    (hlive : x.label.1 = .read_root ∨ x.label.1 = .verify_child) :
    exE E (MemoryRowTemplate.encodeRow E.cfg.challenges.lam x.label) =
      gExp E (timestampExpAt E.cfg.challenges.α x) := by
  have hst := nodeA_st E i hx
  have hlive' : (MemoryRowTemplate.encodeRow E.cfg.challenges.lam x.label).2.2.st = .read_root ∨
      (MemoryRowTemplate.encodeRow E.cfg.challenges.lam x.label).2.2.st = .verify_child := by
    rw [MemoryRowTemplate.encodeRow_st, ← hst]; exact hlive
  unfold exE gExp
  rw [if_pos hlive', live_enc_recOf E hver hprl hC i hx hlive]
  apply RecordCarrier.natLift_natCast
  obtain ⟨s, hs, hexp⟩ := node_svc E i hx hlive
  rw [← hexp, recOf_eq E (mem_allSvc E hs)]
  have h1 := honestExp_le_of_mem (svc_enc_mem E (mem_allSvc E hs))
  have h2 := reqList_length_le E
  rw [← OptimizedComputeFormRSlots.ringChar_K_eq F K]
  omega

/-- `encRecFormR` keeps the timestamp in slot `7`. -/
theorem encRecFormR_ts (r : ComputeTable.MemRec K) (lmb : K) :
    NockVM.encRecFormR r lmb 7 = r.ts := rfl

/-- **`gExp` is injective on each root's exponents.** -/
theorem gExp_inj (i : Fin E.cfg.kMem) :
    InjOnExps (gExp E) (fun x => x ∈ exps (exactAxisTree E.cfg E.execA i)) := by
  intro e1 e2 h1 h2 hg
  obtain ⟨s1, hs1, rfl⟩ := exps_svc E i h1
  obtain ⟨s2, hs2, rfl⟩ := exps_svc E i h2
  unfold gExp at hg
  rw [recOf_eq E (mem_allSvc E hs1), recOf_eq E (mem_allSvc E hs2)] at hg
  have hm1 := svc_enc_mem E (mem_allSvc E hs1)
  have hm2 := svc_enc_mem E (mem_allSvc E hs2)
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
  rw [svc_eq_of_pow E (mem_allSvc E hs1) (mem_allSvc E hs2) hts]

end

end Nock.RedTeam.Batch998
