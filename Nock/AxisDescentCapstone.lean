/-
  Nock/AxisDescentCapstone.lean

  ITEMS 3 + 4 of the direct axis-descent development:

    3. BRIDGE onto the real reconstructed memory trace.  `AxisBridge.MemWalk` nodes ARE real
       `MemoryTable.Pub` rows; `toMTree` reads the idealized value off them, carrying the COMMITTED
       `mem.axis` at each `verify_child` (`MemWalk.vaxis_verify_here`).  So `AxisDescent.axis_correct`
       (unconditional) transfers to: the real committed `mem.axis` of a used record equals its true
       topological `axis_root(child)` (`AxisBatching.Relaxis`).  We reuse `AxisBridge.ofNTree` to read
       a `MemWalk` off each reconstructed `Walk.NTree` and expose axis validity for the reconstructed
       forest (`Walk.ForestReconGoal`).

    4. END-TO-END CAPSTONE `NockVM.V_NockVMROM_forest_direct`.  The paper's witness-linked verifier
       (compute chip + IO exactly as `NockVM.V_NockVMROM_forest`) with an added axis-validity conjunct
       that is THREADED through conjunct (2)'s OWN reconstructed `ForestReconGoal` forest `ts` (not a
       fresh `∀ tr`), and carries NONE of the batched crutches — NO `Nested`, NO `∑z^{i_j}` positivity,
       NO `axis_counts = 0` boundary.  The only memory-axis hypothesis is the descent gate `DescOK`
       (the deployed impl's `axis` column, memory.hoon:288–289 — a §0-legal per-node scalar recurrence).

  The batched development is left UNTOUCHED; this is a NEW, parallel, direct baseline.
-/
import Nock.AxisDescent
import Nock.AxisBridge

namespace Nock
namespace AxisDescent

open AxisBatching AxisBatching.MTree
open MemoryTable
open AxisBridge AxisBridge.MemWalk

variable {K : Type*} [Field K]

/-! ## Item 3 — the bridge onto the REAL reconstructed memory trace -/

/-- **`committed_axis_correct_direct` (item 3, `MemWalk` level).**  For a real memory trace whose
    root is a `verify_child` for record `e`, if the direct descent gate holds on the idealized
    value `toMTree` (the impl's `axis` column, `DescOK`) and the record is used once, then the REAL
    committed `mem.axis` (surfaced by `MemWalk.vaxis_verify_here`) equals the true topological
    `axis_root(child) = Relaxis`.  UNCONDITIONAL: NO `Nested`, NO positivity, NO `axis_counts = 0`. -/
theorem committed_axis_correct_direct (row : Pub K) (e : ℕ) (c : MemWalk K)
    (hok : DescOK e none (toMTree (MemWalk.verify row e c)))
    (hr : readCount e (toMTree (MemWalk.verify row e c)) = 1)
    (hv : verifyCount e (toMTree (MemWalk.verify row e c)) = 1) :
    row.mem.axis = Relaxis e (toMTree (MemWalk.verify row e c)) := by
  rw [← MemWalk.vaxis_verify_here row e c]
  exact axis_correct e _ hok hr hv

/-! ## Item 3 (forest level) — axis validity of a reconstructed `Walk.NTree`

  `ofNTree` reads a `MemWalk` off a reconstructed memory tree; `toMTree ∘ ofNTree` is its idealized
  value.  `vaxis e (toMTree (ofNTree E tr))` is the committed `mem.axis` of record `e` in `tr`. -/

open NockVM Walk

/-- Axis validity of one reconstructed memory tree `tr` (via exponent oracle `E`): every USED
    record's committed axis equals its true topological `Relaxis`. -/
def treeAxisValid (E : NTree (MState × DTmem K) → ℕ) (tr : NTree (MState × DTmem K)) : Prop :=
  ∀ e : ℕ, readCount e (toMTree (ofNTree E tr)) = 1 → verifyCount e (toMTree (ofNTree E tr)) = 1 →
    vaxis e (toMTree (ofNTree E tr)) = Relaxis e (toMTree (ofNTree E tr))

/-- **`treeAxisValid` from the descent gate.**  If the direct descent gate `DescOK` holds for every
    record on the idealized value of a reconstructed tree (the impl's `axis`-column constraint), the
    tree is axis-valid — UNCONDITIONALLY (no Nested/positivity/`counts=0`). -/
theorem treeAxisValid_of_descOK (E : NTree (MState × DTmem K) → ℕ) (tr : NTree (MState × DTmem K))
    (hdesc : ∀ e : ℕ, DescOK e none (toMTree (ofNTree E tr))) :
    treeAxisValid E tr :=
  fun e hr hv => axis_correct e _ (hdesc e) hr hv

end AxisDescent

/-! ═══════════════════════════════════════════════════════════════════════════════════════════
  ## Item 4 — the end-to-end capstone `V_NockVMROM_forest_direct`
  ═══════════════════════════════════════════════════════════════════════════════════════════ -/

namespace NockVM

open Walk ComputeTable MemoryTable AxisBatching AxisBatching.MTree
open AxisBridge AxisBridge.MemWalk AxisDescent

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **`V_NockVMROM_forest_direct` (item 4).**  The multi-root forest capstone of
    `V_NockVMROM_forest`, with the axis chip discharged the HONEST NON-BATCHED way — a per-node
    descended-axis register (`AxisDescent.DescOK`, the deployed impl's `axis` column,
    memory.hoon:288–289) instead of the batched `axis_indicator`/`axis_counts`.

    Conjuncts (1) compute and (3) IO are EXACTLY `V_NockVMROM_forest`'s (obtained by delegating to
    it).  The DIRECT contribution:

    * conjunct (2′) EXPOSES the reconstructed memory forest `ts` as a literal `ForestReconGoal`
      (the object conjunct (2) bounds membership in), and

    * conjunct (4) is UNCONDITIONAL axis validity THREADED through that SAME `ts` (`∀ tr ∈ ts`, not
      a fresh `∀`): for every used memory record, the committed `mem.axis` equals its true
      topological `axis_root(child) = Relaxis`.

    HYPOTHESIS LIST — note what is ABSENT from the axis conjunct: NO `Nested` (derived,
    `AxisDescent.nested_of_descent`), NO `∑z^{i_j}` positivity, NO `axis_counts = 0` boundary.  The
    only memory-axis hypothesis is the descent gate `hdesc` (`DescOK`, a §0 scalar recurrence over
    parent/child labels — the impl's `axis` column). -/
theorem V_NockVMROM_forest_direct
    {p : ℕ} [CharP K p]
    -- compute chip (UNCHANGED — single-root execution walk)
    {ncs : ℕ} (encc : (State × DTcomp K) → (Fin ncs → K)) (hEncc : Function.Injective encc)
    (lblc : ℕ → State × DTcomp K) (clabc : ℕ → ℕ → State × DTcomp K) (foc : ℕ → ℕ)
    {hc : ℕ} (harityc : ∀ i, foc i ≤ 3)
    (qc qinvc : ℕ → K) (hqc : Walk.QGate foc qc qinvc 1 hc) (hwrapc : 1 + hc * 3 < p)
    (hfoc : ∀ i, 1 ≤ i → i ≤ hc → foc i = (comp_stateSep (K := K)).fanout (lblc i).1)
    (hRc : ∀ i, 1 ≤ i → i ≤ hc →
      (∃ ex, ComputeTable.RAPcomp (lblc i).2.1 (lblc i).2.2.1 (lblc i).2.2.2 ex)
        ∧ (lblc i).2.2.1.state = (lblc i).1
        ∧ (∀ j : Fin 3, (j : ℕ) < foc i ↔
            (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none)
        ∧ ComputeTable.childLinkComp (lblc i)
            (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none))
    -- memory chip (MULTI-ROOT FOREST)
    {nms : ℕ} (encm : (MState × DTmem K) → (Fin nms → K)) (hEncm : Function.Injective encm)
    (lblm : ℕ → MState × DTmem K) (clabm : ℕ → ℕ → MState × DTmem K) (fom : ℕ → ℕ)
    {kroots_m hm : ℕ} (hkm : 1 ≤ kroots_m) (haritym : ∀ i, fom i ≤ 2)
    (qm qinvm : ℕ → K) (hqm : Walk.QGate fom qm qinvm kroots_m hm)
    (hwrapm : kroots_m + hm * 2 < p)
    (hfom : ∀ i, 1 ≤ i → i ≤ hm → fom i = (mem_stateSep (K := K)).fanout (lblm i).1)
    (hRm : ∀ i, 1 ≤ i → i ≤ hm →
      (∃ g, MemoryTable.RAPmem (lblm i).2.1 (lblm i).2.2 g)
        ∧ (lblm i).2.2.st = (lblm i).1
        ∧ (∀ j : Fin 2, (j : ℕ) < fom i ↔
            (if (j : ℕ) < fom i then some (clabm i (j + 1)) else none) ≠ none)
        ∧ MemoryTable.childLinkMem (lblm i)
            (fun j : Fin 2 => if (j : ℕ) < fom i then some (clabm i (j + 1)) else none))
    -- IO linking over the SHARED derived record lists (UNCHANGED)
    (lmb : K) (Ksz : ℕ) (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz (reqRecs lblc hc lmb).length)
    (hKresp : (respRecs lblm hm).length ≤ Ksz)
    (hreqnd : (reqRecs lblc hc lmb).Nodup) (hrespnd : (respRecs lblm hm).Nodup)
    -- DIRECT memory-axis extension: the reconstructed forest `ts` (conjunct-(2) object) + the
    -- descent gate (the impl's `axis` column, a §0 per-node scalar recurrence)
    (E : NTree (MState × DTmem K) → ℕ)
    (ts : List (NTree (MState × DTmem K)))
    (htslen : ts.length = kroots_m)
    (htsrvt : ∀ tr ∈ ts, RVT (Fmem (K := K)) tr)
    (htslab : (bfsForest ts).map NTree.label = (List.range' 1 hm).map lblm)
    (htsfan : ∀ tr ∈ bfsForest ts,
        (mem_stateSep (K := K)).fanout (NTree.label tr).1 = tr.children.length)
    (htsleaf : ∀ tr ∈ bfsForest ts,
        tr.isLeaf ↔ (mem_stateSep (K := K)).Sleaf (NTree.label tr).1)
    (hdesc : ∀ tr ∈ ts, ∀ e : ℕ, DescOK e none (toMTree (ofNTree E tr))) :
    -- (1) compute chip soundness (single-root)
    (((walkBad (comp_stateSep (K := K)) encc lblc clabc foc hc).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hc : ℚ) / (Fintype.card K : ℚ)
          + ((hc * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (2) memory chip soundness (multi-root forest)
    ∧ (((walkBadForest (mem_stateSep (K := K)) encm lblm clabm fom kroots_m hm).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hm : ℚ) / (Fintype.card K : ℚ)
          + ((hm * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    -- (3) IO memory-execution linking over the SHARED derived lists (Thm:IO_result, UNCHANGED)
    ∧ ((∃ (m : Fin (respRecs lblm hm).length → ZMod p) (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt (reqRecs lblc hc lmb) i)) accP requests
              (reqRecs lblc hc lmb).length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt (respRecs lblm hm) i)) (IO.castμ m) accM
              responses out_mem (respRecs lblm hm).length
          ∧ requests = responses ∧ out_mem = 0)
        ↔ IO.LIO Ksz (reqRecs lblc hc lmb) (respRecs lblm hm))
    -- (2′) the reconstructed memory forest, EXPOSED as a literal `ForestReconGoal` (the object that
    -- conjunct (2) bounds membership in) — the forest conjunct (4) threads through
    ∧ ForestReconGoal (mem_stateSep (K := K)) lblm kroots_m hm
    -- (4) UNCONDITIONAL axis validity, THREADED through the SAME reconstructed forest `ts`
    ∧ (∀ tr ∈ ts, AxisDescent.treeAxisValid E tr) := by
  have hbase := V_NockVMROM_forest encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc hfoc hRc
    encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom hRm
    Ksz hKp hKreq hKresp hreqnd hrespnd
  refine ⟨hbase.1, hbase.2.1, hbase.2.2, ?_, ?_⟩
  · exact ⟨ts, htslen, htsrvt, htslab, htsfan, htsleaf⟩
  · intro tr htr
    exact AxisDescent.treeAxisValid_of_descOK E tr (hdesc tr htr)

end NockVM
end Nock
