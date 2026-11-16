/-
  Nock/NockVMROM/Thm54/AxisBridgeTopo.lean

  `AxisBridge.MemWalk.WF` asks every row for `MemoryTable.Vmem` = `verBool ∧ eqBlk ∧ interV`, and
  the `axis_lookups_valid_endToEnd*` / `V_NockVMROM_forest_axisvalid*` / `wf_memwalk_of_memAIR`
  family reads it off `RVT Fmem` / `ForestReconGoal mem_stateSep`.  This module is the additive twin:

  * **`MemWalk.WFTopo`** — `WF` with `eqBlk inp row` in place of `Vmem inp row` (state match,
    BFS cell chaining and `mem.ts = z^e` unchanged).  `MemWalk.WF.toTopo`: production `WF`
    implies it; `MemWalk.WF_of_topo`: the converse needs exactly `interV` at every row
    (`verBool` is free, `MemoryTable.verBool_holds`).
  * **The domain lift** `indP_eval_topo` / `countsP_eval_topo` — the production proofs read only
    `hV.2.1` (the `eqBlk` conjunct); the twins read `eqBlk` directly.
  * **The twins**, each with the original's conclusion verbatim, fed by `RVT FmemTopo` /
    `ForestReconGoal mem_stateSep_topo` / `ExactAxisBridgeLocalTopo` (`…_topo`, `…_of_bridgeTopo`):
    `axis_lookups_valid_of_memtrace`, `…_perfect_of_memtrace`, `committed_axis_correct_of_memtrace`,
    `chainNode_of_Fcon`, `chainNode_of_RVT`, `wf_ofNTree` (`wfTopo_ofNTree`),
    `wf_memwalk_of_memAIR` (`wfTopo_memwalk_of_memAIR`), `axis_lookups_valid_endToEnd`,
    `…_of_seedGate`, `…_perfect`, `…_uniqReq`, `…_uniqReq_of_seedGate`, `…_perfect_defE`,
    `…_uniqReq_of_seedGate_defE`, `…_seedpinned`, `…_honestRecon`, `…_rvn`, the three
    `forest_tsExists` / `seedCoupled` helpers, and `V_NockVMROM_forest_axisvalid`,
    `…_seedpinned`, `…_pinned_derived`, `…_rvn`.  The four `V_…_topo` keep conjuncts (1)–(3)
    VERBATIM (they are `NockVM.V_NockVMROM_forest`'s walk-soundness / IO conjuncts, which read
    `RAPmem` through `hRm` exactly as the originals do); only conjunct (4)'s forest antecedent is
    `ForestReconGoal mem_stateSep_topo`, which the production goal implies
    (`forestReconGoal_topo_of_fmem`), so each twin's (4) implies the original's.
    `forest_axisvalid_topo` is conjunct (4) of `V_NockVMROM_forest_axisvalid_topo` standalone,
    with none of the compute / `hRm` hypotheses.

  Universe note: `FmemTopo` is stated at `K : Type`, so the twins are at `K : Type` (every
  production instance is).
-/
import Nock.AxisBridge
import Nock.NockVMROM.Thm54.MemoryTopoBetaFree
import Nock.NockVMROM.Thm54.AxisBridgeLocalTopo

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock
namespace AxisBridge

open Polynomial
open MemoryTable
open AxisBatching AxisBatching.MTree
open scoped Classical
open Nock.Walk
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree (FmemTopo mem_stateSep_topo fmemTopo_of_fmem)

variable {K : Type} [Field K]

namespace MemWalk

/-- **The β-free well-formedness of a reified memory walk**: `WF` with `eqBlk inp row` in place
of `Vmem inp row` at every node.
State match, BFS cell chaining (`lc`/`rc` = child `pt`) and the monomial timestamps are `WF`'s
verbatim. -/
def WFTopo (inp : Inputs K) : MemWalk K → Prop
  | halt row        =>
      row.st = MState.halt ∧ eqBlk inp row
  | decompose row l r =>
      row.st = MState.decompose ∧ eqBlk inp row
        ∧ row.lc = l.rootRow.pt ∧ row.rc = r.rootRow.pt
        ∧ WFTopo inp l ∧ WFTopo inp r
  | read row e c    =>
      row.st = MState.read_root ∧ eqBlk inp row ∧ row.mem.ts = inp.z ^ e
        ∧ row.lc = c.rootRow.pt ∧ WFTopo inp c
  | verify row e c  =>
      row.st = MState.verify_child ∧ eqBlk inp row ∧ row.mem.ts = inp.z ^ e
        ∧ row.lc = c.rootRow.pt ∧ WFTopo inp c

/-- Every row of the walk satisfies `P`. -/
def AllRows (P : Pub K → Prop) : MemWalk K → Prop
  | halt row => P row
  | decompose row l r => P row ∧ AllRows P l ∧ AllRows P r
  | read row _ c => P row ∧ AllRows P c
  | verify row _ c => P row ∧ AllRows P c

/-- **Production `WF` implies `WFTopo`** (each row's `Vmem` projects to its `eqBlk`). -/
theorem WF.toTopo {inp : Inputs K} : ∀ {w : MemWalk K}, WF inp w → WFTopo inp w
  | halt _, ⟨hst, hV⟩ => ⟨hst, hV.2.1⟩
  | decompose _ _ _, ⟨hst, hV, hlc, hrc, hl, hr⟩ => ⟨hst, hV.2.1, hlc, hrc, hl.toTopo, hr.toTopo⟩
  | read _ _ _, ⟨hst, hV, hts, hlc, hc⟩ => ⟨hst, hV.2.1, hts, hlc, hc.toTopo⟩
  | verify _ _ _, ⟨hst, hV, hts, hlc, hc⟩ => ⟨hst, hV.2.1, hts, hlc, hc.toTopo⟩

/-- Production `WF` gives `interV` at every row (the β-dependent clause). -/
theorem WF.allRows_interV {inp : Inputs K} : ∀ {w : MemWalk K}, WF inp w → AllRows (interV inp) w
  | halt _, ⟨_, hV⟩ => hV.2.2
  | decompose _ _ _, ⟨_, hV, _, _, hl, hr⟩ => ⟨hV.2.2, hl.allRows_interV, hr.allRows_interV⟩
  | read _ _ _, ⟨_, hV, _, _, hc⟩ => ⟨hV.2.2, hc.allRows_interV⟩
  | verify _ _ _, ⟨_, hV, _, _, hc⟩ => ⟨hV.2.2, hc.allRows_interV⟩

/-- **`WFTopo` + `interV` at every row ⟹ `WF`**: exactly `interV` separates the two (`verBool`
holds definitionally).  So `WF ↔ WFTopo ∧ AllRows interV` (`WF_iff_topo`). -/
theorem WF_of_topo {inp : Inputs K} : ∀ {w : MemWalk K}, WFTopo inp w → AllRows (interV inp) w →
    WF inp w
  | halt _, ⟨hst, hE⟩, hI => ⟨hst, verBool_holds _, hE, hI⟩
  | decompose _ _ _, ⟨hst, hE, hlc, hrc, hl, hr⟩, ⟨hI, hIl, hIr⟩ =>
      ⟨hst, ⟨verBool_holds _, hE, hI⟩, hlc, hrc, WF_of_topo hl hIl, WF_of_topo hr hIr⟩
  | read _ _ _, ⟨hst, hE, hts, hlc, hc⟩, ⟨hI, hIc⟩ =>
      ⟨hst, ⟨verBool_holds _, hE, hI⟩, hts, hlc, WF_of_topo hc hIc⟩
  | verify _ _ _, ⟨hst, hE, hts, hlc, hc⟩, ⟨hI, hIc⟩ =>
      ⟨hst, ⟨verBool_holds _, hE, hI⟩, hts, hlc, WF_of_topo hc hIc⟩

theorem WF_iff_topo (inp : Inputs K) (w : MemWalk K) :
    WF inp w ↔ WFTopo inp w ∧ AllRows (interV inp) w :=
  ⟨fun h => ⟨h.toTopo, h.allRows_interV⟩, fun h => WF_of_topo h.1 h.2⟩

/-- β-free twin of `MemWalk.indP_eval`: the same domain lift from `WFTopo` (each row `eqBlk`, no
    `Vmem`); the proof reads only the `eqBlk` conjunct. -/
theorem indP_eval_topo (inp : Inputs K) (lmb : K) (T : ℕ → K) :
    ∀ w : MemWalk K, WFTopo inp w → sameLambda lmb w → readAxis T w →
      (indP w.toMTree lmb T).eval inp.z = w.rootRow.pt.indicator := by
  intro w
  induction w with
  | halt row =>
      intro hw hlam _hT
      obtain ⟨hst, hV⟩ := hw
      have hEq := hV
      simp only [eqBlk, hst] at hEq
      simp only [toMTree, indP, eval_zero, rootRow]
      exact hEq.2.2.1.symm
  | decompose row l r ihl ihr =>
      intro hw hlam hT
      obtain ⟨hst, hV, hlc, hrc, hWl, hWr⟩ := hw
      obtain ⟨hlamrow, hlaml, hlamr⟩ := hlam
      obtain ⟨hTl, hTr⟩ := hT
      have hEq := hV
      simp only [eqBlk, hst] at hEq
      simp only [toMTree, indP, eval_mul, eval_C, eval_add, rootRow]
      rw [ihl hWl hlaml hTl, ihr hWr hlamr hTr, hEq.2.1, hlc, hrc, hlamrow]
  | read row e c ih =>
      intro hw hlam hT
      obtain ⟨hst, hV, hts, hlc, hWc⟩ := hw
      obtain ⟨hlamrow, hlamc⟩ := hlam
      obtain ⟨hTrow, hTc⟩ := hT
      have hEq := hV
      simp only [eqBlk, hst] at hEq
      simp only [toMTree, indP, eval_sub, eval_mul, eval_C, eval_pow, eval_X, rootRow, pwScale]
      rw [ih hWc hlamc hTc, hEq.2.2.1, hlc, hts, hlamrow, hTrow]
      rw [mul_comm row.mem.axis (lmb ^ MemoryTable.pwScaleExp K)]
  | verify row e c ih =>
      intro hw hlam hT
      obtain ⟨hst, hV, hts, hlc, hWc⟩ := hw
      obtain ⟨hlamrow, hlamc⟩ := hlam
      have hEq := hV
      simp only [eqBlk, hst] at hEq
      simp only [toMTree, indP, eval_add, eval_mul, eval_C, eval_pow, eval_X, rootRow, pwScale]
      rw [ih hWc hlamc hT]
      rw [hEq.2.2.1, hlc, hts, hlamrow]

/-- β-free twin of `MemWalk.countsP_eval`: the same domain lift from `WFTopo` (each row `eqBlk`, no
    `Vmem`); the proof reads only the `eqBlk` conjunct. -/
theorem countsP_eval_topo (inp : Inputs K) (lmb : K) (T C' : ℕ → K) :
    ∀ w : MemWalk K, WFTopo inp w → sameLambda lmb w → readAxis T w → readCprime C' w →
      (countsP w.toMTree lmb T C').eval inp.z = w.rootRow.pt.counts := by
  intro w
  induction w with
  | halt row =>
      intro hw hlam _hT _hC
      obtain ⟨hst, hV⟩ := hw
      have hEq := hV
      simp only [eqBlk, hst] at hEq
      simp only [toMTree, countsP, eval_zero, rootRow]
      exact hEq.2.2.2.1.symm
  | decompose row l r ihl ihr =>
      intro hw hlam hT hC
      obtain ⟨hst, hV, hlc, hrc, hWl, hWr⟩ := hw
      obtain ⟨hlamrow, hlaml, hlamr⟩ := hlam
      obtain ⟨hTl, hTr⟩ := hT
      obtain ⟨hCl, hCr⟩ := hC
      have hEq := hV
      simp only [eqBlk, hst] at hEq
      simp only [toMTree, countsP, eval_add, eval_mul, eval_C, rootRow]
      rw [ihl hWl hlaml hTl hCl, ihr hWr hlamr hTr hCr,
          indP_eval_topo inp lmb T l hWl hlaml hTl, indP_eval_topo inp lmb T r hWr hlamr hTr]
      rw [hEq.2.2.1, hlc, hrc, hlamrow]
  | read row e c ih =>
      intro hw hlam hT hC
      obtain ⟨hst, hV, hts, hlc, hWc⟩ := hw
      obtain ⟨hlamrow, hlamc⟩ := hlam
      obtain ⟨hTrow, hTc⟩ := hT
      obtain ⟨hCrow, hCc⟩ := hC
      have hEq := hV
      simp only [eqBlk, hst] at hEq
      simp only [toMTree, countsP, eval_sub, eval_mul, eval_C, eval_pow, eval_X, rootRow]
      rw [ih hWc hlamc hTc hCc]
      rw [hEq.2.2.2.1, hlc, hts, hCrow, hTrow]
  | verify row e c ih =>
      intro hw hlam hT hC
      obtain ⟨hst, hV, hts, hlc, hWc⟩ := hw
      obtain ⟨hlamrow, hlamc⟩ := hlam
      have hEq := hV
      simp only [eqBlk, hst] at hEq
      simp only [toMTree, countsP, eval_add, eval_mul, eval_C, eval_pow, eval_X, rootRow, pwScale]
      rw [ih hWc hlamc hT hC]
      rw [hEq.2.2.2.1, hlc, hts, hlamrow]

end MemWalk

open MemWalk
open NockVM

/-- β-free twin of `axis_lookups_valid_of_memtrace` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_of_memtrace_topo [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (inp : Inputs K) (T C' : ℕ → K)
    (w : MemWalk K) (hw : WFTopo inp w)
    (hlam : sameLambda (w.rootRow.lambda) w)
    (hT : readAxis T w) (hC : readCprime C' w)
    (hterm : w.rootPt.counts = 0)
    (e : ℕ)
    (hn : Nested e w.toMTree)
    (hr : readCount e w.toMTree = 1) (hv : verifyCount e w.toMTree = 1)
    (hbad : vaxis e w.toMTree ≠ Relaxis e w.toMTree) :
    inp.z ∈ Finset.univ.filter
        (fun z : K => (countsP w.toMTree w.rootRow.lambda T C').eval z = 0)
      ∧ (Finset.univ.filter
            (fun z : K => (countsP_bin w.toMTree).eval z = 0)).card
          ≤ (countsP_bin w.toMTree).natDegree := by
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [countsP_eval_topo inp w.rootRow.lambda T C' w hw hlam hT hC]; exact hterm
  · exact axis_batching_sound_card h2 w.toMTree e hn hr hv hbad

/-- β-free twin of `axis_lookups_valid_perfect_of_memtrace` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_perfect_of_memtrace_topo
    (h2 : (2 : K) ≠ 0) (inp : Inputs K) (w : MemWalk K) (_hw : WFTopo inp w)
    (hterm : countsP_bin w.toMTree = 0)
    (e : ℕ) (hn : Nested e w.toMTree)
    (hr : readCount e w.toMTree = 1) (hv : verifyCount e w.toMTree = 1) :
    vaxis e w.toMTree = Relaxis e w.toMTree :=
  axis_batching_sound h2 w.toMTree hterm e hn hr hv

/-- β-free twin of `committed_axis_correct_of_memtrace` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem committed_axis_correct_of_memtrace_topo
    (h2 : (2 : K) ≠ 0) (inp : Inputs K) (row : Pub K) (e : ℕ) (c : MemWalk K)
    (hw : WFTopo inp (MemWalk.verify row e c))
    (hterm : countsP_bin (MemWalk.verify row e c).toMTree = 0)
    (hn : Nested e (MemWalk.verify row e c).toMTree)
    (hr : readCount e (MemWalk.verify row e c).toMTree = 1)
    (hv : verifyCount e (MemWalk.verify row e c).toMTree = 1) :
    row.mem.axis = Relaxis e (MemWalk.verify row e c).toMTree := by
  have h := axis_lookups_valid_perfect_of_memtrace_topo h2 inp (MemWalk.verify row e c) hw hterm e hn hr hv
  rwa [vaxis_verify_here] at h

/-- β-free twin of `chainNode_of_Fcon` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem chainNode_of_Fcon_topo (t : NTree (MState × DTmem K))
    (hFcon : Walk.Fcon FmemTopo t)
    (hshape : fanoutMem (NTree.label t).1 = (NTree.children t).length) :
    ChainNode t := by
  have hlink : childLinkMem (NTree.label t) (fun i : Fin 2 => NTree.childLabel t ↑i) :=
    hFcon.1.2.2.2
  cases t with
  | node lbl ch =>
    obtain ⟨s, d⟩ := lbl
    simp only [NTree.label_node, NTree.children_node] at hshape hlink
    cases s
    · -- decompose (fanout 2): lc = child₀.pt, rc = child₁.pt
      have hlen : ch.length = 2 := by simp only [fanoutMem] at hshape; omega
      obtain ⟨l, r, rfl⟩ := List.length_eq_two.mp hlen
      have h0 := hlink 0 (by simp [fanoutMem])
      have h1 := hlink 1 (by simp [fanoutMem])
      simp only [NTree.childLabel, NTree.childOpt, NTree.children_node, Fin.val_zero, Fin.val_one,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, memCell,
        Option.some.injEq] at h0 h1
      simp only [ChainNode, NTree.label_node, NTree.children_node]
      exact ⟨h0.symm, h1.symm⟩
    · -- halt (fanout 0): ChainNode is `True`
      simp only [ChainNode, NTree.label_node, NTree.children_node]
    · -- read_root (fanout 1): lc = child₀.pt
      have hlen : ch.length = 1 := by simp only [fanoutMem] at hshape; omega
      obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hlen
      have h0 := hlink 0 (by simp [fanoutMem])
      simp only [NTree.childLabel, NTree.childOpt, NTree.children_node, Fin.val_zero,
        List.getElem?_cons_zero, Option.map_some, memCell, Option.some.injEq] at h0
      simp only [ChainNode, NTree.label_node, NTree.children_node]
      exact h0.symm
    · -- verify_child (fanout 1): lc = child₀.pt
      have hlen : ch.length = 1 := by simp only [fanoutMem] at hshape; omega
      obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hlen
      have h0 := hlink 0 (by simp [fanoutMem])
      simp only [NTree.childLabel, NTree.childOpt, NTree.children_node, Fin.val_zero,
        List.getElem?_cons_zero, Option.map_some, memCell, Option.some.injEq] at h0
      simp only [ChainNode, NTree.label_node, NTree.children_node]
      exact h0.symm

/-- β-free twin of `chainNode_of_RVT` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem chainNode_of_RVT_topo (root : NTree (MState × DTmem K)) (hrvt : RVT FmemTopo root)
    (hshape : ∀ t', InTree root t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (t : NTree (MState × DTmem K)) (ht : InTree root t) :
    ChainNode t :=
  chainNode_of_Fcon_topo t ((RVT_iff_forall_InTree FmemTopo root).mp hrvt t ht) (hshape t ht)

/-- β-free twin of `wf_ofNTree` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem wfTopo_ofNTree (E : NTree (MState × DTmem K) → ℕ) (inp : Inputs K)
    (root : NTree (MState × DTmem K))
    (hrvt : RVT FmemTopo root)
    (hinp : ∀ t', InTree root t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree root t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree root t' → TsNode E inp t') :
    MemWalk.WFTopo inp (ofNTree E root) := by
  suffices H : ∀ n : ℕ, ∀ root : NTree (MState × DTmem K), sizeOf root ≤ n →
      RVT FmemTopo root →
      (∀ t', InTree root t' → (NTree.label t').2.1 = inp) →
      (∀ t', InTree root t' → fanoutMem (NTree.label t').1 = (NTree.children t').length) →
      (∀ t', InTree root t' → TsNode E inp t') →
      MemWalk.WFTopo inp (ofNTree E root) by
    exact H (sizeOf root) root le_rfl hrvt hinp hshape hts
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro root hn hrvt hinp hshape hts
    have hFcon := (RVT_iff_forall_InTree FmemTopo root).mp hrvt root (InTree.here root)
    have hshR := hshape root (InTree.here root)
    -- `ChainNode` is now DERIVED from `RVT FmemTopo` (the child-content link inside `Fmem`), not carried
    have hchR := chainNode_of_Fcon_topo root hFcon hshR
    have htsR := hts root (InTree.here root)
    have hinpR := hinp root (InTree.here root)
    cases root with
    | node lbl ch =>
      obtain ⟨s, d⟩ := lbl
      simp only [NTree.label_node, NTree.children_node] at hFcon hshR hchR htsR hinpR hn
      have hstrow : d.2.st = s := hFcon.1.1
      have hVm : eqBlk d.1 d.2 := hFcon.1.2.1
      rw [hinpR] at hVm
      cases s
      · -- decompose
        have hlen : ch.length = 2 := by
          have := hshR; simp only [fanoutMem] at this; omega
        obtain ⟨l, r, rfl⟩ := List.length_eq_two.mp hlen
        have hRootL : InTree (NTree.node (MState.decompose, d) [l, r]) l :=
          InTree.sub (by simp) (InTree.here l)
        have hRootR : InTree (NTree.node (MState.decompose, d) [l, r]) r :=
          InTree.sub (by simp) (InTree.here r)
        have hszL : sizeOf l < sizeOf (NTree.node (MState.decompose, d) [l, r]) := by
          simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
        have hszR : sizeOf r < sizeOf (NTree.node (MState.decompose, d) [l, r]) := by
          simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
        simp only [ChainNode, NTree.label_node, NTree.children_node] at hchR
        rw [ofNTree_decompose]
        refine ⟨hstrow, hVm, ?_, ?_, ?_, ?_⟩
        · rw [rootRow_ofNTree]; exact hchR.1
        · rw [rootRow_ofNTree]; exact hchR.2
        · exact ih (sizeOf l) (by omega) l le_rfl (RVT_of_InTree hrvt hRootL)
            (fun t' ht' => hinp t' (InTree_trans hRootL ht'))
            (fun t' ht' => hshape t' (InTree_trans hRootL ht'))
            (fun t' ht' => hts t' (InTree_trans hRootL ht'))
        · exact ih (sizeOf r) (by omega) r le_rfl (RVT_of_InTree hrvt hRootR)
            (fun t' ht' => hinp t' (InTree_trans hRootR ht'))
            (fun t' ht' => hshape t' (InTree_trans hRootR ht'))
            (fun t' ht' => hts t' (InTree_trans hRootR ht'))
      · -- halt
        have hlen : ch.length = 0 := by
          have := hshR; simp only [fanoutMem] at this; omega
        obtain rfl := List.length_eq_zero_iff.mp hlen
        rw [ofNTree_halt]
        exact ⟨hstrow, hVm⟩
      · -- read_root
        have hlen : ch.length = 1 := by
          have := hshR; simp only [fanoutMem] at this; omega
        obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hlen
        have hRootC : InTree (NTree.node (MState.read_root, d) [c]) c :=
          InTree.sub (by simp) (InTree.here c)
        have hszC : sizeOf c < sizeOf (NTree.node (MState.read_root, d) [c]) := by
          simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
        simp only [ChainNode, NTree.label_node, NTree.children_node] at hchR
        simp only [TsNode, NTree.label_node] at htsR
        rw [ofNTree_read]
        refine ⟨hstrow, hVm, ?_, ?_, ?_⟩
        · exact htsR
        · rw [rootRow_ofNTree]; exact hchR
        · exact ih (sizeOf c) (by omega) c le_rfl (RVT_of_InTree hrvt hRootC)
            (fun t' ht' => hinp t' (InTree_trans hRootC ht'))
            (fun t' ht' => hshape t' (InTree_trans hRootC ht'))
            (fun t' ht' => hts t' (InTree_trans hRootC ht'))
      · -- verify_child
        have hlen : ch.length = 1 := by
          have := hshR; simp only [fanoutMem] at this; omega
        obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hlen
        have hRootC : InTree (NTree.node (MState.verify_child, d) [c]) c :=
          InTree.sub (by simp) (InTree.here c)
        have hszC : sizeOf c < sizeOf (NTree.node (MState.verify_child, d) [c]) := by
          simp only [NTree.node.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
        simp only [ChainNode, NTree.label_node, NTree.children_node] at hchR
        simp only [TsNode, NTree.label_node] at htsR
        rw [ofNTree_verify]
        refine ⟨hstrow, hVm, ?_, ?_, ?_⟩
        · exact htsR
        · rw [rootRow_ofNTree]; exact hchR
        · exact ih (sizeOf c) (by omega) c le_rfl (RVT_of_InTree hrvt hRootC)
            (fun t' ht' => hinp t' (InTree_trans hRootC ht'))
            (fun t' ht' => hshape t' (InTree_trans hRootC ht'))
            (fun t' ht' => hts t' (InTree_trans hRootC ht'))

/-- β-free twin of `wf_memwalk_of_memAIR` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem wfTopo_memwalk_of_memAIR (E : NTree (MState × DTmem K) → ℕ) (inp : Inputs K)
    (lblm : ℕ → MState × DTmem K) (kroots hm : ℕ)
    (hgoal : ForestReconGoal (mem_stateSep_topo (K := K)) lblm kroots hm)
    (hinp   : ∀ t' : NTree (MState × DTmem K), (NTree.label t').2.1 = inp)
    (hts    : ∀ t' : NTree (MState × DTmem K), TsNode E inp t') :
    ∃ ts : List (NTree (MState × DTmem K)),
      ts.length = kroots
      ∧ (bfsForest ts).map NTree.label = (List.range' 1 hm).map lblm
      ∧ (∀ tree ∈ ts, MemWalk.WFTopo inp (ofNTree E tree)) := by
  obtain ⟨ts, hlen, hrvt, hlab, hfan, _hleaf⟩ := hgoal
  refine ⟨ts, hlen, hlab, ?_⟩
  intro tree htree
  refine wfTopo_ofNTree E inp tree (hrvt tree htree) (fun t' _ => hinp t') ?_
    (fun t' _ => hts t')
  intro t' ht'
  have hmem : t' ∈ bfsForest ts := (mem_bfsForest ts t').mpr ⟨tree, htree, ht'⟩
  exact hfan t' hmem

/-- β-free twin of `axis_lookups_valid_endToEnd` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_endToEnd_topo [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (E : NTree (MState × DTmem K) → ℕ) (inp : Inputs K)
    (tr : NTree (MState × DTmem K))
    (hrvt : RVT FmemTopo tr)
    (hinp : ∀ t', InTree tr t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree tr t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree tr t' → TsNode E inp t')
    (hterm : (ofNTree E tr).rootPt.counts = 0)
    (T C' : ℕ → K)
    (hlam : sameLambda (ofNTree E tr).rootRow.lambda (ofNTree E tr))
    (hT : readAxis T (ofNTree E tr)) (hC : readCprime C' (ofNTree E tr))
    (e : ℕ)
    (hnest : Nested e (ofNTree E tr).toMTree)
    (hrnd : (readExps (ofNTree E tr).toMTree).Nodup)
    (hvnd : (verifyExps (ofNTree E tr).toMTree).Nodup)
    (hused_r : e ∈ readExps (ofNTree E tr).toMTree)
    (hused_v : e ∈ verifyExps (ofNTree E tr).toMTree)
    (hbad : vaxis e (ofNTree E tr).toMTree ≠ Relaxis e (ofNTree E tr).toMTree) :
    inp.z ∈ Finset.univ.filter
        (fun z : K => (countsP (ofNTree E tr).toMTree (ofNTree E tr).rootRow.lambda T C').eval z = 0)
      ∧ (Finset.univ.filter
            (fun z : K => (countsP_bin (ofNTree E tr).toMTree).eval z = 0)).card
          ≤ (countsP_bin (ofNTree E tr).toMTree).natDegree := by
  have hwf : MemWalk.WFTopo inp (ofNTree E tr) := wfTopo_ofNTree E inp tr hrvt hinp hshape hts
  obtain ⟨hr, hv⟩ := used_once_of_unique_ts e (ofNTree E tr).toMTree hrnd hvnd hused_r hused_v
  exact axis_lookups_valid_of_memtrace_topo h2 inp T C' (ofNTree E tr) hwf hlam hT hC
    hterm e hnest hr hv hbad

/-- β-free twin of `axis_lookups_valid_endToEnd_of_seedGate` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_endToEnd_of_seedGate_topo [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (E : NTree (MState × DTmem K) → ℕ) (inp : Inputs K)
    (mop : MState → K) (mg : K)
    (tr : NTree (MState × DTmem K))
    (hrvt : RVT FmemTopo tr)
    (hinp : ∀ t', InTree tr t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree tr t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree tr t' → TsNode E inp t')
    (hgate : ∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
        ex.eval (Reified.memoryEnvFull inp mop (ofNTree E tr).rootRow mg) = 0)
    (T C' : ℕ → K)
    (hlam : sameLambda (ofNTree E tr).rootRow.lambda (ofNTree E tr))
    (hT : readAxis T (ofNTree E tr)) (hC : readCprime C' (ofNTree E tr))
    (e : ℕ)
    (hnest : Nested e (ofNTree E tr).toMTree)
    (hrnd : (readExps (ofNTree E tr).toMTree).Nodup)
    (hvnd : (verifyExps (ofNTree E tr).toMTree).Nodup)
    (hused_r : e ∈ readExps (ofNTree E tr).toMTree)
    (hused_v : e ∈ verifyExps (ofNTree E tr).toMTree)
    (hbad : vaxis e (ofNTree E tr).toMTree ≠ Relaxis e (ofNTree E tr).toMTree) :
    inp.z ∈ Finset.univ.filter
        (fun z : K => (countsP (ofNTree E tr).toMTree (ofNTree E tr).rootRow.lambda T C').eval z = 0)
      ∧ (Finset.univ.filter
            (fun z : K => (countsP_bin (ofNTree E tr).toMTree).eval z = 0)).card
          ≤ (countsP_bin (ofNTree E tr).toMTree).natDegree :=
  axis_lookups_valid_endToEnd_topo h2 E inp tr hrvt hinp hshape hts
    (seedGate_gives_rootPt_zero inp mop mg (ofNTree E tr) hgate).1
    T C' hlam hT hC e hnest hrnd hvnd hused_r hused_v hbad

/-- β-free twin of `axis_lookups_valid_endToEnd_perfect` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_endToEnd_perfect_topo
    (h2 : (2 : K) ≠ 0) (E : NTree (MState × DTmem K) → ℕ) (inp : Inputs K)
    (tr : NTree (MState × DTmem K))
    (hrvt : RVT FmemTopo tr)
    (hinp : ∀ t', InTree tr t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree tr t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree tr t' → TsNode E inp t')
    (hterm : countsP_bin (ofNTree E tr).toMTree = 0)
    (e : ℕ)
    (hnest : Nested e (ofNTree E tr).toMTree)
    (hrnd : (readExps (ofNTree E tr).toMTree).Nodup)
    (hvnd : (verifyExps (ofNTree E tr).toMTree).Nodup)
    (hused_r : e ∈ readExps (ofNTree E tr).toMTree)
    (hused_v : e ∈ verifyExps (ofNTree E tr).toMTree) :
    vaxis e (ofNTree E tr).toMTree = Relaxis e (ofNTree E tr).toMTree := by
  have hwf : MemWalk.WFTopo inp (ofNTree E tr) := wfTopo_ofNTree E inp tr hrvt hinp hshape hts
  obtain ⟨hr, hv⟩ := used_once_of_unique_ts e (ofNTree E tr).toMTree hrnd hvnd hused_r hused_v
  exact axis_lookups_valid_perfect_of_memtrace_topo h2 inp (ofNTree E tr) hwf hterm e hnest hr hv

/-- β-free twin of `axis_lookups_valid_endToEnd_uniqReq` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_endToEnd_uniqReq_topo [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (E : NTree (MState × DTmem K) → ℕ) (inp : Inputs K) (Ksz : ℕ)
    (tr : NTree (MState × DTmem K))
    (hrvt : RVT FmemTopo tr)
    (hinp : ∀ t', InTree tr t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree tr t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree tr t' → TsNode E inp t')
    (hterm : (ofNTree E tr).rootPt.counts = 0)
    (T C' : ℕ → K)
    (hlam : sameLambda (ofNTree E tr).rootRow.lambda (ofNTree E tr))
    (hT : readAxis T (ofNTree E tr)) (hC : readCprime C' (ofNTree E tr))
    (e : ℕ)
    (hnest : Nested e (ofNTree E tr).toMTree)
    (hUReq : ((readExps (ofNTree E tr).toMTree).map (fun k => inp.z ^ k)).Nodup)
    (hmatch : IO.LmIO Ksz ((readExps (ofNTree E tr).toMTree).map (fun k => inp.z ^ k))
        ((verifyExps (ofNTree E tr).toMTree).map (fun k => inp.z ^ k)))
    (hused_r : e ∈ readExps (ofNTree E tr).toMTree)
    (hused_v : e ∈ verifyExps (ofNTree E tr).toMTree)
    (hbad : vaxis e (ofNTree E tr).toMTree ≠ Relaxis e (ofNTree E tr).toMTree) :
    inp.z ∈ Finset.univ.filter
        (fun z : K => (countsP (ofNTree E tr).toMTree (ofNTree E tr).rootRow.lambda T C').eval z = 0)
      ∧ (Finset.univ.filter
            (fun z : K => (countsP_bin (ofNTree E tr).toMTree).eval z = 0)).card
          ≤ (countsP_bin (ofNTree E tr).toMTree).natDegree := by
  have hrnd : (readExps (ofNTree E tr).toMTree).Nodup :=
    readExps_nodup_of_ts inp.z _ hUReq
  have hvnd : (verifyExps (ofNTree E tr).toMTree).Nodup :=
    verifyExps_nodup_of_ts inp.z _ (verifyTs_nodup_of_uniqueRequest Ksz inp.z _ hUReq hmatch)
  exact axis_lookups_valid_endToEnd_topo h2 E inp tr hrvt hinp hshape hts hterm T C' hlam hT hC
    e hnest hrnd hvnd hused_r hused_v hbad

/-- β-free twin of `axis_lookups_valid_endToEnd_uniqReq_of_seedGate` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_endToEnd_uniqReq_of_seedGate_topo [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (E : NTree (MState × DTmem K) → ℕ) (inp : Inputs K) (Ksz : ℕ)
    (mop : MState → K) (mg : K)
    (tr : NTree (MState × DTmem K))
    (hrvt : RVT FmemTopo tr)
    (hinp : ∀ t', InTree tr t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree tr t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree tr t' → TsNode E inp t')
    (hgate : ∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
        ex.eval (Reified.memoryEnvFull inp mop (ofNTree E tr).rootRow mg) = 0)
    (T C' : ℕ → K)
    (hlam : sameLambda (ofNTree E tr).rootRow.lambda (ofNTree E tr))
    (hT : readAxis T (ofNTree E tr)) (hC : readCprime C' (ofNTree E tr))
    (e : ℕ)
    (hnest : Nested e (ofNTree E tr).toMTree)
    (hUReq : ((readExps (ofNTree E tr).toMTree).map (fun k => inp.z ^ k)).Nodup)
    (hmatch : IO.LmIO Ksz ((readExps (ofNTree E tr).toMTree).map (fun k => inp.z ^ k))
        ((verifyExps (ofNTree E tr).toMTree).map (fun k => inp.z ^ k)))
    (hused_r : e ∈ readExps (ofNTree E tr).toMTree)
    (hused_v : e ∈ verifyExps (ofNTree E tr).toMTree)
    (hbad : vaxis e (ofNTree E tr).toMTree ≠ Relaxis e (ofNTree E tr).toMTree) :
    inp.z ∈ Finset.univ.filter
        (fun z : K => (countsP (ofNTree E tr).toMTree (ofNTree E tr).rootRow.lambda T C').eval z = 0)
      ∧ (Finset.univ.filter
            (fun z : K => (countsP_bin (ofNTree E tr).toMTree).eval z = 0)).card
          ≤ (countsP_bin (ofNTree E tr).toMTree).natDegree :=
  axis_lookups_valid_endToEnd_uniqReq_topo h2 E inp Ksz tr hrvt hinp hshape hts
    (seedGate_gives_rootPt_zero inp mop mg (ofNTree E tr) hgate).1
    T C' hlam hT hC e hnest hUReq hmatch hused_r hused_v hbad

/-- β-free twin of `axis_lookups_valid_endToEnd_perfect_defE` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_endToEnd_perfect_defE_topo
    (h2 : (2 : K) ≠ 0) (inp : Inputs K)
    (tr : NTree (MState × DTmem K))
    (hrvt : RVT FmemTopo tr)
    (hinp : ∀ t', InTree tr t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree tr t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree tr t' → TsExists inp t')
    (hterm : countsP_bin (ofNTree (expOf inp) tr).toMTree = 0)
    (e : ℕ)
    (hnest : Nested e (ofNTree (expOf inp) tr).toMTree)
    (hrnd : (readExps (ofNTree (expOf inp) tr).toMTree).Nodup)
    (hvnd : (verifyExps (ofNTree (expOf inp) tr).toMTree).Nodup)
    (hused_r : e ∈ readExps (ofNTree (expOf inp) tr).toMTree)
    (hused_v : e ∈ verifyExps (ofNTree (expOf inp) tr).toMTree) :
    vaxis e (ofNTree (expOf inp) tr).toMTree = Relaxis e (ofNTree (expOf inp) tr).toMTree :=
  axis_lookups_valid_endToEnd_perfect_topo h2 (expOf inp) inp tr hrvt hinp hshape
    (fun t' ht' => tsNode_expOf inp t' (hts t' ht')) hterm e hnest hrnd hvnd hused_r hused_v

/-- β-free twin of `axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE_topo [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (inp : Inputs K) (Ksz : ℕ)
    (mop : MState → K) (mg : K)
    (tr : NTree (MState × DTmem K))
    (hrvt : RVT FmemTopo tr)
    (hinp : ∀ t', InTree tr t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree tr t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree tr t' → TsExists inp t')
    (hgate : ∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
        ex.eval (Reified.memoryEnvFull inp mop (ofNTree (expOf inp) tr).rootRow mg) = 0)
    (T C' : ℕ → K)
    (hlam : sameLambda (ofNTree (expOf inp) tr).rootRow.lambda (ofNTree (expOf inp) tr))
    (hT : readAxis T (ofNTree (expOf inp) tr))
    (hC : readCprime C' (ofNTree (expOf inp) tr))
    (e : ℕ)
    (hnest : Nested e (ofNTree (expOf inp) tr).toMTree)
    (hUReq : ((readExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k)).Nodup)
    (hmatch : IO.LmIO Ksz ((readExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k))
        ((verifyExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k)))
    (hused_r : e ∈ readExps (ofNTree (expOf inp) tr).toMTree)
    (hused_v : e ∈ verifyExps (ofNTree (expOf inp) tr).toMTree)
    (hbad : vaxis e (ofNTree (expOf inp) tr).toMTree ≠ Relaxis e (ofNTree (expOf inp) tr).toMTree) :
    inp.z ∈ Finset.univ.filter
        (fun z : K =>
          (countsP (ofNTree (expOf inp) tr).toMTree
            (ofNTree (expOf inp) tr).rootRow.lambda T C').eval z = 0)
      ∧ (Finset.univ.filter
            (fun z : K => (countsP_bin (ofNTree (expOf inp) tr).toMTree).eval z = 0)).card
          ≤ (countsP_bin (ofNTree (expOf inp) tr).toMTree).natDegree :=
  axis_lookups_valid_endToEnd_uniqReq_of_seedGate_topo
    (E := expOf inp) h2 inp Ksz mop mg tr hrvt hinp hshape
    (fun t' ht' => tsNode_expOf inp t' (hts t' ht')) hgate
    (T := T) (C' := C') hlam hT hC e hnest hUReq hmatch hused_r hused_v hbad

open NockVM in
/-- β-free twin of `forest_tsExists_of_LIO` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem forest_tsExists_of_LIO_topo
    (lblc : ℕ → ComputeTable.State × ComputeTable.DTcomp K) (hc : ℕ)
    (lblm : ℕ → MState × DTmem K) (hm : ℕ) (inpM : Inputs K) (lmb : K) (Ksz : ℕ)
    (hhon : HonestVer lblm hm)
    (hLIO : IO.LIO Ksz (reqRecs lblc hc lmb) (respRecs lblm hm))
    (hReqTs : ∀ v ∈ reqRecs lblc hc lmb, ∃ e : ℕ, v 7 = inpM.z ^ e)
    (ts : List (NTree (MState × DTmem K)))
    (hlab : (bfsForest ts).map NTree.label = (List.range' 1 hm).map lblm)
    (tree : NTree (MState × DTmem K)) (htree : tree ∈ ts) (hrvt : RVT FmemTopo tree)
    (hVerTs : ∀ t', InTree tree t' → (NTree.label t').1 = MState.verify_child →
        ∃ e : ℕ, (NTree.label t').2.2.mem.ts = inpM.z ^ e) :
    ∀ t', InTree tree t' → TsExists inpM t' := by
  -- served-record timestamps are closed powers of `z`
  have hresp := respTs_closed_of_LIO Ksz (fun v : Fin 9 → K => v 7) inpM.z _ _ hReqTs hLIO
  intro t' ht'
  -- the node's label is the committed row `lblm i`, `1 ≤ i ≤ hm`
  have hmem : t' ∈ bfsForest ts := (mem_bfsForest ts t').mpr ⟨tree, htree, ht'⟩
  have hlabmem : NTree.label t' ∈ (bfsForest ts).map NTree.label := List.mem_map_of_mem hmem
  rw [hlab, List.mem_map] at hlabmem
  obtain ⟨i, hi, hival⟩ := hlabmem
  rw [List.mem_range'] at hi; obtain ⟨kk, hkk, hik⟩ := hi
  -- state match `(label t').2.2.st = (label t').1` from `RVT FmemTopo`
  have hFcon := (RVT_iff_forall_InTree FmemTopo tree).mp hrvt t' ht'
  have hstmatch : (NTree.label t').2.2.st = (NTree.label t').1 := hFcon.1.1
  rw [TsExists]
  cases hlbl : (NTree.label t').1 with
  | decompose => trivial
  | halt => trivial
  | read_root =>
    -- served, so timestamp closed
    have hst_i : (lblm i).2.2.st = MState.read_root := by
      rw [hival]; rw [hstmatch, hlbl]
    have hver_i : (lblm i).2.2.ver = true :=
      ver_true_of_honest_read_root lblm hm i hhon (by omega) (by omega) hst_i
    have hmemR : encRecC (lblm i).2.2.mem (lblm i).2.2.cprime ∈ respRecs lblm hm :=
      encRec_mem_respRecs lblm hm i (by omega) (by omega) hver_i
    obtain ⟨e, he⟩ := hresp _ hmemR
    rw [encRecC_ts] at he
    exact ⟨e, by rw [← hival]; exact he⟩
  | verify_child =>
    -- carried (intermediate accumulator not materialized)
    exact hVerTs t' ht' hlbl

open NockVM in
/-- β-free twin of `seedCoupled_tsExists_read` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem seedCoupled_tsExists_read_topo
    (lblc : ℕ → ComputeTable.State × ComputeTable.DTcomp K) (hc : ℕ) (lmb : K)
    (lblm : ℕ → MState × DTmem K) (hm : ℕ) (inpM : Inputs K)
    (hhon : HonestVer lblm hm)
    (hsc : NockVM.SeedCoupled lmb lblc hc lblm hm inpM.z)
    (ts : List (NTree (MState × DTmem K)))
    (hlab : (bfsForest ts).map NTree.label = (List.range' 1 hm).map lblm)
    (tree : NTree (MState × DTmem K)) (htree : tree ∈ ts) (hrvt : RVT FmemTopo tree) :
    ∀ t', InTree tree t' → (NTree.label t').1 = MState.read_root → TsExists inpM t' := by
  intro t' ht' hlbl
  have hmem : t' ∈ bfsForest ts := (mem_bfsForest ts t').mpr ⟨tree, htree, ht'⟩
  have hlabmem : NTree.label t' ∈ (bfsForest ts).map NTree.label := List.mem_map_of_mem hmem
  rw [hlab, List.mem_map] at hlabmem
  obtain ⟨i, hi, hival⟩ := hlabmem
  rw [List.mem_range'] at hi; obtain ⟨kk, hkk, hik⟩ := hi
  have hFcon := (RVT_iff_forall_InTree FmemTopo tree).mp hrvt t' ht'
  have hstmatch : (NTree.label t').2.2.st = (NTree.label t').1 := hFcon.1.1
  rw [TsExists, hlbl]
  have hst_i : (lblm i).2.2.st = MState.read_root := by rw [hival, hstmatch, hlbl]
  have hver_i : (lblm i).2.2.ver = true :=
    ver_true_of_honest_read_root lblm hm i hhon (by omega) (by omega) hst_i
  have hmemR : encRecC (lblm i).2.2.mem (lblm i).2.2.cprime ∈ NockVM.respRecs lblm hm :=
    encRec_mem_respRecs lblm hm i (by omega) (by omega) hver_i
  obtain ⟨e, he⟩ := hsc.2 _ hmemR
  rw [encRecC_ts] at he
  exact ⟨e, by rw [← hival]; exact he⟩

open NockVM in
/-- β-free twin of `forest_tsExists_of_interLIO` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem forest_tsExists_of_interLIO_topo
    (lblc : ℕ → ComputeTable.State × ComputeTable.DTcomp K) (hc : ℕ)
    (lblm : ℕ → MState × DTmem K) (hm : ℕ) (inpM : Inputs K) (lmb : K) (Ksz : ℕ)
    (hhon : HonestVer lblm hm)
    (hLIO : IO.LIO Ksz (reqRecs lblc hc lmb) (respRecs lblm hm))
    (hReqTs : ∀ v ∈ reqRecs lblc hc lmb, ∃ e : ℕ, v 7 = inpM.z ^ e)
    (hInterLIO : IO.LIO Ksz (respRecs lblm hm) (verifyRecsMem lblm hm))
    (ts : List (NTree (MState × DTmem K)))
    (hlab : (bfsForest ts).map NTree.label = (List.range' 1 hm).map lblm)
    (tree : NTree (MState × DTmem K)) (htree : tree ∈ ts) (hrvt : RVT FmemTopo tree) :
    ∀ t', InTree tree t' → TsExists inpM t' := by
  -- served-record timestamps are closed powers of `z` (read/served side)
  have hresp := respTs_closed_of_LIO Ksz (fun v : Fin 9 → K => v 7) inpM.z _ _ hReqTs hLIO
  -- verify-removed records are, by the intermediate matching, among the served records
  have hverInResp : ∀ v ∈ verifyRecsMem lblm hm, v ∈ respRecs lblm hm := by
    obtain ⟨_, _, hperm⟩ := hInterLIO
    intro v hv; exact hperm.mem_iff.mpr hv
  intro t' ht'
  have hmem : t' ∈ bfsForest ts := (mem_bfsForest ts t').mpr ⟨tree, htree, ht'⟩
  have hlabmem : NTree.label t' ∈ (bfsForest ts).map NTree.label := List.mem_map_of_mem hmem
  rw [hlab, List.mem_map] at hlabmem
  obtain ⟨i, hi, hival⟩ := hlabmem
  rw [List.mem_range'] at hi; obtain ⟨kk, hkk, hik⟩ := hi
  have hFcon := (RVT_iff_forall_InTree FmemTopo tree).mp hrvt t' ht'
  have hstmatch : (NTree.label t').2.2.st = (NTree.label t').1 := hFcon.1.1
  rw [TsExists]
  cases hlbl : (NTree.label t').1 with
  | decompose => trivial
  | halt => trivial
  | read_root =>
    have hst_i : (lblm i).2.2.st = MState.read_root := by rw [hival]; rw [hstmatch, hlbl]
    have hver_i : (lblm i).2.2.ver = true :=
      ver_true_of_honest_read_root lblm hm i hhon (by omega) (by omega) hst_i
    have hmemR : encRecC (lblm i).2.2.mem (lblm i).2.2.cprime ∈ respRecs lblm hm :=
      encRec_mem_respRecs lblm hm i (by omega) (by omega) hver_i
    obtain ⟨e, he⟩ := hresp _ hmemR
    rw [encRecC_ts] at he
    exact ⟨e, by rw [← hival]; exact he⟩
  | verify_child =>
    have hst_i : (lblm i).2.2.st = MState.verify_child := by rw [hival]; rw [hstmatch, hlbl]
    have hmemV : encRec (lblm i).2.2.mem ∈ verifyRecsMem lblm hm :=
      encRec_mem_verifyRecsMem lblm hm i (by omega) (by omega) hst_i
    -- intermediate matching: the verify record is a served (read) record ⟹ ts = z^e
    obtain ⟨e, he⟩ := hresp _ (hverInResp _ hmemV)
    rw [encRec_ts] at he
    exact ⟨e, by rw [← hival]; exact he⟩

/-- β-free twin of `V_NockVMROM_forest_axisvalid`.  Hypotheses verbatim; conjuncts (1)–(3) verbatim
    (`NockVM.V_NockVMROM_forest`, which reads `RAPmem` through `hRm` exactly as the original
    does); conjunct (4) is the original's with its forest antecedent `ForestReconGoal
    mem_stateSep_topo` (implied by the original's `ForestReconGoal mem_stateSep`,
    `forestReconGoal_topo_of_fmem`), so it implies the original's (4), and its axis-validity proof
    runs on `MemWalk.WFTopo` / `RVT FmemTopo`. -/
theorem V_NockVMROM_forest_axisvalid_topo
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0)
    {p : ℕ} [CharP K p]
    -- compute chip
    {ncs : ℕ} (encc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K))
    (hEncc : Function.Injective encc)
    (lblc : ℕ → ComputeTable.State × ComputeTable.DTcomp K) (clabc : ℕ → ℕ → ComputeTable.State × ComputeTable.DTcomp K)
    (foc : ℕ → ℕ) {hc : ℕ} (harityc : ∀ i, foc i ≤ 3)
    (qc qinvc : ℕ → K) (hqc : Walk.QGate foc qc qinvc 1 hc) (hwrapc : 1 + hc * 3 < p)
    (hfoc : ∀ i, 1 ≤ i → i ≤ hc → foc i = (ComputeTable.comp_stateSep (K := K)).fanout (lblc i).1)
    (hRc : ∀ i, 1 ≤ i → i ≤ hc →
      (∃ ex, ComputeTable.RAPcomp (lblc i).2.1 (lblc i).2.2.1 (lblc i).2.2.2 ex)
        ∧ (lblc i).2.2.1.state = (lblc i).1
        ∧ (∀ j : Fin 3, (j : ℕ) < foc i ↔
            (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none)
        ∧ ComputeTable.childLinkComp (lblc i)
            (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none))
    -- memory chip (multi-root forest)
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
    -- IO linking over the SHARED derived record lists
    (lmb : K) (Ksz : ℕ) (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz (NockVM.reqRecs lblc hc lmb).length)
    (hKresp : (NockVM.respRecs lblm hm).length ≤ Ksz)
    (hreqnd : (NockVM.reqRecs lblc hc lmb).Nodup) (hrespnd : (NockVM.respRecs lblm hm).Nodup) :
    -- (1)(2)(3) — verbatim the `V_NockVMROM_forest` capstone (un-weakened, NO new hypothesis)
    (((NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) encc lblc clabc foc hc).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hc : ℚ) / (Fintype.card K : ℚ)
          + ((hc * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    ∧ (((NockVM.walkBadForest (mem_stateSep (K := K)) encm lblm clabm fom kroots_m hm).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hm : ℚ) / (Fintype.card K : ℚ)
          + ((hm * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    ∧ ((∃ (m : Fin (NockVM.respRecs lblm hm).length → ZMod p)
          (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests
              (NockVM.reqRecs lblc hc lmb).length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m)
              accM responses out_mem (NockVM.respRecs lblm hm).length
          ∧ requests = responses ∧ out_mem = 0)
        ↔ IO.LIO Ksz (NockVM.reqRecs lblc hc lmb) (NockVM.respRecs lblm hm))
    -- (4) — INTEGRATED axis validity, THREADED through conjunct (2)'s OWN reconstructed forest.  `inpM` is FIXED to the memory chip's shared RAP inputs
    -- `(lblm i).2.1`; the forest is conjunct (2)'s `ForestReconGoal` witness (the good/reconstruction
    -- event whose failure probability conjunct (2) bounds), NOT a fresh `∀ tr`.
    -- gated ONLY on the IO-accepted good event — an antecedent of
    -- conjunct (4) alone, so conjuncts (1)(2)(3) stay ungated / `V_NockVMROM_forest` verbatim.
    ∧ (IO.LIO Ksz (NockVM.reqRecs lblc hc lmb) (NockVM.respRecs lblm hm) →
        ∀ (inpM : Inputs K),
          (∀ i, 1 ≤ i → i ≤ hm → (lblm i).2.1 = inpM) →
          -- Honest `ver = (st = read_root)`: responses are `ver`-selected.
          HonestVer lblm hm →
          -- compute-chip request timestamps in closed form `z^i`: the read/served
          -- half of `TsExists` is DISCHARGED from this + the IO matching via `respTs_closed_of_LIO`.
          (∀ v ∈ NockVM.reqRecs lblc hc lmb, ∃ e : ℕ, v 7 = inpM.z ^ e) →
          -- MATERIALIZED `intermediate` accumulator: the ordered read/verify record
          -- lists match (`read_root` ADDS `respRecs`, `verify_child` REMOVES `verifyRecsMem`; the
          -- LogUp balance of `MemoryTable.interChain_balance`, upgraded to a perfect matching by
          -- `Thm:IO_result`).
          IO.LIO Ksz (NockVM.respRecs lblm hm) (verifyRecsMem lblm hm) →
          ForestReconGoal (mem_stateSep_topo (K := K)) lblm kroots_m hm →
          ∃ ts : List (NTree (MState × DTmem K)),
            ts.length = kroots_m
            ∧ (bfsForest ts).map NTree.label = (List.range' 1 hm).map lblm
            ∧ ∀ tree ∈ ts,
                -- DISCHARGED (`countsP = 0`): the exported memory seed `.boundary` gate at the
                -- walk-root row, a REAL RAP gate — not a raw `counts = 0`.
                ∀ (mop : MState → K) (mg : K),
                  (∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
                      ex.eval (Reified.memoryEnvFull inpM mop
                        (ofNTree (expOf inpM) tree).rootRow mg) = 0) →
                  ∀ (T C' : ℕ → K),
                    sameLambda (ofNTree (expOf inpM) tree).rootRow.lambda
                      (ofNTree (expOf inpM) tree) →
                    readAxis T (ofNTree (expOf inpM) tree) →
                    readCprime C' (ofNTree (expOf inpM) tree) →
                  ∀ e : ℕ,
                    -- carried: well-nesting.
                    Nested e (ofNTree (expOf inpM) tree).toMTree →
                    -- DISCHARGED (both `Nodup`): from the paper's IO unique-request object `hUReq`
                    -- and the intermediate matching `hmatch` via `IO.cor_uni_req_uni_resp` — no raw read/verify `Nodup`.
                    ((readExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k)).Nodup →
                    IO.LmIO Ksz
                        ((readExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k))
                        ((verifyExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k)) →
                    e ∈ readExps (ofNTree (expOf inpM) tree).toMTree →
                    e ∈ verifyExps (ofNTree (expOf inpM) tree).toMTree →
                    vaxis e (ofNTree (expOf inpM) tree).toMTree
                        ≠ Relaxis e (ofNTree (expOf inpM) tree).toMTree →
                    inpM.z ∈ Finset.univ.filter
                        (fun z : K =>
                          (countsP (ofNTree (expOf inpM) tree).toMTree
                            (ofNTree (expOf inpM) tree).rootRow.lambda T C').eval z = 0)
                      ∧ (Finset.univ.filter
                          (fun z : K => (countsP_bin (ofNTree (expOf inpM) tree).toMTree).eval z = 0)).card
                          ≤ (countsP_bin (ofNTree (expOf inpM) tree).toMTree).natDegree) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (NockVM.V_NockVMROM_forest encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc hfoc hRc
      encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom hRm
      Ksz hKp hKreq hKresp hreqnd hrespnd).1
  · exact (NockVM.V_NockVMROM_forest encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc hfoc hRc
      encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom hRm
      Ksz hKp hKreq hKresp hreqnd hrespnd).2.1
  · exact (NockVM.V_NockVMROM_forest encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc hfoc hRc
      encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom hRm
      Ksz hKp hKreq hKresp hreqnd hrespnd).2.2
  · -- (4) THREADED: obtain the reconstructed forest from conjunct (2)'s OWN `ForestReconGoal`,
    -- fix `inpM` to the shared RAP inputs, and certify axis validity for every reconstructed tree.
    intro hLIO inpM hinpM hhon hReqTs hInterLIO hgoal
    obtain ⟨ts, hlen, hrvtall, hlab, hfan, _hleaf⟩ := hgoal
    refine ⟨ts, hlen, hlab, ?_⟩
    intro tree htree mop mg hgate T C' hlam hT hC e hnest hUReq hmatch hur hv hbad
    -- `RVT FmemTopo`, shared inputs, and `StateSep` fanout are all READ OUT of `ForestReconGoal`.
    have hrvt : RVT FmemTopo tree := hrvtall tree htree
    have hinp : ∀ t', InTree tree t' → (NTree.label t').2.1 = inpM := by
      intro t' ht'
      have hmem : t' ∈ bfsForest ts := (mem_bfsForest ts t').mpr ⟨tree, htree, ht'⟩
      have hlabmem : NTree.label t' ∈ (bfsForest ts).map NTree.label :=
        List.mem_map_of_mem hmem
      rw [hlab, List.mem_map] at hlabmem
      obtain ⟨i, hi, hival⟩ := hlabmem
      rw [List.mem_range'] at hi
      obtain ⟨kk, hkk, hik⟩ := hi
      rw [← hival]; exact hinpM i (by omega) (by omega)
    have hshape : ∀ t', InTree tree t' →
        fanoutMem (NTree.label t').1 = (NTree.children t').length := by
      intro t' ht'
      have hmem : t' ∈ bfsForest ts := (mem_bfsForest ts t').mpr ⟨tree, htree, ht'⟩
      exact hfan t' hmem
    -- FULL `TsExists` (read + VERIFY) DISCHARGED: read/served side from `hLIO` + `hReqTs`; VERIFY
    -- side from the materialized `intermediate` matching `hInterLIO`, no `hVerTs`.
    have htsE : ∀ t', InTree tree t' → TsExists inpM t' :=
      forest_tsExists_of_interLIO_topo lblc hc lblm hm inpM lmb Ksz hhon hLIO hReqTs hInterLIO ts hlab tree htree hrvt
    exact axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE_topo h2 inpM Ksz mop mg tree hrvt hinp
      hshape htsE hgate T C' hlam hT hC e hnest hUReq hmatch hur hv hbad

/-- β-free twin of `axis_lookups_valid_endToEnd_seedpinned` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_endToEnd_seedpinned_topo [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (inp : Inputs K) (Ksz : ℕ) (mop : MState → K) (mg : K)
    (subj : Noun)
    (tr : NTree (MState × DTmem K))
    (hrvt : RVT FmemTopo tr)
    (hinp : ∀ t', InTree tr t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree tr t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree tr t' → TsExists inp t')
    (hgate : ∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
        ex.eval (Reified.memoryEnvFull inp mop (ofNTree (expOf inp) tr).rootRow mg) = 0)
    (T C' : ℕ → K)
    (hlam : sameLambda (ofNTree (expOf inp) tr).rootRow.lambda (ofNTree (expOf inp) tr))
    (hT : readAxis T (ofNTree (expOf inp) tr))
    (hC : readCprime C' (ofNTree (expOf inp) tr))
    (e : ℕ)
    (hsp : SeedPinned subj (ofNTree (expOf inp) tr).toMTree)
    (hUReq : ((readExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k)).Nodup)
    (hmatch : IO.LmIO Ksz ((readExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k))
        ((verifyExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k)))
    (hused_r : e ∈ readExps (ofNTree (expOf inp) tr).toMTree)
    (hused_v : e ∈ verifyExps (ofNTree (expOf inp) tr).toMTree)
    (hbad : vaxis e (ofNTree (expOf inp) tr).toMTree ≠ Relaxis e (ofNTree (expOf inp) tr).toMTree) :
    inp.z ∈ Finset.univ.filter
        (fun z : K =>
          (countsP (ofNTree (expOf inp) tr).toMTree
            (ofNTree (expOf inp) tr).rootRow.lambda T C').eval z = 0)
      ∧ (Finset.univ.filter
            (fun z : K => (countsP_bin (ofNTree (expOf inp) tr).toMTree).eval z = 0)).card
          ≤ (countsP_bin (ofNTree (expOf inp) tr).toMTree).natDegree := by
  have hrnd : (readExps (ofNTree (expOf inp) tr).toMTree).Nodup :=
    readExps_nodup_of_ts inp.z _ hUReq
  have hvnd : (verifyExps (ofNTree (expOf inp) tr).toMTree).Nodup :=
    verifyExps_nodup_of_ts inp.z _ (verifyTs_nodup_of_uniqueRequest Ksz inp.z _ hUReq hmatch)
  obtain ⟨hr1, hv1⟩ := used_once_of_unique_ts e (ofNTree (expOf inp) tr).toMTree hrnd hvnd hused_r hused_v
  have hnest : Nested e (ofNTree (expOf inp) tr).toMTree :=
    nested_of_seedPinned hsp e (le_of_eq hr1) (le_of_eq hv1)
  exact axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE_topo h2 inp Ksz mop mg tr hrvt hinp hshape
    hts hgate T C' hlam hT hC e hnest hUReq hmatch hused_r hused_v hbad

/-- β-free twin of `V_NockVMROM_forest_axisvalid_seedpinned`.  Hypotheses verbatim; conjuncts (1)–(3) verbatim
    (`NockVM.V_NockVMROM_forest`, which reads `RAPmem` through `hRm` exactly as the original
    does); conjunct (4) is the original's with its forest antecedent `ForestReconGoal
    mem_stateSep_topo` (implied by the original's `ForestReconGoal mem_stateSep`,
    `forestReconGoal_topo_of_fmem`), so it implies the original's (4), and its axis-validity proof
    runs on `MemWalk.WFTopo` / `RVT FmemTopo`. -/
theorem V_NockVMROM_forest_axisvalid_seedpinned_topo
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0)
    {p : ℕ} [CharP K p]
    -- compute chip
    {ncs : ℕ} (encc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K))
    (hEncc : Function.Injective encc)
    (lblc : ℕ → ComputeTable.State × ComputeTable.DTcomp K) (clabc : ℕ → ℕ → ComputeTable.State × ComputeTable.DTcomp K)
    (foc : ℕ → ℕ) {hc : ℕ} (harityc : ∀ i, foc i ≤ 3)
    (qc qinvc : ℕ → K) (hqc : Walk.QGate foc qc qinvc 1 hc) (hwrapc : 1 + hc * 3 < p)
    (hfoc : ∀ i, 1 ≤ i → i ≤ hc → foc i = (ComputeTable.comp_stateSep (K := K)).fanout (lblc i).1)
    (hRc : ∀ i, 1 ≤ i → i ≤ hc →
      (∃ ex, ComputeTable.RAPcomp (lblc i).2.1 (lblc i).2.2.1 (lblc i).2.2.2 ex)
        ∧ (lblc i).2.2.1.state = (lblc i).1
        ∧ (∀ j : Fin 3, (j : ℕ) < foc i ↔
            (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none)
        ∧ ComputeTable.childLinkComp (lblc i)
            (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none))
    -- memory chip (multi-root forest)
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
    -- IO linking over the SHARED derived record lists
    (lmb : K) (Ksz : ℕ) (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz (NockVM.reqRecs lblc hc lmb).length)
    (hKresp : (NockVM.respRecs lblm hm).length ≤ Ksz)
    (hreqnd : (NockVM.reqRecs lblc hc lmb).Nodup) (hrespnd : (NockVM.respRecs lblm hm).Nodup) :
    -- (1)(2)(3) — verbatim the `V_NockVMROM_forest` capstone (un-weakened, NO new hypothesis)
    (((NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) encc lblc clabc foc hc).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hc : ℚ) / (Fintype.card K : ℚ)
          + ((hc * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    ∧ (((NockVM.walkBadForest (mem_stateSep (K := K)) encm lblm clabm fom kroots_m hm).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hm : ℚ) / (Fintype.card K : ℚ)
          + ((hm * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    ∧ ((∃ (m : Fin (NockVM.respRecs lblm hm).length → ZMod p)
          (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests
              (NockVM.reqRecs lblc hc lmb).length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m)
              accM responses out_mem (NockVM.respRecs lblm hm).length
          ∧ requests = responses ∧ out_mem = 0)
        ↔ IO.LIO Ksz (NockVM.reqRecs lblc hc lmb) (NockVM.respRecs lblm hm))
    -- (4) — INTEGRATED axis validity, `Nested` DISCHARGED by the per-root seed-pin.  Threaded
    -- through conjunct (2)'s OWN `ForestReconGoal` forest `ts`; `inpM` FIXED to the shared RAP
    -- inputs; the `Nested e …` antecedent is GONE, replaced by the single `SeedPinned subj …`.
    ∧ (IO.LIO Ksz (NockVM.reqRecs lblc hc lmb) (NockVM.respRecs lblm hm) →
        ∀ (inpM : Inputs K),
          (∀ i, 1 ≤ i → i ≤ hm → (lblm i).2.1 = inpM) →
          HonestVer lblm hm →
          (∀ v ∈ NockVM.reqRecs lblc hc lmb, ∃ e : ℕ, v 7 = inpM.z ^ e) →
          IO.LIO Ksz (NockVM.respRecs lblm hm) (verifyRecsMem lblm hm) →
          ForestReconGoal (mem_stateSep_topo (K := K)) lblm kroots_m hm →
          ∃ ts : List (NTree (MState × DTmem K)),
            ts.length = kroots_m
            ∧ (bfsForest ts).map NTree.label = (List.range' 1 hm).map lblm
            ∧ ∀ tree ∈ ts,
                -- the seed-pin: the reconstructed tree honestly
                -- walks the PUBLIC subject noun `subj` (per forest root — primary AND virtual
                -- subjects).  REPLACES the carried `∀ e, Nested e …` antecedent entirely.
                ∀ (subj : Noun), SeedPinned subj (ofNTree (expOf inpM) tree).toMTree →
                ∀ (mop : MState → K) (mg : K),
                  (∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
                      ex.eval (Reified.memoryEnvFull inpM mop
                        (ofNTree (expOf inpM) tree).rootRow mg) = 0) →
                  ∀ (T C' : ℕ → K),
                    sameLambda (ofNTree (expOf inpM) tree).rootRow.lambda
                      (ofNTree (expOf inpM) tree) →
                    readAxis T (ofNTree (expOf inpM) tree) →
                    readCprime C' (ofNTree (expOf inpM) tree) →
                  ∀ e : ℕ,
                    ((readExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k)).Nodup →
                    IO.LmIO Ksz
                        ((readExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k))
                        ((verifyExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k)) →
                    e ∈ readExps (ofNTree (expOf inpM) tree).toMTree →
                    e ∈ verifyExps (ofNTree (expOf inpM) tree).toMTree →
                    vaxis e (ofNTree (expOf inpM) tree).toMTree
                        ≠ Relaxis e (ofNTree (expOf inpM) tree).toMTree →
                    inpM.z ∈ Finset.univ.filter
                        (fun z : K =>
                          (countsP (ofNTree (expOf inpM) tree).toMTree
                            (ofNTree (expOf inpM) tree).rootRow.lambda T C').eval z = 0)
                      ∧ (Finset.univ.filter
                          (fun z : K => (countsP_bin (ofNTree (expOf inpM) tree).toMTree).eval z = 0)).card
                          ≤ (countsP_bin (ofNTree (expOf inpM) tree).toMTree).natDegree) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (NockVM.V_NockVMROM_forest encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc hfoc hRc
      encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom hRm
      Ksz hKp hKreq hKresp hreqnd hrespnd).1
  · exact (NockVM.V_NockVMROM_forest encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc hfoc hRc
      encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom hRm
      Ksz hKp hKreq hKresp hreqnd hrespnd).2.1
  · exact (NockVM.V_NockVMROM_forest encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc hfoc hRc
      encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom hRm
      Ksz hKp hKreq hKresp hreqnd hrespnd).2.2
  · -- (4) THREADED with `Nested` DISCHARGED: obtain conjunct (2)'s forest, fix `inpM`, and — for
    intro hLIO inpM hinpM hhon hReqTs hInterLIO hgoal
    obtain ⟨ts, hlen, hrvtall, hlab, hfan, _hleaf⟩ := hgoal
    refine ⟨ts, hlen, hlab, ?_⟩
    intro tree htree subj hsp mop mg hgate T C' hlam hT hC e hUReq hmatch hur hv hbad
    have hrvt : RVT FmemTopo tree := hrvtall tree htree
    have hinp : ∀ t', InTree tree t' → (NTree.label t').2.1 = inpM := by
      intro t' ht'
      have hmem : t' ∈ bfsForest ts := (mem_bfsForest ts t').mpr ⟨tree, htree, ht'⟩
      have hlabmem : NTree.label t' ∈ (bfsForest ts).map NTree.label := List.mem_map_of_mem hmem
      rw [hlab, List.mem_map] at hlabmem
      obtain ⟨i, hi, hival⟩ := hlabmem
      rw [List.mem_range'] at hi
      obtain ⟨kk, hkk, hik⟩ := hi
      rw [← hival]; exact hinpM i (by omega) (by omega)
    have hshape : ∀ t', InTree tree t' →
        fanoutMem (NTree.label t').1 = (NTree.children t').length := by
      intro t' ht'
      have hmem : t' ∈ bfsForest ts := (mem_bfsForest ts t').mpr ⟨tree, htree, ht'⟩
      exact hfan t' hmem
    have htsE : ∀ t', InTree tree t' → TsExists inpM t' :=
      forest_tsExists_of_interLIO_topo lblc hc lblm hm inpM lmb Ksz hhon hLIO hReqTs hInterLIO ts hlab tree htree hrvt
    exact axis_lookups_valid_endToEnd_seedpinned_topo h2 inpM Ksz mop mg subj tree hrvt hinp
      hshape htsE hgate T C' hlam hT hC e hsp hUReq hmatch hur hv hbad

/-- β-free twin of `axis_lookups_valid_endToEnd_honestRecon` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_endToEnd_honestRecon_topo [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (inp : Inputs K) (Ksz : ℕ) (mop : MState → K) (mg : K)
    (subj : Noun)
    (tr : NTree (MState × DTmem K))
    (hrvt : RVT FmemTopo tr)
    (hinp : ∀ t', InTree tr t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree tr t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree tr t' → TsExists inp t')
    (hgate : ∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
        ex.eval (Reified.memoryEnvFull inp mop (ofNTree (expOf inp) tr).rootRow mg) = 0)
    (T C' : ℕ → K)
    (hlam : sameLambda (ofNTree (expOf inp) tr).rootRow.lambda (ofNTree (expOf inp) tr))
    (hT : readAxis T (ofNTree (expOf inp) tr))
    (hC : readCprime C' (ofNTree (expOf inp) tr))
    (e : ℕ)
    (hhr : HonestRecon subj (ofNTree (expOf inp) tr).toMTree)
    (hUReq : ((readExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k)).Nodup)
    (hmatch : IO.LmIO Ksz ((readExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k))
        ((verifyExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k)))
    (hused_r : e ∈ readExps (ofNTree (expOf inp) tr).toMTree)
    (hused_v : e ∈ verifyExps (ofNTree (expOf inp) tr).toMTree)
    (hbad : vaxis e (ofNTree (expOf inp) tr).toMTree ≠ Relaxis e (ofNTree (expOf inp) tr).toMTree) :
    inp.z ∈ Finset.univ.filter
        (fun z : K =>
          (countsP (ofNTree (expOf inp) tr).toMTree
            (ofNTree (expOf inp) tr).rootRow.lambda T C').eval z = 0)
      ∧ (Finset.univ.filter
            (fun z : K => (countsP_bin (ofNTree (expOf inp) tr).toMTree).eval z = 0)).card
          ≤ (countsP_bin (ofNTree (expOf inp) tr).toMTree).natDegree := by
  have hrnd : (readExps (ofNTree (expOf inp) tr).toMTree).Nodup :=
    readExps_nodup_of_ts inp.z _ hUReq
  have hvnd : (verifyExps (ofNTree (expOf inp) tr).toMTree).Nodup :=
    verifyExps_nodup_of_ts inp.z _ (verifyTs_nodup_of_uniqueRequest Ksz inp.z _ hUReq hmatch)
  have hsp : SeedPinned subj (ofNTree (expOf inp) tr).toMTree :=
    seedWalk_of_honestReconstruction hhr
      (fun e => readCount_le_one e _ hrnd) (fun e => verifyCount_le_one e _ hvnd)
  exact axis_lookups_valid_endToEnd_seedpinned_topo h2 inp Ksz mop mg subj tr hrvt hinp hshape hts
    hgate T C' hlam hT hC e hsp hUReq hmatch hused_r hused_v hbad

/-- β-free twin of `axis_lookups_valid_endToEnd_rvn` (`MemWalk.WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` in place of
    `MemWalk.WF` / `RVT Fmem` / `mem_stateSep`); the conclusion is the original's, verbatim. -/
theorem axis_lookups_valid_endToEnd_rvn_topo [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (inp : Inputs K) (Ksz : ℕ) (mop : MState → K) (mg : K)
    (tr : NTree (MState × DTmem K))
    (hrvt : RVT FmemTopo tr)
    (hinp : ∀ t', InTree tr t' → (NTree.label t').2.1 = inp)
    (hshape : ∀ t', InTree tr t' → fanoutMem (NTree.label t').1 = (NTree.children t').length)
    (hts : ∀ t', InTree tr t' → TsExists inp t')
    (hgate : ∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
        ex.eval (Reified.memoryEnvFull inp mop (ofNTree (expOf inp) tr).rootRow mg) = 0)
    (T C' : ℕ → K)
    (hlam : sameLambda (ofNTree (expOf inp) tr).rootRow.lambda (ofNTree (expOf inp) tr))
    (hT : readAxis T (ofNTree (expOf inp) tr))
    (hC : readCprime C' (ofNTree (expOf inp) tr))
    (e : ℕ)
    (hrvn : ReadVerifyNested (ofNTree (expOf inp) tr).toMTree)
    (hUReq : ((readExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k)).Nodup)
    (hmatch : IO.LmIO Ksz ((readExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k))
        ((verifyExps (ofNTree (expOf inp) tr).toMTree).map (fun k => inp.z ^ k)))
    (hused_r : e ∈ readExps (ofNTree (expOf inp) tr).toMTree)
    (hused_v : e ∈ verifyExps (ofNTree (expOf inp) tr).toMTree)
    (hbad : vaxis e (ofNTree (expOf inp) tr).toMTree ≠ Relaxis e (ofNTree (expOf inp) tr).toMTree) :
    inp.z ∈ Finset.univ.filter
        (fun z : K =>
          (countsP (ofNTree (expOf inp) tr).toMTree
            (ofNTree (expOf inp) tr).rootRow.lambda T C').eval z = 0)
      ∧ (Finset.univ.filter
            (fun z : K => (countsP_bin (ofNTree (expOf inp) tr).toMTree).eval z = 0)).card
          ≤ (countsP_bin (ofNTree (expOf inp) tr).toMTree).natDegree := by
  have hrnd : (readExps (ofNTree (expOf inp) tr).toMTree).Nodup :=
    readExps_nodup_of_ts inp.z _ hUReq
  have hvnd : (verifyExps (ofNTree (expOf inp) tr).toMTree).Nodup :=
    verifyExps_nodup_of_ts inp.z _ (verifyTs_nodup_of_uniqueRequest Ksz inp.z _ hUReq hmatch)
  have hsp : SeedPinned (canonNoun (ofNTree (expOf inp) tr).toMTree)
      (ofNTree (expOf inp) tr).toMTree :=
    seedWalk_of_readVerifyNested _ hrvn
      (fun e => readCount_le_one e _ hrnd) (fun e => verifyCount_le_one e _ hvnd)
  exact axis_lookups_valid_endToEnd_seedpinned_topo h2 inp Ksz mop mg _ tr hrvt hinp hshape hts
    hgate T C' hlam hT hC e hsp hUReq hmatch hused_r hused_v hbad

/-- β-free twin of `V_NockVMROM_forest_axisvalid_pinned_derived`.  Hypotheses verbatim; conjuncts (1)–(3) verbatim
    (`NockVM.V_NockVMROM_forest`, which reads `RAPmem` through `hRm` exactly as the original
    does); conjunct (4) is the original's with its forest antecedent `ForestReconGoal
    mem_stateSep_topo` (implied by the original's `ForestReconGoal mem_stateSep`,
    `forestReconGoal_topo_of_fmem`), so it implies the original's (4), and its axis-validity proof
    runs on `MemWalk.WFTopo` / `RVT FmemTopo`. -/
theorem V_NockVMROM_forest_axisvalid_pinned_derived_topo
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0)
    {p : ℕ} [CharP K p]
    {ncs : ℕ} (encc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K))
    (hEncc : Function.Injective encc)
    (lblc : ℕ → ComputeTable.State × ComputeTable.DTcomp K) (clabc : ℕ → ℕ → ComputeTable.State × ComputeTable.DTcomp K)
    (foc : ℕ → ℕ) {hc : ℕ} (harityc : ∀ i, foc i ≤ 3)
    (qc qinvc : ℕ → K) (hqc : Walk.QGate foc qc qinvc 1 hc) (hwrapc : 1 + hc * 3 < p)
    (hfoc : ∀ i, 1 ≤ i → i ≤ hc → foc i = (ComputeTable.comp_stateSep (K := K)).fanout (lblc i).1)
    (hRc : ∀ i, 1 ≤ i → i ≤ hc →
      (∃ ex, ComputeTable.RAPcomp (lblc i).2.1 (lblc i).2.2.1 (lblc i).2.2.2 ex)
        ∧ (lblc i).2.2.1.state = (lblc i).1
        ∧ (∀ j : Fin 3, (j : ℕ) < foc i ↔
            (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none)
        ∧ ComputeTable.childLinkComp (lblc i)
            (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none))
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
    (lmb : K) (Ksz : ℕ) (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz (NockVM.reqRecs lblc hc lmb).length)
    (hKresp : (NockVM.respRecs lblm hm).length ≤ Ksz)
    (hreqnd : (NockVM.reqRecs lblc hc lmb).Nodup) (hrespnd : (NockVM.respRecs lblm hm).Nodup) :
    (((NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) encc lblc clabc foc hc).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hc : ℚ) / (Fintype.card K : ℚ)
          + ((hc * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    ∧ (((NockVM.walkBadForest (mem_stateSep (K := K)) encm lblm clabm fom kroots_m hm).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hm : ℚ) / (Fintype.card K : ℚ)
          + ((hm * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    ∧ ((∃ (m : Fin (NockVM.respRecs lblm hm).length → ZMod p)
          (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests
              (NockVM.reqRecs lblc hc lmb).length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m)
              accM responses out_mem (NockVM.respRecs lblm hm).length
          ∧ requests = responses ∧ out_mem = 0)
        ↔ IO.LIO Ksz (NockVM.reqRecs lblc hc lmb) (NockVM.respRecs lblm hm))
    ∧ (IO.LIO Ksz (NockVM.reqRecs lblc hc lmb) (NockVM.respRecs lblm hm) →
        ∀ (inpM : Inputs K),
          (∀ i, 1 ≤ i → i ≤ hm → (lblm i).2.1 = inpM) →
          HonestVer lblm hm →
          (∀ v ∈ NockVM.reqRecs lblc hc lmb, ∃ e : ℕ, v 7 = inpM.z ^ e) →
          IO.LIO Ksz (NockVM.respRecs lblm hm) (verifyRecsMem lblm hm) →
          ForestReconGoal (mem_stateSep_topo (K := K)) lblm kroots_m hm →
          ∃ ts : List (NTree (MState × DTmem K)),
            ts.length = kroots_m
            ∧ (bfsForest ts).map NTree.label = (List.range' 1 hm).map lblm
            ∧ ∀ tree ∈ ts,
                -- the PRIMITIVE honest reconstruction: noun-shape (I) +
                -- slot-descendant existence (II).  REPLACES the count-laden `SeedPinned subj …`.
                ∀ (subj : Noun), HonestRecon subj (ofNTree (expOf inpM) tree).toMTree →
                ∀ (mop : MState → K) (mg : K),
                  (∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
                      ex.eval (Reified.memoryEnvFull inpM mop
                        (ofNTree (expOf inpM) tree).rootRow mg) = 0) →
                  ∀ (T C' : ℕ → K),
                    sameLambda (ofNTree (expOf inpM) tree).rootRow.lambda
                      (ofNTree (expOf inpM) tree) →
                    readAxis T (ofNTree (expOf inpM) tree) →
                    readCprime C' (ofNTree (expOf inpM) tree) →
                  ∀ e : ℕ,
                    ((readExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k)).Nodup →
                    IO.LmIO Ksz
                        ((readExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k))
                        ((verifyExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k)) →
                    e ∈ readExps (ofNTree (expOf inpM) tree).toMTree →
                    e ∈ verifyExps (ofNTree (expOf inpM) tree).toMTree →
                    vaxis e (ofNTree (expOf inpM) tree).toMTree
                        ≠ Relaxis e (ofNTree (expOf inpM) tree).toMTree →
                    inpM.z ∈ Finset.univ.filter
                        (fun z : K =>
                          (countsP (ofNTree (expOf inpM) tree).toMTree
                            (ofNTree (expOf inpM) tree).rootRow.lambda T C').eval z = 0)
                      ∧ (Finset.univ.filter
                          (fun z : K => (countsP_bin (ofNTree (expOf inpM) tree).toMTree).eval z = 0)).card
                          ≤ (countsP_bin (ofNTree (expOf inpM) tree).toMTree).natDegree) := by
  obtain ⟨h1, h2c, h3, h4⟩ :=
    V_NockVMROM_forest_axisvalid_seedpinned_topo h2 encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc
      hfoc hRc encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom hRm
      lmb Ksz hKp hKreq hKresp hreqnd hrespnd
  refine ⟨h1, h2c, h3, ?_⟩
  intro hLIO inpM hinpM hhon hReqTs hInterLIO hgoal
  obtain ⟨ts, hlen, hlab, hax⟩ := h4 hLIO inpM hinpM hhon hReqTs hInterLIO hgoal
  refine ⟨ts, hlen, hlab, ?_⟩
  intro tree htree subj hhr mop mg hgate T C' hlam hT hC e hUReq hmatch hur hv hbad
  -- DISCHARGE `SeedPinned` from the primitive `HonestRecon` (uniqueness from the `Nodup` timestamps)
  have hrnd : (readExps (ofNTree (expOf inpM) tree).toMTree).Nodup :=
    readExps_nodup_of_ts inpM.z _ hUReq
  have hvnd : (verifyExps (ofNTree (expOf inpM) tree).toMTree).Nodup :=
    verifyExps_nodup_of_ts inpM.z _ (verifyTs_nodup_of_uniqueRequest Ksz inpM.z _ hUReq hmatch)
  have hsp : SeedPinned subj (ofNTree (expOf inpM) tree).toMTree :=
    seedWalk_of_honestReconstruction hhr
      (fun e => readCount_le_one e _ hrnd) (fun e => verifyCount_le_one e _ hvnd)
  exact hax tree htree subj hsp mop mg hgate T C' hlam hT hC e hUReq hmatch hur hv hbad

/-- β-free twin of `V_NockVMROM_forest_axisvalid_rvn`.  Hypotheses verbatim; conjuncts (1)–(3) verbatim
    (`NockVM.V_NockVMROM_forest`, which reads `RAPmem` through `hRm` exactly as the original
    does); conjunct (4) is the original's with its forest antecedent `ForestReconGoal
    mem_stateSep_topo` (implied by the original's `ForestReconGoal mem_stateSep`,
    `forestReconGoal_topo_of_fmem`), so it implies the original's (4), and its axis-validity proof
    runs on `MemWalk.WFTopo` / `RVT FmemTopo`. -/
theorem V_NockVMROM_forest_axisvalid_rvn_topo
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0)
    {p : ℕ} [CharP K p]
    {ncs : ℕ} (encc : (ComputeTable.State × ComputeTable.DTcomp K) → (Fin ncs → K))
    (hEncc : Function.Injective encc)
    (lblc : ℕ → ComputeTable.State × ComputeTable.DTcomp K) (clabc : ℕ → ℕ → ComputeTable.State × ComputeTable.DTcomp K)
    (foc : ℕ → ℕ) {hc : ℕ} (harityc : ∀ i, foc i ≤ 3)
    (qc qinvc : ℕ → K) (hqc : Walk.QGate foc qc qinvc 1 hc) (hwrapc : 1 + hc * 3 < p)
    (hfoc : ∀ i, 1 ≤ i → i ≤ hc → foc i = (ComputeTable.comp_stateSep (K := K)).fanout (lblc i).1)
    (hRc : ∀ i, 1 ≤ i → i ≤ hc →
      (∃ ex, ComputeTable.RAPcomp (lblc i).2.1 (lblc i).2.2.1 (lblc i).2.2.2 ex)
        ∧ (lblc i).2.2.1.state = (lblc i).1
        ∧ (∀ j : Fin 3, (j : ℕ) < foc i ↔
            (if (j : ℕ) < foc i then some (clabc i (j + 1)) else none) ≠ none)
        ∧ ComputeTable.childLinkComp (lblc i)
            (fun j : Fin 3 => if (j : ℕ) < foc i then some (clabc i (j + 1)) else none))
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
    (lmb : K) (Ksz : ℕ) (hKp : Ksz < p)
    (hKreq : IO.InRange Ksz (NockVM.reqRecs lblc hc lmb).length)
    (hKresp : (NockVM.respRecs lblm hm).length ≤ Ksz)
    (hreqnd : (NockVM.reqRecs lblc hc lmb).Nodup) (hrespnd : (NockVM.respRecs lblm hm).Nodup) :
    (((NockVM.walkBad (ComputeTable.comp_stateSep (K := K)) encc lblc clabc foc hc).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hc : ℚ) / (Fintype.card K : ℚ)
          + ((hc * (ncs - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    ∧ (((NockVM.walkBadForest (mem_stateSep (K := K)) encm lblm clabm fom kroots_m hm).card : ℚ)
        / ((Fintype.card K : ℚ) * (Fintype.card K : ℚ))
      ≤ (hm : ℚ) / (Fintype.card K : ℚ)
          + ((hm * (nms - 1) : ℕ) : ℚ) / (Fintype.card K : ℚ))
    ∧ ((∃ (m : Fin (NockVM.respRecs lblm hm).length → ZMod p)
          (accP accM : ℕ → RatFunc (RatFunc K))
          (requests responses out_mem : RatFunc (RatFunc K)),
          (∀ j, m j ≠ 0)
          ∧ IO.ProgIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.reqRecs lblc hc lmb) i)) accP requests
              (NockVM.reqRecs lblc hc lmb).length
          ∧ IO.MemIOSat (fun i => SetEq.RLC (IO.listExt (NockVM.respRecs lblm hm) i)) (IO.castμ m)
              accM responses out_mem (NockVM.respRecs lblm hm).length
          ∧ requests = responses ∧ out_mem = 0)
        ↔ IO.LIO Ksz (NockVM.reqRecs lblc hc lmb) (NockVM.respRecs lblm hm))
    ∧ (IO.LIO Ksz (NockVM.reqRecs lblc hc lmb) (NockVM.respRecs lblm hm) →
        ∀ (inpM : Inputs K),
          (∀ i, 1 ≤ i → i ≤ hm → (lblm i).2.1 = inpM) →
          HonestVer lblm hm →
          (∀ v ∈ NockVM.reqRecs lblc hc lmb, ∃ e : ℕ, v 7 = inpM.z ^ e) →
          IO.LIO Ksz (NockVM.respRecs lblm hm) (verifyRecsMem lblm hm) →
          ForestReconGoal (mem_stateSep_topo (K := K)) lblm kroots_m hm →
          ∃ ts : List (NTree (MState × DTmem K)),
            ts.length = kroots_m
            ∧ (bfsForest ts).map NTree.label = (List.range' 1 hm).map lblm
            ∧ ∀ tree ∈ ts,
                -- the SOLE axis-soundness datum: the slot-descendant primitive (II).  No noun, no
                -- `SeedPinned`, no `Nested`.
                ReadVerifyNested (ofNTree (expOf inpM) tree).toMTree →
                ∀ (mop : MState → K) (mg : K),
                  (∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
                      ex.eval (Reified.memoryEnvFull inpM mop
                        (ofNTree (expOf inpM) tree).rootRow mg) = 0) →
                  ∀ (T C' : ℕ → K),
                    sameLambda (ofNTree (expOf inpM) tree).rootRow.lambda
                      (ofNTree (expOf inpM) tree) →
                    readAxis T (ofNTree (expOf inpM) tree) →
                    readCprime C' (ofNTree (expOf inpM) tree) →
                  ∀ e : ℕ,
                    ((readExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k)).Nodup →
                    IO.LmIO Ksz
                        ((readExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k))
                        ((verifyExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k)) →
                    e ∈ readExps (ofNTree (expOf inpM) tree).toMTree →
                    e ∈ verifyExps (ofNTree (expOf inpM) tree).toMTree →
                    vaxis e (ofNTree (expOf inpM) tree).toMTree
                        ≠ Relaxis e (ofNTree (expOf inpM) tree).toMTree →
                    inpM.z ∈ Finset.univ.filter
                        (fun z : K =>
                          (countsP (ofNTree (expOf inpM) tree).toMTree
                            (ofNTree (expOf inpM) tree).rootRow.lambda T C').eval z = 0)
                      ∧ (Finset.univ.filter
                          (fun z : K => (countsP_bin (ofNTree (expOf inpM) tree).toMTree).eval z = 0)).card
                          ≤ (countsP_bin (ofNTree (expOf inpM) tree).toMTree).natDegree) := by
  obtain ⟨h1, h2c, h3, h4⟩ :=
    V_NockVMROM_forest_axisvalid_seedpinned_topo h2 encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc
      hfoc hRc encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom hRm
      lmb Ksz hKp hKreq hKresp hreqnd hrespnd
  refine ⟨h1, h2c, h3, ?_⟩
  intro hLIO inpM hinpM hhon hReqTs hInterLIO hgoal
  obtain ⟨ts, hlen, hlab, hax⟩ := h4 hLIO inpM hinpM hhon hReqTs hInterLIO hgoal
  refine ⟨ts, hlen, hlab, ?_⟩
  intro tree htree hrvn mop mg hgate T C' hlam hT hC e hUReq hmatch hur hv hbad
  -- DISCHARGE `SeedPinned` from the descendant primitive ALONE (canonical noun; noun-shape free)
  have hrnd : (readExps (ofNTree (expOf inpM) tree).toMTree).Nodup :=
    readExps_nodup_of_ts inpM.z _ hUReq
  have hvnd : (verifyExps (ofNTree (expOf inpM) tree).toMTree).Nodup :=
    verifyExps_nodup_of_ts inpM.z _ (verifyTs_nodup_of_uniqueRequest Ksz inpM.z _ hUReq hmatch)
  have hsp : SeedPinned (canonNoun (ofNTree (expOf inpM) tree).toMTree)
      (ofNTree (expOf inpM) tree).toMTree :=
    seedWalk_of_readVerifyNested _ hrvn
      (fun e => readCount_le_one e _ hrnd) (fun e => verifyCount_le_one e _ hvnd)
  exact hax tree htree _ hsp mop mg hgate T C' hlam hT hC e hUReq hmatch hur hv hbad

/-- **Conjunct (4) of `V_NockVMROM_forest_axisvalid_topo`, standalone and β-free**: axis validity
threaded through a `ForestReconGoal mem_stateSep_topo` forest of the committed memory rows, with
none of the compute-chip / `hRm` hypotheses (those feed only conjuncts (1)–(3)). -/
theorem forest_axisvalid_topo
    [Fintype K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0)
    (lblc : ℕ → ComputeTable.State × ComputeTable.DTcomp K) (hc : ℕ)
    (lblm : ℕ → MState × DTmem K) {kroots_m hm : ℕ}
    (lmb : K) (Ksz : ℕ) :
    IO.LIO Ksz (NockVM.reqRecs lblc hc lmb) (NockVM.respRecs lblm hm) →
        ∀ (inpM : Inputs K),
          (∀ i, 1 ≤ i → i ≤ hm → (lblm i).2.1 = inpM) →
          -- Honest `ver = (st = read_root)`: responses are `ver`-selected.
          HonestVer lblm hm →
          -- compute-chip request timestamps in closed form `z^i`: the read/served
          -- half of `TsExists` is DISCHARGED from this + the IO matching via `respTs_closed_of_LIO`.
          (∀ v ∈ NockVM.reqRecs lblc hc lmb, ∃ e : ℕ, v 7 = inpM.z ^ e) →
          -- MATERIALIZED `intermediate` accumulator: the ordered read/verify record
          -- lists match (`read_root` ADDS `respRecs`, `verify_child` REMOVES `verifyRecsMem`; the
          -- LogUp balance of `MemoryTable.interChain_balance`, upgraded to a perfect matching by
          -- `Thm:IO_result`).
          IO.LIO Ksz (NockVM.respRecs lblm hm) (verifyRecsMem lblm hm) →
          ForestReconGoal (mem_stateSep_topo (K := K)) lblm kroots_m hm →
          ∃ ts : List (NTree (MState × DTmem K)),
            ts.length = kroots_m
            ∧ (bfsForest ts).map NTree.label = (List.range' 1 hm).map lblm
            ∧ ∀ tree ∈ ts,
                -- DISCHARGED (`countsP = 0`): the exported memory seed `.boundary` gate at the
                -- walk-root row, a REAL RAP gate — not a raw `counts = 0`.
                ∀ (mop : MState → K) (mg : K),
                  (∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
                      ex.eval (Reified.memoryEnvFull inpM mop
                        (ofNTree (expOf inpM) tree).rootRow mg) = 0) →
                  ∀ (T C' : ℕ → K),
                    sameLambda (ofNTree (expOf inpM) tree).rootRow.lambda
                      (ofNTree (expOf inpM) tree) →
                    readAxis T (ofNTree (expOf inpM) tree) →
                    readCprime C' (ofNTree (expOf inpM) tree) →
                  ∀ e : ℕ,
                    -- carried: well-nesting.
                    Nested e (ofNTree (expOf inpM) tree).toMTree →
                    -- DISCHARGED (both `Nodup`): from the paper's IO unique-request object `hUReq`
                    -- and the intermediate matching `hmatch` via `IO.cor_uni_req_uni_resp` — no raw read/verify `Nodup`.
                    ((readExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k)).Nodup →
                    IO.LmIO Ksz
                        ((readExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k))
                        ((verifyExps (ofNTree (expOf inpM) tree).toMTree).map (fun k => inpM.z ^ k)) →
                    e ∈ readExps (ofNTree (expOf inpM) tree).toMTree →
                    e ∈ verifyExps (ofNTree (expOf inpM) tree).toMTree →
                    vaxis e (ofNTree (expOf inpM) tree).toMTree
                        ≠ Relaxis e (ofNTree (expOf inpM) tree).toMTree →
                    inpM.z ∈ Finset.univ.filter
                        (fun z : K =>
                          (countsP (ofNTree (expOf inpM) tree).toMTree
                            (ofNTree (expOf inpM) tree).rootRow.lambda T C').eval z = 0)
                      ∧ (Finset.univ.filter
                          (fun z : K => (countsP_bin (ofNTree (expOf inpM) tree).toMTree).eval z = 0)).card
                          ≤ (countsP_bin (ofNTree (expOf inpM) tree).toMTree).natDegree := by
  -- fix `inpM` to the shared RAP inputs, and certify axis validity for every reconstructed tree.
  intro hLIO inpM hinpM hhon hReqTs hInterLIO hgoal
  obtain ⟨ts, hlen, hrvtall, hlab, hfan, _hleaf⟩ := hgoal
  refine ⟨ts, hlen, hlab, ?_⟩
  intro tree htree mop mg hgate T C' hlam hT hC e hnest hUReq hmatch hur hv hbad
  -- `RVT FmemTopo`, shared inputs, and `StateSep` fanout are all READ OUT of `ForestReconGoal`.
  have hrvt : RVT FmemTopo tree := hrvtall tree htree
  have hinp : ∀ t', InTree tree t' → (NTree.label t').2.1 = inpM := by
    intro t' ht'
    have hmem : t' ∈ bfsForest ts := (mem_bfsForest ts t').mpr ⟨tree, htree, ht'⟩
    have hlabmem : NTree.label t' ∈ (bfsForest ts).map NTree.label :=
      List.mem_map_of_mem hmem
    rw [hlab, List.mem_map] at hlabmem
    obtain ⟨i, hi, hival⟩ := hlabmem
    rw [List.mem_range'] at hi
    obtain ⟨kk, hkk, hik⟩ := hi
    rw [← hival]; exact hinpM i (by omega) (by omega)
  have hshape : ∀ t', InTree tree t' →
      fanoutMem (NTree.label t').1 = (NTree.children t').length := by
    intro t' ht'
    have hmem : t' ∈ bfsForest ts := (mem_bfsForest ts t').mpr ⟨tree, htree, ht'⟩
    exact hfan t' hmem
  -- FULL `TsExists` (read + VERIFY) DISCHARGED: read/served side from `hLIO` + `hReqTs`; VERIFY
  -- side from the materialized `intermediate` matching `hInterLIO`, no `hVerTs`.
  have htsE : ∀ t', InTree tree t' → TsExists inpM t' :=
    forest_tsExists_of_interLIO_topo lblc hc lblm hm inpM lmb Ksz hhon hLIO hReqTs hInterLIO ts hlab tree htree hrvt
  exact axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE_topo h2 inpM Ksz mop mg tree hrvt hinp
    hshape htsE hgate T C' hlam hT hC e hnest hUReq hmatch hur hv hbad


/-! ### Feeding the twins: production goal ⟹ β-free goal; the β-free bridge -/

/-- **The production forest goal implies the β-free one** (each tree's `RVT Fmem` becomes
`RVT FmemTopo` through the goal's own fanout binding, `rvtWithArity_topo_of_rvt_fmem`; labels,
fanout and leaf bindings carry over: `mem_stateSep_topo` and `mem_stateSep` share `fanout` and
`Sleaf`).  So every `V_…_topo` conjunct (4) implies its original's. -/
theorem forestReconGoal_topo_of_fmem {lblm : ℕ → MState × DTmem K} {kroots hm : ℕ}
    (h : ForestReconGoal (mem_stateSep (K := K)) lblm kroots hm) :
    ForestReconGoal (mem_stateSep_topo (K := K)) lblm kroots hm := by
  obtain ⟨ts, hlen, hrvt, hlab, hfan, hleaf⟩ := h
  refine ⟨ts, hlen, fun t ht => ?_, hlab, hfan, hleaf⟩
  refine (Nock.NockVMROM.Thm54.AxisBridgeLocalTopo.rvtWithArity_topo_of_rvt_fmem t (hrvt t ht)
    fun t' ht' => hfan t' ((mem_bfsForest ts t').mpr ⟨t, ht, ht'⟩)).1

section Bridge

open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.AxisBridgeLocalTopo

variable {F : Type} [Field F] [Algebra F K]

theorem axis_lookups_valid_endToEnd_perfect_defE_of_bridgeTopo
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (hb : ExactAxisBridgeLocalTopo cfg exec i) (h2 : (2 : K) ≠ 0)
    (hts : ∀ t', InTree (exec.memoryTreeAt i) t' → TsExists cfg.challenges.memoryInputs t')
    (hterm : countsP_bin
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree = 0)
    (e : ℕ)
    (hnest : Nested e (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree)
    (hrnd : (readExps
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree).Nodup)
    (hvnd : (verifyExps
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree).Nodup)
    (hused_r : e ∈ readExps
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree)
    (hused_v : e ∈ verifyExps
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree) :
    vaxis e (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree =
      Relaxis e (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree :=
  axis_lookups_valid_endToEnd_perfect_defE_topo h2 cfg.challenges.memoryInputs
    (exec.memoryTreeAt i) hb.rvt.1 hb.shared_inputs hb.fanout hts hterm e hnest hrnd hvnd
    hused_r hused_v

/-- **Fed by the β-free bridge**: the Schwartz–Zippel form
`axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE_topo` at `exec.memoryTreeAt i`. -/
theorem axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE_of_bridgeTopo [Fintype K]
    [DecidableEq K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg} {i : Fin cfg.kMem}
    (hb : ExactAxisBridgeLocalTopo cfg exec i) (h2 : (2 : K) ≠ 0) (Ksz : ℕ)
    (mop : MState → K) (mg : K)
    (hts : ∀ t', InTree (exec.memoryTreeAt i) t' → TsExists cfg.challenges.memoryInputs t')
    (hgate : ∀ ex ∈ Reified.Trans.memSeedBoundaryExprs,
        ex.eval (Reified.memoryEnvFull cfg.challenges.memoryInputs mop
          (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).rootRow mg) = 0)
    (T C' : ℕ → K)
    (hlam : sameLambda
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).rootRow.lambda
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)))
    (hT : readAxis T (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)))
    (hC : readCprime C' (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)))
    (e : ℕ)
    (hnest : Nested e (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree)
    (hUReq : ((readExps (ofNTree (expOf cfg.challenges.memoryInputs)
      (exec.memoryTreeAt i)).toMTree).map (fun k => cfg.challenges.memoryInputs.z ^ k)).Nodup)
    (hmatch : IO.LmIO Ksz
      ((readExps (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree).map
        (fun k => cfg.challenges.memoryInputs.z ^ k))
      ((verifyExps (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree).map
        (fun k => cfg.challenges.memoryInputs.z ^ k)))
    (hused_r : e ∈ readExps
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree)
    (hused_v : e ∈ verifyExps
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree)
    (hbad : vaxis e (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree ≠
      Relaxis e (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree) :
    cfg.challenges.memoryInputs.z ∈ Finset.univ.filter
        (fun z : K =>
          (countsP (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree
            (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).rootRow.lambda
              T C').eval z = 0)
      ∧ (Finset.univ.filter
            (fun z : K => (countsP_bin (ofNTree (expOf cfg.challenges.memoryInputs)
              (exec.memoryTreeAt i)).toMTree).eval z = 0)).card
          ≤ (countsP_bin (ofNTree (expOf cfg.challenges.memoryInputs)
              (exec.memoryTreeAt i)).toMTree).natDegree :=
  axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE_topo h2 cfg.challenges.memoryInputs Ksz
    mop mg (exec.memoryTreeAt i) hb.rvt.1 hb.shared_inputs hb.fanout hts hgate T C' hlam hT hC e
    hnest hUReq hmatch hused_r hused_v hbad

theorem axis_lookups_valid_endToEnd_perfect_defE_of_language [Fintype K] [DecidableEq K]
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hL : TraversableChainedSemanticExactLanguage cfg exec) (i : Fin cfg.kMem) (h2 : (2 : K) ≠ 0)
    (hts : ∀ t', InTree (exec.memoryTreeAt i) t' → TsExists cfg.challenges.memoryInputs t')
    (hterm : countsP_bin
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree = 0)
    (e : ℕ)
    (hnest : Nested e (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree)
    (hrnd : (readExps
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree).Nodup)
    (hvnd : (verifyExps
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree).Nodup)
    (hused_r : e ∈ readExps
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree)
    (hused_v : e ∈ verifyExps
      (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree) :
    vaxis e (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree =
      Relaxis e (ofNTree (expOf cfg.challenges.memoryInputs) (exec.memoryTreeAt i)).toMTree :=
  axis_lookups_valid_endToEnd_perfect_defE_of_bridgeTopo (hL.exactAxisBridgeLocalTopo i) h2 hts
    hterm e hnest hrnd hvnd hused_r hused_v

end Bridge

end AxisBridge
end Nock
