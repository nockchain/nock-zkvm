/-
  Nock/RedTeam/Batch797Thm54MemWalkTopo.lean

  * **(A) Production `WF` ⟹ `WFTopo`, and exactly `interV` separates them**
    (`MemWalk.WF.toTopo`, `MemWalk.WF_iff_topo`, restated as `wf_iff_topo_and_interV`).
  * **(B) The twins' conclusions are at least the originals'.**  `forestReconGoal_topo_of_fmem`
    (production forest goal ⟹ β-free goal) and `V_NockVMROM_forest_axisvalid_via_topo`: the
    ORIGINAL capstone's statement re-derived from its twin.
  * **(C) The bridge-twin note, confirmed by compiling and by a reach check.**  `PV` recorded,
    argued from grep, that no `interV` projection appears in `AxisBridge.lean` and that the
    `axis_lookups_valid_endToEnd*` / `V_NockVMROM_forest_axisvalid*` / `wf_memwalk_of_memAIR`
    family needs either `interV` per node or a β-free `WF`.  Measured here: (i) the whole family
    compiles on `WFTopo` / `RVT FmemTopo` / `mem_stateSep_topo` with the original conclusions
    (`AxisBridgeTopo`); (ii) proof-term reach (types and values, `allowOpaque := true`, `Nock.*`
    only) from every axis-validity twin and from the bridge-fed twins reaches NONE of
    `MemoryTable.interV`, `MemoryTable.Vmem`, `MemoryTable.pole`, `MemoryTable.Fmem`, and none
    reaches `MemoryTable.Inputs.β` except through the seed-gate hypothesis's environment
    `Reified.memoryEnvFull` (verbatim from the originals; its gate content is
    `rootPt.counts = 0 ∧ rootPt.indicator = 0`) — asserted at compile time (`run_cmd` throws
    otherwise; `memoryEnvFull` itself reaching `β` is checked as the stop's control); (iii) positive
    control, same instrument: the production originals `axis_lookups_valid_endToEnd`,
    `wf_memwalk_of_memAIR` and `V_NockVMROM_forest_axisvalid` DO reach `interV` and `Vmem`.
    The four `V_…_topo` capstone twins reach `interV` through conjuncts (1)–(3) only (their
    `hRm : RAPmem` premise, verbatim from the originals): reported, not asserted absent.
-/
import Lean
import Nock.NockVMROM.Thm54.AxisBridgeTopo

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.AxisBridge

open Polynomial
open MemoryTable
open AxisBatching AxisBatching.MTree
open scoped Classical
open Nock.Walk
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree (FmemTopo mem_stateSep_topo)
open MemWalk
open NockVM

/-- (A) `WF ↔ WFTopo ∧ interV at every row`. -/
theorem wf_iff_topo_and_interV {K : Type} [Field K] (inp : Inputs K) (w : MemWalk K) :
    WF inp w ↔ WFTopo inp w ∧ AllRows (interV inp) w :=
  WF_iff_topo inp w

/-- **The original capstone, re-derived from its β-free twin**: `V_NockVMROM_forest_axisvalid`'s
statement verbatim (at `K : Type`), proved from `V_NockVMROM_forest_axisvalid_topo` and
`forestReconGoal_topo_of_fmem`.  So the twin's conclusion is at least the original's. -/
theorem V_NockVMROM_forest_axisvalid_via_topo
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
          ForestReconGoal (mem_stateSep (K := K)) lblm kroots_m hm →
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
  obtain ⟨h1, h2c, h3, h4⟩ :=
    V_NockVMROM_forest_axisvalid_topo h2 encc hEncc lblc clabc foc harityc qc qinvc hqc hwrapc
      hfoc hRc encm hEncm lblm clabm fom hkm haritym qm qinvm hqm hwrapm hfom hRm
      lmb Ksz hKp hKreq hKresp hreqnd hrespnd
  exact ⟨h1, h2c, h3, fun hLIO inpM hinpM hhon hReqTs hInterLIO hgoal =>
    h4 hLIO inpM hinpM hhon hReqTs hInterLIO (forestReconGoal_topo_of_fmem hgoal)⟩

end Nock.AxisBridge

namespace Nock.RedTeam.Batch797

open Lean Elab Command

/-- Proof-term reach (types and values, `allowOpaque := true`), restricted to `Nock.*`; the
names in `stops` are recorded but not entered. -/
partial def reachStop (env : Environment) (roots : Array Name) (stops : Array Name) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut work := roots.toList
  while true do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      if seen.contains n then continue
      seen := seen.insert n
      if !(`Nock).isPrefixOf n then continue
      if stops.contains n then continue
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
        for c in cs do
          unless seen.contains c do work := c :: work
  return seen

/-- Full reach (no stops). -/
def reach (env : Environment) (roots : Array Name) : Std.HashSet Name := reachStop env roots #[]

/-- The β-dependent names: the `intermediate` clause, the verifier that carries it, its pole, the
per-node predicate that carries `Vmem`, and the `β` projection of the inputs. -/
def betaNames : Array Name := #[``Nock.MemoryTable.interV, ``Nock.MemoryTable.Vmem,
  ``Nock.MemoryTable.pole, ``Nock.MemoryTable.Fmem, ``Nock.MemoryTable.Inputs.β]

/-- The axis-validity twins (every end-to-end axis conclusion of the family, plus the bridge-fed
and standalone forms). -/
def twinRoots : Array Name := #[
  ``Nock.AxisBridge.MemWalk.indP_eval_topo,
  ``Nock.AxisBridge.MemWalk.countsP_eval_topo,
  ``Nock.AxisBridge.axis_lookups_valid_of_memtrace_topo,
  ``Nock.AxisBridge.axis_lookups_valid_perfect_of_memtrace_topo,
  ``Nock.AxisBridge.committed_axis_correct_of_memtrace_topo,
  ``Nock.AxisBridge.wfTopo_ofNTree,
  ``Nock.AxisBridge.wfTopo_memwalk_of_memAIR,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_topo,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_of_seedGate_topo,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_perfect_topo,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_uniqReq_topo,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_uniqReq_of_seedGate_topo,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_perfect_defE_topo,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE_topo,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_seedpinned_topo,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_honestRecon_topo,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_rvn_topo,
  ``Nock.AxisBridge.forest_axisvalid_topo,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_perfect_defE_of_bridgeTopo,
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE_of_bridgeTopo]

/-- The production originals (positive control). -/
def origRoots : Array Name := #[
  ``Nock.AxisBridge.axis_lookups_valid_endToEnd,
  ``Nock.AxisBridge.wf_memwalk_of_memAIR,
  ``Nock.AxisBridge.V_NockVMROM_forest_axisvalid]

/-- The capstone twins (conjuncts (1)–(3) verbatim; reported). -/
def capRoots : Array Name := #[
  ``Nock.AxisBridge.V_NockVMROM_forest_axisvalid_topo,
  ``Nock.AxisBridge.V_NockVMROM_forest_axisvalid_seedpinned_topo,
  ``Nock.AxisBridge.V_NockVMROM_forest_axisvalid_pinned_derived_topo,
  ``Nock.AxisBridge.V_NockVMROM_forest_axisvalid_rvn_topo]

run_cmd do
  let env ← getEnv
  -- (ii) every twin: no β-dependent name.  The seed-gate hypothesis `hgate` (verbatim from the
  -- originals) evaluates the seed boundary in `Reified.memoryEnvFull`, an environment that also
  -- carries the inputs' `β`; the gate's content is `rootPt.counts = 0 ∧ rootPt.indicator = 0`
  -- (`seedGate_gives_rootPt_zero`).  So the instrument runs twice: full reach must avoid the four
  -- `interV`-carrying names, and reach with `memoryEnvFull` as a leaf must avoid all five.
  let full := betaNames.filter (· != ``Nock.MemoryTable.Inputs.β)
  for r in twinRoots do
    let s := reach env #[r]
    for b in full do
      if s.contains b then throwError m!"{r} reaches {b}"
    let s' := reachStop env #[r] #[``Nock.Reified.memoryEnvFull]
    for b in betaNames do
      if s'.contains b then throwError m!"{r} reaches {b} outside the seed-gate environment"
    logInfo m!"{r}: reach {s.size}, no interV/Vmem/pole/Fmem; Inputs.β reached: {s.contains ``Nock.MemoryTable.Inputs.β} (outside memoryEnvFull: false)"
  -- the instrument sees `β` through `memoryEnvFull` (positive control for the stop)
  unless (reach env #[``Nock.Reified.memoryEnvFull]).contains ``Nock.MemoryTable.Inputs.β do
    throwError "positive control failed: memoryEnvFull does not reach Inputs.β"
  -- (iii) positive control: each original reaches `interV` and `Vmem`
  for r in origRoots do
    let s := reach env #[r]
    unless s.contains ``Nock.MemoryTable.interV ∧ s.contains ``Nock.MemoryTable.Vmem do
      throwError m!"positive control failed: {r} does not reach interV / Vmem"
    logInfo m!"{r} (original): reach {s.size}, reaches interV and Vmem"
  -- the four capstone twins: report (conjuncts (1)–(3) read `RAPmem` through `hRm`)
  for r in capRoots do
    let s := reach env #[r]
    logInfo m!"{r}: reach {s.size}, β names reached: {betaNames.filter s.contains}"

end Nock.RedTeam.Batch797

#print axioms Nock.AxisBridge.MemWalk.WF_iff_topo
#print axioms Nock.AxisBridge.forestReconGoal_topo_of_fmem
#print axioms Nock.AxisBridge.V_NockVMROM_forest_axisvalid_via_topo
#print axioms Nock.AxisBridge.wfTopo_memwalk_of_memAIR
#print axioms Nock.AxisBridge.axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE_topo
#print axioms Nock.AxisBridge.axis_lookups_valid_endToEnd_rvn_topo
#print axioms Nock.AxisBridge.forest_axisvalid_topo
#print axioms Nock.AxisBridge.V_NockVMROM_forest_axisvalid_topo
#print axioms Nock.AxisBridge.V_NockVMROM_forest_axisvalid_seedpinned_topo
#print axioms Nock.AxisBridge.V_NockVMROM_forest_axisvalid_pinned_derived_topo
#print axioms Nock.AxisBridge.V_NockVMROM_forest_axisvalid_rvn_topo
#print axioms Nock.AxisBridge.axis_lookups_valid_endToEnd_uniqReq_of_seedGate_defE_of_bridgeTopo
#print axioms Nock.AxisBridge.axis_lookups_valid_endToEnd_perfect_defE_of_language
