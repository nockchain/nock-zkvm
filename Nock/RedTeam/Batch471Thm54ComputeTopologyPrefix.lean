/-
  Nock/RedTeam/Batch471Thm54ComputeTopologyPrefix.lean

  **A. `ExecOfTraces.clabC` sets the child label's STATE to the parent's (`clabC_eq_childOfSlot`),
  while the walk's declared child vector `childVec` carries the HOSTED tag at coordinate `0`
  (`childVec_coord0`).  So `labelVecOfPub ∘ clabC` is NOT the chip's `chld'` vector
  (`clabC_vector_mismatch`: at hosted tag `tag(parent) + 1` they differ at coordinate `0`, in
  every field).  **Routed around, not fixed:** `Fcomp`'s child link (`childLinkComp`,
  `NockVM.lean`) reads only the child's `(s, f, e)` — the child state is the child ROW's own
  state, bound by that row's selector, not by `clabC` — so the reconstruction runs at the
  PROJECTED encoder `encSFE` (coordinates `1..9`, dropping the tag): `encSFE_clab`
  (`encSFE ∘ clabC` = projected `childVec`, any tags), `encSFE_label` (`encSFE` determines
  `sfeOf`), `respects_sfe` (`Fcomp` respects `sfeOf`), and `vecBFT_map` (the walk's `VecBFT`
  survives any coordinatewise projection).  `clabC` is unchanged; its one production consumer
  (`topologyOfTraces.compute.childPayload`) reads `(s, f, e)` only.

  **B. Step 3 on the prefix (generic, then deployed).**
  * `reconGoal_prefix_sfe`: for ANY decoded label column `lbl` and hosted tags, `PrefixBFT` of
    `(labelVecOfPub ∘ lbl, childVecN ∘ lbl)` in its tiling case + per-row `V_comp` on rows
    `1..k` ⟹ `Walk.ReconGoal comp_stateSep lbl k` at `k = prefixLen fo h`: rows `1..k` are
    the BFS of an `RVT^{Fcomp}` tree.  Rows beyond `k` are asked nothing.
  * `deployed_walkSat_lblC`: `Batch459::deployed_walkSat` restated at `ExecOfTraces.lblC` /
    `foC` for ALL indices (`rowOf` mirrors `lblC`'s clamp).
  * `deployed_prefixBFT`: at every `c` and every accepted trace, under
    `hic : computeWalkAlpha = alphaC c.1` (kept; unused after walk-α — `initial_count`
    is the coin) and `hseed : seedOfClaim c = α · cur 1` (the root binding — `Batch458`'s residual), outside
    `walkPrefixAlphaEvent` and `prefixBadGammas`: `PrefixBFT` — no tiling, no queue gate.
  * `deployed_reconGoal_prefix`: the composition — `ReconGoal comp_stateSep (lblC) k`.

  **C. `AcceptedContent.computeTopology` is
  `ComputeExactTopology (T.specializedExec …)`, and at `strategyOfTraces` that execution is
  built by `execOfTraces`, which needs `TracesWalkHyps` — WHOLE-table `Sf foC N + 1 = N` and
  `BFSValid foC N`.  On a proper prefix these are FALSE
  (`ExecOfTracesPrefix.not_tracesWalkHyps_of_prefix_lt`), so `strategyOfTraces` is not
  constructible and the conjunct is not even stated for such a trace.  The truncation
  constructor `ExecOfTracesPrefix.execOfTracesPrefix` exists (compute rows = prefix,
  `execOfTracesPrefix_computeRows`; conservative, `execOfTracesPrefix_rows_eq_of_hyps`), but its
  configuration has `compRows = k < N` (`cfgOfTracesPrefix_compRows_lt`), and the SAME
  `AcceptedContent` quantifies over all `compRows` rows in `vcomp`, `ln_chain`, `io`
  (`derivedRequestIO` of the BFS rows, while the chip's LogUp terminal `finalAccTerminal`
  sums requests over ALL `N` rows, garbage included).  The overflow branch of `PrefixBFT`
  (`prefixLen = N`, `1 + Sf foC N > N`: declared children beyond row `N` have the zero
  label vector) is a second, separate gap: `ExecOfTracesPrefix.sfPrefix_or_overflow`; whether
  `V_comp` excludes a zero child vector is not measured here.

  `openConjuncts` (live, `Batch398`): 10 names, UNMOVED; `Batch448.openConjunctsAfterVer`: 7
  names, UNMOVED; `computeTopology` stays on both.
-/
import Nock.WalkPrefix
import Nock.NockVMROM.Thm54.ExecOfTracesPrefix
import Nock.RedTeam.Batch459Thm54ComputeTopologyStop
import Nock.RedTeam.Batch448Thm54VerTransfer
import Nock.NockVMROM.Thm54.P8Core.Batch471Thm54ComputeTopologyPrefix
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch471

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.ExecOfTracesPrefix
open Nock.Framework
open MonolithicRAP

/-! ## A. `clabC` versus the hosted tag -/

section ClabC
variable {K : Type} [Field K]

theorem childVec_coord0 (pub : Pub K) (tags : Fin 3 → K) (j : Fin 3) :
    childVec pub tags j 0 = tags j := rfl

theorem labelVec_childOfSlot_coord0 (pub : Pub K) (j : Fin 3) :
    labelVecOfPub (childOfSlot pub j) 0 = stateTagField pub.state := rfl

/-- **The mismatch, compiled:** at hosted tag `tag(parent) + 1` the `clabC`-shaped label vector
and the walk's declared child vector differ (coordinate `0`), in every field. -/
theorem clabC_vector_mismatch (pub : Pub K) (j : Fin 3) :
    labelVecOfPub (childOfSlot pub j) ≠
      childVec pub (fun _ => stateTagField pub.state + 1) j := by
  intro h
  have := congrFun h 0
  rw [labelVec_childOfSlot_coord0, childVec_coord0] at this
  have h1 : (1 : K) = 0 := by linear_combination -this
  exact one_ne_zero h1

end ClabC

/-! ## B. `VecBFT` under projection and congruence -/

section VecMap
variable {K : Type*} [Field K] {n m : ℕ}

end VecMap

/-! ## C. Step 3 on the prefix, generic in the decoded label column -/

section Generic
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- **Step 3 at the prefix.**  From the walk's `PrefixBFT` (tiling case) and per-row `V_comp`
on rows `1..k` only, the rows `1..k` are the BFS of an `RVT^{Fcomp}` tree. -/
theorem reconGoal_prefix_sfe (lbl : ℕ → State × DTcomp K) (tags : ℕ → Fin 3 → K) {h : ℕ}
    (hpre : PrefixBFT (fun i => labelVecOfPub (lbl i).2.2.1)
      (fun i l => childVecN (lbl i).2.2.1 (tags i) (l - 1)) (fun i => fanoutComp (lbl i).1) h)
    (htile : Sf (fun i => fanoutComp (lbl i).1) (prefixLen (fun i => fanoutComp (lbl i).1) h) + 1
      = prefixLen (fun i => fanoutComp (lbl i).1) h)
    (hrow : ∀ i, 1 ≤ i → i ≤ prefixLen (fun i => fanoutComp (lbl i).1) h →
      (lbl i).2.2.1.state = (lbl i).1 ∧ Vcomp (lbl i).2.1 (lbl i).2.2.1 (lbl i).2.2.2) :
    ReconGoal (comp_stateSep (K := K)) lbl (prefixLen (fun i => fanoutComp (lbl i).1) h) := by
  set fo : ℕ → ℕ := fun i => fanoutComp (lbl i).1 with hfo_def
  obtain ⟨hv, hcase⟩ := hpre
  have hbft : VecBFT (fun i => labelVecOfPub (lbl i).2.2.1)
      (fun i l => childVecN (lbl i).2.2.1 (tags i) (l - 1)) fo (prefixLen fo h) := by
    rcases hcase with ⟨_, hb⟩ | ⟨hkh, hgt, _⟩
    · exact hb
    · exfalso; rw [hkh] at htile; omega
  have hproj := vecBFT_map sfeProj hbft
  have hb' : VecBFT (fun i => encSFE (lbl i)) (fun i l => encSFE (clabOf lbl i l)) fo
      (prefixLen fo h) := by
    refine vecBFT_congr_children (fun i l hl => ?_) hproj
    have hl3 : l < 3 := lt_of_lt_of_le hl ((comp_stateSep (K := K)).fanout_le _)
    show sfeProj (childVecN (lbl i).2.2.1 (tags i) (l + 1 - 1)) =
      sfeProj (labelVecOfPub (childOfSlot (lbl i).2.2.1 ⟨(l + 1 - 1) % 3, _⟩))
    have hl' : l + 1 - 1 = l := by omega
    have hm : (l + 1 - 1) % 3 = l := by rw [hl']; exact Nat.mod_eq_of_lt hl3
    have hfin : (⟨(l + 1 - 1) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = ⟨l, hl3⟩ :=
      Fin.ext hm
    rw [hfin, encSFE_clab (lbl i).2.2.1 (tags i) ⟨l, hl3⟩]
    congr 1
    rw [hl']
    exact childVecN_fin (lbl i).2.2.1 (tags i) ⟨l, hl3⟩
  have harity : ∀ i, fo i ≤ 3 := fun i => (comp_stateSep (K := K)).fanout_le _
  refine reconTree_ReconGoal_of_label (comp_stateSep (K := K)) sfeOf respects_sfe encSFE
    encSFE_label lbl (clabOf lbl) fo htile hv harity (fun i _ _ => rfl) ?_ hb'
  intro i hi1 hik
  obtain ⟨hst, hV⟩ := hrow i hi1 hik
  refine ⟨hst, hV, ?_, ?_⟩
  · intro j
    simp only [hfo_def]
    constructor
    · intro hj; simp [hj]
    · intro hne; by_contra hj; simp [hj] at hne
  · intro j hj
    simp only [hfo_def] at hj ⊢
    rw [if_pos hj]
    simp only [Option.map_some, clabOf, childOfSlot, sfeOf]
    have hm : ((j : ℕ) + 1 - 1) % 3 = j := by
      rw [show (j : ℕ) + 1 - 1 = j by omega]; exact Nat.mod_eq_of_lt j.isLt
    have hfin : (⟨((j : ℕ) + 1 - 1) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = j := Fin.ext hm
    rw [hfin]

end Generic

/-! ## D. At the deployed chip -/

section Deployed

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hsat
include hax hbasis hwidth

theorem deployed_prefixBFT
    (hic : P.optimized.family.computeWalkAlpha = alphaC c.1)
    (hseed : seedOfClaim P.optimized.verifier.raw.claim c =
      rlc (gamma c.1) (Vd P c Qc₀ 1) * alphaC c.1)
    (hα : alphaC c.1 ∉ walkPrefixAlphaEvent (fun i => rlc (gamma c.1) (Vd P c Qc₀ i))
      (fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsat i l)) (ExecOfTraces.foC P Qc₀ c) (rows P))
    (hγ : gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsat)
      (ExecOfTraces.foC P Qc₀ c) (rows P)) :
    PrefixBFT (Vd P c Qc₀) (Cvd P c Qc₀ hsat) (ExecOfTraces.foC P Qc₀ c) (rows P) := by
  let _ := hic
  have hw := deployed_walkSat_lblC P c Qc₀ hsat hax hbasis hwidth
  have hout : Batch459.accW P c (familyQc P c Qc₀) (rows P) = 0 :=
    Batch459.deployed_walk_out P c (familyQc P c Qc₀) hsat hax hbasis hwidth
  -- After walk-α (`OF`), WalkSat's `initial_count` is `alphaC` (the coin), so
  -- `hic : computeWalkAlpha = alphaC` is unused here; `initial_count = α` is `rfl`.
  rcases isFullBFT_or_mem_alphaEvent hw hseed (rfl : alphaC c.1 = alphaC c.1) hout with hbft | hmem
  · exact prefixBFT_of_isFullBFT _ _ _ P.optimized.family.problem.cfg.compRows_pos hγ hbft
  · exact absurd hmem hα

/-- **** the decoded rows `1..k` are the BFS of an
`RVT^{Fcomp}` tree, `k = prefixRows`.  Premises: `hic`, `hseed` (named, other lanes), the two
events, the prefix tiling `htile` (automatic on a proper prefix, `sfPrefix_of_lt`; the
overflow branch is `sfPrefix_or_overflow`), and per-row `V_comp` on the prefix rows. -/
theorem deployed_reconGoal_prefix
    (hic : P.optimized.family.computeWalkAlpha = alphaC c.1)
    (hseed : seedOfClaim P.optimized.verifier.raw.claim c =
      rlc (gamma c.1) (Vd P c Qc₀ 1) * alphaC c.1)
    (hα : alphaC c.1 ∉ walkPrefixAlphaEvent (fun i => rlc (gamma c.1) (Vd P c Qc₀ i))
      (fun i l => rlc (gamma c.1) (Cvd P c Qc₀ hsat i l)) (ExecOfTraces.foC P Qc₀ c) (rows P))
    (hγ : gamma c.1 ∉ prefixBadGammas (Vd P c Qc₀) (Cvd P c Qc₀ hsat)
      (ExecOfTraces.foC P Qc₀ c) (rows P))
    (htile : Sf (ExecOfTraces.foC P Qc₀ c) (prefixRows P Qc₀ c) + 1 = prefixRows P Qc₀ c)
    (hV : ∀ i, 1 ≤ i → i ≤ prefixRows P Qc₀ c →
      Vcomp (ExecOfTraces.lblC P Qc₀ c i).2.1 (ExecOfTraces.lblC P Qc₀ c i).2.2.1
        (ExecOfTraces.lblC P Qc₀ c i).2.2.2) :
    ReconGoal (comp_stateSep (K := K)) (ExecOfTraces.lblC P Qc₀ c) (prefixRows P Qc₀ c) := by
  have hpre := deployed_prefixBFT P c Qc₀ hsat hax hbasis hwidth hic hseed hα hγ
  exact reconGoal_prefix_sfe (ExecOfTraces.lblC P Qc₀ c)
    (fun i => Batch459.tagsAt P c (familyQc P c Qc₀) hsat (Batch459.rowOf P i)) hpre htile
    (fun i hi1 hik => ⟨lblC_state P c Qc₀ i, hV i hi1 hik⟩)

end Deployed

/-! ## E. -/

/-- Which `AcceptedContent` conjuncts quantify over the WHOLE compute table (all
`cfg.compRows` rows of `specializedExec`) and would change meaning under a prefix reading. -/
def wholeTableConjuncts : List (String × String) :=
  [("computeTopology", "ComputeExactTopology of execOfTraces: needs TracesWalkHyps (whole-table)"),
    ("computeRows", "ComputeRowsAccepted over all compRows BFS rows"),
    ("vcomp", "∀ i : Fin compRows"),
    ("ln_chain", "∀ i : Fin compRows, i + 1 < compRows"),
    ("io", "derivedRequestIO of the BFS rows vs the chip's all-row LogUp terminal")]

theorem wholeTableConjuncts_length : wholeTableConjuncts.length = 5 := by decide

def STEP4_STOP : String :=
  "computeTopology at a proper prefix needs specializedExec := execOfTracesPrefix (compRows = k)" ++
  " — an AcceptedContent meaning change that also moves io/vcomp/ln_chain; not edited"

def openConjunctsBefore : List String := Nock.RedTeam.Batch398.openConjuncts
def openConjunctsAfter : List String := Nock.RedTeam.Batch398.openConjuncts

theorem openConjuncts_unmoved : openConjunctsBefore = openConjunctsAfter := rfl

theorem openConjuncts_after_names :
    openConjunctsAfter =
      ["memoryRows", "vmem", "mem_first_counts", "mem_first_indicator",
        "io", "computeTopology", "memoryTopology", "axisStructural",
        "rootBoundary", "structuralChecks"] := by
  decide

theorem afterVer_names :
    Nock.RedTeam.Batch448.openConjunctsAfterVer =
      ["mem_first_counts", "mem_first_indicator",
        "computeTopology", "memoryTopology", "axisStructural",
        "rootBoundary", "structuralChecks"] := by
  decide

theorem computeTopology_still_open :
    "computeTopology" ∈ openConjunctsAfter ∧
      "computeTopology" ∈ Nock.RedTeam.Batch448.openConjunctsAfterVer := by
  decide

/-- Landed (compiled references). -/
def landed_clab_mismatch := @clabC_vector_mismatch
def landed_clab_route := @encSFE_clab
def landed_recon_generic := @reconGoal_prefix_sfe
def landed_deployed_prefix := @deployed_prefixBFT
def landed_deployed_recon := @deployed_reconGoal_prefix
noncomputable def landed_trunc := @execOfTracesPrefix
def landed_trunc_conservative := @execOfTracesPrefix_rows_eq_of_hyps
def landed_whole_false := @not_tracesWalkHyps_of_prefix_lt

end Nock.RedTeam.Batch471

#print axioms Nock.RedTeam.Batch471.clabC_vector_mismatch
#print axioms Nock.RedTeam.Batch471.encSFE_clab
#print axioms Nock.RedTeam.Batch471.respects_sfe
#print axioms Nock.RedTeam.Batch471.reconGoal_prefix_sfe
#print axioms Nock.RedTeam.Batch471.deployed_walkSat_lblC
#print axioms Nock.RedTeam.Batch471.deployed_prefixBFT
#print axioms Nock.RedTeam.Batch471.deployed_reconGoal_prefix
#print axioms Nock.NockVMROM.Thm54.ExecOfTracesPrefix.execOfTracesPrefix
#print axioms Nock.NockVMROM.Thm54.ExecOfTracesPrefix.not_tracesWalkHyps_of_prefix_lt
#print axioms Nock.NockVMROM.Thm54.ExecOfTracesPrefix.sfPrefix_or_overflow
