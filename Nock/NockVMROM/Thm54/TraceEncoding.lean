import Nock.NockVMROM.Thm54.Config
import Nock.NockVMROM.TraceEncoding

/-!
# Exact whole-trace encoding for the segmented Theorem 5.4 RAPs

This module connects the Lagrange trace assignments already used for the row-local compute and
memory RAPs to the exact orbit-prefix domains.  The same polynomial assignment is presented to
all four ordinary kind segments.  In particular, transition constraints read the next active
row through `envOfTrace.traceNext`; the final active point is not in the transition domain.
-/

namespace Nock.NockVMROM.Thm54

open Classical
open Nock.Framework Nock.Framework.Reify Nock.Framework.Thm54
open Nock.Reified
open scoped Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

set_option maxRecDepth 200000

/-! ## Generic orbit/Lagrange connectors -/

/-- The transition domain is exactly the set of active orbit nodes which have an active
successor.  This strengthens the one-sided membership lemmas in `OrbitDomain`. -/
theorem orbit_mem_transitionDomain_iff_active_nonterminal
    (D : OrbitDomain K) (n : ℕ) (hn : 0 < n) (hcap : n ≤ 2 ^ D.h) (x : K) :
    x ∈ D.transitionDomain n hn ↔
      ∃ i : Fin n, (i : ℕ) + 1 < n ∧ x = D.orbitPoint i := by
  constructor
  · intro hx
    have hrow := D.transitionDomain_subset_rowDomain n hn hx
    rw [OrbitDomain.rowDomain] at hrow
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hrow
    refine ⟨i, ?_, rfl⟩
    by_contra hi
    have hilast : i = D.lastIndex n hn := by
      apply Fin.ext
      simp only [OrbitDomain.lastIndex]
      omega
    exact D.terminalPoint_not_mem_transitionDomain n hn
      (by simpa [OrbitDomain.terminalPoint, hilast] using hx)
  · rintro ⟨i, hi, rfl⟩
    exact D.orbitPoint_mem_transitionDomain hn hcap i hi

/-- Evaluating an encoded trace at an active node returns the corresponding concrete current-row
column.  The statement is generic in the polynomial assignment and its interpolation equation. -/
theorem encodedTrace_current_at_activeOrbitNode
    {n w : ℕ} (D : OrbitDomain K) (P : Fin w → K[X]) (rows : Fin n → Env K)
    (nodes : Fin n → K) (_nodes_spec : ∀ i, nodes i = D.orbitPoint i)
    (heval : ∀ i j, (P j).eval (nodes i) = (rows i).trace j)
    (chalVal pubVal : ℕ → K) (i : Fin n) (j : ℕ) (hj : j < w) :
    (envOfTrace P D.ω (nodes i) chalVal pubVal).trace j = (rows i).trace j := by
  simp only [envOfTrace, dif_pos hj]
  exact heval i ⟨j, hj⟩

/-- At an active nonterminal node, `envOfTrace.traceNext` returns the corresponding column of the
next concrete row.  The proof uses the certified orbit adjacency and then interpolation at the
next active node. -/
theorem encodedTrace_next_at_activeOrbitNode
    {n w : ℕ} (D : OrbitDomain K) (P : Fin w → K[X]) (rows : Fin n → Env K)
    (nodes : Fin n → K) (nodes_spec : ∀ i, nodes i = D.orbitPoint i)
    (heval : ∀ i j, (P j).eval (nodes i) = (rows i).trace j)
    (chalVal pubVal : ℕ → K) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (j : ℕ) (hj : j < w) :
    (envOfTrace P D.ω (nodes i) chalVal pubVal).traceNext j =
      (rows ⟨(i : ℕ) + 1, hi⟩).trace j := by
  let next : Fin n := ⟨(i : ℕ) + 1, hi⟩
  rw [nodes_spec i]
  have hadj := D.orbit_gives_adjacency P (i : ℕ) chalVal pubVal
    (fun q => D.orbitPoint q) (fun _ => rfl) j hj
  rw [hadj]
  rw [← nodes_spec next]
  exact heval next ⟨j, hj⟩

/-- On every in-range current and next column, and on all challenge/public variables, the
environment produced at an active nonterminal node agrees with `twoRow cur next`.  This is the
generic variable-level connector consumed by the chained-expression specializations below. -/
theorem encodedTrace_transitionEnv_agrees_twoRow
    {n w : ℕ} (D : OrbitDomain K) (P : Fin w → K[X]) (rows : Fin n → Env K)
    (nodes : Fin n → K) (nodes_spec : ∀ i, nodes i = D.orbitPoint i)
    (heval : ∀ i j, (P j).eval (nodes i) = (rows i).trace j)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    let next : Fin n := ⟨(i : ℕ) + 1, hi⟩
    let encoded := envOfTrace P D.ω (nodes i) (rows i).chal (rows i).pub
    (∀ j, j < w → encoded.trace j = (Trans.twoRow (rows i) (rows next)).trace j) ∧
      (∀ j, j < w →
        encoded.traceNext j = (Trans.twoRow (rows i) (rows next)).traceNext j) ∧
      (∀ j, encoded.chal j = (Trans.twoRow (rows i) (rows next)).chal j) ∧
      (∀ j, encoded.pub j = (Trans.twoRow (rows i) (rows next)).pub j) := by
  dsimp only
  refine ⟨?_, ?_, fun _ => rfl, fun _ => rfl⟩
  · intro j hj
    simpa only [Trans.twoRow_trace] using
      encodedTrace_current_at_activeOrbitNode D P rows nodes nodes_spec heval
        (rows i).chal (rows i).pub i j hj
  · intro j hj
    simpa only [Trans.twoRow_traceNext] using
      encodedTrace_next_at_activeOrbitNode D P rows nodes nodes_spec heval
        (rows i).chal (rows i).pub i hi j hj

/-! ## Exact domains and node regressions -/

/-- The exact compute row domain is the image of the exact compute-node map. -/
theorem ExactConfig.computeRowDomain_eq_nodes (cfg : ExactConfig F K) :
    cfg.computeDomain .row = Finset.image cfg.compNodes Finset.univ := by
  classical
  ext x
  constructor
  · intro hx
    rw [ExactConfig.computeDomain, OrbitDomain.rowDomain] at hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, cfg.compNodes_eq_orbitPoint i⟩
  · intro hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [ExactConfig.computeDomain, OrbitDomain.rowDomain]
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, cfg.compNodes_eq_orbitPoint i |>.symm⟩

/-- The exact memory row domain is the image of the exact memory-node map. -/
theorem ExactConfig.memoryRowDomain_eq_nodes (cfg : ExactConfig F K) :
    cfg.memoryDomain .row = Finset.image cfg.memNodes Finset.univ := by
  classical
  ext x
  constructor
  · intro hx
    rw [ExactConfig.memoryDomain, OrbitDomain.rowDomain] at hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, cfg.memNodes_eq_orbitPoint i⟩
  · intro hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [ExactConfig.memoryDomain, OrbitDomain.rowDomain]
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, cfg.memNodes_eq_orbitPoint i |>.symm⟩

/-- Exact characterization of the compute transition domain by active nonterminal compute nodes. -/
theorem ExactConfig.mem_computeTransitionDomain_iff
    (cfg : ExactConfig F K) (x : K) :
    x ∈ cfg.computeDomain .transition ↔
      ∃ i : Fin cfg.compRows, (i : ℕ) + 1 < cfg.compRows ∧ x = cfg.compNodes i := by
  rw [ExactConfig.computeDomain,
    orbit_mem_transitionDomain_iff_active_nonterminal
      cfg.orbit
      cfg.compRows cfg.compRows_pos cfg.compRows_le]
  constructor <;> rintro ⟨i, hi, hxi⟩
  · exact ⟨i, hi, hxi.trans (cfg.compNodes_eq_orbitPoint i).symm⟩
  · exact ⟨i, hi, hxi.trans (cfg.compNodes_eq_orbitPoint i)⟩

/-- Exact characterization of the memory transition domain by active nonterminal memory nodes. -/
theorem ExactConfig.mem_memoryTransitionDomain_iff
    (cfg : ExactConfig F K) (x : K) :
    x ∈ cfg.memoryDomain .transition ↔
      ∃ i : Fin cfg.memRows, (i : ℕ) + 1 < cfg.memRows ∧ x = cfg.memNodes i := by
  rw [ExactConfig.memoryDomain,
    orbit_mem_transitionDomain_iff_active_nonterminal
      cfg.orbit
      cfg.memRows cfg.memRows_pos cfg.memRows_le]
  constructor <;> rintro ⟨i, hi, hxi⟩
  · exact ⟨i, hi, hxi.trans (cfg.memNodes_eq_orbitPoint i).symm⟩
  · exact ⟨i, hi, hxi.trans (cfg.memNodes_eq_orbitPoint i)⟩

/-- The last compute point cannot be a transition point (no cyclic wrap constraint). -/
theorem ExactConfig.computeTransition_excludes_last (cfg : ExactConfig F K) :
    cfg.orbit.terminalPoint cfg.compRows cfg.compRows_pos ∉
      cfg.computeDomain .transition := by
  exact cfg.orbit.terminalPoint_not_mem_transitionDomain cfg.compRows cfg.compRows_pos

/-- The last memory point cannot be a transition point (no cyclic wrap constraint). -/
theorem ExactConfig.memoryTransition_excludes_last (cfg : ExactConfig F K) :
    cfg.orbit.terminalPoint cfg.memRows cfg.memRows_pos ∉
      cfg.memoryDomain .transition := by
  exact cfg.orbit.terminalPoint_not_mem_transitionDomain cfg.memRows cfg.memRows_pos

/-- A positive exact orbit cannot use `ω = 1`: its certified order is at least two. -/
theorem ExactConfig.orbit_omega_ne_one (cfg : ExactConfig F K) :
    cfg.orbit.ω ≠ 1 := by
  intro hω
  have hord := cfg.orbit.order_ω
  rw [hω, orderOf_one] at hord
  have hpow : 2 ≤ 2 ^ cfg.orbit.h := by
    simpa using (pow_le_pow_right' (a := 2) (by omega) cfg.orbit_h_pos)
  omega

/-- A node map different from the exact compute map cannot satisfy the orbit-node equations. -/
theorem ExactConfig.wrong_computeNodeMap_rejected (cfg : ExactConfig F K)
    (nodes : Fin cfg.compRows → K) (hne : nodes ≠ cfg.compNodes) :
    ¬ (∀ i, nodes i = cfg.orbit.orbitPoint i) := by
  intro h
  exact hne (cfg.compNodes_determined nodes h)

/-- A node map different from the exact memory map cannot satisfy the orbit-node equations. -/
theorem ExactConfig.wrong_memoryNodeMap_rejected (cfg : ExactConfig F K)
    (nodes : Fin cfg.memRows → K) (hne : nodes ≠ cfg.memNodes) :
    ¬ (∀ i, nodes i = cfg.orbit.orbitPoint i) := by
  intro h
  exact hne (cfg.memNodes_determined nodes h)

/-! ## The four exact ordinary-RAP families -/

/-- Satisfaction of all four exact ordinary compute RAP segments by one shared trace assignment. -/
def ComputeSegmentedRAPSatisfies (cfg : ExactConfig F K)
    (P : Fin Trans.computeAIRchained.numTraceCols → K[X]) : Prop :=
  ∀ kind : ConstraintKind,
    (airToRAP (kindSeg Trans.computeAIRchained kind)
      cfg.challenges.computeValuation (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (cfg.computeDomain kind) cfg.orbit.βcoset_ne_zero cfg.orbit_h_pos).Satisfies P

/-- Satisfaction of all four exact ordinary memory RAP segments by one shared trace assignment.
    `lmb` is the form R accounting base (AIR chal 8); it is the table-constant `Pub.lambda`. -/
def MemorySegmentedRAPSatisfies (cfg : ExactConfig F K) (lmb : K)
    (P : Fin (Trans.memoryAIRchained (K := K)).numTraceCols → K[X]) : Prop :=
  ∀ kind : ConstraintKind,
    (airToRAP (kindSeg (Trans.memoryAIRchained (K := K)) kind)
      (cfg.challenges.memoryChalVal lmb) (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (cfg.memoryDomain kind) cfg.orbit.βcoset_ne_zero cfg.orbit_h_pos).Satisfies P

/-! ## Chained-expression evaluation on the encoded trace -/

/-- The compute transition expression sees exactly `twoRow cur next` on an active adjacent pair. -/
theorem computeChainExpr_encoded_eq_twoRow (cfg : ExactConfig F K)
    (pub : Fin cfg.compRows → ComputeTable.Pub K)
    (dec : Fin cfg.compRows → ComputeTable.Dec K)
    (ex : Fin cfg.compRows → ComputeTable.Extra K)
    (i : Fin cfg.compRows) (hi : (i : ℕ) + 1 < cfg.compRows) :
    let rows := fun k => computeEnvFull cfg.challenges.computeInputs
      (ComputeTable.opSel (pub k).state) (pub k) (dec k) (ex k)
    Trans.lnChainExpr.eval
        (envOfTrace (encodeComputeTrace rows cfg.compNodes)
          cfg.orbit.ω (cfg.compNodes i) cfg.challenges.computeValuation (fun _ => 0))
      =
    Trans.lnChainExpr.eval (Trans.twoRow (rows i) (rows ⟨(i : ℕ) + 1, hi⟩)) := by
  dsimp only
  simp only [Trans.lnChainExpr, tc, Trans.tn, Expr.eval,
    Trans.twoRow_trace, Trans.twoRow_traceNext]
  rw [encodedTrace_current_at_activeOrbitNode cfg.orbit
      (encodeComputeTrace
        (fun k => computeEnvFull cfg.challenges.computeInputs
          (ComputeTable.opSel (pub k).state) (pub k) (dec k) (ex k)) cfg.compNodes)
      (fun k => computeEnvFull cfg.challenges.computeInputs
        (ComputeTable.opSel (pub k).state) (pub k) (dec k) (ex k))
      cfg.compNodes cfg.compNodes_eq_orbitPoint
      (fun k j => encodeComputeTrace_eval_at_node
        (fun q => computeEnvFull cfg.challenges.computeInputs
          (ComputeTable.opSel (pub q).state) (pub q) (dec q) (ex q))
        cfg.compNodes cfg.compNodes_injective k j)
      cfg.challenges.computeValuation (fun _ => 0) i 66 (by norm_num [computeAIR_numTraceCols])]
  rw [encodedTrace_next_at_activeOrbitNode cfg.orbit
      (encodeComputeTrace
        (fun k => computeEnvFull cfg.challenges.computeInputs
          (ComputeTable.opSel (pub k).state) (pub k) (dec k) (ex k)) cfg.compNodes)
      (fun k => computeEnvFull cfg.challenges.computeInputs
        (ComputeTable.opSel (pub k).state) (pub k) (dec k) (ex k))
      cfg.compNodes cfg.compNodes_eq_orbitPoint
      (fun k j => encodeComputeTrace_eval_at_node
        (fun q => computeEnvFull cfg.challenges.computeInputs
          (ComputeTable.opSel (pub q).state) (pub q) (dec q) (ex q))
        cfg.compNodes cfg.compNodes_injective k j)
      cfg.challenges.computeValuation (fun _ => 0) i hi 65
      (by norm_num [computeAIR_numTraceCols])]

/-- The memory transition expression sees exactly `twoRow cur next` on an active adjacent pair. -/
theorem memoryChainExpr_encoded_eq_twoRow (cfg : ExactConfig F K)
    (mrow : Fin cfg.memRows → MemoryTable.Pub K) (g : Fin cfg.memRows → K)
    (i : Fin cfg.memRows) (hi : (i : ℕ) + 1 < cfg.memRows) :
    let rows := fun k => memoryEnvFull cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow k).st) (mrow k) (g k)
    Trans.icurChainExpr.eval
        (envOfTrace (encodeMemoryTrace rows cfg.memNodes)
          cfg.orbit.ω (cfg.memNodes i) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0))
      =
    Trans.icurChainExpr.eval (Trans.twoRow (rows i) (rows ⟨(i : ℕ) + 1, hi⟩)) := by
  dsimp only
  simp only [Trans.icurChainExpr, tc, Trans.tn, Expr.eval,
    Trans.twoRow_trace, Trans.twoRow_traceNext]
  rw [encodedTrace_current_at_activeOrbitNode cfg.orbit
      (encodeMemoryTrace
        (fun k => memoryEnvFull cfg.challenges.memoryInputs
          (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) cfg.memNodes)
      (fun k => memoryEnvFull cfg.challenges.memoryInputs
        (MemoryTable.opSel (mrow k).st) (mrow k) (g k))
      cfg.memNodes cfg.memNodes_eq_orbitPoint
      (fun k j => encodeMemoryTrace_eval_at_node
        (fun q => memoryEnvFull cfg.challenges.memoryInputs
          (MemoryTable.opSel (mrow q).st) (mrow q) (g q))
        cfg.memNodes cfg.memNodes_injective k j)
      (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0) i 32
      (by norm_num [memoryAIR_numTraceCols])]
  rw [encodedTrace_next_at_activeOrbitNode cfg.orbit
      (encodeMemoryTrace
        (fun k => memoryEnvFull cfg.challenges.memoryInputs
          (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) cfg.memNodes)
      (fun k => memoryEnvFull cfg.challenges.memoryInputs
        (MemoryTable.opSel (mrow k).st) (mrow k) (g k))
      cfg.memNodes cfg.memNodes_eq_orbitPoint
      (fun k j => encodeMemoryTrace_eval_at_node
        (fun q => memoryEnvFull cfg.challenges.memoryInputs
          (MemoryTable.opSel (mrow q).st) (mrow q) (g q))
        cfg.memNodes cfg.memNodes_injective k j)
      (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0) i hi 31
      (by norm_num [memoryAIR_numTraceCols])]

/-! ## Individual exact segment characterizations -/

/-- The compute row segment is the shipped 526-row-gate RAP over the exact row-node image. -/
theorem computeRowSegment_iff (cfg : ExactConfig F K)
    (P : Fin computeAIR.numTraceCols → K[X]) :
    (airToRAP (kindSeg Trans.computeAIRchained .row)
      cfg.challenges.computeValuation (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (cfg.computeDomain .row) cfg.orbit.βcoset_ne_zero
      cfg.orbit_h_pos).Satisfies P
      ↔
    (airToRAP computeAIR
      cfg.challenges.computeValuation (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (Finset.image cfg.compNodes Finset.univ) cfg.orbit.βcoset_ne_zero
      cfg.orbit_h_pos).Satisfies P := by
  erw [airToRAP_satisfies_iff, airToRAP_satisfies_iff]
  rw [comp_row_seg_is_computeAIR, cfg.computeRowDomain_eq_nodes]
  rfl

/-- The exact compute transition RAP is precisely adjacent line-nonce handoff. -/
theorem computeTransitionSegment_iff (cfg : ExactConfig F K)
    (pub : Fin cfg.compRows → ComputeTable.Pub K)
    (dec : Fin cfg.compRows → ComputeTable.Dec K)
    (ex : Fin cfg.compRows → ComputeTable.Extra K) :
    let rows := fun k => computeEnvFull cfg.challenges.computeInputs
      (ComputeTable.opSel (pub k).state) (pub k) (dec k) (ex k)
    (airToRAP (kindSeg Trans.computeAIRchained .transition)
      cfg.challenges.computeValuation (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (cfg.computeDomain .transition) cfg.orbit.βcoset_ne_zero
      cfg.orbit_h_pos).Satisfies (encodeComputeTrace rows cfg.compNodes)
      ↔ ∀ i : Fin cfg.compRows, ∀ hi : (i : ℕ) + 1 < cfg.compRows,
          (pub i).ln = (pub ⟨(i : ℕ) + 1, hi⟩).ln_prev := by
  dsimp only
  erw [airToRAP_satisfies_iff]
  constructor
  · intro h i hi
    have hx : cfg.compNodes i ∈ cfg.computeDomain .transition :=
      (cfg.mem_computeTransitionDomain_iff (cfg.compNodes i)).2 ⟨i, hi, rfl⟩
    have hzero := h (cfg.compNodes i) hx
      ⟨.transition, Trans.lnChainExpr⟩
        (by simp only [comp_trans_seg, List.mem_singleton])
    change Trans.lnChainExpr.eval
      (envOfTrace
        (encodeComputeTrace
          (fun k => computeEnvFull cfg.challenges.computeInputs
            (ComputeTable.opSel (pub k).state) (pub k) (dec k) (ex k))
          cfg.compNodes)
        cfg.orbit.ω (cfg.compNodes i) cfg.challenges.computeValuation (fun _ => 0)) = 0 at hzero
    rw [computeChainExpr_encoded_eq_twoRow cfg pub dec ex i hi] at hzero
    exact (Trans.reified_ln_chain_sound
      cfg.challenges.computeInputs cfg.challenges.computeInputs
      (ComputeTable.opSel (pub i).state)
      (ComputeTable.opSel (pub ⟨(i : ℕ) + 1, hi⟩).state)
      (pub i) (pub ⟨(i : ℕ) + 1, hi⟩)
      (dec i) (dec ⟨(i : ℕ) + 1, hi⟩)
      (ex i) (ex ⟨(i : ℕ) + 1, hi⟩)).mp hzero
  · intro h x hx c hc
    obtain ⟨i, hi, rfl⟩ := (cfg.mem_computeTransitionDomain_iff x).1 hx
    have hc' : c = ⟨.transition, Trans.lnChainExpr⟩ := by
      simpa only [comp_trans_seg, List.mem_singleton] using hc
    subst c
    change Trans.lnChainExpr.eval
      (envOfTrace
        (encodeComputeTrace
          (fun k => computeEnvFull cfg.challenges.computeInputs
            (ComputeTable.opSel (pub k).state) (pub k) (dec k) (ex k))
          cfg.compNodes)
        cfg.orbit.ω (cfg.compNodes i) cfg.challenges.computeValuation (fun _ => 0)) = 0
    rw [computeChainExpr_encoded_eq_twoRow cfg pub dec ex i hi]
    exact (Trans.reified_ln_chain_sound
      cfg.challenges.computeInputs cfg.challenges.computeInputs
      (ComputeTable.opSel (pub i).state)
      (ComputeTable.opSel (pub ⟨(i : ℕ) + 1, hi⟩).state)
      (pub i) (pub ⟨(i : ℕ) + 1, hi⟩)
      (dec i) (dec ⟨(i : ℕ) + 1, hi⟩)
      (ex i) (ex ⟨(i : ℕ) + 1, hi⟩)).mpr (h i hi)

/-- Compute boundary constraints are literally absent, so the exact boundary RAP is satisfied by
every trace assignment. -/
theorem computeBoundarySegment_satisfies (cfg : ExactConfig F K)
    (P : Fin Trans.computeAIRchained.numTraceCols → K[X]) :
    (airToRAP (kindSeg Trans.computeAIRchained .boundary)
      cfg.challenges.computeValuation (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (cfg.computeDomain .boundary) cfg.orbit.βcoset_ne_zero
      cfg.orbit_h_pos).Satisfies P := by
  erw [airToRAP_satisfies_iff]
  intro x hx c hc
  have hempty := comp_boundary_terminal_segs_empty
  rw [hempty.1] at hc
  simp at hc

/-- Compute terminal constraints are literally absent, so the exact terminal RAP is satisfied by
every trace assignment. -/
theorem computeTerminalSegment_satisfies (cfg : ExactConfig F K)
    (P : Fin Trans.computeAIRchained.numTraceCols → K[X]) :
    (airToRAP (kindSeg Trans.computeAIRchained .terminal)
      cfg.challenges.computeValuation (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (cfg.computeDomain .terminal) cfg.orbit.βcoset_ne_zero
      cfg.orbit_h_pos).Satisfies P := by
  erw [airToRAP_satisfies_iff]
  intro x hx c hc
  have hempty := comp_boundary_terminal_segs_empty
  rw [hempty.2] at hc
  simp at hc

/-! The memory endpoint segments are proved below together with the whole-trace theorem. -/

/-! ## Whole compute trace -/

/-- **P3 option-E whole compute trace.**  The existential chooses auxiliary columns once; the
resulting one Lagrange polynomial assignment is then used unchanged by all four exact ordinary
kind RAPs. -/
theorem computeSegmentedRAP_wholeTrace_iff (cfg : ExactConfig F K)
    (pub : Fin cfg.compRows → ComputeTable.Pub K)
    (dec : Fin cfg.compRows → ComputeTable.Dec K)
    (hwf : ∀ i, ComputeTable.WF cfg.challenges.computeInputs (pub i))
    (hz : cfg.challenges.z ≠ 0) :
    (∃ ex : Fin cfg.compRows → ComputeTable.Extra K,
      ComputeSegmentedRAPSatisfies cfg
        (encodeComputeTrace
          (fun i => computeEnvFull cfg.challenges.computeInputs
            (ComputeTable.opSel (pub i).state) (pub i) (dec i) (ex i))
          cfg.compNodes))
      ↔
    ((∀ i, ComputeTable.Vcomp cfg.challenges.computeInputs (pub i) (dec i)) ∧
      ∀ i : Fin cfg.compRows, ∀ hi : (i : ℕ) + 1 < cfg.compRows,
        (pub i).ln = (pub ⟨(i : ℕ) + 1, hi⟩).ln_prev) := by
  let rowIff := computeTable_reified_iff
    (fun _ : Fin cfg.compRows => cfg.challenges.computeInputs) pub dec
    cfg.compNodes cfg.compNodes_injective cfg.challenges.computeValuation
    cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
    cfg.orbit.βcoset_ne_zero cfg.orbit_h_pos
    (fun _ => rfl) hwf (fun _ => hz)
  constructor
  · rintro ⟨ex, hseg⟩
    refine ⟨?_, (computeTransitionSegment_iff cfg pub dec ex).mp (hseg .transition)⟩
    apply rowIff.mpr
    refine ⟨ex, ?_⟩
    exact (computeRowSegment_iff cfg _).mp (hseg .row)
  · rintro ⟨hrows, hchain⟩
    obtain ⟨ex, hrow⟩ := rowIff.mp hrows
    refine ⟨ex, ?_⟩
    intro kind
    cases kind with
    | row =>
        exact (computeRowSegment_iff cfg _).mpr hrow
    | transition =>
        exact (computeTransitionSegment_iff cfg pub dec ex).mpr hchain
    | boundary =>
        exact computeBoundarySegment_satisfies cfg _
    | terminal =>
        exact computeTerminalSegment_satisfies cfg _

/-! ## Memory segments and whole memory trace -/

/-- The memory row segment is the shipped 75-row-gate RAP over the exact row-node image. -/
theorem memoryRowSegment_iff (cfg : ExactConfig F K)
    (mrow : Fin cfg.memRows → MemoryTable.Pub K)
    (P : Fin (memoryAIR (K := K)).numTraceCols → K[X]) :
    (airToRAP (kindSeg (Trans.memoryAIRchained (K := K)) .row)
      (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (cfg.memoryDomain .row) cfg.orbit.βcoset_ne_zero
      cfg.orbit_h_pos).Satisfies P
      ↔
    (airToRAP (memoryAIR (K := K))
      (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (Finset.image cfg.memNodes Finset.univ) cfg.orbit.βcoset_ne_zero
      cfg.orbit_h_pos).Satisfies P := by
  erw [airToRAP_satisfies_iff, airToRAP_satisfies_iff]
  rw [mem_row_seg_is_memoryAIR, cfg.memoryRowDomain_eq_nodes]
  rfl

/-- Current-column evaluation for the exact encoded memory trace at any active memory node. -/
theorem memoryEncodedTrace_current (cfg : ExactConfig F K)
    (mrow : Fin cfg.memRows → MemoryTable.Pub K) (g : Fin cfg.memRows → K)
    (i : Fin cfg.memRows) (j : ℕ) (hj : j < (memoryAIR (K := K)).numTraceCols) :
    let rows := fun k => memoryEnvFull cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow k).st) (mrow k) (g k)
    (envOfTrace (encodeMemoryTrace rows cfg.memNodes)
      cfg.orbit.ω (cfg.memNodes i) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0)).trace j
      = (rows i).trace j := by
  dsimp only
  exact encodedTrace_current_at_activeOrbitNode cfg.orbit
    (encodeMemoryTrace
      (fun k => memoryEnvFull cfg.challenges.memoryInputs
        (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) cfg.memNodes)
    (fun k => memoryEnvFull cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow k).st) (mrow k) (g k))
    cfg.memNodes cfg.memNodes_eq_orbitPoint
    (fun k q => encodeMemoryTrace_eval_at_node
      (fun t => memoryEnvFull cfg.challenges.memoryInputs
        (MemoryTable.opSel (mrow t).st) (mrow t) (g t))
      cfg.memNodes cfg.memNodes_injective k q)
    (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0) i j hj

/-- The exact memory transition RAP is precisely adjacent `icur = next.ipre` handoff. -/
theorem memoryTransitionSegment_iff (cfg : ExactConfig F K)
    (mrow : Fin cfg.memRows → MemoryTable.Pub K) (g : Fin cfg.memRows → K) :
    let rows := fun k => memoryEnvFull cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow k).st) (mrow k) (g k)
    (airToRAP (kindSeg (Trans.memoryAIRchained (K := K)) .transition)
      (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (cfg.memoryDomain .transition) cfg.orbit.βcoset_ne_zero
      cfg.orbit_h_pos).Satisfies (encodeMemoryTrace rows cfg.memNodes)
      ↔ ∀ i : Fin cfg.memRows, ∀ hi : (i : ℕ) + 1 < cfg.memRows,
          (mrow i).icur = (mrow ⟨(i : ℕ) + 1, hi⟩).ipre := by
  dsimp only
  erw [airToRAP_satisfies_iff]
  constructor
  · intro h i hi
    have hx : cfg.memNodes i ∈ cfg.memoryDomain .transition :=
      (cfg.mem_memoryTransitionDomain_iff (cfg.memNodes i)).2 ⟨i, hi, rfl⟩
    have hzero := h (cfg.memNodes i) hx
      ⟨.transition, Trans.icurChainExpr⟩
        (by simp only [mem_trans_seg, List.mem_singleton])
    change Trans.icurChainExpr.eval
      (envOfTrace
        (encodeMemoryTrace
          (fun k => memoryEnvFull cfg.challenges.memoryInputs
            (MemoryTable.opSel (mrow k).st) (mrow k) (g k))
          cfg.memNodes)
        cfg.orbit.ω (cfg.memNodes i) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0)) = 0 at hzero
    rw [memoryChainExpr_encoded_eq_twoRow cfg mrow g i hi] at hzero
    exact (Trans.reified_icur_chain_sound
      cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow i).st)
      (MemoryTable.opSel (mrow ⟨(i : ℕ) + 1, hi⟩).st)
      (mrow i) (mrow ⟨(i : ℕ) + 1, hi⟩)
      (g i) (g ⟨(i : ℕ) + 1, hi⟩)).mp hzero
  · intro h x hx c hc
    obtain ⟨i, hi, rfl⟩ := (cfg.mem_memoryTransitionDomain_iff x).1 hx
    have hc' : c = ⟨.transition, Trans.icurChainExpr⟩ := by
      simpa only [mem_trans_seg, List.mem_singleton] using hc
    subst c
    change Trans.icurChainExpr.eval
      (envOfTrace
        (encodeMemoryTrace
          (fun k => memoryEnvFull cfg.challenges.memoryInputs
            (MemoryTable.opSel (mrow k).st) (mrow k) (g k))
          cfg.memNodes)
        cfg.orbit.ω (cfg.memNodes i) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0)) = 0
    rw [memoryChainExpr_encoded_eq_twoRow cfg mrow g i hi]
    exact (Trans.reified_icur_chain_sound
      cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow i).st)
      (MemoryTable.opSel (mrow ⟨(i : ℕ) + 1, hi⟩).st)
      (mrow i) (mrow ⟨(i : ℕ) + 1, hi⟩)
      (g i) (g ⟨(i : ℕ) + 1, hi⟩)).mpr (h i hi)

/-- The first exact memory node is the boundary point. -/
theorem ExactConfig.memNodes_first_eq_boundary (cfg : ExactConfig F K) :
    cfg.memNodes ⟨0, cfg.memRows_pos⟩ = cfg.orbit.βcoset := by
  rw [cfg.memNodes_eq_orbitPoint]
  exact cfg.orbit.orbitPoint_zero

/-- The last exact memory node is the terminal point. -/
theorem ExactConfig.memNodes_last_eq_terminal (cfg : ExactConfig F K) :
    cfg.memNodes (cfg.orbit.lastIndex cfg.memRows cfg.memRows_pos) =
      cfg.orbit.terminalPoint cfg.memRows cfg.memRows_pos := by
  rw [cfg.memNodes_eq_orbitPoint]
  rfl

/-- The exact memory boundary RAP is exactly the two axis-seed zeroes and `ipre(first)=0`. -/
theorem memoryBoundarySegment_iff (cfg : ExactConfig F K)
    (mrow : Fin cfg.memRows → MemoryTable.Pub K) (g : Fin cfg.memRows → K) :
    let rows := fun k => memoryEnvFull cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow k).st) (mrow k) (g k)
    (airToRAP (kindSeg (Trans.memoryAIRchained (K := K)) .boundary)
      (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (cfg.memoryDomain .boundary) cfg.orbit.βcoset_ne_zero
      cfg.orbit_h_pos).Satisfies (encodeMemoryTrace rows cfg.memNodes)
      ↔
    (mrow ⟨0, cfg.memRows_pos⟩).pt.counts = 0 ∧
      (mrow ⟨0, cfg.memRows_pos⟩).pt.indicator = 0 ∧
      (mrow ⟨0, cfg.memRows_pos⟩).ipre = 0 := by
  dsimp only
  erw [airToRAP_satisfies_iff]
  let first : Fin cfg.memRows := ⟨0, cfg.memRows_pos⟩
  have hfirst : cfg.memNodes first = cfg.orbit.βcoset :=
    cfg.memNodes_first_eq_boundary
  have hx : cfg.memNodes first ∈ cfg.memoryDomain .boundary := by
    rw [ExactConfig.memoryDomain, hfirst]
    exact cfg.orbit.boundaryPoint_mem_boundaryDomain
  constructor
  · intro h
    have hcounts := h (cfg.memNodes first) hx
      ⟨.boundary, Trans.memSeedCountsExpr⟩
        (by rw [mem_boundary_seg]; simp)
    have hindicator := h (cfg.memNodes first) hx
      ⟨.boundary, Trans.memSeedIndicatorExpr⟩
        (by rw [mem_boundary_seg]; simp)
    have hipre := h (cfg.memNodes first) hx
      ⟨.boundary, Trans.memIpreInitExpr⟩
        (by rw [mem_boundary_seg]; simp)
    change (envOfTrace
      (encodeMemoryTrace
        (fun k => memoryEnvFull cfg.challenges.memoryInputs
          (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) cfg.memNodes)
      cfg.orbit.ω (cfg.memNodes first) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda)
      (fun _ => 0)).trace 8 = 0 at hcounts
    change (envOfTrace
      (encodeMemoryTrace
        (fun k => memoryEnvFull cfg.challenges.memoryInputs
          (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) cfg.memNodes)
      cfg.orbit.ω (cfg.memNodes first) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda)
      (fun _ => 0)).trace 7 = 0 at hindicator
    change (envOfTrace
      (encodeMemoryTrace
        (fun k => memoryEnvFull cfg.challenges.memoryInputs
          (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) cfg.memNodes)
      cfg.orbit.ω (cfg.memNodes first) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda)
      (fun _ => 0)).trace 31 = 0 at hipre
    rw [memoryEncodedTrace_current cfg mrow g first 8
      (by norm_num [memoryAIR_numTraceCols])] at hcounts
    rw [memoryEncodedTrace_current cfg mrow g first 7
      (by norm_num [memoryAIR_numTraceCols])] at hindicator
    rw [memoryEncodedTrace_current cfg mrow g first 31
      (by norm_num [memoryAIR_numTraceCols])] at hipre
    change Trans.memSeedCountsExpr.eval
      (memoryEnvFull cfg.challenges.memoryInputs
        (MemoryTable.opSel (mrow first).st) (mrow first) (g first)) = 0 at hcounts
    change Trans.memSeedIndicatorExpr.eval
      (memoryEnvFull cfg.challenges.memoryInputs
        (MemoryTable.opSel (mrow first).st) (mrow first) (g first)) = 0 at hindicator
    change Trans.memIpreInitExpr.eval
      (memoryEnvFull cfg.challenges.memoryInputs
        (MemoryTable.opSel (mrow first).st) (mrow first) (g first)) = 0 at hipre
    have hseedEval : ∀ e ∈ Trans.memSeedBoundaryExprs,
        e.eval (memoryEnvFull cfg.challenges.memoryInputs
          (MemoryTable.opSel (mrow first).st) (mrow first) (g first)) = 0 := by
      intro e he
      simp only [Trans.memSeedBoundaryExprs, List.mem_cons, List.not_mem_nil,
        or_false] at he
      rcases he with rfl | rfl
      · exact hcounts
      · exact hindicator
    have hseed := (Trans.memSeedBoundary_sound cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow first).st) (mrow first) (g first)).mp hseedEval
    have hipreValue := (Trans.memIpreInit_sound cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow first).st) (mrow first) (g first)).mp hipre
    exact ⟨hseed.1, hseed.2, hipreValue⟩
  · rintro ⟨hcounts, hindicator, hipre⟩ x hx' c hc
    have hseedEval := (Trans.memSeedBoundary_sound cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow first).st) (mrow first) (g first)).mpr
        ⟨hcounts, hindicator⟩
    have hipreEval := (Trans.memIpreInit_sound cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow first).st) (mrow first) (g first)).mpr hipre
    rw [ExactConfig.memoryDomain, OrbitDomain.boundaryDomain,
      Finset.mem_singleton] at hx'
    have hxnode : x = cfg.memNodes first := hx'.trans hfirst.symm
    rw [hxnode]
    rw [mem_boundary_seg] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | hc
    · subst c
      change (envOfTrace
        (encodeMemoryTrace
          (fun k => memoryEnvFull cfg.challenges.memoryInputs
            (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) cfg.memNodes)
        cfg.orbit.ω (cfg.memNodes first) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda)
        (fun _ => 0)).trace 8 = 0
      rw [memoryEncodedTrace_current cfg mrow g first 8
        (by norm_num [memoryAIR_numTraceCols])]
      exact hseedEval Trans.memSeedCountsExpr (by simp [Trans.memSeedBoundaryExprs])
    · subst c
      change (envOfTrace
        (encodeMemoryTrace
          (fun k => memoryEnvFull cfg.challenges.memoryInputs
            (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) cfg.memNodes)
        cfg.orbit.ω (cfg.memNodes first) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda)
        (fun _ => 0)).trace 7 = 0
      rw [memoryEncodedTrace_current cfg mrow g first 7
        (by norm_num [memoryAIR_numTraceCols])]
      exact hseedEval Trans.memSeedIndicatorExpr (by simp [Trans.memSeedBoundaryExprs])
    · subst c
      change (envOfTrace
        (encodeMemoryTrace
          (fun k => memoryEnvFull cfg.challenges.memoryInputs
            (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) cfg.memNodes)
        cfg.orbit.ω (cfg.memNodes first) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda)
        (fun _ => 0)).trace 31 = 0
      rw [memoryEncodedTrace_current cfg mrow g first 31
        (by norm_num [memoryAIR_numTraceCols])]
      exact hipreEval

/-- The exact memory terminal RAP is exactly `icur(last)=0`. -/
theorem memoryTerminalSegment_iff (cfg : ExactConfig F K)
    (mrow : Fin cfg.memRows → MemoryTable.Pub K) (g : Fin cfg.memRows → K) :
    let rows := fun k => memoryEnvFull cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow k).st) (mrow k) (g k)
    (airToRAP (kindSeg (Trans.memoryAIRchained (K := K)) .terminal)
      (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda) (fun _ => 0)
      cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
      (cfg.memoryDomain .terminal) cfg.orbit.βcoset_ne_zero
      cfg.orbit_h_pos).Satisfies (encodeMemoryTrace rows cfg.memNodes)
      ↔
    (mrow (cfg.orbit.lastIndex cfg.memRows cfg.memRows_pos)).icur = 0 := by
  dsimp only
  erw [airToRAP_satisfies_iff]
  let last := cfg.orbit.lastIndex cfg.memRows cfg.memRows_pos
  have hlast : cfg.memNodes last =
      cfg.orbit.terminalPoint cfg.memRows cfg.memRows_pos :=
    cfg.memNodes_last_eq_terminal
  have hx : cfg.memNodes last ∈ cfg.memoryDomain .terminal := by
    rw [ExactConfig.memoryDomain, hlast]
    exact cfg.orbit.terminalPoint_mem_terminalDomain cfg.memRows cfg.memRows_pos
  constructor
  · intro h
    have hzero := h (cfg.memNodes last) hx
      ⟨.terminal, Trans.memIcurTermExpr⟩
        (by simp only [mem_terminal_seg, List.mem_singleton])
    change (envOfTrace
      (encodeMemoryTrace
        (fun k => memoryEnvFull cfg.challenges.memoryInputs
          (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) cfg.memNodes)
      cfg.orbit.ω (cfg.memNodes last) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda)
      (fun _ => 0)).trace 32 = 0 at hzero
    rw [memoryEncodedTrace_current cfg mrow g last 32
      (by norm_num [memoryAIR_numTraceCols])] at hzero
    change Trans.memIcurTermExpr.eval
      (memoryEnvFull cfg.challenges.memoryInputs
        (MemoryTable.opSel (mrow last).st) (mrow last) (g last)) = 0 at hzero
    exact (Trans.memIcurTerm_sound cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow last).st) (mrow last) (g last)).mp hzero
  · intro h x hx' c hc
    have htermEval := (Trans.memIcurTerm_sound cfg.challenges.memoryInputs
      (MemoryTable.opSel (mrow last).st) (mrow last) (g last)).mpr h
    rw [ExactConfig.memoryDomain, OrbitDomain.terminalDomain,
      Finset.mem_singleton] at hx'
    have hxnode : x = cfg.memNodes last := hx'.trans hlast.symm
    rw [hxnode]
    have hc' : c = ⟨.terminal, Trans.memIcurTermExpr⟩ := by
      simpa only [mem_terminal_seg, List.mem_singleton] using hc
    subst c
    change (envOfTrace
      (encodeMemoryTrace
        (fun k => memoryEnvFull cfg.challenges.memoryInputs
          (MemoryTable.opSel (mrow k).st) (mrow k) (g k)) cfg.memNodes)
      cfg.orbit.ω (cfg.memNodes last) (cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda)
      (fun _ => 0)).trace 32 = 0
    rw [memoryEncodedTrace_current cfg mrow g last 32
      (by norm_num [memoryAIR_numTraceCols])]
    exact htermEval

/-- **P3 option-E whole memory trace.**  One existential LogUp-witness family determines one
Lagrange polynomial assignment shared by the row, transition, boundary, and terminal RAPs. -/
theorem memorySegmentedRAP_wholeTrace_iff (cfg : ExactConfig F K)
    (mrow : Fin cfg.memRows → MemoryTable.Pub K)
    (hwf : ∀ i, MemoryTable.WF cfg.challenges.memoryInputs (mrow i))
    (hz : cfg.challenges.z ≠ 0)
    (hlam : ∀ i, (mrow i).lambda = (mrow ⟨0, cfg.memRows_pos⟩).lambda) :
    (∃ g : Fin cfg.memRows → K,
      MemorySegmentedRAPSatisfies cfg (mrow ⟨0, cfg.memRows_pos⟩).lambda
        (encodeMemoryTrace
          (fun i => memoryEnvFull cfg.challenges.memoryInputs
            (MemoryTable.opSel (mrow i).st) (mrow i) (g i))
          cfg.memNodes))
      ↔
    ((∀ i, MemoryTable.Vmem cfg.challenges.memoryInputs (mrow i)) ∧
      (∀ i : Fin cfg.memRows, ∀ hi : (i : ℕ) + 1 < cfg.memRows,
        (mrow i).icur = (mrow ⟨(i : ℕ) + 1, hi⟩).ipre) ∧
      (mrow ⟨0, cfg.memRows_pos⟩).pt.counts = 0 ∧
      (mrow ⟨0, cfg.memRows_pos⟩).pt.indicator = 0 ∧
      (mrow ⟨0, cfg.memRows_pos⟩).ipre = 0 ∧
      (mrow (cfg.orbit.lastIndex cfg.memRows cfg.memRows_pos)).icur = 0) := by
  let chalVal : ℕ → K :=
    cfg.challenges.memoryChalVal (mrow ⟨0, cfg.memRows_pos⟩).lambda
  let rowIff := memoryTable_reified_iff
    (fun _ : Fin cfg.memRows => cfg.challenges.memoryInputs) mrow
    cfg.memNodes cfg.memNodes_injective chalVal
    cfg.eDeg cfg.orbit.h cfg.orbit.ω cfg.orbit.βcoset
    cfg.orbit.βcoset_ne_zero cfg.orbit_h_pos
    (fun k => by
      funext i
      change
        (match i with
          | 0 => cfg.challenges.memoryInputs.z
          | 1 => cfg.challenges.memoryInputs.β
          | 2 => cfg.challenges.memoryInputs.γ
          | 8 => (mrow k).lambda
          | _ => 0) =
        (match i with
          | 0 => cfg.challenges.z
          | 1 => cfg.challenges.β
          | 2 => cfg.challenges.γ
          | 8 => (mrow ⟨0, cfg.memRows_pos⟩).lambda
          | _ => 0)
      simp only [ChallengeVector.memoryInputs]
      split <;> first | rfl | exact hlam k) hwf (fun _ => hz)
  constructor
  · rintro ⟨g, hseg⟩
    have hrows : ∀ i, MemoryTable.Vmem cfg.challenges.memoryInputs (mrow i) := by
      apply rowIff.mpr
      exact ⟨g, (memoryRowSegment_iff cfg mrow _).mp (hseg .row)⟩
    have htrans := (memoryTransitionSegment_iff cfg mrow g).mp (hseg .transition)
    have hboundary := (memoryBoundarySegment_iff cfg mrow g).mp (hseg .boundary)
    have hterminal := (memoryTerminalSegment_iff cfg mrow g).mp (hseg .terminal)
    exact ⟨hrows, htrans, hboundary.1, hboundary.2.1, hboundary.2.2, hterminal⟩
  · rintro ⟨hrows, htrans, hcounts, hindicator, hipre, hicur⟩
    obtain ⟨g, hrow⟩ := rowIff.mp hrows
    refine ⟨g, ?_⟩
    intro kind
    cases kind with
    | row =>
        exact (memoryRowSegment_iff cfg mrow _).mpr hrow
    | transition =>
        exact (memoryTransitionSegment_iff cfg mrow g).mpr htrans
    | boundary =>
        exact (memoryBoundarySegment_iff cfg mrow g).mpr
          ⟨hcounts, hindicator, hipre⟩
    | terminal =>
        exact (memoryTerminalSegment_iff cfg mrow g).mpr hicur

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.encodedTrace_next_at_activeOrbitNode
#print axioms Nock.NockVMROM.Thm54.ExactConfig.mem_computeTransitionDomain_iff
#print axioms Nock.NockVMROM.Thm54.computeSegmentedRAP_wholeTrace_iff
#print axioms Nock.NockVMROM.Thm54.memorySegmentedRAP_wholeTrace_iff
