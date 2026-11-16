import Nock.NockVMROM.Thm54.PlusIOSegmentedRAP

/-!
# Exact whole-trace wiring for the `+IO` walk and IO families

This module connects the walk and IO traces in `PlusIOSameExecutionAssignment` to the exact
kind-segmented orbit-prefix RAPs.  It uses the same interpolated assignment for every kind,
evaluates transition gates only at active nonterminal points, and evaluates the boundary and
terminal gates only at the first and last active points.
-/

namespace Nock.NockVMROM.Thm54

open Classical
open Nock Framework Framework.Reify Framework.Thm54
open Nock.Reified
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Generic interpolation facts used by all three AIRs -/

private noncomputable def orbitPrefixDomain (D : OrbitDomain K) (n : ℕ) (hn : 0 < n) :
    ConstraintKind → Finset K
  | .row => D.rowDomain n
  | .transition => D.transitionDomain n hn
  | .boundary => D.boundaryDomain
  | .terminal => D.terminalDomain n hn

private theorem walk_row_seg :
    (kindSeg Trans.walkAIR .row).constraints = [] := by
  rfl

private theorem walk_boundary_seg :
    (kindSeg Trans.walkAIR .boundary).constraints =
      [⟨.boundary, Trans.walkLn1⟩, ⟨.boundary, Trans.walkCount1⟩,
        ⟨.boundary, Trans.walkAccInit⟩] := by
  rfl

private theorem walk_transition_seg :
    (kindSeg Trans.walkAIR .transition).constraints =
      [⟨.transition, Trans.walkLnStep⟩, ⟨.transition, Trans.walkCountStep⟩,
        ⟨.transition, Trans.walkAccStep⟩] := by
  rfl

private theorem walk_terminal_seg :
    (kindSeg Trans.walkAIR .terminal).constraints =
      [⟨.terminal, Trans.walkOut⟩] := by
  rfl

theorem encodeEnvTrace_current_at_node {L : Type*} [Field L] {n w : ℕ}
    (rows : Fin n → Env L) (nodes : Fin n → L) (hnodes : Function.Injective nodes)
    (ω : L) (chalVal pubVal : ℕ → L) (i : Fin n) (j : ℕ) (hj : j < w) :
    (envOfTrace (w := w) (encodeEnvTrace (w := w) rows nodes)
      ω (nodes i) chalVal pubVal).trace j =
      (rows i).trace j := by
  simp only [envOfTrace, dif_pos hj]
  exact encodeEnvTrace_eval_at_node rows nodes hnodes i ⟨j, hj⟩

theorem encodeEnvTrace_next_at_orbit_node {L : Type*} [Field L] {n w : ℕ}
    (D : OrbitDomain L) (rows : Fin n → Env L) (nodes : Fin n → L)
    (hnodes : Function.Injective nodes) (hnodes_spec : ∀ i, nodes i = D.orbitPoint i)
    (chalVal pubVal : ℕ → L)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) (hj : j < w) :
    (envOfTrace (w := w) (encodeEnvTrace (w := w) rows nodes)
      D.ω (nodes i) chalVal pubVal).traceNext j =
      (rows ⟨(i : ℕ) + 1, hi⟩).trace j := by
  let next : Fin n := ⟨(i : ℕ) + 1, hi⟩
  simp only [envOfTrace, dif_pos hj]
  rw [hnodes_spec i, D.orbitPoint_succ, ← hnodes_spec next]
  exact encodeEnvTrace_eval_at_node rows nodes hnodes next ⟨j, hj⟩

theorem encodeEnvTrace_next_at_mapped_orbit_node
    {L M : Type*} [Field L] [Field M] [Algebra L M] {n w : ℕ}
    (D : OrbitDomain L) (rows : Fin n → Env M)
    (nodes : Fin n → M)
    (hnodes : Function.Injective nodes)
    (hnodes_spec : ∀ i, nodes i = algebraMap L M (D.orbitPoint i))
    (chalVal pubVal : ℕ → M)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) (j : ℕ) (hj : j < w) :
    (envOfTrace (w := w) (encodeEnvTrace (w := w) rows nodes) (algebraMap L M D.ω)
      (nodes i) chalVal pubVal).traceNext j =
      (rows ⟨(i : ℕ) + 1, hi⟩).trace j := by
  let next : Fin n := ⟨(i : ℕ) + 1, hi⟩
  simp only [envOfTrace, dif_pos hj]
  rw [hnodes_spec i, ← map_mul, D.orbitPoint_succ, ← hnodes_spec next]
  exact encodeEnvTrace_eval_at_node rows nodes hnodes next ⟨j, hj⟩

/-! ## Generic exact orbit-prefix walk trace -/

private theorem walk_boundary_expr_encoded_eq
    {n : ℕ} (D : OrbitDomain K) (hn : 0 < n)
    (cur : ℕ → K) (chld : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln count acc : ℕ → K) (α seed initialCount : K)
    (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (_hnodes_spec : ∀ i, nodes i = D.orbitPoint i)
    (e : Expr)
    (he : e ∈ [Trans.walkLn1, Trans.walkCount1, Trans.walkAccInit]) :
    let rows := fun i : Fin n =>
      Trans.walkRowEnv cur chld fo ln count acc α seed initialCount ((i : ℕ) + 1)
    e.eval (envOfTrace (w := Trans.walkAIR.numTraceCols)
        (encodeEnvTrace (w := Trans.walkAIR.numTraceCols) rows nodes) D.ω
        (nodes ⟨0, hn⟩) (rows ⟨0, hn⟩).chal (rows ⟨0, hn⟩).pub) =
      e.eval (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1) := by
  dsimp only
  let first : Fin n := ⟨0, hn⟩
  have hcur : ∀ j, j < Trans.walkAIR.numTraceCols →
      (envOfTrace (w := Trans.walkAIR.numTraceCols)
        (encodeEnvTrace (w := Trans.walkAIR.numTraceCols)
          (fun i : Fin n =>
            Trans.walkRowEnv cur chld fo ln count acc α seed initialCount ((i : ℕ) + 1))
          nodes)
        D.ω (nodes first)
        (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1).chal
        (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1).pub).trace j =
      (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1).trace j := by
    intro j hj
    simpa [first] using
      encodeEnvTrace_current_at_node
        (fun i : Fin n =>
          Trans.walkRowEnv cur chld fo ln count acc α seed initialCount ((i : ℕ) + 1))
        nodes hnodes D.ω
        (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1).chal
        (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1).pub
        first j hj
  simp only [first] at hcur
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · simp only [Trans.walkLn1, Reified.tc, Reified.chl, Expr.eval]
    rw [hcur 0 (by norm_num [Trans.walkAIR_numTraceCols])]
    rfl
  · simp only [Trans.walkCount1, Reified.tc, Trans.pubv, Expr.eval]
    rw [hcur 1 (by norm_num [Trans.walkAIR_numTraceCols]),
      hcur 5 (by norm_num [Trans.walkAIR_numTraceCols])]
    rfl
  · simp only [Trans.walkAccInit, Reified.tc, Trans.pubv, Expr.eval]
    rw [hcur 0 (by norm_num [Trans.walkAIR_numTraceCols]),
      hcur 3 (by norm_num [Trans.walkAIR_numTraceCols]),
      hcur 2 (by norm_num [Trans.walkAIR_numTraceCols]),
      hcur 4 (by norm_num [Trans.walkAIR_numTraceCols])]
    rfl

private theorem walk_transition_expr_encoded_eq
    {n : ℕ} (D : OrbitDomain K) (hn : 0 < n)
    (cur : ℕ → K) (chld : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln count acc : ℕ → K) (α seed initialCount : K)
    (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (hnodes_spec : ∀ i, nodes i = D.orbitPoint i)
    (i : Fin n) (hi : (i : ℕ) + 1 < n)
    (e : Expr)
    (he : e ∈ [Trans.walkLnStep, Trans.walkCountStep, Trans.walkAccStep]) :
    let rows := fun q : Fin n =>
      Trans.walkRowEnv cur chld fo ln count acc α seed initialCount ((q : ℕ) + 1)
    e.eval (envOfTrace (w := Trans.walkAIR.numTraceCols)
        (encodeEnvTrace (w := Trans.walkAIR.numTraceCols) rows nodes) D.ω
        (nodes i) (rows ⟨0, hn⟩).chal (rows ⟨0, hn⟩).pub) =
      e.eval (Trans.walkStep cur chld fo ln count acc α seed initialCount ((i : ℕ) + 1)) := by
  dsimp only
  let rows := fun q : Fin n =>
    Trans.walkRowEnv cur chld fo ln count acc α seed initialCount ((q : ℕ) + 1)
  let next : Fin n := ⟨(i : ℕ) + 1, hi⟩
  let encoded := envOfTrace (w := Trans.walkAIR.numTraceCols)
    (encodeEnvTrace (w := Trans.walkAIR.numTraceCols) rows nodes) D.ω
    (nodes i) (rows ⟨0, hn⟩).chal (rows ⟨0, hn⟩).pub
  have hcur : ∀ j, j < Trans.walkAIR.numTraceCols →
      encoded.trace j = (Trans.walkStep cur chld fo ln count acc α seed initialCount
        ((i : ℕ) + 1)).trace j := by
    intro j hj
    simpa [encoded, rows, Trans.walkStep] using
      encodeEnvTrace_current_at_node rows nodes hnodes D.ω
        (rows ⟨0, hn⟩).chal (rows ⟨0, hn⟩).pub i j hj
  have hnext : ∀ j, j < Trans.walkAIR.numTraceCols →
      encoded.traceNext j = (Trans.walkStep cur chld fo ln count acc α seed initialCount
        ((i : ℕ) + 1)).traceNext j := by
    intro j hj
    simpa [encoded, rows, next, Trans.walkStep] using
      encodeEnvTrace_next_at_orbit_node D rows nodes hnodes hnodes_spec
        (rows ⟨0, hn⟩).chal (rows ⟨0, hn⟩).pub i hi j hj
  dsimp [encoded] at hcur hnext
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · simp only [Trans.walkLnStep, Trans.tn, Reified.chl, Reified.tc, Expr.eval]
    rw [hnext 0 (by norm_num [Trans.walkAIR_numTraceCols]),
      hcur 0 (by norm_num [Trans.walkAIR_numTraceCols])]
    rfl
  · simp only [Trans.walkCountStep, Trans.tn, Reified.tc, Expr.eval]
    rw [hnext 1 (by norm_num [Trans.walkAIR_numTraceCols]),
      hcur 1 (by norm_num [Trans.walkAIR_numTraceCols]),
      hnext 5 (by norm_num [Trans.walkAIR_numTraceCols])]
  · simp only [Trans.walkAccStep, Trans.tn, Reified.tc, Expr.eval]
    rw [hnext 0 (by norm_num [Trans.walkAIR_numTraceCols]),
      hnext 3 (by norm_num [Trans.walkAIR_numTraceCols]),
      hnext 2 (by norm_num [Trans.walkAIR_numTraceCols]),
      hcur 2 (by norm_num [Trans.walkAIR_numTraceCols]),
      hcur 1 (by norm_num [Trans.walkAIR_numTraceCols]),
      hnext 4 (by norm_num [Trans.walkAIR_numTraceCols])]

private theorem walk_terminal_expr_encoded_eq
    {n : ℕ} (D : OrbitDomain K) (hn : 0 < n)
    (cur : ℕ → K) (chld : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln count acc : ℕ → K) (α seed initialCount : K)
    (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (_hnodes_spec : ∀ i, nodes i = D.orbitPoint i)
    (chalVal pubVal : ℕ → K) :
    let rows := fun i : Fin n =>
      Trans.walkRowEnv cur chld fo ln count acc α seed initialCount ((i : ℕ) + 1)
    Trans.walkOut.eval
        (envOfTrace (w := Trans.walkAIR.numTraceCols)
          (encodeEnvTrace (w := Trans.walkAIR.numTraceCols) rows nodes) D.ω
          (nodes (D.lastIndex n hn))
          chalVal pubVal) =
      Trans.walkOut.eval
        (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount n) := by
  dsimp only
  let last := D.lastIndex n hn
  have hlast : (last : ℕ) + 1 = n := by
    simp [last, OrbitDomain.lastIndex, Nat.sub_add_cancel hn]
  simp only [Trans.walkOut, Reified.tc, Expr.eval]
  simpa [last, hlast] using
    encodeEnvTrace_current_at_node
      (fun i : Fin n =>
        Trans.walkRowEnv cur chld fo ln count acc α seed initialCount ((i : ℕ) + 1))
      nodes hnodes D.ω
      chalVal pubVal
      last 2 (by norm_num [Trans.walkAIR_numTraceCols])

theorem walkSegmentedRAP_wholeTrace_iff
    {n : ℕ} (D : OrbitDomain K) (hn : 0 < n) (hcap : n ≤ 2 ^ D.h)
    (hExpPos : 1 ≤ D.h) (eDeg : ℕ)
    (cur : ℕ → K) (chld : ℕ → ℕ → K) (fo : ℕ → ℕ)
    (ln count acc : ℕ → K) (α seed initialCount : K)
    (nodes : Fin n → K) (hnodes : Function.Injective nodes)
    (hnodes_spec : ∀ i, nodes i = D.orbitPoint i) :
    let rows := fun i : Fin n =>
      Trans.walkRowEnv cur chld fo ln count acc α seed initialCount ((i : ℕ) + 1)
    (∀ kind : ConstraintKind,
      (airToRAP (kindSeg Trans.walkAIR kind)
        (rows ⟨0, hn⟩).chal (rows ⟨0, hn⟩).pub
        eDeg D.h D.ω D.βcoset
        (orbitPrefixDomain D n hn kind)
        D.βcoset_ne_zero hExpPos).Satisfies
          (encodeEnvTrace (w := Trans.walkAIR.numTraceCols) rows nodes))
      ↔
    (Walk.WalkSat cur chld fo ln count acc α seed initialCount n ∧ acc n = 0) := by
  dsimp only
  let rows := fun i : Fin n =>
    Trans.walkRowEnv cur chld fo ln count acc α seed initialCount ((i : ℕ) + 1)
  let P : Fin Trans.walkAIR.numTraceCols → K[X] :=
    encodeEnvTrace (w := Trans.walkAIR.numTraceCols) rows nodes
  have hboundary :
      (airToRAP (kindSeg Trans.walkAIR .boundary)
        (rows ⟨0, hn⟩).chal (rows ⟨0, hn⟩).pub eDeg D.h D.ω D.βcoset
        (orbitPrefixDomain D n hn .boundary)
        D.βcoset_ne_zero hExpPos).Satisfies P
        ↔
      (Trans.walkLn1.eval
          (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1) = 0 ∧
       Trans.walkCount1.eval
          (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1) = 0 ∧
       Trans.walkAccInit.eval
          (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1) = 0) := by
    erw [airToRAP_satisfies_iff]
    constructor
    · intro h
      let first : Fin n := ⟨0, hn⟩
      have hx : nodes first ∈ orbitPrefixDomain D n hn .boundary := by
        rw [orbitPrefixDomain, hnodes_spec first]
        simp [first]
      have hln := h (nodes first) hx
        ⟨.boundary, Trans.walkLn1⟩ (by rw [walk_boundary_seg]; simp)
      have hcount := h (nodes first) hx
        ⟨.boundary, Trans.walkCount1⟩ (by rw [walk_boundary_seg]; simp)
      have hacc := h (nodes first) hx
        ⟨.boundary, Trans.walkAccInit⟩ (by rw [walk_boundary_seg]; simp)
      dsimp [P, rows, first] at hln hcount hacc
      rw [walk_boundary_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
        nodes hnodes hnodes_spec Trans.walkLn1 (by simp)] at hln
      rw [walk_boundary_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
        nodes hnodes hnodes_spec Trans.walkCount1 (by simp)] at hcount
      rw [walk_boundary_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
        nodes hnodes hnodes_spec Trans.walkAccInit (by simp)] at hacc
      exact ⟨hln, hcount, hacc⟩
    · rintro ⟨hln, hcount, hacc⟩ x hx c hc
      rw [orbitPrefixDomain, OrbitDomain.boundaryDomain,
        Finset.mem_singleton] at hx
      have hxnode : x = nodes ⟨0, hn⟩ := by
        rw [hnodes_spec]
        simpa using hx
      rw [hxnode]
      dsimp [P, rows]
      rw [walk_boundary_seg] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · rw [walk_boundary_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
          nodes hnodes hnodes_spec Trans.walkLn1 (by simp)]
        exact hln
      · rw [walk_boundary_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
          nodes hnodes hnodes_spec Trans.walkCount1 (by simp)]
        exact hcount
      · rw [walk_boundary_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
          nodes hnodes hnodes_spec Trans.walkAccInit (by simp)]
        exact hacc
  have htransition :
      (airToRAP (kindSeg Trans.walkAIR .transition)
        (rows ⟨0, hn⟩).chal (rows ⟨0, hn⟩).pub eDeg D.h D.ω D.βcoset
        (orbitPrefixDomain D n hn .transition)
        D.βcoset_ne_zero hExpPos).Satisfies P
        ↔
      ∀ i, 1 ≤ i → i < n →
        Trans.walkLnStep.eval
            (Trans.walkStep cur chld fo ln count acc α seed initialCount i) = 0 ∧
          Trans.walkCountStep.eval
            (Trans.walkStep cur chld fo ln count acc α seed initialCount i) = 0 ∧
          Trans.walkAccStep.eval
            (Trans.walkStep cur chld fo ln count acc α seed initialCount i) = 0 := by
    erw [airToRAP_satisfies_iff]
    constructor
    · intro h i hi1 hin
      let q : Fin n := ⟨i - 1, by omega⟩
      have hqnext : (q : ℕ) + 1 < n := by dsimp [q]; omega
      have hx : nodes q ∈ orbitPrefixDomain D n hn .transition := by
        rw [orbitPrefixDomain, hnodes_spec q]
        exact D.orbitPoint_mem_transitionDomain hn hcap q hqnext
      have hln := h (nodes q) hx
        ⟨.transition, Trans.walkLnStep⟩ (by rw [walk_transition_seg]; simp)
      have hcount := h (nodes q) hx
        ⟨.transition, Trans.walkCountStep⟩ (by rw [walk_transition_seg]; simp)
      have hacc := h (nodes q) hx
        ⟨.transition, Trans.walkAccStep⟩ (by rw [walk_transition_seg]; simp)
      have hqi : (q : ℕ) + 1 = i := by dsimp [q]; omega
      dsimp [P, rows] at hln hcount hacc
      rw [walk_transition_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
        nodes hnodes hnodes_spec q hqnext Trans.walkLnStep (by simp), hqi] at hln
      rw [walk_transition_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
        nodes hnodes hnodes_spec q hqnext Trans.walkCountStep (by simp), hqi] at hcount
      rw [walk_transition_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
        nodes hnodes hnodes_spec q hqnext Trans.walkAccStep (by simp), hqi] at hacc
      exact ⟨hln, hcount, hacc⟩
    · intro h x hx c hc
      obtain ⟨q, hqnext, hxq⟩ :=
        (orbit_mem_transitionDomain_iff_active_nonterminal D n hn hcap x).1
          (by simpa [orbitPrefixDomain] using hx)
      subst x
      dsimp [P, rows]
      rw [walk_transition_seg] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      have hq1 : 1 ≤ (q : ℕ) + 1 := by omega
      have hgates := h ((q : ℕ) + 1) hq1 hqnext
      rcases hc with rfl | rfl | rfl
      · rw [← hnodes_spec q,
          walk_transition_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
            nodes hnodes hnodes_spec q hqnext Trans.walkLnStep (by simp)]
        exact hgates.1
      · rw [← hnodes_spec q,
          walk_transition_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
            nodes hnodes hnodes_spec q hqnext Trans.walkCountStep (by simp)]
        exact hgates.2.1
      · rw [← hnodes_spec q,
          walk_transition_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
            nodes hnodes hnodes_spec q hqnext Trans.walkAccStep (by simp)]
        exact hgates.2.2
  have hterminal :
      (airToRAP (kindSeg Trans.walkAIR .terminal)
        (rows ⟨0, hn⟩).chal (rows ⟨0, hn⟩).pub eDeg D.h D.ω D.βcoset
        (orbitPrefixDomain D n hn .terminal)
        D.βcoset_ne_zero hExpPos).Satisfies P
        ↔
      Trans.walkOut.eval
        (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount n) = 0 := by
    erw [airToRAP_satisfies_iff]
    let last := D.lastIndex n hn
    have hx : nodes last ∈ orbitPrefixDomain D n hn .terminal := by
      rw [orbitPrefixDomain, hnodes_spec last]
      exact D.terminalPoint_mem_terminalDomain n hn
    constructor
    · intro h
      have hout := h (nodes last) hx
        ⟨.terminal, Trans.walkOut⟩ (by rw [walk_terminal_seg]; simp)
      dsimp [P, rows, last] at hout
      rw [walk_terminal_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
        nodes hnodes hnodes_spec
        (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1).chal
        (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1).pub] at hout
      exact hout
    · intro hout x hx' c hc
      rw [orbitPrefixDomain, OrbitDomain.terminalDomain,
        Finset.mem_singleton] at hx'
      have hxnode : x = nodes last := by
        rw [hnodes_spec]
        exact hx'
      rw [hxnode]
      have hc' : c = ⟨.terminal, Trans.walkOut⟩ := by
        simpa [walk_terminal_seg] using hc
      subst c
      dsimp [P, rows, last]
      rw [walk_terminal_expr_encoded_eq D hn cur chld fo ln count acc α seed initialCount
        nodes hnodes hnodes_spec
        (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1).chal
        (Trans.walkRowEnv cur chld fo ln count acc α seed initialCount 1).pub]
      exact hout
  constructor
  · intro h
    have hb := hboundary.mp (h .boundary)
    have ht := htransition.mp (h .transition)
    have hz := hterminal.mp (h .terminal)
    exact ⟨(Trans.reified_walk_sound).2 ⟨by omega, hb.1, hb.2.1, hb.2.2, ht⟩,
      (Trans.reified_walk_out_sound).1 hz⟩
  · rintro ⟨hwalk, hout⟩ kind
    have hgates := (Trans.reified_walk_sound).1 hwalk
    cases kind with
    | boundary => exact hboundary.mpr ⟨hgates.2.1, hgates.2.2.1, hgates.2.2.2.1⟩
    | transition => exact htransition.mpr hgates.2.2.2.2
    | terminal => exact hterminal.mpr ((Trans.reified_walk_out_sound).2 hout)
    | row =>
        erw [airToRAP_satisfies_iff]
        intro x hx c hc
        rw [walk_row_seg] at hc
        simp at hc

/-! ## The two exact walk components of one same-execution assignment -/

namespace PlusIOSameExecutionAssignment

variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- Exact proof-carrying compute-walk obligation.  The recurrence and terminal value are fields of
this proposition; they are not free theorem hypotheses. -/
def ComputeWalkCertificate (A : PlusIOSameExecutionAssignment R p) : Prop :=
  Walk.WalkSat
    (Walk.curCol R.computeNodeVal R.computeWalkRows)
    (Walk.chldCol R.computeNodeVal R.computeWalkRows)
    (Walk.foCol R.computeWalkRows)
    A.computeWalk.ln A.computeWalk.count A.computeWalk.acc
    R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha
    R.problem.cfg.compRows
  ∧ A.computeWalk.acc R.problem.cfg.compRows = 0

/-- Exact proof-carrying aggregate-memory-walk obligation. -/
def MemoryWalkCertificate (A : PlusIOSameExecutionAssignment R p) : Prop :=
  Walk.WalkSat
    (Walk.curCol R.memoryNodeVal R.memoryWalkRows)
    (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
    (Walk.foCol R.memoryWalkRows)
    A.memoryWalk.ln A.memoryWalk.count A.memoryWalk.acc
    R.memoryWalkAlpha R.memoryWalkSeed
    (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
    R.problem.cfg.memRows
  ∧ A.memoryWalk.acc R.problem.cfg.memRows = 0

/-- All four compute-walk RAP kinds use `A.computeWalkTrace`, and are equivalent to the exact
walk recurrence plus terminal closure on the configured compute prefix. -/
theorem computeWalkRAP_wholeTrace_iff (A : PlusIOSameExecutionAssignment R p) :
    (∀ kind, (R.computeWalkRAP kind).Satisfies A.computeWalkTrace)
      ↔ A.ComputeWalkCertificate := by
  have hchal :
      PlusIOSegmentedFamily.walkChallengeValuation R.computeWalkAlpha =
        (Trans.walkRowEnv
          (Walk.curCol R.computeNodeVal R.computeWalkRows)
          (Walk.chldCol R.computeNodeVal R.computeWalkRows)
          (Walk.foCol R.computeWalkRows)
          A.computeWalk.ln A.computeWalk.count A.computeWalk.acc
          R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha 1).chal := by
    funext j
    cases j <;> rfl
  have hpub :
      R.computeWalkPublicValuation =
        (Trans.walkRowEnv
          (Walk.curCol R.computeNodeVal R.computeWalkRows)
          (Walk.chldCol R.computeNodeVal R.computeWalkRows)
          (Walk.foCol R.computeWalkRows)
          A.computeWalk.ln A.computeWalk.count A.computeWalk.acc
          R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha 1).pub := by
    funext j
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  simp only [ComputeWalkCertificate, PlusIOSegmentedFamily.computeWalkRAP,
    PlusIOSegmentedFamily.computeWalkParams, SegmentedRAPParams.rap,
    PlusIOSameExecutionAssignment.computeWalkTrace]
  rw [hchal, hpub]
  have hg := walkSegmentedRAP_wholeTrace_iff
      R.problem.cfg.orbit R.problem.cfg.compRows_pos R.problem.cfg.compRows_le
      R.problem.cfg.orbit_h_pos R.problem.cfg.eDeg
      (Walk.curCol R.computeNodeVal R.computeWalkRows)
      (Walk.chldCol R.computeNodeVal R.computeWalkRows)
      (Walk.foCol R.computeWalkRows)
      A.computeWalk.ln A.computeWalk.count A.computeWalk.acc
      R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha
      R.problem.cfg.compNodes R.problem.cfg.compNodes_injective
      R.problem.cfg.compNodes_eq_orbitPoint
  constructor
  · intro h
    apply hg.mp
    intro kind
    have hk := h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    intro x hx c hc
    exact hk x (by
      cases kind <;> simpa [orbitPrefixDomain, ExactConfig.computeDomain] using hx) c hc
  · intro h kind
    have hk := hg.mpr h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    intro x hx c hc
    exact hk x (by
      cases kind <;> simpa [orbitPrefixDomain, ExactConfig.computeDomain] using hx) c hc

/-- Memory-walk analogue of `computeWalkRAP_wholeTrace_iff`, on the exact memory BFS prefix. -/
theorem memoryWalkRAP_wholeTrace_iff (A : PlusIOSameExecutionAssignment R p) :
    (∀ kind, (R.memoryWalkRAP kind).Satisfies A.memoryWalkTrace)
      ↔ A.MemoryWalkCertificate := by
  have hchal :
      PlusIOSegmentedFamily.walkChallengeValuation R.memoryWalkAlpha =
        (Trans.walkRowEnv
          (Walk.curCol R.memoryNodeVal R.memoryWalkRows)
          (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
          (Walk.foCol R.memoryWalkRows)
          A.memoryWalk.ln A.memoryWalk.count A.memoryWalk.acc
          R.memoryWalkAlpha R.memoryWalkSeed
          (R.memoryWalkAlpha ^ R.problem.cfg.kMem) 1).chal := by
    funext j
    cases j <;> rfl
  have hpub :
      R.memoryWalkPublicValuation =
        (Trans.walkRowEnv
          (Walk.curCol R.memoryNodeVal R.memoryWalkRows)
          (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
          (Walk.foCol R.memoryWalkRows)
          A.memoryWalk.ln A.memoryWalk.count A.memoryWalk.acc
          R.memoryWalkAlpha R.memoryWalkSeed
          (R.memoryWalkAlpha ^ R.problem.cfg.kMem) 1).pub := by
    funext j
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  simp only [MemoryWalkCertificate, PlusIOSegmentedFamily.memoryWalkRAP,
    PlusIOSegmentedFamily.memoryWalkParams, SegmentedRAPParams.rap,
    PlusIOSameExecutionAssignment.memoryWalkTrace]
  rw [hchal, hpub]
  have hg := walkSegmentedRAP_wholeTrace_iff
      R.problem.cfg.orbit R.problem.cfg.memRows_pos R.problem.cfg.memRows_le
      R.problem.cfg.orbit_h_pos R.problem.cfg.eDeg
      (Walk.curCol R.memoryNodeVal R.memoryWalkRows)
      (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
      (Walk.foCol R.memoryWalkRows)
      A.memoryWalk.ln A.memoryWalk.count A.memoryWalk.acc
      R.memoryWalkAlpha R.memoryWalkSeed
      (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
      R.problem.cfg.memNodes R.problem.cfg.memNodes_injective
      R.problem.cfg.memNodes_eq_orbitPoint
  constructor
  · intro h
    apply hg.mp
    intro kind
    have hk := h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    intro x hx c hc
    exact hk x (by
      cases kind <;> simpa [orbitPrefixDomain, ExactConfig.memoryDomain] using hx) c hc
  · intro h kind
    have hk := hg.mpr h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    intro x hx c hc
    exact hk x (by
      cases kind <;> simpa [orbitPrefixDomain, ExactConfig.memoryDomain] using hx) c hc

end PlusIOSameExecutionAssignment

/-! ## Mapped IO-field orbit prefixes -/

private theorem ioProg_row_seg :
    (kindSeg Trans.ioProgAIR .row).constraints = [] := by
  rfl

private theorem ioProg_boundary_seg :
    (kindSeg Trans.ioProgAIR .boundary).constraints =
      [⟨.boundary, Trans.ioProgInit⟩] := by
  rfl

private theorem ioProg_transition_seg :
    (kindSeg Trans.ioProgAIR .transition).constraints =
      [⟨.transition, Trans.ioProgStep⟩] := by
  rfl

private theorem ioProg_terminal_seg :
    (kindSeg Trans.ioProgAIR .terminal).constraints =
      [⟨.terminal, Trans.ioProgTerm⟩] := by
  rfl

private theorem ioMem_row_seg :
    (kindSeg Trans.ioMemAIR .row).constraints = [] := by
  rfl

private theorem ioMem_boundary_seg :
    (kindSeg Trans.ioMemAIR .boundary).constraints =
      [⟨.boundary, Trans.ioMemInit⟩] := by
  rfl

private theorem ioMem_transition_seg :
    (kindSeg Trans.ioMemAIR .transition).constraints =
      [⟨.transition, Trans.ioMemStep⟩] := by
  rfl

private theorem ioMem_terminal_seg :
    (kindSeg Trans.ioMemAIR .terminal).constraints =
      [⟨.terminal, Trans.ioMemTerm⟩] := by
  rfl

theorem mem_liftedIO_transitionDomain_iff
    (D : OrbitDomain K) (records : ℕ) (hcap : records + 1 ≤ 2 ^ D.h)
    (x : IOField K) :
    x ∈ PlusIOSegmentedFamily.liftFinsetToIO
        (PlusIOSegmentedFamily.ioBaseDomain D records .transition)
      ↔
    ∃ i : Fin (records + 1), (i : ℕ) + 1 < records + 1 ∧
      x = algebraMap K (IOField K) (D.orbitPoint i) := by
  rw [PlusIOSegmentedFamily.liftFinsetToIO, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi, rfl⟩ :=
      (orbit_mem_transitionDomain_iff_active_nonterminal
        D (records + 1) (by omega) hcap y).1
        (by simpa [PlusIOSegmentedFamily.ioBaseDomain] using hy)
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨D.orbitPoint i, ?_, rfl⟩
    simpa [PlusIOSegmentedFamily.ioBaseDomain] using
      D.orbitPoint_mem_transitionDomain (by omega) hcap i hi

theorem mem_liftedIO_boundaryDomain_iff
    (D : OrbitDomain K) (records : ℕ) (x : IOField K) :
    x ∈ PlusIOSegmentedFamily.liftFinsetToIO
        (PlusIOSegmentedFamily.ioBaseDomain D records .boundary)
      ↔ x = algebraMap K (IOField K) D.βcoset := by
  simp [PlusIOSegmentedFamily.liftFinsetToIO,
    PlusIOSegmentedFamily.ioBaseDomain, OrbitDomain.boundaryDomain]

theorem mem_liftedIO_terminalDomain_iff
    (D : OrbitDomain K) (records : ℕ) (x : IOField K) :
    x ∈ PlusIOSegmentedFamily.liftFinsetToIO
        (PlusIOSegmentedFamily.ioBaseDomain D records .terminal)
      ↔
    x = algebraMap K (IOField K)
      (D.terminalPoint (records + 1) (by omega)) := by
  simp [PlusIOSegmentedFamily.liftFinsetToIO,
    PlusIOSegmentedFamily.ioBaseDomain, OrbitDomain.terminalDomain]

private theorem ioProg_init_encoded_eq
    (D : OrbitDomain K) (records : ℕ) (hcap : records + 1 ≤ 2 ^ D.h)
    (a : ℕ → RatFunc K) (acc : ℕ → IOField K) (requests : IOField K) :
    let rows := fun i : Fin (records + 1) => Trans.ioProgRowEnv a acc requests i
    let nodes := fun i : Fin (records + 1) =>
      algebraMap K (IOField K) (D.orbitPoint i)
    Trans.ioProgInit.eval
        (envOfTrace (w := Trans.ioProgAIR.numTraceCols)
          (encodeEnvTrace (w := Trans.ioProgAIR.numTraceCols) rows nodes)
          (algebraMap K (IOField K) D.ω)
          (nodes ⟨0, by omega⟩) (rows ⟨0, by omega⟩).chal
          (rows ⟨0, by omega⟩).pub) =
      Trans.ioProgInit.eval (Trans.ioProgRowEnv a acc requests 0) := by
  dsimp only
  simp only [Trans.ioProgInit, Reified.tc, Expr.eval]
  exact encodeEnvTrace_current_at_node
    (fun i : Fin (records + 1) => Trans.ioProgRowEnv a acc requests i)
    (fun i => algebraMap K (IOField K) (D.orbitPoint i))
    ((algebraMap K (IOField K)).injective.comp (D.orbitPoint_injective hcap))
    (algebraMap K (IOField K) D.ω)
    (Trans.ioProgRowEnv a acc requests 0).chal
    (Trans.ioProgRowEnv a acc requests 0).pub
    ⟨0, by omega⟩ 0 (by norm_num [Trans.ioProgAIR_numTraceCols])

private theorem ioProg_step_encoded_eq
    (D : OrbitDomain K) (records : ℕ) (hcap : records + 1 ≤ 2 ^ D.h)
    (a : ℕ → RatFunc K) (acc : ℕ → IOField K) (requests : IOField K)
    (i : Fin (records + 1)) (hi : (i : ℕ) + 1 < records + 1) :
    let rows := fun q : Fin (records + 1) => Trans.ioProgRowEnv a acc requests q
    let nodes := fun q : Fin (records + 1) =>
      algebraMap K (IOField K) (D.orbitPoint q)
    Trans.ioProgStep.eval
        (envOfTrace (w := Trans.ioProgAIR.numTraceCols)
          (encodeEnvTrace (w := Trans.ioProgAIR.numTraceCols) rows nodes)
          (algebraMap K (IOField K) D.ω)
          (nodes i) (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub) =
      Trans.ioProgStep.eval
        (Trans.twoRow (Trans.ioProgRowEnv a acc requests i)
          (Trans.ioProgRowEnv a acc requests ((i : ℕ) + 1))) := by
  dsimp only
  let rows := fun q : Fin (records + 1) => Trans.ioProgRowEnv a acc requests q
  let nodes := fun q : Fin (records + 1) =>
    algebraMap K (IOField K) (D.orbitPoint q)
  have hnodes : Function.Injective nodes :=
    (algebraMap K (IOField K)).injective.comp (D.orbitPoint_injective hcap)
  have hcur := encodeEnvTrace_current_at_node
    (w := Trans.ioProgAIR.numTraceCols) rows nodes hnodes
    (algebraMap K (IOField K) D.ω)
    (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub i
  have hnext := encodeEnvTrace_next_at_mapped_orbit_node
    (w := Trans.ioProgAIR.numTraceCols) D rows nodes hnodes (fun _ => rfl)
    (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub i hi
  simp only [Trans.ioProgStep, Trans.tn, Reified.tc, Expr.eval]
  rw [hnext 0 (by norm_num [Trans.ioProgAIR_numTraceCols]),
    hcur 0 (by norm_num [Trans.ioProgAIR_numTraceCols]),
    hcur 1 (by norm_num [Trans.ioProgAIR_numTraceCols])]
  rfl

private theorem ioProg_term_encoded_eq
    (D : OrbitDomain K) (records : ℕ) (hcap : records + 1 ≤ 2 ^ D.h)
    (a : ℕ → RatFunc K) (acc : ℕ → IOField K) (requests : IOField K) :
    let rows := fun i : Fin (records + 1) => Trans.ioProgRowEnv a acc requests i
    let nodes := fun i : Fin (records + 1) =>
      algebraMap K (IOField K) (D.orbitPoint i)
    Trans.ioProgTerm.eval
        (envOfTrace (w := Trans.ioProgAIR.numTraceCols)
          (encodeEnvTrace (w := Trans.ioProgAIR.numTraceCols) rows nodes)
          (algebraMap K (IOField K) D.ω)
          (nodes (D.lastIndex (records + 1) (by omega)))
          (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub) =
      Trans.ioProgTerm.eval (Trans.ioProgRowEnv a acc requests records) := by
  dsimp only
  let last := D.lastIndex (records + 1) (by omega)
  have hlast : (last : ℕ) = records := by
    simp [last, OrbitDomain.lastIndex]
  simp only [Trans.ioProgTerm, Trans.pubv, Reified.tc, Expr.eval]
  rw [encodeEnvTrace_current_at_node
    (w := Trans.ioProgAIR.numTraceCols)
    (fun i : Fin (records + 1) => Trans.ioProgRowEnv a acc requests i)
    (fun i => algebraMap K (IOField K) (D.orbitPoint i))
    ((algebraMap K (IOField K)).injective.comp (D.orbitPoint_injective hcap))
    (algebraMap K (IOField K) D.ω)
    (Trans.ioProgRowEnv a acc requests 0).chal
    (Trans.ioProgRowEnv a acc requests 0).pub
    last 0 (by norm_num [Trans.ioProgAIR_numTraceCols])]
  simp [hlast, Trans.ioProgRowEnv, envOfTrace]

theorem ioProgSegmentedRAP_wholeTrace_iff
    (D : OrbitDomain K) (records : ℕ) (hcap : records + 1 ≤ 2 ^ D.h)
    (hExpPos : 1 ≤ D.h) (eDeg : ℕ)
    (a : ℕ → RatFunc K) (acc : ℕ → IOField K) (requests : IOField K) :
    let rows := fun i : Fin (records + 1) => Trans.ioProgRowEnv a acc requests i
    let nodes := fun i : Fin (records + 1) =>
      algebraMap K (IOField K) (D.orbitPoint i)
    (∀ kind,
      (airToRAP (kindSeg Trans.ioProgAIR kind)
        (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub
        eDeg D.h (algebraMap K (IOField K) D.ω)
        (algebraMap K (IOField K) D.βcoset)
        (PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records kind))
        (by
          intro hz
          exact D.βcoset_ne_zero ((algebraMap K (IOField K)).injective (by simpa using hz)))
        hExpPos).Satisfies (encodeEnvTrace rows nodes))
      ↔ IO.ProgIOSat a acc requests records := by
  dsimp only
  let rows := fun i : Fin (records + 1) => Trans.ioProgRowEnv a acc requests i
  let nodes := fun i : Fin (records + 1) =>
    algebraMap K (IOField K) (D.orbitPoint i)
  let P : Fin Trans.ioProgAIR.numTraceCols → (IOField K)[X] := encodeEnvTrace rows nodes
  have hboundary :
      (airToRAP (kindSeg Trans.ioProgAIR .boundary)
        (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub
        eDeg D.h (algebraMap K (IOField K) D.ω)
        (algebraMap K (IOField K) D.βcoset)
        (PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records .boundary))
        (by
          intro hz
          exact D.βcoset_ne_zero ((algebraMap K (IOField K)).injective (by simpa using hz)))
        hExpPos).Satisfies P
      ↔ Trans.ioProgInit.eval (Trans.ioProgRowEnv a acc requests 0) = 0 := by
    erw [airToRAP_satisfies_iff]
    constructor
    · intro h
      let first : Fin (records + 1) := ⟨0, by omega⟩
      have hx : nodes first ∈ PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records .boundary) := by
        rw [mem_liftedIO_boundaryDomain_iff D records]
        simp [nodes, first]
      have hi := h (nodes first) hx
        ⟨.boundary, Trans.ioProgInit⟩ (by rw [ioProg_boundary_seg]; simp)
      dsimp [P, rows, nodes, first] at hi
      rw [ioProg_init_encoded_eq D records hcap a acc requests] at hi
      exact hi
    · intro hi x hx c hc
      have hx' := (mem_liftedIO_boundaryDomain_iff D records x).1 hx
      rw [hx']
      dsimp [P, rows, nodes]
      have hc' : c = ⟨.boundary, Trans.ioProgInit⟩ := by
        simpa [ioProg_boundary_seg] using hc
      subst c
      rw [← D.orbitPoint_zero]
      rw [ioProg_init_encoded_eq D records hcap a acc requests]
      exact hi
  have htransition :
      (airToRAP (kindSeg Trans.ioProgAIR .transition)
        (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub
        eDeg D.h (algebraMap K (IOField K) D.ω)
        (algebraMap K (IOField K) D.βcoset)
        (PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records .transition))
        (by
          intro hz
          exact D.βcoset_ne_zero ((algebraMap K (IOField K)).injective (by simpa using hz)))
        hExpPos).Satisfies P
      ↔ ∀ i, i < records →
        Trans.ioProgStep.eval
          (Trans.twoRow (Trans.ioProgRowEnv a acc requests i)
            (Trans.ioProgRowEnv a acc requests (i + 1))) = 0 := by
    erw [airToRAP_satisfies_iff]
    constructor
    · intro h i hi
      let q : Fin (records + 1) := ⟨i, by omega⟩
      have hq : (q : ℕ) + 1 < records + 1 := by dsimp [q]; omega
      have hx : nodes q ∈ PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records .transition) :=
        (mem_liftedIO_transitionDomain_iff D records hcap (nodes q)).2
          ⟨q, hq, rfl⟩
      have hs := h (nodes q) hx
        ⟨.transition, Trans.ioProgStep⟩ (by rw [ioProg_transition_seg]; simp)
      dsimp [P, rows, nodes, q] at hs
      rw [ioProg_step_encoded_eq D records hcap a acc requests q hq] at hs
      simpa [q] using hs
    · intro hs x hx c hc
      obtain ⟨q, hq, rfl⟩ :=
        (mem_liftedIO_transitionDomain_iff D records hcap x).1 hx
      dsimp [P, rows, nodes]
      have hc' : c = ⟨.transition, Trans.ioProgStep⟩ := by
        simpa [ioProg_transition_seg] using hc
      subst c
      rw [ioProg_step_encoded_eq D records hcap a acc requests q hq]
      exact hs q (by omega)
  have hterminal :
      (airToRAP (kindSeg Trans.ioProgAIR .terminal)
        (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub
        eDeg D.h (algebraMap K (IOField K) D.ω)
        (algebraMap K (IOField K) D.βcoset)
        (PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records .terminal))
        (by
          intro hz
          exact D.βcoset_ne_zero ((algebraMap K (IOField K)).injective (by simpa using hz)))
        hExpPos).Satisfies P
      ↔ Trans.ioProgTerm.eval (Trans.ioProgRowEnv a acc requests records) = 0 := by
    erw [airToRAP_satisfies_iff]
    let last := D.lastIndex (records + 1) (by omega)
    have hx : nodes last ∈ PlusIOSegmentedFamily.liftFinsetToIO
        (PlusIOSegmentedFamily.ioBaseDomain D records .terminal) := by
      rw [mem_liftedIO_terminalDomain_iff D records]
      rfl
    constructor
    · intro h
      have ht := h (nodes last) hx
        ⟨.terminal, Trans.ioProgTerm⟩ (by rw [ioProg_terminal_seg]; simp)
      dsimp [P, rows, nodes, last] at ht
      rw [ioProg_term_encoded_eq D records hcap a acc requests] at ht
      exact ht
    · intro ht x hx' c hc
      have hxterm := (mem_liftedIO_terminalDomain_iff D records x).1 hx'
      have hxnode : x = nodes last := hxterm
      rw [hxnode]
      dsimp [P, rows, nodes, last]
      have hc' : c = ⟨.terminal, Trans.ioProgTerm⟩ := by
        simpa [ioProg_terminal_seg] using hc
      subst c
      rw [ioProg_term_encoded_eq D records hcap a acc requests]
      exact ht
  constructor
  · intro h
    exact (Trans.reified_io_prog_sound records).2
      ⟨hboundary.mp (h .boundary), htransition.mp (h .transition),
        hterminal.mp (h .terminal)⟩
  · intro h kind
    have hg := (Trans.reified_io_prog_sound records).1 h
    cases kind with
    | boundary => exact hboundary.mpr hg.1
    | transition => exact htransition.mpr hg.2.1
    | terminal => exact hterminal.mpr hg.2.2
    | row =>
        erw [airToRAP_satisfies_iff]
        intro x hx c hc
        rw [ioProg_row_seg] at hc
        simp at hc

private theorem ioMem_init_encoded_eq
    (D : OrbitDomain K) (records : ℕ) (hcap : records + 1 ≤ 2 ^ D.h)
    (b μ : ℕ → RatFunc K) (acc : ℕ → IOField K)
    (responses outMem : IOField K) :
    let rows := fun i : Fin (records + 1) =>
      Trans.ioMemRowEnv b μ acc responses outMem i
    let nodes := fun i : Fin (records + 1) =>
      algebraMap K (IOField K) (D.orbitPoint i)
    Trans.ioMemInit.eval
        (envOfTrace (w := Trans.ioMemAIR.numTraceCols)
          (encodeEnvTrace (w := Trans.ioMemAIR.numTraceCols) rows nodes)
          (algebraMap K (IOField K) D.ω)
          (nodes ⟨0, by omega⟩) (rows ⟨0, by omega⟩).chal
          (rows ⟨0, by omega⟩).pub) =
      Trans.ioMemInit.eval (Trans.ioMemRowEnv b μ acc responses outMem 0) := by
  dsimp only
  simp only [Trans.ioMemInit, Reified.tc, Trans.pubv, Expr.eval]
  rw [encodeEnvTrace_current_at_node
    (w := Trans.ioMemAIR.numTraceCols)
    (fun i : Fin (records + 1) => Trans.ioMemRowEnv b μ acc responses outMem i)
    (fun i => algebraMap K (IOField K) (D.orbitPoint i))
    ((algebraMap K (IOField K)).injective.comp (D.orbitPoint_injective hcap))
    (algebraMap K (IOField K) D.ω)
    (Trans.ioMemRowEnv b μ acc responses outMem 0).chal
    (Trans.ioMemRowEnv b μ acc responses outMem 0).pub
    ⟨0, by omega⟩ 0 (by norm_num [Trans.ioMemAIR_numTraceCols])]
  rfl

private theorem ioMem_step_encoded_eq
    (D : OrbitDomain K) (records : ℕ) (hcap : records + 1 ≤ 2 ^ D.h)
    (b μ : ℕ → RatFunc K) (acc : ℕ → IOField K)
    (responses outMem : IOField K)
    (i : Fin (records + 1)) (hi : (i : ℕ) + 1 < records + 1) :
    let rows := fun q : Fin (records + 1) =>
      Trans.ioMemRowEnv b μ acc responses outMem q
    let nodes := fun q : Fin (records + 1) =>
      algebraMap K (IOField K) (D.orbitPoint q)
    Trans.ioMemStep.eval
        (envOfTrace (w := Trans.ioMemAIR.numTraceCols)
          (encodeEnvTrace (w := Trans.ioMemAIR.numTraceCols) rows nodes)
          (algebraMap K (IOField K) D.ω)
          (nodes i) (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub) =
      Trans.ioMemStep.eval
        (Trans.twoRow (Trans.ioMemRowEnv b μ acc responses outMem i)
          (Trans.ioMemRowEnv b μ acc responses outMem ((i : ℕ) + 1))) := by
  dsimp only
  let rows := fun q : Fin (records + 1) =>
    Trans.ioMemRowEnv b μ acc responses outMem q
  let nodes := fun q : Fin (records + 1) =>
    algebraMap K (IOField K) (D.orbitPoint q)
  have hnodes : Function.Injective nodes :=
    (algebraMap K (IOField K)).injective.comp (D.orbitPoint_injective hcap)
  have hcur := encodeEnvTrace_current_at_node
    (w := Trans.ioMemAIR.numTraceCols) rows nodes hnodes
    (algebraMap K (IOField K) D.ω)
    (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub i
  have hnext := encodeEnvTrace_next_at_mapped_orbit_node
    (w := Trans.ioMemAIR.numTraceCols) D rows nodes hnodes (fun _ => rfl)
    (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub i hi
  simp only [Trans.ioMemStep, Trans.tn, Reified.tc, Expr.eval]
  rw [hnext 0 (by norm_num [Trans.ioMemAIR_numTraceCols]),
    hcur 0 (by norm_num [Trans.ioMemAIR_numTraceCols]),
    hcur 2 (by norm_num [Trans.ioMemAIR_numTraceCols]),
    hcur 1 (by norm_num [Trans.ioMemAIR_numTraceCols])]
  rfl

private theorem ioMem_term_encoded_eq
    (D : OrbitDomain K) (records : ℕ) (hcap : records + 1 ≤ 2 ^ D.h)
    (b μ : ℕ → RatFunc K) (acc : ℕ → IOField K)
    (responses outMem : IOField K) :
    let rows := fun i : Fin (records + 1) =>
      Trans.ioMemRowEnv b μ acc responses outMem i
    let nodes := fun i : Fin (records + 1) =>
      algebraMap K (IOField K) (D.orbitPoint i)
    Trans.ioMemTerm.eval
        (envOfTrace (w := Trans.ioMemAIR.numTraceCols)
          (encodeEnvTrace (w := Trans.ioMemAIR.numTraceCols) rows nodes)
          (algebraMap K (IOField K) D.ω)
          (nodes (D.lastIndex (records + 1) (by omega)))
          (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub) =
      Trans.ioMemTerm.eval
        (Trans.ioMemRowEnv b μ acc responses outMem records) := by
  dsimp only
  let last := D.lastIndex (records + 1) (by omega)
  have hlast : (last : ℕ) = records := by
    simp [last, OrbitDomain.lastIndex]
  simp only [Trans.ioMemTerm, Trans.pubv, Reified.tc, Expr.eval]
  rw [encodeEnvTrace_current_at_node
    (w := Trans.ioMemAIR.numTraceCols)
    (fun i : Fin (records + 1) => Trans.ioMemRowEnv b μ acc responses outMem i)
    (fun i => algebraMap K (IOField K) (D.orbitPoint i))
    ((algebraMap K (IOField K)).injective.comp (D.orbitPoint_injective hcap))
    (algebraMap K (IOField K) D.ω)
    (Trans.ioMemRowEnv b μ acc responses outMem 0).chal
    (Trans.ioMemRowEnv b μ acc responses outMem 0).pub
    last 0 (by norm_num [Trans.ioMemAIR_numTraceCols])]
  simp [hlast, Trans.ioMemRowEnv, envOfTrace]

theorem ioMemSegmentedRAP_wholeTrace_iff
    (D : OrbitDomain K) (records : ℕ) (hcap : records + 1 ≤ 2 ^ D.h)
    (hExpPos : 1 ≤ D.h) (eDeg : ℕ)
    (b μ : ℕ → RatFunc K) (acc : ℕ → IOField K)
    (responses outMem : IOField K) :
    let rows := fun i : Fin (records + 1) =>
      Trans.ioMemRowEnv b μ acc responses outMem i
    let nodes := fun i : Fin (records + 1) =>
      algebraMap K (IOField K) (D.orbitPoint i)
    (∀ kind,
      (airToRAP (kindSeg Trans.ioMemAIR kind)
        (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub
        eDeg D.h (algebraMap K (IOField K) D.ω)
        (algebraMap K (IOField K) D.βcoset)
        (PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records kind))
        (by
          intro hz
          exact D.βcoset_ne_zero
            ((algebraMap K (IOField K)).injective (by simpa using hz)))
        hExpPos).Satisfies (encodeEnvTrace rows nodes))
      ↔ IO.MemIOSat b μ acc responses outMem records := by
  dsimp only
  let rows := fun i : Fin (records + 1) =>
    Trans.ioMemRowEnv b μ acc responses outMem i
  let nodes := fun i : Fin (records + 1) =>
    algebraMap K (IOField K) (D.orbitPoint i)
  let P : Fin Trans.ioMemAIR.numTraceCols → (IOField K)[X] := encodeEnvTrace rows nodes
  have hboundary :
      (airToRAP (kindSeg Trans.ioMemAIR .boundary)
        (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub
        eDeg D.h (algebraMap K (IOField K) D.ω)
        (algebraMap K (IOField K) D.βcoset)
        (PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records .boundary))
        (by
          intro hz
          exact D.βcoset_ne_zero
            ((algebraMap K (IOField K)).injective (by simpa using hz)))
        hExpPos).Satisfies P
      ↔ Trans.ioMemInit.eval
        (Trans.ioMemRowEnv b μ acc responses outMem 0) = 0 := by
    erw [airToRAP_satisfies_iff]
    constructor
    · intro h
      let first : Fin (records + 1) := ⟨0, by omega⟩
      have hx : nodes first ∈ PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records .boundary) := by
        rw [mem_liftedIO_boundaryDomain_iff D records]
        simp [nodes, first]
      have hi := h (nodes first) hx
        ⟨.boundary, Trans.ioMemInit⟩ (by rw [ioMem_boundary_seg]; simp)
      dsimp [P, rows, nodes, first] at hi
      rw [ioMem_init_encoded_eq D records hcap b μ acc responses outMem] at hi
      exact hi
    · intro hi x hx c hc
      have hx' := (mem_liftedIO_boundaryDomain_iff D records x).1 hx
      rw [hx']
      dsimp [P, rows, nodes]
      have hc' : c = ⟨.boundary, Trans.ioMemInit⟩ := by
        simpa [ioMem_boundary_seg] using hc
      subst c
      rw [← D.orbitPoint_zero]
      rw [ioMem_init_encoded_eq D records hcap b μ acc responses outMem]
      exact hi
  have htransition :
      (airToRAP (kindSeg Trans.ioMemAIR .transition)
        (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub
        eDeg D.h (algebraMap K (IOField K) D.ω)
        (algebraMap K (IOField K) D.βcoset)
        (PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records .transition))
        (by
          intro hz
          exact D.βcoset_ne_zero
            ((algebraMap K (IOField K)).injective (by simpa using hz)))
        hExpPos).Satisfies P
      ↔ ∀ i, i < records →
        Trans.ioMemStep.eval
          (Trans.twoRow (Trans.ioMemRowEnv b μ acc responses outMem i)
            (Trans.ioMemRowEnv b μ acc responses outMem (i + 1))) = 0 := by
    erw [airToRAP_satisfies_iff]
    constructor
    · intro h i hi
      let q : Fin (records + 1) := ⟨i, by omega⟩
      have hq : (q : ℕ) + 1 < records + 1 := by dsimp [q]; omega
      have hx : nodes q ∈ PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records .transition) :=
        (mem_liftedIO_transitionDomain_iff D records hcap (nodes q)).2
          ⟨q, hq, rfl⟩
      have hs := h (nodes q) hx
        ⟨.transition, Trans.ioMemStep⟩ (by rw [ioMem_transition_seg]; simp)
      dsimp [P, rows, nodes, q] at hs
      rw [ioMem_step_encoded_eq D records hcap b μ acc responses outMem q hq] at hs
      simpa [q] using hs
    · intro hs x hx c hc
      obtain ⟨q, hq, rfl⟩ :=
        (mem_liftedIO_transitionDomain_iff D records hcap x).1 hx
      dsimp [P, rows, nodes]
      have hc' : c = ⟨.transition, Trans.ioMemStep⟩ := by
        simpa [ioMem_transition_seg] using hc
      subst c
      rw [ioMem_step_encoded_eq D records hcap b μ acc responses outMem q hq]
      exact hs q (by omega)
  have hterminal :
      (airToRAP (kindSeg Trans.ioMemAIR .terminal)
        (rows ⟨0, by omega⟩).chal (rows ⟨0, by omega⟩).pub
        eDeg D.h (algebraMap K (IOField K) D.ω)
        (algebraMap K (IOField K) D.βcoset)
        (PlusIOSegmentedFamily.liftFinsetToIO
          (PlusIOSegmentedFamily.ioBaseDomain D records .terminal))
        (by
          intro hz
          exact D.βcoset_ne_zero
            ((algebraMap K (IOField K)).injective (by simpa using hz)))
        hExpPos).Satisfies P
      ↔ Trans.ioMemTerm.eval
        (Trans.ioMemRowEnv b μ acc responses outMem records) = 0 := by
    erw [airToRAP_satisfies_iff]
    let last := D.lastIndex (records + 1) (by omega)
    have hx : nodes last ∈ PlusIOSegmentedFamily.liftFinsetToIO
        (PlusIOSegmentedFamily.ioBaseDomain D records .terminal) := by
      rw [mem_liftedIO_terminalDomain_iff D records]
      rfl
    constructor
    · intro h
      have ht := h (nodes last) hx
        ⟨.terminal, Trans.ioMemTerm⟩ (by rw [ioMem_terminal_seg]; simp)
      dsimp [P, rows, nodes, last] at ht
      rw [ioMem_term_encoded_eq D records hcap b μ acc responses outMem] at ht
      exact ht
    · intro ht x hx' c hc
      have hxterm := (mem_liftedIO_terminalDomain_iff D records x).1 hx'
      have hxnode : x = nodes last := hxterm
      rw [hxnode]
      dsimp [P, rows, nodes, last]
      have hc' : c = ⟨.terminal, Trans.ioMemTerm⟩ := by
        simpa [ioMem_terminal_seg] using hc
      subst c
      rw [ioMem_term_encoded_eq D records hcap b μ acc responses outMem]
      exact ht
  constructor
  · intro h
    exact (Trans.reified_io_mem_sound records).2
      ⟨hboundary.mp (h .boundary), htransition.mp (h .transition),
        hterminal.mp (h .terminal)⟩
  · intro h kind
    have hg := (Trans.reified_io_mem_sound records).1 h
    cases kind with
    | boundary => exact hboundary.mpr hg.1
    | transition => exact htransition.mpr hg.2.1
    | terminal => exact hterminal.mpr hg.2.2
    | row =>
        erw [airToRAP_satisfies_iff]
        intro x hx c hc
        rw [ioMem_row_seg] at hc
        simp at hc

/-! ## The two exact IO components of one same-execution assignment -/

namespace PlusIOSameExecutionAssignment

variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

theorem computeIORAP_wholeTrace_iff (A : PlusIOSameExecutionAssignment R p) :
    (∀ kind, (R.computeIORAP kind).Satisfies A.computeIOTrace)
      ↔
    IO.ProgIOSat
      (fun i => SetEq.RLC (IO.listExt R.problem.exec.derivedRequestIO i))
      A.exactIO.progAcc R.requests R.problem.exec.derivedRequestIO.length := by
  let a := fun i => SetEq.RLC (IO.listExt R.problem.exec.derivedRequestIO i)
  let rows := fun i : Fin (R.problem.exec.derivedRequestIO.length + 1) =>
    Trans.ioProgRowEnv a A.exactIO.progAcc R.requests i
  have hchal :
      (R.progIOParams).chalVal = (rows ⟨0, by omega⟩).chal := by
    funext j
    rfl
  have hpub :
      (R.progIOParams).pubVal = (rows ⟨0, by omega⟩).pub := by
    funext j
    cases j <;> rfl
  simp only [PlusIOSegmentedFamily.computeIORAP, SegmentedRAPParams.rap,
    PlusIOSameExecutionAssignment.computeIOTrace]
  rw [hchal, hpub]
  have hg := ioProgSegmentedRAP_wholeTrace_iff
    R.problem.cfg.orbit R.problem.exec.derivedRequestIO.length R.progIO_capacity
    R.problem.cfg.orbit_h_pos R.problem.cfg.eDeg
    a A.exactIO.progAcc R.requests
  constructor
  · intro h
    apply hg.mp
    intro kind
    have hk := h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    exact hk
  · intro h kind
    have hk := hg.mpr h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    exact hk

theorem memoryIORAP_wholeTrace_iff (A : PlusIOSameExecutionAssignment R p) :
    (∀ kind, (R.memoryIORAP kind).Satisfies A.memoryIOTrace)
      ↔
    IO.MemIOSat
      (fun i => SetEq.RLC (IO.listExt R.problem.exec.derivedResponseIO i))
      (IO.castμ (𝔽 := K) A.exactIO.multiplicity)
      A.exactIO.memAcc R.responses R.outMem
      R.problem.exec.derivedResponseIO.length := by
  let b := fun i => SetEq.RLC (IO.listExt R.problem.exec.derivedResponseIO i)
  let μ := IO.castμ (𝔽 := K) A.exactIO.multiplicity
  let rows := fun i : Fin (R.problem.exec.derivedResponseIO.length + 1) =>
    Trans.ioMemRowEnv b μ A.exactIO.memAcc R.responses R.outMem i
  have hchal :
      (R.memIOParams).chalVal = (rows ⟨0, by omega⟩).chal := by
    funext j
    rfl
  have hpub :
      (R.memIOParams).pubVal = (rows ⟨0, by omega⟩).pub := by
    funext j
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  simp only [PlusIOSegmentedFamily.memoryIORAP, SegmentedRAPParams.rap,
    PlusIOSameExecutionAssignment.memoryIOTrace]
  rw [hchal, hpub]
  have hg := ioMemSegmentedRAP_wholeTrace_iff
    R.problem.cfg.orbit R.problem.exec.derivedResponseIO.length R.memIO_capacity
    R.problem.cfg.orbit_h_pos R.problem.cfg.eDeg
    b μ A.exactIO.memAcc R.responses R.outMem
  constructor
  · intro h
    apply hg.mp
    intro kind
    have hk := h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    exact hk
  · intro h kind
    have hk := hg.mpr h kind
    erw [airToRAP_satisfies_iff] at hk ⊢
    exact hk

/-- The six load-bearing obligations for one assignment: the two P4 table families, the two exact
walk certificates, and the two concrete IO accumulator predicates. -/
def SixConcreteObligations (A : PlusIOSameExecutionAssignment R p) : Prop :=
  (∀ kind, (R.computeTableRAP kind).Satisfies A.computeTableTrace) ∧
  (∀ kind, (R.memoryTableRAP kind).Satisfies A.memoryTableTrace) ∧
  A.ComputeWalkCertificate ∧
  A.MemoryWalkCertificate ∧
  IO.ProgIOSat
    (fun i => SetEq.RLC (IO.listExt R.problem.exec.derivedRequestIO i))
    A.exactIO.progAcc R.requests R.problem.exec.derivedRequestIO.length ∧
  IO.MemIOSat
    (fun i => SetEq.RLC (IO.listExt R.problem.exec.derivedResponseIO i))
    (IO.castμ (𝔽 := K) A.exactIO.multiplicity)
    A.exactIO.memAcc R.responses R.outMem
    R.problem.exec.derivedResponseIO.length

/-- `PlusIOSameExecutionAssignment.Satisfies` is exactly the six concrete table/walk/IO
obligations.  No padded or full-coset rows occur in this statement. -/
theorem satisfies_iff_six_concrete_obligations
    (A : PlusIOSameExecutionAssignment R p) :
    A.Satisfies ↔ A.SixConcreteObligations := by
  unfold PlusIOSameExecutionAssignment.Satisfies SixConcreteObligations
  rw [computeWalkRAP_wholeTrace_iff A, memoryWalkRAP_wholeTrace_iff A,
    computeIORAP_wholeTrace_iff A, memoryIORAP_wholeTrace_iff A]

/-- Assemble one satisfying assignment from the paired P4 table certificate, two exact
proof-carrying walk assignments, and one `ExactDerivedIOAssignment`. -/
theorem exists_satisfies_of_P4_walks_IO
    (hP4 : ExactCanonicalRAPSameExecutionCertificate R.problem)
    (computeWalk memoryWalk : WalkAssignment K)
    (hComputeWalk :
      Walk.WalkSat
        (Walk.curCol R.computeNodeVal R.computeWalkRows)
        (Walk.chldCol R.computeNodeVal R.computeWalkRows)
        (Walk.foCol R.computeWalkRows)
        computeWalk.ln computeWalk.count computeWalk.acc
        R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha
        R.problem.cfg.compRows ∧
      computeWalk.acc R.problem.cfg.compRows = 0)
    (hMemoryWalk :
      Walk.WalkSat
        (Walk.curCol R.memoryNodeVal R.memoryWalkRows)
        (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
        (Walk.foCol R.memoryWalkRows)
        memoryWalk.ln memoryWalk.count memoryWalk.acc
        R.memoryWalkAlpha R.memoryWalkSeed
        (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
        R.problem.cfg.memRows ∧
      memoryWalk.acc R.problem.cfg.memRows = 0)
    (io : ExactDerivedIOAssignment R p) :
    ∃ A : PlusIOSameExecutionAssignment R p, A.Satisfies := by
  obtain ⟨⟨ex, hcomp⟩, ⟨g, hmem⟩⟩ := hP4
  let A : PlusIOSameExecutionAssignment R p :=
    { computeTableAux := ex
      memoryTableAux := g
      computeWalk := computeWalk
      memoryWalk := memoryWalk
      exactIO := io }
  refine ⟨A, (satisfies_iff_six_concrete_obligations A).2 ?_⟩
  exact ⟨hcomp, hmem, hComputeWalk, hMemoryWalk, io.progSat, io.memSat⟩

end PlusIOSameExecutionAssignment

/-! ## Honest forest-walk completeness connector -/

private theorem flatBlks_chldCol_exact {LT : Type*}
    (nodeVal : Walk.NTree LT → K) (W : List (Walk.NTree LT)) (n : ℕ) :
    Walk.flatBlks (Walk.chldCol nodeVal W) (Walk.foCol W) n =
      ((W.take n).flatMap Walk.NTree.children).map nodeVal := by
  apply Walk.lpoly_inj 2
  · rw [Walk.flatBlks_length, List.length_map, Walk.Sf_foCol]
  · rw [← Walk.queueSum_eq_gen, Walk.queueSum_eq]

private theorem curVals_curCol_full_exact {LT : Type*}
    (nodeVal : Walk.NTree LT → K) (W : List (Walk.NTree LT)) :
    Walk.curVals (Walk.curCol nodeVal W) W.length = W.map nodeVal := by
  apply Walk.lpoly_inj 1
  · rw [Walk.curVals_length, List.length_map]
  · rw [← Walk.nodeListP_eq_lpoly_gen, ← Walk.nodeListP_eq_lpoly]

private theorem curVals_curCol_prefix_exact {LT : Type*}
    (nodeVal : Walk.NTree LT → K) (l rest : List (Walk.NTree LT)) :
    Walk.curVals (Walk.curCol nodeVal (l ++ rest)) l.length = l.map nodeVal := by
  apply List.ext_getElem (by simp)
  intro j hj hj2
  simp only [Walk.curVals, List.getElem_map, List.getElem_range]
  have hjl : j < l.length := by simpa [Walk.curVals] using hj
  unfold Walk.curCol
  rw [Nat.add_sub_cancel, List.getElem?_append_left hjl,
    List.getElem?_eq_getElem hjl]
  rfl

/-- The missing forward forest analogue of `Walk.bfs_isFullBFT`: an honest nonempty aggregate
BFS forest satisfies the exact multi-root polynomial identity used by `forest_out_zero_iff`. -/
theorem bfsForest_isForestFullBFT_exact {LT : Type*}
    (nodeVal : Walk.NTree LT → K) (l : List (Walk.NTree LT)) (hne : l ≠ []) :
    Walk.IsForestFullBFT
      (Walk.curCol nodeVal (Walk.bfsForest l))
      (Walk.chldCol nodeVal (Walk.bfsForest l))
      (Walk.foCol (Walk.bfsForest l))
      l.length (Walk.bfsForest l).length := by
  have hsplit :
      Walk.bfsForest l = l ++ (Walk.bfsForest l).flatMap Walk.NTree.children :=
    Walk.bfsForest_eq_append_flatMap l hne
  have hpre :
      Walk.curVals (Walk.curCol nodeVal (Walk.bfsForest l)) l.length =
        l.map nodeVal := by
    conv_lhs => rw [hsplit]
    exact curVals_curCol_prefix_exact nodeVal l _
  unfold Walk.IsForestFullBFT
  rw [Walk.nodeListP_eq_lpoly_gen, Walk.forestQueueP_eq_lpoly,
    curVals_curCol_full_exact, flatBlks_chldCol_exact, List.take_length, hpre]
  congr 1
  conv_lhs => rw [hsplit]
  rw [List.map_append]

namespace PlusIOSameExecutionAssignment

variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

/-- Walk completeness constructs a closed compute-walk assignment for the authoritative exact
compute BFS tree. -/
theorem computeWalkCertificate_exists :
    ∃ W : WalkAssignment K,
      Walk.WalkSat
        (Walk.curCol R.computeNodeVal R.computeWalkRows)
        (Walk.chldCol R.computeNodeVal R.computeWalkRows)
        (Walk.foCol R.computeWalkRows)
        W.ln W.count W.acc
        R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha
        R.problem.cfg.compRows ∧
      W.acc R.problem.cfg.compRows = 0 := by
  obtain ⟨ln, count, acc, hsat⟩ :=
    Walk.walkSat_exists
      (Walk.curCol R.computeNodeVal R.computeWalkRows)
      (Walk.chldCol R.computeNodeVal R.computeWalkRows)
      (Walk.foCol R.computeWalkRows)
      R.computeWalkAlpha R.computeWalkSeed R.computeWalkAlpha
      R.problem.cfg.compRows_pos
  have hbft :
      Walk.IsFullBFT
        (Walk.curCol R.computeNodeVal R.computeWalkRows)
        (Walk.chldCol R.computeNodeVal R.computeWalkRows)
        (Walk.foCol R.computeWalkRows) R.problem.cfg.compRows := by
    unfold Walk.IsFullBFT
    simpa [PlusIOSegmentedFamily.computeWalkRows,
      R.problem.exec.compute_bfs_length] using
      (Walk.bfs_isFullBFT
        (nodeVal := R.computeNodeVal) R.problem.exec.computeTree)
  have hout : acc R.problem.cfg.compRows = 0 :=
    Walk.walk_completeness hsat rfl rfl hbft
  exact ⟨{ ln := ln, count := count, acc := acc }, hsat, hout⟩

/-- Forest walk completeness constructs a closed memory-walk assignment for the authoritative
nonempty exact memory forest. -/
theorem memoryWalkCertificate_exists :
    ∃ W : WalkAssignment K,
      Walk.WalkSat
        (Walk.curCol R.memoryNodeVal R.memoryWalkRows)
        (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
        (Walk.foCol R.memoryWalkRows)
        W.ln W.count W.acc
        R.memoryWalkAlpha R.memoryWalkSeed
        (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
        R.problem.cfg.memRows ∧
      W.acc R.problem.cfg.memRows = 0 := by
  obtain ⟨ln, count, acc, hsat⟩ :=
    Walk.walkSat_exists
      (Walk.curCol R.memoryNodeVal R.memoryWalkRows)
      (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
      (Walk.foCol R.memoryWalkRows)
      R.memoryWalkAlpha R.memoryWalkSeed
      (R.memoryWalkAlpha ^ R.problem.cfg.kMem)
      R.problem.cfg.memRows_pos
  have hbft :
      Walk.IsForestFullBFT
        (Walk.curCol R.memoryNodeVal R.memoryWalkRows)
        (Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
        (Walk.foCol R.memoryWalkRows)
        R.problem.cfg.kMem R.problem.cfg.memRows := by
    simpa [PlusIOSegmentedFamily.memoryWalkRows,
      R.problem.exec.memory_root_count, R.problem.exec.memory_bfs_length] using
      (bfsForest_isForestFullBFT_exact
        R.memoryNodeVal R.problem.exec.memoryForest
        R.problem.exec.memoryForest_nonempty)
  have hout : acc R.problem.cfg.memRows = 0 := by
    rw [Walk.forest_out_zero_iff hsat rfl rfl]
    exact congrArg (Polynomial.eval R.memoryWalkAlpha) hbft
  exact ⟨{ ln := ln, count := count, acc := acc }, hsat, hout⟩

/-- Full constructive assembly: the paired P4 table certificate and one exact derived-IO
assignment suffice; both closed walk assignments are generated by honest BFS completeness. -/
theorem exists_satisfies_of_P4_IO
    (hP4 : ExactCanonicalRAPSameExecutionCertificate R.problem)
    (io : ExactDerivedIOAssignment R p) :
    ∃ A : PlusIOSameExecutionAssignment R p, A.Satisfies := by
  obtain ⟨computeWalk, hComputeWalk⟩ :=
    computeWalkCertificate_exists (R := R)
  obtain ⟨memoryWalk, hMemoryWalk⟩ :=
    memoryWalkCertificate_exists (R := R)
  exact exists_satisfies_of_P4_walks_IO
    hP4 computeWalk memoryWalk hComputeWalk hMemoryWalk io

/-- A chained exact execution supplies the paired P4 table certificate; together with an explicit
derived-IO assignment this constructs a satisfying six-component assignment. -/
theorem exists_satisfies_of_chained_IO
    (h : ChainedSemanticExactLanguage R.problem.cfg R.problem.exec)
    (io : ExactDerivedIOAssignment R p) :
    ∃ A : PlusIOSameExecutionAssignment R p, A.Satisfies := by
  have hP4 : ExactCanonicalRAPSameExecutionCertificate R.problem := by
    simpa [ExactCanonicalRAPSameExecutionCertificate,
      exactCanonicalProgParams, exactCanonicalMemParams,
      exactCanonicalEncodeProg, exactCanonicalEncodeMem,
      ComputeExecutionSegmentedRAPSatisfies,
      MemoryExecutionSegmentedRAPSatisfies,
      ComputeSegmentedRAPSatisfies, MemorySegmentedRAPSatisfies,
      SegmentedRAPParams.rap,
      SegmentedRAPParams.ofComputeConfig,
      SegmentedRAPParams.ofMemoryConfig] using h.segmentedRAP
  exact exists_satisfies_of_P4_IO hP4 io

end PlusIOSameExecutionAssignment

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.walkSegmentedRAP_wholeTrace_iff
#print axioms Nock.NockVMROM.Thm54.ioProgSegmentedRAP_wholeTrace_iff
#print axioms Nock.NockVMROM.Thm54.ioMemSegmentedRAP_wholeTrace_iff
#print axioms Nock.NockVMROM.Thm54.PlusIOSameExecutionAssignment.satisfies_iff_six_concrete_obligations
#print axioms Nock.NockVMROM.Thm54.PlusIOSameExecutionAssignment.exists_satisfies_of_P4_IO
#print axioms Nock.NockVMROM.Thm54.PlusIOSameExecutionAssignment.exists_satisfies_of_chained_IO
