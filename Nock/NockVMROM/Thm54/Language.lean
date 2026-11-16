import Nock.NockVMROM.Thm54.Execution
import Nock.NockVMROM.Thm54.RecordBridge

/-!
# Exact Theorem 5.4 execution language

Flat rows and both IO lists are functions of the authoritative tree/forest:
there are no independent table rows and no independent encoded IO fields.

`ExactLanguage` is the honest field-table layer: it uses the paper's multiplicity-sensitive
`IO.LmIO` on the canonical encoded records.  `StrongExactLanguage` exposes the separate `IO.LIO`
strengthening used by the uniqueness-sensitive IO argument.
-/

namespace Nock.NockVMROM.Thm54

open scoped Classical

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

namespace ExactExecution

/-! ## Canonical IO projections -/

/-- Raw table requests extracted, in BFS row order, from the authoritative compute tree.
Each row uses the opcode-active request prefix, so slot order and state `regs` arity have one
source of truth; active zero-valued records are not confused with inactive padding. -/
def rawRequests {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (ComputeTable.MemRec K) :=
  exec.computeRows.flatMap fun row =>
    NockVM.activeRequestRecords row.2.2.1

/-- Raw table responses extracted, in BFS row order, from the authoritative memory forest.
Rows with `ver = true` emit records; honest generators set
`ver := (st = read_root)`. -/
def rawResponses {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (ComputeTable.MemRec K) :=
  exec.memoryRows.flatMap fun row =>
    MemoryTable.responseRecords row.2.2

/-- The exact encoded compute IO.  Encoding is applied only after canonical raw extraction: each
compute record carries the Nock axis (`V_comp`), and the single Form R encode writes `(T, C')` at
the configuration's `λ` (`cfg.challenges.lam`).  Memory rows already carry `(T, C')`, so
`derivedResponseIO` reads them. -/
noncomputable def derivedRequestIO {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (Fin 9 → K) :=
  exec.rawRequests.map (fun r => NockVM.encRecFormR r cfg.challenges.lam)

/-- The exact encoded memory IO.  Encoding is applied only after canonical raw extraction. -/
def derivedResponseIO {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (Fin 9 → K) :=
  exec.memoryRows.flatMap fun row =>
    if row.2.2.ver then [NockVM.encRecC row.2.2.mem row.2.2.cprime] else []

/-- Unfolding of the canonical raw compute-request projection. -/
theorem rawRequests_eq_computeRows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.rawRequests =
      exec.computeRows.flatMap
        (fun row => NockVM.activeRequestRecords row.2.2.1) :=
  rfl

/-- Unfolding of the canonical raw memory-response projection. -/
theorem rawResponses_eq_memoryRows {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.rawResponses =
      exec.memoryRows.flatMap
        (fun row => MemoryTable.responseRecords row.2.2) :=
  rfl

/-- The encoded request IO is the single Form R encode of the canonical row extraction. -/
theorem derivedRequestIO_eq_computeRows {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    exec.derivedRequestIO =
      (exec.computeRows.flatMap
        (fun row => NockVM.activeRequestRecords row.2.2.1)).map
        (fun r => NockVM.encRecFormR r cfg.challenges.lam) :=
  rfl

/-- The encoded response IO is `encRecC` on `ver`-selected rows (form R `C'`). -/
theorem derivedResponseIO_eq_memoryRows {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    exec.derivedResponseIO =
      exec.memoryRows.flatMap fun row =>
        if row.2.2.ver then [NockVM.encRecC row.2.2.mem row.2.2.cprime] else [] :=
  rfl

/-- Each `ver` row contributes at most one response, so the encoded list is
no longer than the memory table. -/
theorem derivedResponseIO_length_le {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    exec.derivedResponseIO.length ≤ exec.memoryRows.length := by
  rw [derivedResponseIO_eq_memoryRows]
  induction exec.memoryRows with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    by_cases hver : a.2.2.ver = true
    · rw [if_pos hver, List.length_singleton]
      omega
    · rw [if_neg hver, List.length_nil, Nat.zero_add]
      exact Nat.le_trans ih (Nat.le_succ _)

/-- Row-level memory rows store `(T, C')` (`BindMemRow`); `C'` is not a function of the stored
record in general (`T = λ^m` forgets `a`).  On an execution where it is — honest traces, by unique
timestamps — `cprimeOf` reads it back from the record. -/
def CprimeCoherent {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  ∀ row ∈ exec.memoryRows, ∀ row' ∈ exec.memoryRows,
    row.2.2.mem = row'.2.2.mem → row.2.2.cprime = row'.2.2.cprime

/-- The `C'` stored beside a record on some memory row (`1`, the `Pub.cprime` default, if none). -/
noncomputable def cprimeOf {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (m : ComputeTable.MemRec K) : K :=
  if h : ∃ row ∈ exec.memoryRows, row.2.2.mem = m then (Classical.choose h).2.2.cprime else 1

theorem cprime_eq_cprimeOf {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hC : exec.CprimeCoherent) :
    ∀ row ∈ exec.memoryRows, row.2.2.cprime = exec.cprimeOf row.2.2.mem := by
  intro row hrow
  have h : ∃ r ∈ exec.memoryRows, r.2.2.mem = row.2.2.mem := ⟨row, hrow, rfl⟩
  unfold cprimeOf
  rw [dif_pos h]
  obtain ⟨hmem, heq⟩ := Classical.choose_spec h
  exact hC row hrow _ hmem heq.symm

/-- Rows whose `C'` is a function of the stored record are coherent. -/
theorem cprimeCoherent_of_fun {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (cp : ComputeTable.MemRec K → K)
    (h : ∀ row ∈ exec.memoryRows, row.2.2.cprime = cp row.2.2.mem) : exec.CprimeCoherent := by
  intro row hrow row' hrow' hmem
  rw [h row hrow, h row' hrow', hmem]

/-- The `C' = 1` placeholder rows (pre-row-level fixtures) are coherent. -/
theorem cprimeCoherent_of_cprime_one {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hC : ∀ row ∈ exec.memoryRows, row.2.2.cprime = 1) : exec.CprimeCoherent := by
  intro row hrow row' hrow' _
  rw [hC row hrow, hC row' hrow']

/-- On a coherent execution the encoded response IO is `encRecC · (cprimeOf ·)` of the raw
responses. -/
theorem derivedResponseIO_eq_map_encRecC {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) (hC : exec.CprimeCoherent) :
    exec.derivedResponseIO =
      exec.rawResponses.map (fun r => NockVM.encRecC r (exec.cprimeOf r)) := by
  have hrows := cprime_eq_cprimeOf hC
  unfold ExactExecution.derivedResponseIO ExactExecution.rawResponses
  revert hrows
  generalize exec.cprimeOf = cp
  induction exec.memoryRows with
  | nil =>
      intro _
      simp
  | cons a t ih =>
      intro hrows
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append,
        ih (fun row hmem => hrows row (List.mem_cons_of_mem a hmem))]
      have hCa : a.2.2.cprime = cp a.2.2.mem := hrows a (List.mem_cons_self ..)
      cases hver : a.2.2.ver <;> simp [MemoryTable.responseRecords, hver]
      · change NockVM.encRecC a.2.2.mem a.2.2.cprime = NockVM.encRecC a.2.2.mem (cp a.2.2.mem)
        rw [hCa]

/-! ## Fixed row recognizers -/

/-- Acceptance of one derived compute row by the production verifier and shared configuration.
The outer BFS label state and the public-row state must agree. -/
def ComputeRowAccepted (cfg : ExactConfig F K)
    (row : ComputeTable.State × ComputeTable.DTcomp K) : Prop :=
  row.1 = row.2.2.1.state
    ∧ row.2.1 = cfg.challenges.computeInputs
    ∧ ComputeTable.Vcomp row.2.1 row.2.2.1 row.2.2.2

/-- Acceptance of one derived memory row by the production verifier and shared configuration.
The outer BFS label state and the public-row state must agree. -/
def MemoryRowAccepted (cfg : ExactConfig F K)
    (row : MemoryTable.MState × MemoryTable.DTmem K) : Prop :=
  row.1 = row.2.2.st
    ∧ row.2.1 = cfg.challenges.memoryInputs
    ∧ MemoryTable.Vmem row.2.1 row.2.2
    ∧ row.2.2.lambda = cfg.challenges.lam

/-- Every row derived from the authoritative compute tree is accepted. -/
def ComputeRowsAccepted {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  exec.computeRows.Forall (ComputeRowAccepted cfg)

/-- Every row derived from the authoritative memory forest is accepted. -/
def MemoryRowsAccepted {cfg : ExactConfig F K} (exec : ExactExecution cfg) : Prop :=
  exec.memoryRows.Forall (MemoryRowAccepted cfg)

/-- Exact specification of one accepted compute row. -/
@[simp]
theorem computeRowAccepted_iff (cfg : ExactConfig F K)
    (row : ComputeTable.State × ComputeTable.DTcomp K) :
    ComputeRowAccepted cfg row ↔
      row.1 = row.2.2.1.state
        ∧ row.2.1 = cfg.challenges.computeInputs
        ∧ ComputeTable.Vcomp row.2.1 row.2.2.1 row.2.2.2 :=
  Iff.rfl

/-- Exact specification of one accepted memory row. -/
@[simp]
theorem memoryRowAccepted_iff (cfg : ExactConfig F K)
    (row : MemoryTable.MState × MemoryTable.DTmem K) :
    MemoryRowAccepted cfg row ↔
      row.1 = row.2.2.st
        ∧ row.2.1 = cfg.challenges.memoryInputs
        ∧ MemoryTable.Vmem row.2.1 row.2.2
        ∧ row.2.2.lambda = cfg.challenges.lam :=
  Iff.rfl

/-- Membership formulation of the compute-row fold. -/
theorem computeRowsAccepted_iff {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.ComputeRowsAccepted ↔
      ∀ row ∈ exec.computeRows, ComputeRowAccepted cfg row := by
  exact List.forall_iff_forall_mem

/-- Membership formulation of the memory-row fold. -/
theorem memoryRowsAccepted_iff {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.MemoryRowsAccepted ↔
      ∀ row ∈ exec.memoryRows, MemoryRowAccepted cfg row := by
  exact List.forall_iff_forall_mem

/-- Positive configured compute length rules out an empty derived compute table. -/
theorem computeRows_nonempty {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.computeRows ≠ [] :=
  List.ne_nil_of_length_pos (by simpa using cfg.compRows_pos)

/-- Positive configured memory length rules out an empty derived memory table. -/
theorem memoryRows_nonempty {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.memoryRows ≠ [] :=
  List.ne_nil_of_length_pos (by simpa using cfg.memRows_pos)

theorem positive_exact_carriers_exclude_empty_tables
    {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    ¬ (exec.computeRows = [] ∨ exec.memoryRows = []) := by
  rintro (hcompute | hmemory)
  · exact exec.computeRows_nonempty hcompute
  · exact exec.memoryRows_nonempty hmemory

end ExactExecution

/-! ## Exact field-table language -/

/-- Its only inputs are the fixed configuration and one forest-first execution.  Both encoded IO
lists are the canonical functions of that execution defined above.  Semantic `nmrMEF` closure is
the distinct, stronger `SemanticExactLanguage` below. -/
def ExactLanguage (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop :=
  exec.ComputeRowsAccepted
    ∧ exec.MemoryRowsAccepted
    ∧ IO.LmIO cfg.Ksz exec.derivedRequestIO exec.derivedResponseIO

/-- A uniqueness-sensitive strengthening for S5/`io_result_LIO`.
The base paper-language predicate remains `ExactLanguage` with `LmIO`. -/
def StrongExactLanguage (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop :=
  exec.ComputeRowsAccepted
    ∧ exec.MemoryRowsAccepted
    ∧ IO.LIO cfg.Ksz exec.derivedRequestIO exec.derivedResponseIO

/-- A proof-carrying member of the exact multiplicity-sensitive language.

The execution carrier and its acceptance proof form one dependent object; there are no
independent IO fields to splice. -/
abbrev AcceptedExecution (cfg : ExactConfig F K) :=
  { exec : ExactExecution cfg // ExactLanguage cfg exec }

/-- A proof-carrying member of the uniqueness-strengthened language. -/
abbrev StrongAcceptedExecution (cfg : ExactConfig F K) :=
  { exec : ExactExecution cfg // StrongExactLanguage cfg exec }

/-- Authoritative unfolding: fixed compute rows, fixed memory rows, and exact IO derived from
those same rows. -/
theorem exactLanguage_unfold (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    ExactLanguage cfg exec ↔
      (∀ row ∈ exec.computeRows, ExactExecution.ComputeRowAccepted cfg row)
        ∧ (∀ row ∈ exec.memoryRows, ExactExecution.MemoryRowAccepted cfg row)
        ∧ IO.LmIO cfg.Ksz exec.derivedRequestIO exec.derivedResponseIO := by
  simp only [ExactLanguage, ExactExecution.computeRowsAccepted_iff,
    ExactExecution.memoryRowsAccepted_iff]

/-- The accepted IO conjunct is always the canonical pair derived from the accepted rows. -/
theorem exactLanguage_derived_io {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ExactLanguage cfg exec) :
    IO.LmIO cfg.Ksz exec.derivedRequestIO exec.derivedResponseIO :=
  h.2.2

/-- Accepted executions have no hidden IO payload: equality of the authoritative forest-first
carriers determines the entire accepted subtype (the proof component is irrelevant).

This is the structural IO-splicing exclusion.  It deliberately does not claim that no other
external pair of lists can independently satisfy `LmIO`. -/
theorem AcceptedExecution.ext
    {cfg : ExactConfig F K} (x y : AcceptedExecution cfg)
    (hcompute : x.1.computeTree = y.1.computeTree)
    (hmemory : x.1.memoryForest = y.1.memoryForest) :
    x = y := by
  apply Subtype.ext
  exact ExactExecution.ext x.1 y.1 hcompute hmemory

/-- The shared `α,z,β,γ` configuration is read by every accepted row, rather than being
phantom metadata. -/
theorem exactLanguage_challenges_loadBearing
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ExactLanguage cfg exec) :
    (∀ row ∈ exec.computeRows,
        row.2.1.α = cfg.challenges.α ∧ row.2.1.z = cfg.challenges.z)
      ∧ (∀ row ∈ exec.memoryRows,
        row.2.1.z = cfg.challenges.z
          ∧ row.2.1.β = cfg.challenges.β
          ∧ row.2.1.γ = cfg.challenges.γ) := by
  constructor
  · intro row hrow
    have hr :=
      (ExactExecution.computeRowsAccepted_iff exec).1 h.1 row hrow
    have hinp := hr.2.1
    constructor
    · simpa [ChallengeVector.computeInputs] using
        congrArg (fun inp : ComputeTable.Inputs K => inp.α) hinp
    · simpa [ChallengeVector.computeInputs] using
        congrArg (fun inp : ComputeTable.Inputs K => inp.z) hinp
  · intro row hrow
    have hr :=
      (ExactExecution.memoryRowsAccepted_iff exec).1 h.2.1 row hrow
    have hinp := hr.2.1
    constructor
    · simpa [ChallengeVector.memoryInputs] using
        congrArg (fun inp : MemoryTable.Inputs K => inp.z) hinp
    · constructor
      · simpa [ChallengeVector.memoryInputs] using
          congrArg (fun inp : MemoryTable.Inputs K => inp.β) hinp
      · simpa [ChallengeVector.memoryInputs] using
          congrArg (fun inp : MemoryTable.Inputs K => inp.γ) hinp

/-- If two accepted executions have the same nonempty derived rows, then all eight configured
field challenges agree. -/
theorem exactLanguage_all_challenges_loadBearing
    {cfg₁ cfg₂ : ExactConfig F K}
    {exec₁ : ExactExecution cfg₁} {exec₂ : ExactExecution cfg₂}
    (hcompute : exec₁.computeRows = exec₂.computeRows)
    (hmemory : exec₁.memoryRows = exec₂.memoryRows)
    (h₁ : ExactLanguage cfg₁ exec₁) (h₂ : ExactLanguage cfg₂ exec₂) :
    cfg₁.challenges = cfg₂.challenges := by
  obtain ⟨crow, hcrow₁⟩ :=
    List.exists_mem_of_ne_nil exec₁.computeRows exec₁.computeRows_nonempty
  have hcrow₂ : crow ∈ exec₂.computeRows := by simpa [← hcompute] using hcrow₁
  have hc₁ := (ExactExecution.computeRowsAccepted_iff exec₁).1 h₁.1 crow hcrow₁
  have hc₂ := (ExactExecution.computeRowsAccepted_iff exec₂).1 h₂.1 crow hcrow₂
  have hci : cfg₁.challenges.computeInputs = cfg₂.challenges.computeInputs :=
    hc₁.2.1.symm.trans hc₂.2.1
  obtain ⟨mrow, hmrow₁⟩ :=
    List.exists_mem_of_ne_nil exec₁.memoryRows exec₁.memoryRows_nonempty
  have hmrow₂ : mrow ∈ exec₂.memoryRows := by simpa [← hmemory] using hmrow₁
  have hm₁ := (ExactExecution.memoryRowsAccepted_iff exec₁).1 h₁.2.1 mrow hmrow₁
  have hm₂ := (ExactExecution.memoryRowsAccepted_iff exec₂).1 h₂.2.1 mrow hmrow₂
  have hmi : cfg₁.challenges.memoryInputs = cfg₂.challenges.memoryInputs :=
    hm₁.2.1.symm.trans hm₂.2.1
  have hml : cfg₁.challenges.lam = cfg₂.challenges.lam :=
    hm₁.2.2.2.symm.trans hm₂.2.2.2
  cases c₁ : cfg₁.challenges
  cases c₂ : cfg₂.challenges
  simp_all only [ChallengeVector.computeInputs, ChallengeVector.memoryInputs,
    ComputeTable.Inputs.mk.injEq, MemoryTable.Inputs.mk.injEq]

/-- Positive exact carriers exclude the empty-table attack independently of row acceptance. -/
theorem exactLanguage_excludes_empty_tables
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (_h : ExactLanguage cfg exec) :
    ¬ (exec.computeRows = [] ∨ exec.memoryRows = []) :=
  exec.positive_exact_carriers_exclude_empty_tables


/-- Multiplicity-preserving semantic preimages of an execution's actual table IO.

The semantic lists are not called derived: table records have no total inverse.  Their bridge
equalities make them witnesses for the already-derived encoded lists, while `semantic_lmio`
states the paper's base IO relation on the actual `nmrMEF` records.  Request multiplicity is
deliberately allowed; request uniqueness belongs only to `SemanticIOWitness` below. -/
structure SemanticIOPreimage (cfg : ExactConfig F K) (exec : ExactExecution cfg) where
  /-- Timestamp window used for both semantic lists. -/
  timestampBound : ℕ
  /-- The timestamp window lies within the injective power window of `α`. -/
  timestampBound_le_order : timestampBound ≤ orderOf cfg.challenges.α
  /-- A semantic preimage of the compute table's actual derived requests. -/
  semanticRequests : List ((nmrMEF F K).Rec)
  /-- A semantic preimage of the memory table's actual derived responses. -/
  semanticResponses : List ((nmrMEF F K).Rec)
  /-- Every semantic request timestamp lies in the certified window. -/
  requestTimestampBound :
    ∀ r ∈ semanticRequests, r.2.2 < timestampBound
  /-- Every semantic response timestamp lies in the certified window. -/
  responseTimestampBound :
    ∀ r ∈ semanticResponses, r.2.2 < timestampBound
  /-- The semantic records satisfy the multiplicity-sensitive base IO language. -/
  semantic_lmio : IO.LmIO cfg.Ksz semanticRequests semanticResponses
  /-- Unique request timestamps: within the requests, the timestamp exponent
      determines the record.  This, not injectivity of the Form R encode (which fails: axes `0`
      and `1` collide at every `λ`), is what carries `LmIO` to the encoded IO. -/
  requestTimestamp_determines :
    ∀ x ∈ semanticRequests, ∀ y ∈ semanticRequests, x.2.2 = y.2.2 → x = y
  /-- The semantic requests encode to the compute rows' actual derived IO. -/
  requests_bridge :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam semanticRequests = exec.derivedRequestIO
  /-- The semantic responses encode to the memory rows' actual derived IO. -/
  responses_bridge :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam semanticResponses = exec.derivedResponseIO

namespace SemanticIOPreimage

/-- Public bridge theorem: semantic preimages map to the actual derived table IO. -/
theorem maps_to_actual_derived_io
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOPreimage cfg exec) :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam w.semanticRequests = exec.derivedRequestIO
      ∧ bridgeRecords F K cfg.challenges.α cfg.challenges.lam w.semanticResponses = exec.derivedResponseIO :=
  ⟨w.requests_bridge, w.responses_bridge⟩

/-- Request timestamps also lie below the full injectivity order. -/
theorem requestTimestamp_lt_order
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOPreimage cfg exec) :
    ∀ r ∈ w.semanticRequests, r.2.2 < orderOf cfg.challenges.α := by
  intro r hr
  exact lt_of_lt_of_le (w.requestTimestampBound r hr) w.timestampBound_le_order

/-- Response timestamps also lie below the full injectivity order. -/
theorem responseTimestamp_lt_order
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOPreimage cfg exec) :
    ∀ r ∈ w.semanticResponses, r.2.2 < orderOf cfg.challenges.α := by
  intro r hr
  exact lt_of_lt_of_le (w.responseTimestampBound r hr) w.timestampBound_le_order

/-- Semantic `LmIO` already guarantees response uniqueness; no response `Nodup` field is needed. -/
theorem semanticResponses_nodup
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOPreimage cfg exec) :
    w.semanticResponses.Nodup :=
  (IO.LmIO_iff cfg.Ksz w.semanticRequests w.semanticResponses).1 w.semantic_lmio |>.2.2.1

/-- The load-bearing semantic relation maps to the execution's exact field-table `LmIO`. -/
theorem derivedIO_lmio
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOPreimage cfg exec) :
    IO.LmIO cfg.Ksz exec.derivedRequestIO exec.derivedResponseIO := by
  rw [← w.requests_bridge, ← w.responses_bridge]
  exact bridgeRecords_LmIO F K cfg.Ksz cfg.challenges.α cfg.challenges.lam
    w.timestampBound_le_order w.requestTimestampBound w.requestTimestamp_determines
    w.semantic_lmio

/-- Semantic request preimages of one execution agree after the Form R encode.  Record equality
does not follow: Form R identifies axes `0` and `1`, so only the encoded lists are determined. -/
theorem semanticRequests_unique
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (x y : SemanticIOPreimage cfg exec) :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam x.semanticRequests =
      bridgeRecords F K cfg.challenges.α cfg.challenges.lam y.semanticRequests :=
  x.requests_bridge.trans y.requests_bridge.symm

/-- Semantic response preimages of one execution agree after the Form R encode. -/
theorem semanticResponses_unique
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (x y : SemanticIOPreimage cfg exec) :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam x.semanticResponses =
      bridgeRecords F K cfg.challenges.α cfg.challenges.lam y.semanticResponses :=
  x.responses_bridge.trans y.responses_bridge.symm

end SemanticIOPreimage

def SemanticExactLanguage (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Prop :=
  exec.ComputeRowsAccepted
    ∧ exec.MemoryRowsAccepted
    ∧ Nonempty (SemanticIOPreimage cfg exec)

abbrev SemanticAcceptedExecution (cfg : ExactConfig F K) :=
  { exec : ExactExecution cfg // SemanticExactLanguage cfg exec }

theorem semanticExactLanguage_unfold (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    SemanticExactLanguage cfg exec ↔
      exec.ComputeRowsAccepted
        ∧ exec.MemoryRowsAccepted
        ∧ Nonempty (SemanticIOPreimage cfg exec) :=
  Iff.rfl

theorem SemanticExactLanguage.toExactLanguage
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : SemanticExactLanguage cfg exec) :
    ExactLanguage cfg exec := by
  obtain ⟨hcompute, hmemory, ⟨w⟩⟩ := h
  exact ⟨hcompute, hmemory, w.derivedIO_lmio⟩

/-- Regression boundary: field-table acceptance alone cannot manufacture a missing semantic
preimage.  This is the generic form of the accepted-table/no-semantic-preimage attack. -/
theorem exactLanguage_not_semantic_of_isEmpty_preimage
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hfield : ExactLanguage cfg exec)
    (hempty : IsEmpty (SemanticIOPreimage cfg exec)) :
    ExactLanguage cfg exec ∧ ¬ SemanticExactLanguage cfg exec := by
  refine ⟨hfield, ?_⟩
  rintro ⟨_, _, ⟨w⟩⟩
  exact hempty.false w

/-- Uniqueness-sensitive semantic witness.  It contains the multiplicity-preserving semantic
preimage and adds only request uniqueness; response uniqueness follows from semantic `LmIO`. -/
structure SemanticIOWitness (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    extends SemanticIOPreimage cfg exec where
  /-- Semantic requests are unique, enabling the `LIO` strengthening. -/
  semanticRequests_nodup : semanticRequests.Nodup

namespace SemanticIOWitness

/-- Compatibility projection of the semantic bridge equations. -/
theorem maps_to_actual_derived_io
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOWitness cfg exec) :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam w.semanticRequests = exec.derivedRequestIO
      ∧ bridgeRecords F K cfg.challenges.α cfg.challenges.lam w.semanticResponses = exec.derivedResponseIO :=
  w.toSemanticIOPreimage.maps_to_actual_derived_io

/-- The actual derived request IO is duplicate-free under the explicit uniqueness strengthening. -/
theorem derivedRequestIO_nodup
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOWitness cfg exec) :
    exec.derivedRequestIO.Nodup := by
  rw [← w.requests_bridge]
  exact bridgeRecords_nodup_of_timestamp_bound
    F K cfg.challenges.α cfg.challenges.lam w.timestampBound_le_order
    w.semanticRequests w.requestTimestampBound w.requestTimestamp_determines
    w.semanticRequests_nodup

/-- The actual derived response IO is duplicate-free already from semantic `LmIO`. -/
theorem derivedResponseIO_nodup
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOWitness cfg exec) :
    exec.derivedResponseIO.Nodup :=
  (IO.LmIO_iff cfg.Ksz exec.derivedRequestIO exec.derivedResponseIO).1
    w.toSemanticIOPreimage.derivedIO_lmio |>.2.2.1

/-- Compatibility wrapper; uniqueness is the Form R encoding of the preimage layer. -/
theorem semanticRequests_unique
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (x y : SemanticIOWitness cfg exec) :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam x.semanticRequests =
      bridgeRecords F K cfg.challenges.α cfg.challenges.lam y.semanticRequests :=
  SemanticIOPreimage.semanticRequests_unique x.toSemanticIOPreimage y.toSemanticIOPreimage

/-- Compatibility wrapper; uniqueness is the Form R encoding of the preimage layer. -/
theorem semanticResponses_unique
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (x y : SemanticIOWitness cfg exec) :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam x.semanticResponses =
      bridgeRecords F K cfg.challenges.α cfg.challenges.lam y.semanticResponses :=
  SemanticIOPreimage.semanticResponses_unique x.toSemanticIOPreimage y.toSemanticIOPreimage

/-- A strong semantic witness upgrades field-table multiplicity acceptance to `LIO`. -/
theorem strongExactLanguage_of_exactLanguage
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOWitness cfg exec) (h : ExactLanguage cfg exec) :
    StrongExactLanguage cfg exec :=
  ⟨h.1, h.2.1,
    IO.cor_uni_req_uni_resp cfg.Ksz exec.derivedRequestIO exec.derivedResponseIO
      w.derivedRequestIO_nodup h.2.2⟩

theorem strongExactLanguage_of_semanticExactLanguage
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOWitness cfg exec) (h : SemanticExactLanguage cfg exec) :
    StrongExactLanguage cfg exec :=
  w.strongExactLanguage_of_exactLanguage h.toExactLanguage

end SemanticIOWitness

/-- Forgetting the `LIO` strengthening recovers the multiplicity-sensitive base language. -/
theorem StrongExactLanguage.toExactLanguage
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : StrongExactLanguage cfg exec) :
    ExactLanguage cfg exec :=
  ⟨h.1, h.2.1,
    IO.MEM_1_subset cfg.Ksz exec.derivedRequestIO exec.derivedResponseIO h.2.2⟩

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.ExactExecution.rawRequests_eq_computeRows
#print axioms Nock.NockVMROM.Thm54.ExactExecution.rawResponses_eq_memoryRows
#print axioms Nock.NockVMROM.Thm54.ExactExecution.derivedRequestIO_eq_computeRows
#print axioms Nock.NockVMROM.Thm54.ExactExecution.derivedResponseIO_eq_memoryRows
#print axioms Nock.NockVMROM.Thm54.ExactExecution.computeRowsAccepted_iff
#print axioms Nock.NockVMROM.Thm54.ExactExecution.memoryRowsAccepted_iff
#print axioms Nock.NockVMROM.Thm54.ExactExecution.positive_exact_carriers_exclude_empty_tables
#print axioms Nock.NockVMROM.Thm54.exactLanguage_unfold
#print axioms Nock.NockVMROM.Thm54.AcceptedExecution.ext
#print axioms Nock.NockVMROM.Thm54.exactLanguage_challenges_loadBearing
#print axioms Nock.NockVMROM.Thm54.exactLanguage_all_challenges_loadBearing
#print axioms Nock.NockVMROM.Thm54.exactLanguage_excludes_empty_tables
#print axioms Nock.NockVMROM.Thm54.SemanticIOPreimage.maps_to_actual_derived_io
#print axioms Nock.NockVMROM.Thm54.SemanticIOPreimage.derivedIO_lmio
#print axioms Nock.NockVMROM.Thm54.SemanticIOPreimage.semanticRequests_unique
#print axioms Nock.NockVMROM.Thm54.SemanticIOPreimage.semanticResponses_unique
#print axioms Nock.NockVMROM.Thm54.semanticExactLanguage_unfold
#print axioms Nock.NockVMROM.Thm54.SemanticExactLanguage.toExactLanguage
#print axioms Nock.NockVMROM.Thm54.exactLanguage_not_semantic_of_isEmpty_preimage
#print axioms Nock.NockVMROM.Thm54.SemanticIOWitness.maps_to_actual_derived_io
#print axioms Nock.NockVMROM.Thm54.SemanticIOWitness.derivedRequestIO_nodup
#print axioms Nock.NockVMROM.Thm54.SemanticIOWitness.derivedResponseIO_nodup
#print axioms Nock.NockVMROM.Thm54.SemanticIOWitness.semanticRequests_unique
#print axioms Nock.NockVMROM.Thm54.SemanticIOWitness.semanticResponses_unique
#print axioms Nock.NockVMROM.Thm54.SemanticIOWitness.strongExactLanguage_of_exactLanguage
#print axioms Nock.NockVMROM.Thm54.SemanticIOWitness.strongExactLanguage_of_semanticExactLanguage
#print axioms Nock.NockVMROM.Thm54.StrongExactLanguage.toExactLanguage
