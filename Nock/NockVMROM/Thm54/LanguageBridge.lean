import Nock.NockVMROM.Language
import Nock.NockVMROM.Thm54.ChainedLanguage

/-!
# Forward language bridge: exact chained executions into `L_NockVMROM`

This is the *forward* half of the assembly bridge between the additive exact Theorem 5.4 surface
(`ExactConfig` / `ExactExecution` / `ChainedSemanticExactLanguage`) and the original NockVMROM
recognizer (`Nock.NockVMROM.accepts`, `Language (Tag F K α β Ksz)`).

## What is projected

`stmtOfExact` reads the original language's public `(Inputs × Pub)` row lists off the BFS-derived
rows of the authoritative compute tree and memory forest.  `computeDecOfExact` reads the decided
compute columns off the *same* rows, in the *same* order, so the two lists are `Forall₂`-aligned by
construction.  `witOfExact` completes the witness with the two **semantic** `nmrMEF` record lists of
a `SemanticIOPreimage` — which is exactly what `Wit.progIO` / `Wit.memIO` are, and exactly the lists
that `IO.LmIO` is applied to in `accepts`.

## The hazard this module is built around

`Nock.NockVMROM.accepts` is a conjunction whose table folds never mention `progIO`/`memIO`:
the IO lists are seen only by the separate `IO.LmIO` conjunct.  Consequently the original language
accepts the empty-table statement with an arbitrary self-matched IO record
(`Nock.NockVMROM.language_nonempty`), while *no* `ExactExecution` has empty BFS rows
(`ExactExecution.computeRows_nonempty`, forced by `ExactConfig.compRows_pos`).  A bare biconditional
`Language x ↔ ∃ cfg exec, ChainedSemanticExactLanguage cfg exec` is therefore **false**, and is not
attempted here.  `TableIOEqDerived` is the predicate that ties a projected witness's IO lists to the
*same execution's* derived request/response lists; `tableIOEqDerived_witOfExact` shows the forward
projection satisfies it by construction, and the `§ Reverse-direction guard` section compiles the
countermodel that blocks the unthreaded converse.
-/

namespace Nock.NockVMROM.Thm54

open Nock.Framework

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## Forward projections into the original statement and witness types -/

/-- The original language's decided compute columns, read off the authoritative BFS rows in BFS
order.  This is a projection of the same list `stmtOfExact` projects the public compute rows from,
so no independent row order is introduced. -/
def computeDecOfExact {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    List (ComputeTable.Dec K) :=
  exec.computeRows.map fun row => row.2.2.2

/-- **Forward statement projection.**  The original NockVMROM public statement of an exact
execution: the compute and memory `(Inputs × Pub)` pairs of the BFS-derived rows. -/
def stmtOfExact (cfg : ExactConfig F K) (exec : ExactExecution cfg) : Stmt F K :=
  { compute := exec.computeRows.map fun row => (row.2.1, row.2.2.1)
    memory := exec.memoryRows.map fun row => (row.2.1, row.2.2) }

/-- **Forward witness projection.**  The original NockVMROM private witness of an exact execution
together with one semantic IO preimage: the decided compute columns of the same BFS rows, and the
preimage's two semantic `nmrMEF` record lists as `progIO` / `memIO`.

The IO lists are *not* free: `tableIOEqDerived_witOfExact` pins them to the execution's derived
request/response lists. -/
def witOfExact (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (w : SemanticIOPreimage cfg exec) : Wit F K :=
  { computeDec := computeDecOfExact exec
    progIO := w.semanticRequests
    memIO := w.semanticResponses }

@[simp]
theorem stmtOfExact_compute (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    (stmtOfExact cfg exec).compute =
      exec.computeRows.map (fun row => (row.2.1, row.2.2.1)) :=
  rfl

@[simp]
theorem stmtOfExact_memory (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    (stmtOfExact cfg exec).memory =
      exec.memoryRows.map (fun row => (row.2.1, row.2.2)) :=
  rfl

@[simp]
theorem witOfExact_computeDec (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (w : SemanticIOPreimage cfg exec) :
    (witOfExact cfg exec w).computeDec = computeDecOfExact exec :=
  rfl

@[simp]
theorem witOfExact_progIO (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (w : SemanticIOPreimage cfg exec) :
    (witOfExact cfg exec w).progIO = w.semanticRequests :=
  rfl

@[simp]
theorem witOfExact_memIO (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (w : SemanticIOPreimage cfg exec) :
    (witOfExact cfg exec w).memIO = w.semanticResponses :=
  rfl

/-- The projected public compute list has exactly the configured active compute length. -/
@[simp]
theorem stmtOfExact_compute_length (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    (stmtOfExact cfg exec).compute.length = cfg.compRows := by
  simp

/-- The projected public memory list has exactly the configured active memory length. -/
@[simp]
theorem stmtOfExact_memory_length (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    (stmtOfExact cfg exec).memory.length = cfg.memRows := by
  simp

/-- The projected decided-column list is aligned in length with the projected compute rows. -/
@[simp]
theorem computeDecOfExact_length (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    (computeDecOfExact exec).length = cfg.compRows := by
  simp [computeDecOfExact]

/-! ## The IO threading predicate -/

/-- **`TableIOEqDerived`** — the projected witness's semantic IO lists encode to *exactly* the
execution's own derived request/response IO lists.

The two sides live in different types (`List ((nmrMEF F K).Rec)` versus `List (Fin 9 → K)`), so the
tie is stated through the compiled record bridge `bridgeRecords` at the configuration's own
challenge `cfg.challenges.α`.  This is the conjunct that the original `accepts` does **not** contain,
and whose absence is exactly what makes the unthreaded converse false. -/
def TableIOEqDerived (cfg : ExactConfig F K) (exec : ExactExecution cfg) (wit : Wit F K) : Prop :=
  bridgeRecords F K cfg.challenges.α cfg.challenges.lam wit.progIO = exec.derivedRequestIO ∧
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam wit.memIO = exec.derivedResponseIO

/-- Authoritative unfolding of the IO threading predicate. -/
theorem tableIOEqDerived_unfold (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (wit : Wit F K) :
    TableIOEqDerived cfg exec wit ↔
      bridgeRecords F K cfg.challenges.α cfg.challenges.lam wit.progIO = exec.derivedRequestIO ∧
        bridgeRecords F K cfg.challenges.α cfg.challenges.lam wit.memIO = exec.derivedResponseIO :=
  Iff.rfl

/-- **The forward projection threads IO by construction.**  This is the semantic preimage's own
bridge equations, so it holds definitionally — there is no freedom in the projected IO lists. -/
theorem tableIOEqDerived_witOfExact (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (w : SemanticIOPreimage cfg exec) :
    TableIOEqDerived cfg exec (witOfExact cfg exec w) :=
  ⟨w.requests_bridge, w.responses_bridge⟩

/-- Together with
`tableIOEqDerived_witOfExact` this is the precise sense in which the projection carries no free IO
payload. -/
theorem witOfExact_io_unique {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w₁ w₂ : SemanticIOPreimage cfg exec) :
    bridgeRecords F K cfg.challenges.α cfg.challenges.lam (witOfExact cfg exec w₁).progIO =
      bridgeRecords F K cfg.challenges.α cfg.challenges.lam (witOfExact cfg exec w₂).progIO ∧
      bridgeRecords F K cfg.challenges.α cfg.challenges.lam (witOfExact cfg exec w₁).memIO =
        bridgeRecords F K cfg.challenges.α cfg.challenges.lam (witOfExact cfg exec w₂).memIO :=
  ⟨SemanticIOPreimage.semanticRequests_unique w₁ w₂,
    SemanticIOPreimage.semanticResponses_unique w₁ w₂⟩

/-! ## Forward soundness -/

private theorem forall₂_map_map {α β γ : Type*} {R : β → γ → Prop}
    (f : α → β) (g : α → γ) (l : List α) (h : ∀ a ∈ l, R (f a) (g a)) :
    List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih =>
      exact List.Forall₂.cons (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- The exact per-row compute fold transfers to the original `Forall₂` compute fold on the
projected statement and decided columns.  Both lists are maps over the *same* BFS row list, so the
pairing is the identity on rows. -/
theorem computeTableAccepts_stmtOfExact {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : exec.ComputeRowsAccepted) :
    ComputeTableAccepts (stmtOfExact cfg exec).compute (computeDecOfExact exec) := by
  have h' := (ExactExecution.computeRowsAccepted_iff exec).1 h
  exact forall₂_map_map (R := fun sp d => ComputeTable.Vcomp sp.1 sp.2 d)
    (fun row => (row.2.1, row.2.2.1)) (fun row => row.2.2.2)
    exec.computeRows fun row hrow => (h' row hrow).2.2

/-- The exact per-row memory fold transfers to the original membership memory fold on the
projected statement. -/
theorem memoryTableAccepts_stmtOfExact {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : exec.MemoryRowsAccepted) :
    MemoryTableAccepts (stmtOfExact cfg exec).memory := by
  intro r hr
  simp only [stmtOfExact_memory, List.mem_map] at hr
  obtain ⟨row, hrow, rfl⟩ := hr
  exact ((ExactExecution.memoryRowsAccepted_iff exec).1 h row hrow).2.2.1

/-- **Forward soundness at the acceptance level.**  Semantic exact acceptance plus one semantic IO
preimage yields original NockVMROM acceptance of the projected statement/witness pair, at the
configuration's own IO bound `cfg.Ksz`.

The IO conjunct is discharged by the preimage's `semantic_lmio` *verbatim*: the original witness's
`progIO`/`memIO` are semantic `nmrMEF` records, so no encoding, timestamp-window, characteristic, or
field-capacity side condition is involved. -/
theorem accepts_stmtOfExact {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : SemanticExactLanguage cfg exec) (w : SemanticIOPreimage cfg exec) :
    accepts cfg.Ksz (stmtOfExact cfg exec) (witOfExact cfg exec w) :=
  ⟨computeTableAccepts_stmtOfExact h.1, memoryTableAccepts_stmtOfExact h.2.1, w.semantic_lmio⟩

theorem accepts_stmtOfExact_of_chained {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) (w : SemanticIOPreimage cfg exec) :
    accepts cfg.Ksz (stmtOfExact cfg exec) (witOfExact cfg exec w) :=
  accepts_stmtOfExact h.semantic w

/-- **The forward bridge, IO threaded.**  A chained semantic exact language member with a semantic
IO preimage gives: original acceptance of the projected pair, the `TableIOEqDerived` tie of the
projected IO to the execution's derived IO, and the derived field-table `LmIO` at the same bound. -/
theorem chained_forward_bridge {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) (w : SemanticIOPreimage cfg exec) :
    accepts cfg.Ksz (stmtOfExact cfg exec) (witOfExact cfg exec w) ∧
      TableIOEqDerived cfg exec (witOfExact cfg exec w) ∧
      IO.LmIO cfg.Ksz exec.derivedRequestIO exec.derivedResponseIO :=
  ⟨accepts_stmtOfExact_of_chained h w, tableIOEqDerived_witOfExact cfg exec w,
    w.derivedIO_lmio⟩

/-- **Forward soundness at the language level.**  The projected statement is a member of the
original `L_NockVMROM` at IO bound `cfg.Ksz`.

No IO witness has to be supplied: `SemanticExactLanguage` already carries
`Nonempty (SemanticIOPreimage cfg exec)`.  The tag's `α`, `β` are phantom instance-key data and are
left free; the tag's `Ksz` is *not* free — it is the configuration's own bound `cfg.Ksz`, the bound
at which the preimage's semantic `LmIO` holds. -/
theorem language_stmtOfExact (α β : K) {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    Language (Tag F K α β cfg.Ksz) (stmtOfExact cfg exec) := by
  obtain ⟨w⟩ := h.semantic.2.2
  exact ⟨witOfExact cfg exec w, accepts_stmtOfExact_of_chained h w⟩

/-- The canonical instantiation of the forward language bridge at the configuration's own compute
challenge and memory pole. -/
theorem language_stmtOfExact_canonical {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    Language (Tag F K cfg.challenges.α cfg.challenges.β cfg.Ksz) (stmtOfExact cfg exec) :=
  language_stmtOfExact cfg.challenges.α cfg.challenges.β h

/-- The configured IO bound of any execution carrying a semantic preimage is at least one, since
semantic `LmIO` forces `1 ≤ |requests| ≤ Ksz`.  Hence the bridge never lands in the empty
`Ksz = 0` regime of `Nock.NockVMROM.not_language_Ksz_zero`. -/
theorem one_le_Ksz {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (w : SemanticIOPreimage cfg exec) : 1 ≤ cfg.Ksz :=
  le_trans w.semantic_lmio.1.1 w.semantic_lmio.1.2

/-! ## Reverse-direction guard

The converse is **not** proved, and the bare converse is false.  The two obstructions below are
compiled, not asserted.
-/

/-- Every projected statement has a nonempty public compute list, because an exact configuration
has a positive active compute prefix. -/
theorem stmtOfExact_compute_ne_nil (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    (stmtOfExact cfg exec).compute ≠ [] := by
  intro h
  exact exec.computeRows_nonempty (by simpa using h)

/-- Every projected statement has a nonempty public memory list. -/
theorem stmtOfExact_memory_ne_nil (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    (stmtOfExact cfg exec).memory ≠ [] := by
  intro h
  exact exec.memoryRows_nonempty (by simpa using h)

/-- The empty-table statement is not the projection of any exact carrier. -/
theorem stmtOfExact_ne_empty (cfg : ExactConfig F K) (exec : ExactExecution cfg) :
    stmtOfExact cfg exec ≠ (⟨[], []⟩ : Stmt F K) := fun h =>
  stmtOfExact_compute_ne_nil cfg exec (congrArg Stmt.compute h)

/-- **The empty-table / self-matched-IO countermodel.**  At any bound `Ksz ≥ 1` the original
language accepts the empty-table statement — the table folds are vacuous and the free
self-matched IO record satisfies `IO.LmIO` on its own — yet that statement is the projection of no
exact carrier whatsoever.  So the reverse inclusion cannot hold, with or without acceptance
hypotheses on the exact side. -/
theorem language_empty_stmt_has_no_exact_preimage (α β : K) {Ksz : ℕ} (hK : 1 ≤ Ksz)
    (r : (nmrMEF F K).Rec) :
    Language (Tag F K α β Ksz) (⟨[], []⟩ : Stmt F K) ∧
      ¬ ∃ (cfg : ExactConfig F K) (exec : ExactExecution cfg),
          stmtOfExact cfg exec = (⟨[], []⟩ : Stmt F K) :=
  ⟨language_nonempty F K α β hK r, by
    rintro ⟨cfg, exec, h⟩
    exact stmtOfExact_ne_empty cfg exec h⟩

/-- **The bare reverse implication is refuted.**  There is no map from original language membership
back to an exact chained execution projecting to the same statement. -/
theorem not_reverse_language_projection (α β : K) {Ksz : ℕ} (hK : 1 ≤ Ksz)
    (r : (nmrMEF F K).Rec) :
    ¬ ∀ x : Stmt F K, Language (Tag F K α β Ksz) x →
        ∃ (cfg : ExactConfig F K) (exec : ExactExecution cfg),
          ChainedSemanticExactLanguage cfg exec ∧ stmtOfExact cfg exec = x := by
  intro hrev
  obtain ⟨cfg, exec, -, hx⟩ := hrev (⟨[], []⟩ : Stmt F K) (language_nonempty F K α β hK r)
  exact stmtOfExact_ne_empty cfg exec hx

/-- A witness for the projected statement whose IO lists are a free self-matched record, unrelated
to the execution.  Used only to exhibit that the original `accepts` leaves IO unconstrained. -/
def freeIOWit (cfg : ExactConfig F K) (exec : ExactExecution cfg) (r : (nmrMEF F K).Rec) :
    Wit F K :=
  { computeDec := computeDecOfExact exec
    progIO := [r]
    memIO := [r] }

/-- The original `accepts` accepts the projected statement together with a completely arbitrary
self-matched IO record: the compute and memory folds never read `progIO`/`memIO`. -/
theorem accepts_freeIOWit {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : SemanticExactLanguage cfg exec) (hK : 1 ≤ cfg.Ksz) (r : (nmrMEF F K).Rec) :
    accepts cfg.Ksz (stmtOfExact cfg exec) (freeIOWit cfg exec r) :=
  ⟨computeTableAccepts_stmtOfExact h.1, memoryTableAccepts_stmtOfExact h.2.1,
    ⟨⟨le_refl 1, hK⟩, [r], le_refl 1, List.nodup_singleton r, fun _ => Iff.rfl,
      List.Perm.refl _⟩⟩

/-- A free self-matched singleton cannot be the execution's derived request list unless that list
has length one, so `TableIOEqDerived` genuinely rejects it. -/
theorem freeIOWit_not_tableIOEqDerived (cfg : ExactConfig F K) (exec : ExactExecution cfg)
    (r : (nmrMEF F K).Rec) (hlen : exec.derivedRequestIO.length ≠ 1) :
    ¬ TableIOEqDerived cfg exec (freeIOWit cfg exec r) := by
  intro h
  apply hlen
  have hl := congrArg List.length h.1
  simpa [freeIOWit] using hl.symm

/-- **`accepts` does not pin IO; `TableIOEqDerived` does.**  For a genuine semantic exact execution
whose derived request list does not have length one, original acceptance of the projected statement
survives replacing the projected IO by a free self-matched record, while the IO threading predicate
fails on that same witness.  Hence no reverse direction can recover `TableIOEqDerived` from
`accepts` alone, and the biconditional is not claimed. -/
theorem accepts_does_not_pin_io {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : SemanticExactLanguage cfg exec) (w : SemanticIOPreimage cfg exec)
    (r : (nmrMEF F K).Rec) (hlen : exec.derivedRequestIO.length ≠ 1) :
    accepts cfg.Ksz (stmtOfExact cfg exec) (freeIOWit cfg exec r) ∧
      ¬ TableIOEqDerived cfg exec (freeIOWit cfg exec r) :=
  ⟨accepts_freeIOWit h (one_le_Ksz w) r, freeIOWit_not_tableIOEqDerived cfg exec r hlen⟩

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.stmtOfExact_compute
#print axioms Nock.NockVMROM.Thm54.stmtOfExact_memory
#print axioms Nock.NockVMROM.Thm54.witOfExact_computeDec
#print axioms Nock.NockVMROM.Thm54.witOfExact_progIO
#print axioms Nock.NockVMROM.Thm54.witOfExact_memIO
#print axioms Nock.NockVMROM.Thm54.stmtOfExact_compute_length
#print axioms Nock.NockVMROM.Thm54.stmtOfExact_memory_length
#print axioms Nock.NockVMROM.Thm54.computeDecOfExact_length
#print axioms Nock.NockVMROM.Thm54.tableIOEqDerived_unfold
#print axioms Nock.NockVMROM.Thm54.tableIOEqDerived_witOfExact
#print axioms Nock.NockVMROM.Thm54.witOfExact_io_unique
#print axioms Nock.NockVMROM.Thm54.computeTableAccepts_stmtOfExact
#print axioms Nock.NockVMROM.Thm54.memoryTableAccepts_stmtOfExact
#print axioms Nock.NockVMROM.Thm54.accepts_stmtOfExact
#print axioms Nock.NockVMROM.Thm54.accepts_stmtOfExact_of_chained
#print axioms Nock.NockVMROM.Thm54.chained_forward_bridge
#print axioms Nock.NockVMROM.Thm54.language_stmtOfExact
#print axioms Nock.NockVMROM.Thm54.language_stmtOfExact_canonical
#print axioms Nock.NockVMROM.Thm54.one_le_Ksz
#print axioms Nock.NockVMROM.Thm54.stmtOfExact_compute_ne_nil
#print axioms Nock.NockVMROM.Thm54.stmtOfExact_memory_ne_nil
#print axioms Nock.NockVMROM.Thm54.stmtOfExact_ne_empty
#print axioms Nock.NockVMROM.Thm54.language_empty_stmt_has_no_exact_preimage
#print axioms Nock.NockVMROM.Thm54.not_reverse_language_projection
#print axioms Nock.NockVMROM.Thm54.accepts_freeIOWit
#print axioms Nock.NockVMROM.Thm54.freeIOWit_not_tableIOEqDerived
#print axioms Nock.NockVMROM.Thm54.accepts_does_not_pin_io
