/-
  Nock/Trace.lean

  A trace is a `List Verb` `(t₀, …, tₙ)`.  Consistency (`Nock(tᵢ,tᵢ₊₁) = 0`)
  is realized by the transition function `next` of `Nock/Verb.lean`:
  `Step a b := next a = some b`.

  TWO LEVELS OF DETERMINISM (see also `Nock/Verb.lean`):

  1. *Concrete / functional.*  `next` is a Lean function, so `Step` is single-valued
     for free (`Step.det` is just `Option.some.inj`) and `trace_unique`/`deterministic_Trace`
     follow by induction.  This says nothing about *why* the interpreter is deterministic —
     it is a property of having fixed the selection order into a function; it does not
     depend on `map`'s strict ordering.

  2. *The conditional theorem.*  `Thm:deterministic_Trace`
     is a *conditional*: **if** `map` enforces a *strict* ordering on redexes, **then** each
     finite verb has ≤ 1 consistent trace of size `n`.  We mechanize exactly this over an
     abstract selection order: `Verb.SelStep`/`Verb.StrictSelect`, with `Verb.SelStep.det`
     *genuinely using* strictness.  See
     `selStep_deterministic_Trace` below.  The concrete DFS interpreter is then the *special
     case*: the DFS index order is strict (`Verb.strictSelect_dfs`, where
     `Verb.enum_index_range` is load-bearing) and `next` realizes `SelStep`
     (`Verb.next_eq_some_iff`), yielding `deterministic_Trace_strict`.
-/

import Nock.Verb

namespace Nock
namespace Verb

/-! ### Trace, consistency, completeness -/

/-- A single consistent transition: `b` is obtained from `a` by one Nock step. -/
def Step (a b : Verb) : Prop := next a = some b

/-- The transition relation is deterministic: `next` is a function. -/
theorem Step.det {a b b' : Verb} (h : Step a b) (h' : Step a b') : b = b' :=
  Option.some.inj (h.symm.trans h')

/-- A trace is **consistent** iff each adjacent pair is a `Step`. -/
def Consistent : List Verb → Prop
  | []              => True
  | [_]             => True
  | a :: b :: rest  => Step a b ∧ Consistent (b :: rest)

/-- A trace is **complete** iff its last verb has no successor (terminal or crashed). -/
def Complete (T : List Verb) : Prop := ∃ v, T.getLast? = some v ∧ next v = none

/-- `T` is a consistent trace of the verb `F`. -/
def TraceOf (F : Verb) (T : List Verb) : Prop := T.head? = some F ∧ Consistent T

/-- `c` is a **continuation** of `F`: it occurs in some consistent trace of `F`. -/
def Continuation (F c : Verb) : Prop := ∃ T, TraceOf F T ∧ c ∈ T

/-- `F` is a **valid** verb: it has a complete trace ending in a terminal (non-crash) verb. -/
def Valid (F : Verb) : Prop :=
  ∃ T v, TraceOf F T ∧ T.getLast? = some v ∧ next v = none ∧ isTerminal v = true

/-- `F` is an **invalid** verb: it has a complete trace whose last verb crashed. -/
def Invalid (F : Verb) : Prop :=
  ∃ T v, TraceOf F T ∧ T.getLast? = some v ∧ next v = none ∧ isTerminal v = false

/-- `F` **terminates** / is **finite** (`F ∈ NockVM`): it has a complete trace. -/
def Finite (F : Verb) : Prop := ∃ T, TraceOf F T ∧ Complete T

/-- `FiniteTransitions`: `F` occurs on a *complete* trace of some finite verb `F₀`. -/
def FiniteTransition (F : Verb) : Prop :=
  ∃ (F0 : Verb) (T : List Verb), TraceOf F0 T ∧ Complete T ∧ F ∈ T

/-! ### Small list helpers (Lean core only) -/

private theorem head?_some_mem {F : Verb} {T : List Verb}
    (h : T.head? = some F) : F ∈ T := by
  cases T with
  | nil => simp at h
  | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h; simp

private theorem getLast?_cons₂ (x y : Verb) (t : List Verb) :
    (x :: y :: t).getLast? = (y :: t).getLast? := by
  simp [List.getLast?_cons_cons]

/-- Any element of a consistent trace begins a consistent *suffix* with the same last verb. -/
private theorem consistent_suffix_of_mem {F : Verb} :
    ∀ (T : List Verb), Consistent T → F ∈ T →
      ∃ S, S.head? = some F ∧ Consistent S ∧ S.getLast? = T.getLast? := by
  intro T
  induction T with
  | nil => intro _ hmem; simp at hmem
  | cons a t iht =>
      cases t with
      | nil =>
          intro hc hmem
          simp only [List.mem_singleton] at hmem
          subst hmem
          exact ⟨[F], by simp, hc, rfl⟩
      | cons b t' =>
          intro hc hmem
          obtain ⟨hab, hrest⟩ := hc
          rcases List.mem_cons.1 hmem with hFa | hmem'
          · subst hFa
            exact ⟨F :: b :: t', by simp, ⟨hab, hrest⟩, rfl⟩
          · obtain ⟨S, hS1, hS2, hS3⟩ := iht hrest hmem'
            exact ⟨S, hS1, hS2, hS3.trans (getLast?_cons₂ a b t').symm⟩

/-! ### `Lem:domain` -/

/-- **Lemma (computable domain).**  If a continuation `c` has a (non-null) successor in a
    consistent trace, then the redex it selects, `map (getIndex c) c`, lies in the
    computable opcode domain `D`.  Proof: `next` only produces `some _` after passing the
    `inDomain` guard on `map (getIndex c) c`. -/
theorem domain {c t : Verb} (h : Step c t) :
    ∃ i sub, getIndex c = some i ∧ map i c = some sub ∧ inDomain sub = true := by
  unfold Step next at h
  split at h
  · simp at h
  · rename_i i hg
    split at h
    · simp at h
    · rename_i sub hm
      split at h
      · rename_i hd
        exact ⟨i, sub, hg, hm, hd⟩
      · simp at h

/-! ### `lemma:equiv_continuations` -/

/-- **Lemma (continuation equivalence).**  `NockVM ≡ FiniteTransitions`: the finite verbs
    are exactly the continuations of finite verbs.  (⇒) a finite verb is a continuation of
    itself; (⇐) the suffix of a complete trace from any of its members is itself complete. -/
theorem equiv_continuations (F : Verb) : Finite F ↔ FiniteTransition F := by
  constructor
  · rintro ⟨T, hTof, hComp⟩
    exact ⟨F, T, hTof, hComp, head?_some_mem hTof.1⟩
  · rintro ⟨F0, T, hTof, ⟨v, hlast, hnext⟩, hmem⟩
    obtain ⟨S, hS1, hS2, hS3⟩ := consistent_suffix_of_mem T hTof.2 hmem
    exact ⟨S, ⟨hS1, hS2⟩, ⟨v, hS3.trans hlast, hnext⟩⟩

/-! ### `Thm:deterministic_Trace` -/

/-- Two consistent traces with equal heads and equal lengths are equal.  This is the
    inductive core of determinism: `Step` is functional (`Step.det`), so each verb of the
    trace is forced by its predecessor. -/
theorem trace_unique (T1 : List Verb) : ∀ (T2 : List Verb),
    Consistent T1 → Consistent T2 → T1.head? = T2.head? → T1.length = T2.length → T1 = T2 := by
  induction T1 with
  | nil =>
      intro T2 _ _ _ hl
      cases T2 with
      | nil => rfl
      | cons _ _ => simp at hl
  | cons a t1 ih =>
      intro T2 h1 h2 hh hl
      cases T2 with
      | nil => simp at hl
      | cons c t2 =>
          have hac : a = c := by
            simp only [List.head?_cons, Option.some.injEq] at hh; exact hh
          subst hac
          cases t1 with
          | nil =>
              cases t2 with
              | nil => rfl
              | cons _ _ => simp at hl
          | cons b t1' =>
              cases t2 with
              | nil => simp at hl
              | cons d t2' =>
                  simp only [Consistent] at h1 h2
                  obtain ⟨hab, hbt⟩ := h1
                  obtain ⟨had, hdt⟩ := h2
                  have hbd : b = d := Step.det hab had
                  subst hbd
                  have hrec : (b :: t1') = (b :: t2') :=
                    ih (b :: t2') hbt hdt (by simp)
                      (by simp only [List.length_cons] at hl ⊢; omega)
                  exact congrArg (a :: ·) hrec

/-- **Theorem (deterministic trace), functional form.**  For every verb `F` and every `n`
    there is at most one consistent trace of size `n`.  This form is proved from `Step.det`
    — i.e. from `next` being a Lean *function* — so its proof does NOT use the strict
    ordering of `map` (the selection order is already baked into the function `next`).  For
    the *conditional* statement, where strictness is genuinely the hypothesis that
    yields determinism, see `deterministic_Trace_strict` / `selStep_deterministic_Trace`
    below. -/
theorem deterministic_Trace {F : Verb} {n : Nat} {T1 T2 : List Verb}
    (h1 : TraceOf F T1) (h2 : TraceOf F T2)
    (hn1 : T1.length = n + 1) (hn2 : T2.length = n + 1) : T1 = T2 :=
  trace_unique T1 T2 h1.2 h2.2 (h1.1.trans h2.1.symm) (by omega)

/-! ### The *conditional* theorem

    `Thm:deterministic_Trace` is conditional on `map` enforcing a *strict* ordering.  Here we
    mechanize exactly that: over an abstract strict selection order (`Verb.StrictSelect`) the
    redex-selection step (`Verb.SelStep`) is deterministic (`Verb.SelStep.det`, whose proof
    genuinely uses strictness), hence a verb has at most one consistent trace of each size.
    The concrete interpreter is then a *special case*: the DFS order is strict
    (`Verb.strictSelect_dfs`) and `next` realizes `SelStep` (`Verb.next_eq_some_iff`), which
    recovers the concrete theorem as `deterministic_Trace_strict`. -/

/-- Consistency of a trace with respect to an arbitrary transition relation `R`
    (`Consistent` is the special case `R = Step`). -/
def ConsistentR (R : Verb → Verb → Prop) : List Verb → Prop
  | []             => True
  | [_]            => True
  | a :: b :: rest => R a b ∧ ConsistentR R (b :: rest)

/-- Trace uniqueness for **any deterministic** transition relation.  Determinism of the
    relation is the only hypothesis; this is the inductive core shared by the functional and
    the strict-order forms. -/
theorem trace_unique_of_det {R : Verb → Verb → Prop}
    (hdet : ∀ {a b b' : Verb}, R a b → R a b' → b = b') :
    ∀ (T1 T2 : List Verb), ConsistentR R T1 → ConsistentR R T2 →
      T1.head? = T2.head? → T1.length = T2.length → T1 = T2 := by
  intro T1
  induction T1 with
  | nil =>
      intro T2 _ _ _ hl
      cases T2 with
      | nil => rfl
      | cons _ _ => simp at hl
  | cons a t1 ih =>
      intro T2 h1 h2 hh hl
      cases T2 with
      | nil => simp at hl
      | cons c t2 =>
          have hac : a = c := by
            simp only [List.head?_cons, Option.some.injEq] at hh; exact hh
          subst hac
          cases t1 with
          | nil =>
              cases t2 with
              | nil => rfl
              | cons _ _ => simp at hl
          | cons b t1' =>
              cases t2 with
              | nil => simp at hl
              | cons d t2' =>
                  simp only [ConsistentR] at h1 h2
                  obtain ⟨hab, hbt⟩ := h1
                  obtain ⟨had, hdt⟩ := h2
                  have hbd : b = d := hdet hab had
                  subst hbd
                  have hrec : (b :: t1') = (b :: t2') :=
                    ih (b :: t2') hbt hdt (by simp)
                      (by simp only [List.length_cons] at hl ⊢; omega)
                  exact congrArg (a :: ·) hrec

/-- A trace w.r.t. an arbitrary transition relation `R` (generalizing `TraceOf`). -/
def TraceOfR (R : Verb → Verb → Prop) (F : Verb) (T : List Verb) : Prop :=
  T.head? = some F ∧ ConsistentR R T

/-- **Theorem (deterministic trace), faithful conditional form.**  *If* the redex-selection
    order `lt` is strict, then for every verb `F` and every `n` there is at most one
    consistent (`SelStep lt`) trace of size `n`.  The strictness hypothesis is *load-bearing*:
    it enters through `SelStep.det`, which needs it to force a unique selected redex.  Mirrors `Thm:deterministic_Trace`. -/
theorem selStep_deterministic_Trace {lt : Nat → Nat → Prop} (hs : StrictSelect lt)
    {F : Verb} {n : Nat} {T1 T2 : List Verb}
    (h1 : TraceOfR (SelStep lt) F T1) (h2 : TraceOfR (SelStep lt) F T2)
    (hn1 : T1.length = n + 1) (hn2 : T2.length = n + 1) : T1 = T2 :=
  trace_unique_of_det (R := SelStep lt)
    (fun {a b b'} (hab : SelStep lt a b) (hab' : SelStep lt a b') => SelStep.det hs hab hab')
    T1 T2 h1.2 h2.2 (h1.1.trans h2.1.symm) (by omega)

/-- The concrete consistency (`Consistent`, via `next`) is exactly `SelStep dfsLt`
    consistency, because `next` realizes the DFS selection step (`next_eq_some_iff`). -/
theorem consistent_iff_selStep : ∀ (T : List Verb),
    Consistent T ↔ ConsistentR (SelStep dfsLt) T
  | []             => Iff.rfl
  | [_]            => Iff.rfl
  | a :: b :: rest => by
      simp only [Consistent, ConsistentR]
      exact and_congr next_eq_some_iff (consistent_iff_selStep (b :: rest))

/-- **`deterministic_Trace`, recovered via genuine strictness.**  The concrete DFS
    interpreter's trace determinism is an *instance* of the conditional theorem: the
    DFS order is strict (`strictSelect_dfs`) and `next` realizes `SelStep dfsLt`
    (`next_eq_some_iff`).  Same statement as `deterministic_Trace`, but its proof flows
    through the strict-ordering hypothesis rather than through `next` being a raw function. -/
theorem deterministic_Trace_strict {F : Verb} {n : Nat} {T1 T2 : List Verb}
    (h1 : TraceOf F T1) (h2 : TraceOf F T2)
    (hn1 : T1.length = n + 1) (hn2 : T2.length = n + 1) : T1 = T2 :=
  selStep_deterministic_Trace strictSelect_dfs
    ⟨h1.1, (consistent_iff_selStep T1).1 h1.2⟩
    ⟨h2.1, (consistent_iff_selStep T2).1 h2.2⟩ hn1 hn2

/-! ### Corollary: valid and invalid verbs are finite

    Both `Valid` and `Invalid` already carry a *complete* trace (a witness ending in a verb with
    no successor), so finiteness is immediate. -/

/-- **Corollary (valid ⇒ finite).**  A valid verb terminates. -/
theorem finite_of_valid {F : Verb} (h : Valid F) : Finite F := by
  obtain ⟨T, v, hT, hl, hn, _⟩ := h
  exact ⟨T, hT, v, hl, hn⟩

/-- **Corollary (invalid ⇒ finite).**  An invalid verb (one that crashes) still terminates. -/
theorem finite_of_invalid {F : Verb} (h : Invalid F) : Finite F := by
  obtain ⟨T, v, hT, hl, hn, _⟩ := h
  exact ⟨T, hT, v, hl, hn⟩

/-- **Corollary 4.1.**  *All valid and invalid verbs are finite.*  The single
    statement of the corollary: any verb that is `Valid` **or** `Invalid`
    carries a complete trace, hence is `Finite`.  (Both disjuncts already give a complete-trace
    witness; this is their common consequence.) -/
theorem finite_of_valid_or_invalid {F : Verb} (h : Valid F ∨ Invalid F) : Finite F :=
  h.elim finite_of_valid finite_of_invalid

/-! ### The size bound `λ ≤ Λ` on the verb languages

    `NockVM^Λ` and `FiniteTransitions^Λ` carry a *size bound* `λ ≤ Λ`, where `λ = len(noun)` is the number of leaves
    of the verb's noun.  The unbounded `Finite`/`FiniteTransition` above drop it;
    the `Λ`-bounded predicates below add it. -/

/-- The length `λ = |d|` of a verb: the number of leaves of its noun. -/
def size (F : Verb) : Nat := F.leaves

/-- `F ∈ NockVM^Λ`: `F` is finite *and* has length `λ ≤ Λ`. -/
def FiniteΛ (Λ : Nat) (F : Verb) : Prop := Finite F ∧ size F ≤ Λ

/-- `F ∈ FiniteTransitions^Λ`: `F` is a continuation of a finite verb *and* `λ ≤ Λ`. -/
def FiniteTransitionΛ (Λ : Nat) (F : Verb) : Prop := FiniteTransition F ∧ size F ≤ Λ

/-- **Continuation equivalence, `Λ`-bounded.**  `NockVM^Λ ≡ FiniteTransitions^Λ`: the size bound
    is shared, so this is `equiv_continuations` conjoined with `λ ≤ Λ`. -/
theorem equiv_continuationsΛ (Λ : Nat) (F : Verb) : FiniteΛ Λ F ↔ FiniteTransitionΛ Λ F :=
  and_congr (equiv_continuations F) Iff.rfl

/-! ### `NockProgram^Λ` / `NockValidProgram^Λ` and the strict inclusion -/

/-- **`F ∈ NockProgram^Λ`**: `F = *[subject, formula]` where `subject` and
    `formula` are in terminal state, and `F` has length `λ ≤ Λ`.  (`isTerminal subject/formula`
    is Property 2 "subject and formula are in terminal state"; the `.star` root with the two
    terminal children is Property 1 "`F = *[subject, formula]`".) -/
def IsNockProgram (Λ : Nat) (F : Verb) : Prop :=
  (∃ subject formula, F = .node .star subject formula
      ∧ isTerminal subject = true ∧ isTerminal formula = true)
    ∧ size F ≤ Λ

/-- **`F ∈ NockValidProgram^Λ`**: a Nock program that is a *valid* verb. -/
def NockValidProgramΛ (Λ : Nat) (F : Verb) : Prop := IsNockProgram Λ F ∧ Valid F

/-- Subset of verb-languages (`⊆`): every verb in `P` is in `Q`. -/
def SubLang (P Q : Verb → Prop) : Prop := ∀ ⦃F⦄, P F → Q F

/-- **Strict inclusion of verb-languages (`⊊`)**: `P ⊆ Q` together with a witness in `Q ∖ P`.
    This is exactly the meaning of the set-theoretic `⊊` (proper subset = subset + a strictly
    separating element), spelled out at the predicate level. -/
def SSubLang (P Q : Verb → Prop) : Prop := SubLang P Q ∧ ∃ F, Q F ∧ ¬ P F

/-- A terminal leaf is finite: its one-element trace `[leaf n]` is complete. -/
theorem finite_leaf (n : Nat) : Finite (.leaf n) :=
  ⟨[.leaf n], ⟨rfl, trivial⟩, .leaf n, rfl, next_none_of_terminal rfl⟩

/-- **Strict inclusion.**  `NockValidProgram^Λ ⊊ NockVM^Λ`: every valid program
    is finite of length `≤ Λ` (`⊆`, via `finite_of_valid`), and the containment is *strict* —
    e.g. the terminal leaf `0` is a finite verb of length `1 ≤ Λ` that is **not** a Nock program.  The side condition `1 ≤ Λ` is *necessary*: for `Λ = 0` both
    languages are empty (every verb has `≥ 1` leaf), so `∅ ⊊ ∅` fails; `⊊` is meant
    for the non-degenerate range. -/
theorem nockValidProgram_ssubset_nockVM {Λ : Nat} (hΛ : 1 ≤ Λ) :
    SSubLang (NockValidProgramΛ Λ) (FiniteΛ Λ) := by
  refine ⟨?_, .leaf 0, ⟨finite_leaf 0, ?_⟩, ?_⟩
  · intro F hF
    exact ⟨finite_of_valid hF.2, hF.1.2⟩
  · show size (.leaf 0) ≤ Λ
    simpa [size, leaves] using hΛ
  · rintro ⟨⟨⟨s, f, hEq, _, _⟩, _⟩, _⟩
    simp at hEq

/-! ### `NockVMROM^Λ` at the verb level

    `NockVMROM^Λ` is `NockVM^Λ` with `OP₁₀` excluded, realized by the ROM
    transition function `nextROM` (`Nock/Verb.lean`).  A ROM trace, ROM-completeness, and the
    ROM languages are the `next → nextROM` analogues of the objects above.

    **On the relation to `NockVM^Λ`.**  The faithful, unconditional relation is that `nextROM`
    is a *restriction* of `next` (`next_of_nextROM`), so every ROM trace is a Nock trace
    (`traceOf_of_traceOfROM`) and every ROM-*valid* verb is Nock-finite (`finite_of_validROM`).
    The naive `FiniteROM F → Finite F` is **FALSE**: a ROM-complete trace may end by *crashing*
    at an `OP₁₀` redex (which ROM rejects but Nock rewrites), and the Nock continuation past that
    point may diverge — so such an `F` is `FiniteROM` but not `Finite`.  The two are related by
    transition restriction and valid ⇒ finite. -/

/-- A single `NockVMROM` step (`next` restricted to exclude `OP₁₀`). -/
def StepROM (a b : Verb) : Prop := nextROM a = some b

/-- Every ROM step is a Nock step. -/
theorem step_of_stepROM {a b : Verb} (h : StepROM a b) : Step a b := next_of_nextROM h

/-- A trace is **ROM-complete** iff its last verb has no `nextROM`-successor. -/
def CompleteROM (T : List Verb) : Prop := ∃ v, T.getLast? = some v ∧ nextROM v = none

/-- `T` is a consistent ROM trace of `F` (uses `StepROM` for consistency). -/
def TraceOfROM (F : Verb) (T : List Verb) : Prop := T.head? = some F ∧ ConsistentR StepROM T

/-- Every consistent ROM trace is a consistent Nock trace (ROM steps are Nock steps). -/
theorem consistent_of_consistentROM : ∀ (T : List Verb), ConsistentR StepROM T → Consistent T
  | [],            _ => trivial
  | [_],           _ => trivial
  | _ :: _ :: rest, h => ⟨step_of_stepROM h.1, consistent_of_consistentROM (_ :: rest) h.2⟩

/-- Every ROM trace of `F` is a Nock trace of `F`. -/
theorem traceOf_of_traceOfROM {F : Verb} {T : List Verb} (h : TraceOfROM F T) : TraceOf F T :=
  ⟨h.1, consistent_of_consistentROM T h.2⟩

/-- `F` is **ROM-finite** (`F ∈ NockVMROM`): it has a complete ROM trace. -/
def FiniteROM (F : Verb) : Prop := ∃ T, TraceOfROM F T ∧ CompleteROM T

/-- `F ∈ NockVMROM^Λ`: ROM-finite *and* of length `λ ≤ Λ` (`Def:Nock` without `OP₁₀`). -/
def FiniteROMΛ (Λ : Nat) (F : Verb) : Prop := FiniteROM F ∧ size F ≤ Λ

/-- `F` is **ROM-valid**: it has a complete ROM trace ending in a terminal (non-crash) verb. -/
def ValidROM (F : Verb) : Prop :=
  ∃ T v, TraceOfROM F T ∧ T.getLast? = some v ∧ nextROM v = none ∧ isTerminal v = true

/-- **ROM-valid ⇒ finite.**  A verb that terminates *in a terminal state* using only ROM steps
    is Nock-finite: its ROM trace is a Nock trace (`traceOf_of_traceOfROM`), and its terminal
    last verb has no Nock successor either (`next_none_of_terminal`), so the trace is
    Nock-complete.  (Contrast the false `FiniteROM → Finite`, which fails on `OP₁₀`-crash ends;
    see the section note.) -/
theorem finite_of_validROM {F : Verb} (h : ValidROM F) : Finite F := by
  obtain ⟨T, v, hT, hl, _, hterm⟩ := h
  exact ⟨T, traceOf_of_traceOfROM hT, v, hl, next_none_of_terminal hterm⟩

/-! ### The two-verb checker `Nock` matches `Step`

    `NockCheck` is the
    0/1 transition VERIFIER `Nock(Tᵢ,Tᵢ₊₁)`, consuming both verbs.  Consistency of a
    trace is `Nock(tᵢ,tᵢ₊₁) = 0`, which here is `Step tᵢ tᵢ₊₁`.  The following
    restates the checker/forward-semantics equivalence (`Verb.nockCheck_eq_true_iff`) directly
    in terms of `Step`: the checker accepts `(a, b)` iff `b` is a `Step`-successor of `a`, or
    `a` crashes and `b = ⊥`.  This exhibits `Nock` as 1-1 with the trace's consistency relation
    `Step` plus the crash branch. -/

/-- **`Nock` checker ⟺ trace consistency (`Step`) + crash.**  `NockCheck a b = true` iff `b` is a `Step`-successor of `a` (`Step a v`, i.e. a
    consistent transition `Nock(a,v)=0`) or `a` crashes and `b = ⊥` (`b = none`).  This is the
    genuine biconditional making the two-verb checker 1-1 with the forward semantics `Step`
    plus the crash branch (defeq to `Verb.nockCheck_eq_true_iff`, since `Step a v := next a =
    some v`). -/
theorem nockCheck_iff_step {a : Verb} {b : Option Verb} :
    NockCheck a b = true ↔ (∃ v, b = some v ∧ Step a v) ∨ (b = none ∧ Crashes a) :=
  nockCheck_eq_true_iff

end Verb
end Nock
