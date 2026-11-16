/-
  Nock/RedTeam/Batch33PaperFieldBridge.lean

  * C1 one conditional identifies five formalizations on ONE threaded execution;
  * C2 the conditional is no-overflow, discharged by running, not vacuous;
  * C3 injectivity is the payoff, not a second premise;
  * C4 `evalFBy_of_evalGPaper` is the conclusion in the exact shape the Theorem-5.4 row
    certificates consume;
  * C6 scope: languages only.

  Every finding is a compiled
  declaration; where an attack fails, the compiled witness records that it fails.

  Summary of what compiled here:

  * A. The prover's only non-vacuity witness is at the COMPOSITE modulus `q = 100`, where
    `ZMod q` is not a field (`b33_composite_modulus_is_not_a_field`).  The bridge is repaired,
    not refuted: it is instantiated here at the genuine prime `5` and at the real Goldilocks
    characteristic `Nock.Field.p`, and primality is never used — the Goldilocks instance does
    not even pull `Field.goldilocks_prime`.
  * B. No conjunct of `paper_field_bridge` survives dropping `hG`, so nothing is padding; and
    the `∃ n` on `runProgram` is FORCED — the same-fuel strengthening is compiled FALSE.
  * C. `evalGPaper q` differs from `evalPaperMod q` in OP₄ and nowhere else: both are
    instances of one generic-increment functional (`b33_evalPaperGen_*`).  The fragment cut is
    at `op ≥ 11` exactly.
  * E. `evalFBy_of_evalGPaper` really does plug into `s3_vcomp_semantics`,
    `s4_vcomp_semantics` and `SemanticTrace.LocalOpcodeCertificate` — compiled applications.
    For the OP₄ row it supplies BOTH increment premises from one guarded parent run.
  * F.
  * G. The §(I) delta is intact and the guard cuts exactly at the wrap.
-/

import Nock.PaperFieldBridge
import Nock.NockVMROM.Thm54.SemanticTrace
import Nock.NockVMROM.Thm54.StrictPackage

namespace Nock.RedTeam.Batch33

open Nock Nock.Noun
open Nock.ComputeTable
open Nock.NockVMROM.Thm54

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## A. Vacuity / weak witness: the prover's modulus is composite
    ══════════════════════════════════════════════════════════════════════════════════════

`Nock.bridge_nonvacuous` fires at `q = 100`.  `100` is not prime, so `ZMod 100` is not a
field and the paper's `𝔽` (the paper`\mathcal{DT}(\mathbb{F})`) is not modeled by
`FNounBy 100`.  The witness is therefore inadequate *as a field witness* — but the theorem is
not: nothing in the bridge needs primality.  Both facts are compiled. -/

/-- **Finding A1 (labelling).**  The prover's non-vacuity modulus is composite, and `ZMod 100`
has zero divisors, so `FieldEmbedding.FNounBy 100` does not have field leaves. -/
theorem b33_composite_modulus_is_not_a_field :
    ¬ Nat.Prime 100 ∧ (10 : ZMod 100) ≠ 0 ∧ (10 : ZMod 100) * 10 = 0 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> decide

/-! ### A2. The repair: the bridge at a genuine prime -/

/-- The guarded fragment run `*[0 [4 [1 3]]] = 4` at the prime modulus `5`. -/
theorem b33_evalGPaper_run_at_prime_5 :
    evalGPaper 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
      = some (.atom 4) := by
  decide

/-- **Non-vacuity at a genuine prime.**  The full six-fold bridge conclusion, instantiated at
`q = 5` (so `ZMod q` really is a field). -/
theorem b33_bridge_conclusion_at_prime_5 :
    (∃ n, Verb.runProgram n (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4)) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3))) = some (.atom 4) ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      FieldEmbedding.evalFBy 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalN 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3))) = some (.atom 4) ∧
      FieldEmbedding.BoundedBy 5 (.atom 4) :=
  paper_field_bridge 5 (by norm_num) (by norm_num) (by norm_num) b33_evalGPaper_run_at_prime_5

/-! ### A3. The repair: the bridge at the real Goldilocks characteristic

`Nock.Field.p = 2^64 − 2^32 + 1`. -/

/-- The guarded fragment run `*[0 [4 [1 42]]] = 43` at the Goldilocks modulus. -/
theorem b33_evalGPaper_run_at_goldilocks :
    evalGPaper Nock.Field.p 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42)))
      = some (.atom 43) := by
  simp only [Nock.Field.p_eq]
  decide

/-- **Non-vacuity at the paper's own characteristic.**  The bridge conclusion at
`q = Nock.Field.p`.  Its `#print axioms` (below) shows it does NOT pull
`Nock.Field.goldilocks_prime`: the bridge is primality-free. -/
theorem b33_bridge_conclusion_at_goldilocks :
    (∃ n, Verb.runProgram n (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42)))
        = some (.atom 43)) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42)))
        = some (.atom 43) ∧
      evalPaperMod Nock.Field.p 5 (.atom 0)
          (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      FieldEmbedding.evalFBy Nock.Field.p 5 (.atom 0)
          (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      evalN 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      FieldEmbedding.BoundedBy Nock.Field.p (.atom 43) :=
  paper_field_bridge Nock.Field.p FieldEmbedding.one_lt_p
    (by simp [Nock.Field.p_eq]) (by norm_num [Nock.Field.p_eq]) b33_evalGPaper_run_at_goldilocks

/-- **Attack A fails on the mathematics: primality is genuinely unused.**  The leaf-cast
injectivity that carries OP₅ equality needs only `NeZero q`, so it holds even at the composite
modulus the prover chose. -/
theorem b33_injectivity_needs_no_primality :
    ∀ {a b : Noun}, FieldEmbedding.BoundedBy 100 a → FieldEmbedding.BoundedBy 100 b →
      FieldEmbedding.embBy 100 a = FieldEmbedding.embBy 100 b → a = b :=
  FieldEmbedding.embBy_inj_of_boundedBy

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## B. Weakening / independently-quantified bundling
    ══════════════════════════════════════════════════════════════════════════════════════ -/

/-- **No conjunct is padding.**  Drop `hG` and both the `evalPaper` conjunct and the
`BoundedBy q r` conjunct become false, so every conjunct genuinely consumes the hypothesis
(each mentions `r`, and `r` is introduced only by `hG`). -/
theorem b33_no_conjunct_survives_dropping_hG :
    ¬ (∀ (q fuel : ℕ) (s f r : Noun), 1 < q →
        FieldEmbedding.BoundedBy q s → FieldEmbedding.BoundedBy q f →
        evalPaper fuel s f = some r) ∧
      ¬ (∀ (q : ℕ) (r : Noun), 1 < q → FieldEmbedding.BoundedBy q r) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact absurd (h 100 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42)))
      (.atom 0) (by norm_num) (by norm_num) (by norm_num)) (by decide)
  · exact absurd (h 5 (.atom 7) (by norm_num)) (by decide)

/-- **The conjunction really is threaded on one result noun.**  From the single hypothesis the
five evaluators' *outputs* are equal as `Option Noun` values — impossible if the conjuncts were
independently quantified. -/
theorem b33_bridge_is_threaded (q : ℕ) (hq : 1 < q) {fuel : ℕ} {s f r : Noun}
    (hs : FieldEmbedding.BoundedBy q s) (hf : FieldEmbedding.BoundedBy q f)
    (hG : evalGPaper q fuel s f = some r) :
    evalPaper fuel s f = evalPaperMod q fuel s f ∧
      evalPaperMod q fuel s f = FieldEmbedding.evalFBy q fuel s f ∧
      FieldEmbedding.evalFBy q fuel s f = evalN fuel s f := by
  obtain ⟨-, hP, hM, hF, hN, -⟩ := paper_field_bridge q hq hs hf hG
  exact ⟨by rw [hP, hM], by rw [hM, hF], by rw [hF, hN]⟩

/-- **Attack B fails: the `∃ n` on `runProgram` is not a weakening, it is forced.**  The
small-step machine counts rewrite steps while `evalGPaper` counts recursion depth, so the
same-fuel strengthening of the first conjunct is FALSE: at `fuel = 3` the guarded fragment
evaluator already returns the answer while `Verb.runProgram 3` has not finished. -/
theorem b33_shared_fuel_strengthening_is_false :
    ¬ (∀ (q fuel : ℕ) (s f r : Noun), 1 < q →
        FieldEmbedding.BoundedBy q s → FieldEmbedding.BoundedBy q f →
        evalGPaper q fuel s f = some r → Verb.runProgram fuel s f = some r) := by
  intro h
  exact absurd
    (h 100 3 (.atom 0)
      (.cell (.cell (.cell (.atom 1) (.atom 1)) (.cell (.atom 1) (.atom 2)))
        (.cell (.cell (.atom 1) (.atom 3)) (.cell (.atom 1) (.atom 4))))
      (.cell (.cell (.atom 1) (.atom 2)) (.cell (.atom 3) (.atom 4)))
      (by norm_num) (by norm_num) (by norm_num) (by decide))
    (by decide)

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## C. Definitional drift: is OP₄ really the only difference?
    ══════════════════════════════════════════════════════════════════════════════════════

Rather than compare clause bodies by eye, abstract the increment.  `evalPaperGen inc` is the
paper's OP₀..OP₁₀ fragment with OP₄ = `inc`.  Both `evalPaperMod q` and
`evalGPaper q` are instances of it, which pins "the only difference is OP₄" exactly. -/

/-- The paper's OP₀..OP₁₀ fragment with the OP₄ increment abstracted. -/
def evalPaperGen (inc : Noun → Option Noun) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalPaperGen inc fuel subj (.cell b c), evalPaperGen inc fuel subj d with
      | some l, some r => some (.cell l r)
      | _, _ => none
  | fuel + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => match tail with
           | .atom ax => slot ax subj
           | _ => none
    | 1 => some tail
    | 2 => match tail with
           | .cell b c =>
             match evalPaperGen inc fuel subj b, evalPaperGen inc fuel subj c with
             | some sb, some sc => evalPaperGen inc fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalPaperGen inc fuel subj tail).map wut
    | 4 => (evalPaperGen inc fuel subj tail).bind inc
    | 5 => match tail with
           | .cell b c =>
             match evalPaperGen inc fuel subj b, evalPaperGen inc fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalPaperGen inc fuel subj b with
             | some (.atom 0) => evalPaperGen inc fuel subj c
             | some (.atom 1) => evalPaperGen inc fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalPaperGen inc fuel subj b with
             | some sb => evalPaperGen inc fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalPaperGen inc fuel subj b with
             | some sb => evalPaperGen inc fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalPaperGen inc fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalPaperGen inc fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalPaperGen inc fuel subj c, evalPaperGen inc fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | _ => none

/-- **`evalPaperMod q` is the generic fragment at the paper's modular increment.** -/
theorem b33_evalPaperGen_eq_evalPaperMod (q : ℕ) :
    ∀ (fuel : ℕ) (s f : Noun),
      evalPaperGen (FieldEmbedding.lusFBy q) fuel s f = evalPaperMod q fuel s f := by
  intro fuel s f
  induction fuel, s, f using evalPaperGen.induct (FieldEmbedding.lusFBy q) <;>
    simp_all [evalPaperGen, evalPaperMod]

/-- **`evalGPaper q` is the same generic fragment at the guarded increment.**  Together with
the previous theorem this is the compiled statement that OP₄ is the ONLY clause in which the
two fragment evaluators differ. -/
theorem b33_evalPaperGen_eq_evalGPaper (q : ℕ) :
    ∀ (fuel : ℕ) (s f : Noun),
      evalPaperGen (FieldEmbedding.lusGBy q) fuel s f = evalGPaper q fuel s f := by
  intro fuel s f
  induction fuel, s, f using evalPaperGen.induct (FieldEmbedding.lusGBy q) <;>
    simp_all [evalPaperGen, evalGPaper]

/-- The OP₄ clause of `evalGPaper`, isolated. -/
theorem b33_evalGPaper_op4 (q fuel : ℕ) (s tail : Noun) :
    evalGPaper q (fuel + 1) s (.cell (.atom 4) tail)
      = (evalGPaper q fuel s tail).bind (FieldEmbedding.lusGBy q) := rfl

/-- **The fragment cut is at `op ≥ 11` exactly**. -/
theorem b33_evalGPaper_crashes_above_op10 (q fuel : ℕ) (s tail : Noun) {op : ℕ}
    (hop : 11 ≤ op) : evalGPaper q (fuel + 1) s (.cell (.atom op) tail) = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hop
  rfl

/-- **The OP₁₁ boundary is real, not vacuous.**  The full guarded evaluator `evalGBy` accepts
an OP₁₁ hint formula; the paper-fragment evaluator crashes on the very same formula. -/
theorem b33_op11_separates_fragment_from_full :
    FieldEmbedding.evalGBy 100 3 (.atom 0)
        (.cell (.atom 11) (.cell (.atom 1) (.cell (.atom 1) (.atom 7)))) = some (.atom 7) ∧
      evalGPaper 100 3 (.atom 0)
        (.cell (.atom 11) (.cell (.atom 1) (.cell (.atom 1) (.atom 7)))) = none := by
  refine ⟨by decide, by decide⟩

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## F/G. The guard IS `IncrementNoOverflow`
    ══════════════════════════════════════════════════════════════════════════════════════

This is the hinge of attacks F and G.  `Batch22Thm54ModularOperational` recorded that
`OpcodeSemantics.IncrementNoOverflow` is a *Nat-evaluator artifact* which the strict modular
OP₄ removes, because modular increment is total.  The bridge's
single hypothesis re-introduces exactly that condition — not by a back door, but as its
stated premise.  Compiled pointwise, then propagated to a whole run. -/

/-- **The guard is pointwise identical to `IncrementNoOverflow`.** -/
theorem b33_guard_is_exactly_incrementNoOverflow (q : ℕ) (v : Noun) :
    (FieldEmbedding.lusGBy q v).isSome = true ↔
      OpcodeSemantics.IncrementNoOverflow q v := by
  cases v with
  | atom n =>
      by_cases hlt : n + 1 < q
      · simp [FieldEmbedding.lusGBy, OpcodeSemantics.IncrementNoOverflow, hlt]
      · simp [FieldEmbedding.lusGBy, OpcodeSemantics.IncrementNoOverflow, hlt]
  | cell l r => simp [FieldEmbedding.lusGBy, OpcodeSemantics.IncrementNoOverflow]

/-- A successful guarded increment yields the row certificates' two OP₄ data. -/
theorem b33_lusGBy_gives_incrementNoOverflow {q : ℕ} {v r : Noun}
    (h : FieldEmbedding.lusGBy q v = some r) :
    OpcodeSemantics.IncrementNoOverflow q v ∧ r = OpcodeSemantics.incNoWrap v := by
  cases v with
  | atom n =>
      by_cases hlt : n + 1 < q
      · simp only [FieldEmbedding.lusGBy, if_pos hlt, Option.some.injEq] at h
        exact ⟨hlt, by simp [OpcodeSemantics.incNoWrap, ← h]⟩
      · simp [FieldEmbedding.lusGBy, hlt] at h
  | cell l r => simp [FieldEmbedding.lusGBy] at h

/-- **A guarded OP₄ parent run supplies `IncrementNoOverflow` for its child value.**  So the
bridge's hypothesis is at least as strong as the `s4` row premise `hno`, at every OP₄ node the
run reaches. -/
theorem b33_incrementNoOverflow_of_parent_run {q fuel : ℕ} {s f v rP : Noun}
    (hchild : evalGPaper q fuel s f = some v)
    (hparent : evalGPaper q (fuel + 1) s (.cell (.atom 4) f) = some rP) :
    OpcodeSemantics.IncrementNoOverflow q v ∧ rP = OpcodeSemantics.incNoWrap v := by
  rw [b33_evalGPaper_op4, hchild, Option.bind_some] at hparent
  exact b33_lusGBy_gives_incrementNoOverflow hparent

/-- **The bridge's CONCLUSION is not enough for the `s4` premise.**  `BoundedBy q` gives
`n < q`; `IncrementNoOverflow q` needs `n + 1 < q` and excludes cells.  So `hno` must come from
the guard at the parent OP₄ node (previous theorem), never from `BoundedBy q r`. -/
theorem b33_boundedBy_is_not_incrementNoOverflow :
    FieldEmbedding.BoundedBy 5 (.atom 4) ∧
      ¬ OpcodeSemantics.IncrementNoOverflow 5 (.atom 4) ∧
      FieldEmbedding.BoundedBy 5 (.cell (.atom 0) (.atom 0)) ∧
      ¬ OpcodeSemantics.IncrementNoOverflow 5 (.cell (.atom 0) (.atom 0)) := by
  refine ⟨by norm_num, ?_, by norm_num, ?_⟩ <;>
    simp [OpcodeSemantics.IncrementNoOverflow]

/-- **The bridge's premise is STRICTLY stronger than the strict-paper premise.**  Forward
inclusion is the prover's `evalGPaper_le_evalPaperMod`; strictness is the top-residue run at
the prime `5`, where the paper's own modular OP₄ succeeds and the guard refuses. -/
theorem b33_guard_strictly_stronger_than_strict_paper :
    (∀ (q fuel : ℕ) (s f r : Noun),
        evalGPaper q fuel s f = some r → evalPaperMod q fuel s f = some r) ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4)))
        = some (.atom 0) ∧
      evalGPaper 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4))) = none :=
  ⟨fun _ _ _ _ _ h => evalGPaper_le_evalPaperMod h, by decide, by decide⟩

/-- **The row certificates' `hcall` premise was already available WITHOUT the guard.**  This is
the pre-existing `evalPaperMod_le_evalFBy`.  With the strictness above, `evalFBy_of_evalGPaper`
therefore factors a premise the repository could already discharge through a strictly stronger,
non-paper condition.  Its added value is the identification with `evalPaper`/`runProgram`/`evalN`,
not the supply of `hcall`. -/
theorem b33_hcall_available_without_the_guard {q fuel : ℕ} {s f r : Noun}
    (h : evalPaperMod q fuel s f = some r) :
    FieldEmbedding.evalFBy q fuel s f = some r :=
  evalPaperMod_le_evalFBy h

/-- At the prime `5` the paper's
modular increment wraps the top residue to `0`, the unbounded Nat increment gives `5`, and the
guard refuses — so the bridge never claims the two languages coincide. -/
theorem b33_census_I_delta_intact :
    FieldEmbedding.lusFBy 5 (.atom 4) = some (.atom 0) ∧
      Noun.lus (.atom 4) = some (.atom 5) ∧
      FieldEmbedding.lusGBy 5 (.atom 4) = none ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4)))
        = some (.atom 0) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4))) = some (.atom 5) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## E. Wrong layer: does the bridge actually reach the consumed capstones?
    ══════════════════════════════════════════════════════════════════════════════════════

The claim under attack is C4: `evalFBy_of_evalGPaper` is "the conclusion in the exact shape the
row certificates consume".  The test is not a shape comparison in prose — it is whether a term
type-checks with the bridge's output in the `hcall` position of the production theorems.  It
does; all remaining premises are the AIR-row data the bridge neither supplies nor claims to. -/

variable {K : Type*} [Field K]

/-- **The bridge feeds `OpcodeSemantics.s3_vcomp_semantics`.**  Statement copied from the
production theorem with its `hcall` premise replaced by a guarded fragment run. -/
theorem b33_bridge_feeds_s3_vcomp {q fuel : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hstate : pub.state = .s3) (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : OpcodeSemantics.RootRealization inp pub dec)
    (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (hhead : OpcodeSemantics.PairFaithful inp.z q row.head (.atom 3))
    (hformula : OpcodeSemantics.PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (h1s : OpcodeSemantics.PairFaithful inp.z q call1.subject row.subject)
    (h1f : OpcodeSemantics.PairFaithful inp.z q call1.formula row.tail)
    (hresult : OpcodeSemantics.PairFaithful inp.z q row.result (Noun.wut call1.result))
    (hsize : OpcodeSemantics.SizeWindow inp.z call1.result)
    (hG : evalGPaper q fuel call1.subject call1.formula = some call1.result)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (.node .minus (.leaf 3)
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun row.tail)))
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula = some row.result :=
  OpcodeSemantics.s3_vcomp_semantics hstate hz hcast row call1 hhead hformula h1s h1f hresult
    hsize (evalFBy_of_evalGPaper hG) hv

theorem b33_bridge_feeds_s4_vcomp {q fuel : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K} {rP : Noun}
    (hstate : pub.state = .s4) (hz : inp.z ≠ 0)
    (hq : q = ringChar K)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (row : OpcodeSemantics.RootRealization inp pub dec)
    (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (hhead : OpcodeSemantics.PairFaithful inp.z q row.head (.atom 4))
    (hformula : OpcodeSemantics.PairFaithful inp.z q row.formula (.cell row.head row.tail))
    (h1s : OpcodeSemantics.PairFaithful inp.z q call1.subject row.subject)
    (h1f : OpcodeSemantics.PairFaithful inp.z q call1.formula row.tail)
    (hresult : OpcodeSemantics.PairFaithful inp.z q row.result
      (OpcodeSemantics.incMod (ringChar K) call1.result))
    (hsize : OpcodeSemantics.SizeWindow inp.z call1.result)
    (hchild : evalGPaper q fuel call1.subject call1.formula = some call1.result)
    (hparent : evalGPaper q (fuel + 1) call1.subject (.cell (.atom 4) call1.formula) = some rP)
    (hv : Vcomp inp pub dec) :
    Verb.StepROM
        (Verb.program row.subject row.formula)
        (.node .minus (.leaf 4)
          (.node .star (Verb.ofNoun row.subject) (Verb.ofNoun row.tail)))
      ∧ FieldEmbedding.evalFBy q (fuel + 1) row.subject row.formula = some row.result :=
  OpcodeSemantics.s4_vcomp_semantics hstate hz hq hcast row call1 hhead hformula h1s h1f hresult
    hsize (evalFBy_of_evalGPaper hchild) hv

/-- **The bridge feeds `SemanticTrace.LocalOpcodeCertificate` (OP₃ row).**  `SemanticTrace` is
stated at `Type`-level `K`, hence the local binder. -/
def b33_bridge_builds_local_certificate_s3 {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (data : SemanticTrace.ComputeRowSemanticData q Λ (.s3, (inp, pub, dec)))
    (fuel : ℕ)
    (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (hstate : pub.state = .s3) (hz : inp.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hhead : SemanticTrace.ComparisonListed data .opcodeHead data.root.head (.atom 3))
    (hformula : SemanticTrace.ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail))
    (h1s : SemanticTrace.ComparisonListed data .recursiveSubject call1.subject
      data.root.subject)
    (h1f : SemanticTrace.ComparisonListed data .recursiveFormula call1.formula data.root.tail)
    (hresult : SemanticTrace.ComparisonListed data .producedResult data.root.result
      (Noun.wut call1.result))
    (hsize : OpcodeSemantics.SizeWindow inp.z call1.result)
    (hG : evalGPaper q fuel call1.subject call1.formula = some call1.result)
    (hv : Vcomp inp pub dec) :
    SemanticTrace.LocalOpcodeCertificate q Λ data :=
  .s3 data fuel call1 hstate hz hcast hhead hformula h1s h1f hresult hsize
    (evalFBy_of_evalGPaper hG) hv

/-- The bridge feeds the modular OP4 local certificate. -/
def b33_bridge_builds_local_certificate_s4 {K : Type} [Field K] {q Λ : ℕ}
    {inp : Inputs K} {pub : Pub K} {dec : Dec K} {rP : Noun}
    (data : SemanticTrace.ComputeRowSemanticData q Λ (.s4, (inp, pub, dec)))
    (fuel : ℕ)
    (call1 : OpcodeSemantics.CallRealization inp.z pub.sf1_s pub.sf1_f pub.sf1_e)
    (hstate : pub.state = .s4) (hz : inp.z ≠ 0)
    (hq : q = ringChar K)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hhead : SemanticTrace.ComparisonListed data .opcodeHead data.root.head (.atom 4))
    (hformula : SemanticTrace.ComparisonListed data .formulaCons data.root.formula
      (.cell data.root.head data.root.tail))
    (h1s : SemanticTrace.ComparisonListed data .recursiveSubject call1.subject
      data.root.subject)
    (h1f : SemanticTrace.ComparisonListed data .recursiveFormula call1.formula data.root.tail)
    (hresult : SemanticTrace.ComparisonListed data .producedResult data.root.result
      (OpcodeSemantics.incMod (ringChar K) call1.result))
    (hsize : OpcodeSemantics.SizeWindow inp.z call1.result)
    (hchild : evalGPaper q fuel call1.subject call1.formula = some call1.result)
    (hparent : evalGPaper q (fuel + 1) call1.subject (.cell (.atom 4) call1.formula) = some rP)
    (hv : Vcomp inp pub dec) :
    SemanticTrace.LocalOpcodeCertificate q Λ data :=
  .s4 data fuel call1 hstate hz hq hcast hhead hformula h1s h1f hresult hsize
    (evalFBy_of_evalGPaper hchild) hv

/-! ### E4. Sibling premises at ONE shared fuel

`s2_vcomp_semantics` and `LocalOpcodeCertificate.s2` need THREE `evalFBy` premises at a single
shared `fuel`, but three guarded fragment runs arrive with three independent fuels, and
`Nock/PaperFieldBridge.lean` proves no monotonicity for `evalGPaper`.  The attack fails: the
omission is not load-bearing, because monotonicity is available on the `evalFBy` side
(`evalFBy_commonFuel₃`), and `evalGPaper` monotonicity is a two-line lemma anyway. -/

/-- Guarded fragment success is stable under one more unit of fuel (the lemma the bridge does
not state; recorded here as trivially available, not as a gap). -/
theorem b33_evalGPaper_succ {q n : ℕ} {s form r : Noun}
    (h : evalGPaper q n s form = some r) : evalGPaper q (n + 1) s form = some r := by
  induction n, s, form using evalGPaper.induct q generalizing r with
  | case11 fuel subj tail ih =>
      simp only [evalGPaper, Option.map_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | case12 fuel subj tail ih =>
      simp only [evalGPaper, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | _ => simp_all [evalGPaper]

/-- Guarded fragment success is stable under any larger fuel budget. -/
theorem b33_evalGPaper_mono {q n m : ℕ} {s form r : Noun} (hnm : n ≤ m)
    (h : evalGPaper q n s form = some r) : evalGPaper q m s form = some r := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact b33_evalGPaper_succ ih

/-- **Three independent guarded runs supply the OP₂ row's three `hcall` premises at one shared
fuel.**  So the bridge does reach the multi-call rows, not only the single-call ones. -/
theorem b33_bridge_feeds_siblings_at_shared_fuel {q f₁ f₂ f₃ : ℕ}
    {s₁ p₁ r₁ s₂ p₂ r₂ s₃ p₃ r₃ : Noun}
    (h₁ : evalGPaper q f₁ s₁ p₁ = some r₁)
    (h₂ : evalGPaper q f₂ s₂ p₂ = some r₂)
    (h₃ : evalGPaper q f₃ s₃ p₃ = some r₃) :
    ∃ fuel,
      FieldEmbedding.evalFBy q fuel s₁ p₁ = some r₁ ∧
      FieldEmbedding.evalFBy q fuel s₂ p₂ = some r₂ ∧
      FieldEmbedding.evalFBy q fuel s₃ p₃ = some r₃ :=
  GlobalOpcodeScheduling.evalFBy_commonFuel₃ (evalFBy_of_evalGPaper h₁)
    (evalFBy_of_evalGPaper h₂) (evalFBy_of_evalGPaper h₃)

/-- **The bridge builds the OP₄ half of `SemanticTrace.RowStateNeeds`.**  `increment_safe` is
the row-local list form of `IncrementNoOverflow`; a family of guarded parent runs discharges it.
The list/count fields remain AIR-row data. -/
theorem b33_rowStateNeeds_increment_safe_of_guarded_runs {q : ℕ} (increments : List Noun)
    (h : ∀ v ∈ increments, ∃ (s f rP : Noun) (fuel : ℕ),
      evalGPaper q fuel s f = some v ∧
        evalGPaper q (fuel + 1) s (.cell (.atom 4) f) = some rP) :
    ∀ v ∈ increments, OpcodeSemantics.IncrementNoOverflow q v := by
  intro v hv
  obtain ⟨s, f, rP, fuel, hchild, hparent⟩ := h v hv
  exact (b33_incrementNoOverflow_of_parent_run hchild hparent).1

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## F. Does the bridge help `StrictNockVMROMPackage`?
    ══════════════════════════════════════════════════════════════════════════════════════

Before R1, the package's `noOverflow` field was
`∀ s ∈ computeSkeletonRows commitment.skeleton, s.state =.s4 →
   OpcodeSemantics.IncrementNoOverflow q (P8Census.skeletonSubformula s 0.result)`.
The bridge could discharge it — but only after someone exhibited, for each committed OP₄ row, a
guarded run whose OP₄ child value is that row's recorded value.  That row → run map is exactly
what was missing. -/

open Module
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.StrictPackage
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ExactPrimeFamily

/-- A committed-row → guarded-run map implies the retired
no-overflow proposition.  R1 does not consume this theorem. -/
theorem b33_package_noOverflow_of_guarded_runs
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
    {hOrb q Λ : ℕ}
    (P : StrictNockVMROMPackage F K hOrb q Λ)
    (hmap : ∀ s ∈ computeSkeletonRows P.commitment.skeleton, s.state = .s4 →
      ∃ (subj form rP : Noun) (fuel : ℕ),
        evalGPaper q fuel subj form
            = some (P8Census.skeletonSubformula s 0 .result) ∧
          evalGPaper q (fuel + 1) subj (.cell (.atom 4) form) = some rP) :
    ∀ s ∈ computeSkeletonRows P.commitment.skeleton, s.state = .s4 →
      OpcodeSemantics.IncrementNoOverflow q
        (P8Census.skeletonSubformula s 0 .result) := by
  intro s hs hst
  obtain ⟨subj, form, rP, fuel, hchild, hparent⟩ := hmap s hs hst
  exact (b33_incrementNoOverflow_of_parent_run hchild hparent).1

end Nock.RedTeam.Batch33

/-! ══════════════════════════════════════════════════════════════════════════════════════
    ## D. -/

#print axioms Nock.evalGPaper
#print axioms Nock.lusGBy_le_lus
#print axioms Nock.lusGBy_le_lusFBy
#print axioms Nock.evalGPaper_le_evalGBy
#print axioms Nock.evalGPaper_le_evalPaper
#print axioms Nock.evalGPaper_le_evalPaperMod
#print axioms Nock.paper_field_bridge
#print axioms Nock.runProgram_of_evalGPaper
#print axioms Nock.evalFBy_of_evalGPaper
#print axioms Nock.FieldEmbedding.embBy
#print axioms Nock.FieldEmbedding.embBy_inj_of_boundedBy
#print axioms Nock.bridge_reflects_field_equality
#print axioms Nock.bridge_nonvacuous
#print axioms Nock.bridge_nonvacuous_conclusion
#print axioms Nock.evalGPaper_fails_where_evalPaperMod_wraps
#print axioms Nock.evalGPaper_succeeds_below_top

#print axioms Nock.RedTeam.Batch33.b33_composite_modulus_is_not_a_field
#print axioms Nock.RedTeam.Batch33.b33_bridge_conclusion_at_prime_5
#print axioms Nock.RedTeam.Batch33.b33_bridge_conclusion_at_goldilocks
#print axioms Nock.RedTeam.Batch33.b33_injectivity_needs_no_primality
#print axioms Nock.RedTeam.Batch33.b33_no_conjunct_survives_dropping_hG
#print axioms Nock.RedTeam.Batch33.b33_bridge_is_threaded
#print axioms Nock.RedTeam.Batch33.b33_shared_fuel_strengthening_is_false
#print axioms Nock.RedTeam.Batch33.b33_evalPaperGen_eq_evalPaperMod
#print axioms Nock.RedTeam.Batch33.b33_evalPaperGen_eq_evalGPaper
#print axioms Nock.RedTeam.Batch33.b33_evalGPaper_crashes_above_op10
#print axioms Nock.RedTeam.Batch33.b33_op11_separates_fragment_from_full
#print axioms Nock.RedTeam.Batch33.b33_guard_is_exactly_incrementNoOverflow
#print axioms Nock.RedTeam.Batch33.b33_incrementNoOverflow_of_parent_run
#print axioms Nock.RedTeam.Batch33.b33_boundedBy_is_not_incrementNoOverflow
#print axioms Nock.RedTeam.Batch33.b33_guard_strictly_stronger_than_strict_paper
#print axioms Nock.RedTeam.Batch33.b33_hcall_available_without_the_guard
#print axioms Nock.RedTeam.Batch33.b33_census_I_delta_intact
#print axioms Nock.RedTeam.Batch33.b33_bridge_feeds_s3_vcomp
#print axioms Nock.RedTeam.Batch33.b33_bridge_feeds_s4_vcomp
#print axioms Nock.RedTeam.Batch33.b33_bridge_builds_local_certificate_s3
#print axioms Nock.RedTeam.Batch33.b33_bridge_builds_local_certificate_s4
#print axioms Nock.RedTeam.Batch33.b33_evalGPaper_succ
#print axioms Nock.RedTeam.Batch33.b33_evalGPaper_mono
#print axioms Nock.RedTeam.Batch33.b33_bridge_feeds_siblings_at_shared_fuel
#print axioms Nock.RedTeam.Batch33.b33_rowStateNeeds_increment_safe_of_guarded_runs
#print axioms Nock.RedTeam.Batch33.b33_package_noOverflow_of_guarded_runs
