/-
  Nock/PaperFieldBridge.lean

  **The paper-fragment ↔ finite-field bridge.**

  `Nock.FieldEmbedding.agreeBy` already identifies the *full* evaluators — `evalN` (unbounded Nat
  increment) and `evalFBy q` — conditional on a successful
  run of the *guarded* evaluator `evalGBy q`, which crashes rather than letting any increment reach
  `q`.  But all three of those evaluators include OP₁₁, while

  * the small-step machine `Verb.runProgram` and its unconditional adequacy partner `evalPaper`
    (`Verb.runProgram_adequate_complete`), and
  * the strict Theorem-5.4 language `evalPaperMod q` (Nock/PaperReferenceMod.lean)

  live in the paper's OP₀..OP₁₀ fragment, and the two available refinements
  (`evalPaper_le_evalN`, `evalPaperMod_le_evalFBy`) point *out* of the fragment.  So the fragment
  could not be reached from `agreeBy`: descending back requires an OP₁₁-freeness certificate.

  This module supplies the missing object — the **guarded paper-fragment evaluator** `evalGPaper q`
  (`evalPaperMod q` with the crashing increment `lusGBy q` in place of the wrapping `lusFBy q`) —
  and threads one conditional through every layer:

  * `evalGPaper_le_evalGBy`    — into the full guarded evaluator (so `agreeBy` is reusable);
  * `evalGPaper_le_evalPaper`  — down to the Nat paper oracle;
  * `evalGPaper_le_evalPaperMod` — down to the strict modular paper oracle;
  * `paper_field_bridge`       — the capstone: on `q`-bounded inputs, a successful guarded
    fragment run makes the small-step machine, `evalPaper`, `evalPaperMod q`, `evalFBy q` and
    `evalN` all return the *same* noun, and that noun is again `q`-bounded.

  **The conditional is no-overflow; injectivity is the payoff, not a second hypothesis.**  The
  `BoundedBy q` conclusion is exactly what makes the leaf cast `ℕ → ZMod q` injective
  (`FieldEmbedding.zmod_natCast_inj_of_lt`), hence the structural noun equality used by OP₅ *is* field equality on bridged results: `embBy_inj_of_boundedBy` and
  `bridge_reflects_field_equality`.  Primality of `q` is never used — `1 < q` and `NeZero q`
  suffice — so nothing here pulls `Field.goldilocks_prime`.

  The conditional is not vacuous: `bridge_nonvacuous` runs it, and it is instantiated at a genuine
  prime and at the paper's own characteristic by `bridge_nonvacuous_at_prime_5` /
  `bridge_nonvacuous_at_goldilocks`.

  **The conditional is STRICTLY STRONGER than the paper's own language — read the identification
  accordingly.**  `evalGPaper q` crashes where the paper's total modular OP₄
  merely wraps, so this module identifies the five evaluators on the *no-overflow sublanguage*, not
  on all of the paper's fragment.  It is a real
  hypothesis, openly stated, not a paper-derived fact.

  **What `evalFBy_of_evalGPaper` does and does not add.**  It has the shape the Theorem-5.4 row
  certificates consume (`OpcodeSemantics.s3_vcomp_semantics`/`s4_vcomp_semantics`,
  `SemanticTrace.LocalOpcodeCertificate`), but that `hcall` premise was already obtainable with *no*
  guard at all through the pre-existing `evalPaperMod_le_evalFBy`
  (`Batch33.b33_hcall_available_without_the_guard`).  The genuine added value of this module is the
  identification with `evalPaper` / `Verb.runProgram` / `evalN`, plus — on the OP₄ row only — the
  increment datum `hno` that the same guarded parent run supplies
  (`Batch33.b33_incrementNoOverflow_of_parent_run`).

  Scope: this identifies the *languages*.  It does not address the ROM restriction axis
  (`runProgram` vs `Verb.nextROM`/`Verb.StepROM`), nor the identification of the constructed RAP
  gate bodies with the chained language.  It does not reduce the assumption count of
  `Thm54.StrictPackage.StrictNockVMROMPackage`: its `noOverflow` field is dischargeable from the
  guard only given a committed-row → guarded-run map that nothing here constructs
  (`Batch33.b33_package_noOverflow_of_guarded_runs`), and `BoundedBy q` alone is provably too weak
  (`Batch33.b33_boundedBy_is_not_incrementNoOverflow`).
-/

import Nock.PaperReferenceMod
import Nock.PureComplete

namespace Nock

open Noun

/-! ## The guarded paper-fragment evaluator -/

/-- `*[subject formula]`, fuel-indexed, **guarded paper fragment**: the paper's OP₀..OP₁₀ fragment
    with the OP₄ increment `lusGBy q`, which *crashes* rather than reaching an atom `≥ q`.

    `evalGPaper q fuel s f = some r` is therefore exactly the statement "this paper-fragment
    computation runs without any modular wrap at `q`" — the honest no-overflow side condition, in
    the fragment where `Verb.runProgram` and `evalPaperMod q` live. -/
def evalGPaper (q : Nat) : Nat → Noun → Noun → Option Noun
  | 0, _, _ => none
  | _ + 1, _, .atom _ => none
  | fuel + 1, subj, .cell (.cell b c) d =>
      match evalGPaper q fuel subj (.cell b c), evalGPaper q fuel subj d with
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
             match evalGPaper q fuel subj b, evalGPaper q fuel subj c with
             | some sb, some sc => evalGPaper q fuel sb sc
             | _, _ => none
           | _ => none
    | 3 => (evalGPaper q fuel subj tail).map wut
    | 4 => (evalGPaper q fuel subj tail).bind (FieldEmbedding.lusGBy q)
    | 5 => match tail with
           | .cell b c =>
             match evalGPaper q fuel subj b, evalGPaper q fuel subj c with
             | some sb, some sc => some (tis sb sc)
             | _, _ => none
           | _ => none
    | 6 => match tail with
           | .cell b (.cell c d) =>
             match evalGPaper q fuel subj b with
             | some (.atom 0) => evalGPaper q fuel subj c
             | some (.atom 1) => evalGPaper q fuel subj d
             | _ => none
           | _ => none
    | 7 => match tail with
           | .cell b c =>
             match evalGPaper q fuel subj b with
             | some sb => evalGPaper q fuel sb c
             | none => none
           | _ => none
    | 8 => match tail with
           | .cell b c =>
             match evalGPaper q fuel subj b with
             | some sb => evalGPaper q fuel (.cell sb subj) c
             | none => none
           | _ => none
    | 9 => match tail with
           | .cell (.atom ax) c =>
             match evalGPaper q fuel subj c with
             | some core =>
               match slot ax core with
               | some arm => evalGPaper q fuel core arm
               | none => none
             | none => none
           | _ => none
    | 10 => match tail with
            | .cell (.cell (.atom ax) c) d =>
              match evalGPaper q fuel subj c, evalGPaper q fuel subj d with
              | some new, some old => edit ax new old
              | _, _ => none
            | _ => none
    | _ => none                          -- op ≥ 11 (incl. OP₁₁ hints) ⇒ crash (paper fragment)

/-! ## The increment agrees under the guard

The guard is the only place the three fragment evaluators can differ: a successful `lusGBy q`
pins `n + 1 < q`, and there the unbounded increment `Noun.lus` and the modular increment
`lusFBy q` produce the same atom. -/

/-- A successful guarded increment is the unbounded increment. -/
theorem lusGBy_le_lus {q : Nat} {x m : Noun}
    (h : FieldEmbedding.lusGBy q x = some m) : Noun.lus x = some m := by
  cases x with
  | atom n =>
      by_cases hlt : n + 1 < q
      · simp only [FieldEmbedding.lusGBy, if_pos hlt, Option.some.injEq] at h
        simp [Noun.lus, ← h]
      · simp [FieldEmbedding.lusGBy, hlt] at h
  | cell _ _ => simp [FieldEmbedding.lusGBy] at h

/-- A successful guarded increment is the paper's modular increment. -/
theorem lusGBy_le_lusFBy {q : Nat} {x m : Noun}
    (h : FieldEmbedding.lusGBy q x = some m) : FieldEmbedding.lusFBy q x = some m := by
  cases x with
  | atom n =>
      by_cases hlt : n + 1 < q
      · simp only [FieldEmbedding.lusGBy, if_pos hlt, Option.some.injEq] at h
        simp [FieldEmbedding.lusFBy, ← h, Nat.mod_eq_of_lt hlt]
      · simp [FieldEmbedding.lusGBy, hlt] at h
  | cell _ _ => simp [FieldEmbedding.lusGBy] at h

/-! ## The three refinements out of the guarded fragment -/

/-- **`evalGPaper q` refines `evalGBy q`.**  The guarded fragment run is a guarded full run with
    the same value; they differ only where `evalGBy` fires OP₁₁, which the fragment crashes on.
    This is what makes `FieldEmbedding.agreeBy` reusable inside the fragment. -/
theorem evalGPaper_le_evalGBy {q n : Nat} {s form r : Noun}
    (h : evalGPaper q n s form = some r) : FieldEmbedding.evalGBy q n s form = some r := by
  induction n, s, form using evalGPaper.induct q generalizing r <;>
    simp_all only [evalGPaper, FieldEmbedding.evalGBy, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
    grind

/-- **`evalGPaper q` refines `evalPaper`.**  Under the guard the fragment's modular-range OP₄ and
    the unbounded Nat OP₄ coincide, so a successful guarded run is a `evalPaper` run with the same
    value — the entry point into the unconditional `runProgram ⟺ evalPaper` adequacy. -/
theorem evalGPaper_le_evalPaper {q n : Nat} {s form r : Noun}
    (h : evalGPaper q n s form = some r) : evalPaper n s form = some r := by
  induction n, s, form using evalGPaper.induct q generalizing r <;>
    simp_all only [evalGPaper, evalPaper, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
    grind [lusGBy_le_lus]

/-- **`evalGPaper q` refines `evalPaperMod q`.**  A successful guarded run is a strict-paper
    modular run with the same value: the guard rules out the wrap that is the only difference. -/
theorem evalGPaper_le_evalPaperMod {q n : Nat} {s form r : Noun}
    (h : evalGPaper q n s form = some r) : evalPaperMod q n s form = some r := by
  induction n, s, form using evalGPaper.induct q generalizing r <;>
    simp_all only [evalGPaper, evalPaperMod, Option.map_eq_some_iff,
      Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] <;>
    grind [lusGBy_le_lusFBy]

/-! ## The capstone bridge -/

/-- **Paper ↔ finite-field bridge.**  On `q`-bounded inputs (`CanonicalFieldNoun q`: every atom is
    a canonical residue `< q`), a successful *guarded* paper-fragment run makes all five
    formalizations of the paper's evaluation agree on one noun, which is again `q`-bounded:

    * the small-step machine `Verb.runProgram`,
    * the Nat paper oracle `evalPaper`,
    * the strict modular paper oracle `evalPaperMod q`,
    * the full modular evaluator `FieldEmbedding.evalFBy q`, and
    * the Nat reference `evalN`.

    The single hypothesis `evalGPaper q fuel s f = some r` is no-overflow: it is discharged by
    *running* the guarded evaluator, not assumed.  The `BoundedBy q r` conclusion then delivers
    leaf-cast injectivity for free (`bridge_reflects_field_equality`). -/
theorem paper_field_bridge (q : Nat) (hq : 1 < q) {fuel : Nat} {s f r : Noun}
    (hs : FieldEmbedding.BoundedBy q s) (hf : FieldEmbedding.BoundedBy q f)
    (hG : evalGPaper q fuel s f = some r) :
    (∃ n, Verb.runProgram n s f = some r) ∧
      evalPaper fuel s f = some r ∧
      evalPaperMod q fuel s f = some r ∧
      FieldEmbedding.evalFBy q fuel s f = some r ∧
      evalN fuel s f = some r ∧
      FieldEmbedding.BoundedBy q r := by
  have hP : evalPaper fuel s f = some r := evalGPaper_le_evalPaper hG
  have hM : evalPaperMod q fuel s f = some r := evalGPaper_le_evalPaperMod hG
  have hB : FieldEmbedding.BoundedBy q r :=
    (FieldEmbedding.agreeBy q hq fuel s f r hs hf (evalGPaper_le_evalGBy hG)).2.2
  exact ⟨(Verb.runProgram_adequate_complete s f r).2 ⟨fuel, hP⟩, hP, hM,
    evalPaperMod_le_evalFBy hM, evalPaper_le_evalN hP, hB⟩

/-- The bridge's small-step half in the form the machine consumes. -/
theorem runProgram_of_evalGPaper {q fuel : Nat} {s f r : Noun}
    (hG : evalGPaper q fuel s f = some r) : ∃ n, Verb.runProgram n s f = some r :=
  (Verb.runProgram_adequate_complete s f r).2 ⟨fuel, evalGPaper_le_evalPaper hG⟩

/-- The bridge's field half in the form the Theorem-5.4 row certificates consume
    (`OpcodeSemantics.*_vcomp_semantics` / `LocalOpcodeCertificate` take exactly this premise). -/
theorem evalFBy_of_evalGPaper {q fuel : Nat} {s f r : Noun}
    (hG : evalGPaper q fuel s f = some r) :
    FieldEmbedding.evalFBy q fuel s f = some r :=
  evalPaperMod_le_evalFBy (evalGPaper_le_evalPaperMod hG)

/-! ## The injectivity carry

`BoundedBy q` is precisely the condition under which the leaf cast `ℕ → ZMod q` is injective, so on
bridged results the *structural* noun equality used by OP₅ coincides with equality
of field images.  Injectivity is thus a consequence of the bridge's conclusion, not an extra
hypothesis.  These are the modulus-parameterized counterparts of `FieldEmbedding.FNoun` / `emb` /
`emb_inj_on_bounded`, and they do not use `Field.goldilocks_prime`. -/

namespace FieldEmbedding

/-- Field nouns at a supplied modulus: proper binary trees with leaves in `ZMod q`. -/
inductive FNounBy (q : Nat) where
  | atom : ZMod q → FNounBy q
  | cell : FNounBy q → FNounBy q → FNounBy q

/-- The leaf map `n ↦ (n : ZMod q)`, structural on cells. -/
def embBy (q : Nat) : Noun → FNounBy q
  | .atom n   => .atom (n : ZMod q)
  | .cell l r => .cell (embBy q l) (embBy q r)

@[simp] theorem embBy_atom {q n : Nat} : embBy q (.atom n) = .atom (n : ZMod q) := rfl

/-- **`embBy q` is injective on `q`-bounded nouns.**  Distinct canonical residues `< q` stay
    distinct in `ZMod q`, so structural Nock equality is field equality there. -/
theorem embBy_inj_of_boundedBy {q : Nat} [NeZero q] :
    ∀ {a b : Noun}, BoundedBy q a → BoundedBy q b → embBy q a = embBy q b → a = b := by
  intro a
  induction a with
  | atom m =>
      intro b hm hb h
      cases b with
      | atom n =>
          simp only [embBy, FNounBy.atom.injEq] at h
          rw [zmod_natCast_inj_of_lt hm hb h]
      | cell _ _ => simp [embBy] at h
  | cell la ra ihl ihr =>
      intro b ha hb h
      cases b with
      | atom _ => simp [embBy] at h
      | cell lb rb =>
          simp only [embBy, FNounBy.cell.injEq] at h
          rw [ihl ha.1 hb.1 h.1, ihr ha.2 hb.2 h.2]

end FieldEmbedding

/-- **The bridge carries the equivalence through the field embedding.**  Two guarded fragment runs
    on `q`-bounded inputs whose results have the same field image have the *same result noun*: the
    no-overflow conditional yields boundedness, and boundedness yields injectivity. -/
theorem bridge_reflects_field_equality (q : Nat) [NeZero q] (hq : 1 < q)
    {fuel₁ fuel₂ : Nat} {s₁ f₁ s₂ f₂ r₁ r₂ : Noun}
    (hs₁ : FieldEmbedding.BoundedBy q s₁) (hf₁ : FieldEmbedding.BoundedBy q f₁)
    (hs₂ : FieldEmbedding.BoundedBy q s₂) (hf₂ : FieldEmbedding.BoundedBy q f₂)
    (hG₁ : evalGPaper q fuel₁ s₁ f₁ = some r₁)
    (hG₂ : evalGPaper q fuel₂ s₂ f₂ = some r₂)
    (himg : FieldEmbedding.embBy q r₁ = FieldEmbedding.embBy q r₂) : r₁ = r₂ :=
  FieldEmbedding.embBy_inj_of_boundedBy
    (paper_field_bridge q hq hs₁ hf₁ hG₁).2.2.2.2.2
    (paper_field_bridge q hq hs₂ hf₂ hG₂).2.2.2.2.2 himg

/-! ## Non-vacuity, and the guard cuts exactly at the wrap

`bridge_nonvacuous` uses the modulus `100`, which is **composite**: convenient for reduction, but
`ZMod 100` is not a field, so that witness alone does not exhibit the paper's `𝒟𝒯(𝔽)`.  The two witnesses below repair that at a genuine prime and at the paper's own
characteristic.  Neither pulls `Field.goldilocks_prime`, because the bridge never needs primality. -/

/-- **Non-vacuity at a genuine prime.**  `*[0 [4 [1 3]]] = 4` at `q = 5`, where `ZMod q` really is a
    field, with the full six-fold bridge conclusion. -/
theorem bridge_nonvacuous_at_prime_5 :
    (∃ n, Verb.runProgram n (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4)) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3))) = some (.atom 4) ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      FieldEmbedding.evalFBy 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalN 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3))) = some (.atom 4) ∧
      FieldEmbedding.BoundedBy 5 (.atom 4) :=
  paper_field_bridge 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

/-- **Non-vacuity at the paper's own characteristic** `Nock.Field.p = 2^64 − 2^32 + 1`. -/
theorem bridge_nonvacuous_at_goldilocks :
    (∃ n, Verb.runProgram n (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42)))
        = some (.atom 43)) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      evalPaperMod Nock.Field.p 5 (.atom 0)
          (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      FieldEmbedding.evalFBy Nock.Field.p 5 (.atom 0)
          (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      evalN 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      FieldEmbedding.BoundedBy Nock.Field.p (.atom 43) :=
  paper_field_bridge Nock.Field.p FieldEmbedding.one_lt_p
    (by simp [Nock.Field.p_eq]) (by norm_num [Nock.Field.p_eq])
    (by simp only [Nock.Field.p_eq]; decide)

/-- The bridge fires on a real computation: `*[0 [4 [1 42]]] = 43`, well below the modulus.  Note
    `100` is composite — see `bridge_nonvacuous_at_prime_5` / `bridge_nonvacuous_at_goldilocks`. -/
theorem bridge_nonvacuous :
    evalGPaper 100 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42)))
      = some (.atom 43) := by
  decide

/-- …and the bridge's conclusion on that run: all five formalizations return `43`. -/
theorem bridge_nonvacuous_conclusion :
    (∃ n, Verb.runProgram n (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42)))
        = some (.atom 43)) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      evalPaperMod 100 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42)))
        = some (.atom 43) ∧
      FieldEmbedding.evalFBy 100 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42)))
        = some (.atom 43) ∧
      evalN 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 42))) = some (.atom 43) ∧
      FieldEmbedding.BoundedBy 100 (.atom 43) :=
  paper_field_bridge 100 (by norm_num) (by norm_num) (by norm_num) bridge_nonvacuous

/-- **The guard rejects exactly the divergent computation.**  At the top residue `q-1 = 4` the
    strict modular oracle wraps to `0` while the unbounded oracle produces `5`
    (`evalPaperMod_ne_evalPaper_at_top`); the guarded fragment evaluator crashes there, so the
    bridge never claims agreement across the wrap. -/
theorem evalGPaper_fails_where_evalPaperMod_wraps :
    evalGPaper 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4))) = none ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4)))
        = some (.atom 0) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 4)))
        = some (.atom 5) := by
  refine ⟨by decide, by decide, by decide⟩

/-- One residue below the top the guard holds and all three fragment oracles agree. -/
theorem evalGPaper_succeeds_below_top :
    evalGPaper 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalPaperMod 5 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) ∧
      evalPaper 5 (.atom 0) (.cell (.atom 4) (.cell (.atom 1) (.atom 3)))
        = some (.atom 4) := by
  refine ⟨by decide, by decide, by decide⟩

end Nock

#print axioms Nock.evalGPaper_le_evalGBy
#print axioms Nock.evalGPaper_le_evalPaper
#print axioms Nock.evalGPaper_le_evalPaperMod
#print axioms Nock.paper_field_bridge
#print axioms Nock.runProgram_of_evalGPaper
#print axioms Nock.evalFBy_of_evalGPaper
#print axioms Nock.FieldEmbedding.embBy_inj_of_boundedBy
#print axioms Nock.bridge_reflects_field_equality
#print axioms Nock.bridge_nonvacuous
#print axioms Nock.bridge_nonvacuous_at_prime_5
#print axioms Nock.bridge_nonvacuous_at_goldilocks
#print axioms Nock.bridge_nonvacuous_conclusion
#print axioms Nock.evalGPaper_fails_where_evalPaperMod_wraps
#print axioms Nock.evalGPaper_succeeds_below_top
