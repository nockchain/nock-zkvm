/-
  Nock/Semantics.lean

  Phase-1 target: the paper's *strengthened* Nock semantics and its key theorems.

  The paper does not evaluate `*[subject formula]` as a black box; it
  defines a *verb* `(actions, noun)`, a strict traversal order
  `getIndex`/`map`, the *computable opcode domain* `D` restricting each step to a local, non-recursive rewrite, and an
  *evaluation trace*.  The payoff is:

    Thm:deterministic_Trace: if `map` is a strict order, every finite
    verb has at most one consistent trace of each length.

  Building the full Verb/actions/getIndex/Trace machinery is the next work
  item; below we (a) name the paper's opcode set, and (b) state the two Phase-1 proof
  targets against the executable reference of Nock/Reference.lean.

  DESIGN FLAG (to confirm): leaves/atoms.  The reference uses `Nat`; the paper's
  arithmetized Nock uses field elements with `+` taken mod p.  The agreement theorem
  below therefore holds only up to that embedding (e.g. for computations whose atoms do
  not exceed p).  We will make the atom type a parameter and state agreement under the
  no-overflow side condition; flagged here rather than silently chosen.
-/

import Nock.Reference

namespace Nock

/-- The paper's opcode set: `OP_0.. OP_10` plus `cons`.
    `NockVMROM` is this set minus `op 10`. -/
inductive OpCode where
  | op   : Fin 11 → OpCode   -- 0.. 10
  | cons : OpCode
deriving Repr, DecidableEq

/-- **Fuel monotonicity (single step).**  If an evaluation succeeds at fuel `n`, it succeeds
    with the same result at fuel `n + 1`.  The recursive sub-calls inside `evalN (n+1)` run
    at fuel `n`, so the functional-induction IHs bump each of them from `n-1` to `n`; the
    two operator cases (`?`/OP₃ via `Option.map`, `+`/OP₄ via `Option.bind`) need the witness
    supplied explicitly.  (`Noun.slot`/`Noun.edit` take no fuel, so they are unaffected.) -/
theorem evalN_succ {n : Nat} {s form r : Noun}
    (h : evalN n s form = some r) : evalN (n + 1) s form = some r := by
  induction n, s, form using evalN.induct generalizing r with
  | case11 fuel subj tail ih =>
      simp only [evalN, Option.map_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | case12 fuel subj tail ih =>
      simp only [evalN, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | _ =>
      simp_all [evalN]

/-- **Fuel monotonicity.**  A successful evaluation stays successful, with the same result,
    at any larger fuel budget. -/
theorem evalN_mono {n m : Nat} {s form r : Noun}
    (hle : n ≤ m) (h : evalN n s form = some r) : evalN m s form = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalN_succ ih

/-- **Phase-1 target — determinism.**  The fuel-indexed specialization of
    Thm:deterministic_Trace: any two successful evaluations of the same
    `subject`/`formula`, at any fuel budgets, agree.  (Equivalently: `evalN` defines a
    partial function of `(subject, formula)`.)  This is the big-step shadow of the
    trace-level determinism `deterministic_Trace`.  Proof: bump both evaluations to the
    common fuel `max f₁ f₂` by `evalN_mono`, then `Option.some` is injective. -/
theorem evalN_deterministic
    {f₁ f₂ : Nat} {subj formula r₁ r₂ : Noun}
    (h₁ : evalN f₁ subj formula = some r₁)
    (h₂ : evalN f₂ subj formula = some r₂) :
    r₁ = r₂ := by
  have k₁ := evalN_mono (Nat.le_max_left f₁ f₂) h₁
  have k₂ := evalN_mono (Nat.le_max_right f₁ f₂) h₂
  exact Option.some.inj (k₁.symm.trans k₂)

/- The paper's strengthened verb/trace
   semantics computes the same result as the standard reference on the shared opcode
   fragment.  Precise statement pending the `Verb`/`Trace`/`Step` definitions; the two
   directions (reference terminates ⇒ trace terminates with equal result, and conversely)
   will be split into two lemmas.

   TODO(phase1):
     * Verb            : structure (actions : Array Action, noun : Noun)
     * getIndex, map   : strict DFS traversal order
     * computable domain D
     * Step : Verb → Verb → Prop  (single opcode rewrite)
     * Trace, consistent, complete/valid/invalid
     * deterministic_Trace   -- the real statement
-/

end Nock
