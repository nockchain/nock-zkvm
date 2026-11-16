import Nock.AIR

/-!
# Compute-row environment agreement: the converse of `computeEnvFull`

`Nock.Reified.computeEnvFull` (`Nock/AIR.lean:478`) assembles an `Env K` out of the *structured*
compute-row records `(inp, op, pub, dec, ex)` by a literal slot match: trace slots `0…10` are the
opcode selectors, `11…64` the fingerprint triples, `65,66` the line nonces, `67…90` the three
memory records, `91,92` the two auxiliary witnesses, `93` the honest `z⁻¹` witness, and `_ => 0`
beyond; `chal 0…4` are `(α, z, a, b, c)`; `traceNext` and `pub` are identically `0`.

This module supplies the **converse projection**: from an *arbitrary* `E : Env K` it reads back
records (`inpOf`, `opOf`, `pubOfState`, `decOf`, `exOf`) and proves that re-assembling them with
`computeEnvFull` reproduces `E` on every slot the compute AIR can read — trace columns `< 94` and
challenge columns `< 5`.  The payoff is `row_constraint_eval_agree`: every `.row` constraint of
`Trans.computeAIRchained` evaluates identically in `E` and in the reconstituted environment, so
gate facts obtained about a hostile `Env K` (e.g. from
`CoordinateRAPCore.expandChip_satisfies_iff_language`) can be read as facts about
`computeEnvFull`, which is the shape the per-row soundness bridges consume.

## Scope of the agreement, and why each exclusion is forced

* **`traceNext` is excluded.**  `computeEnvFull` sets `traceNext := fun _ => 0`, so no projection
  can recover it.  It costs nothing: of the 527 constraints of `Trans.computeAIRchained` exactly
  one reads `traceNext`, and it is the single `.transition` gate (`lnChainExpr`, cols 66 → 65).
  Every `.row` constraint is `traceNext`-free, which is what `Expr.rowScoped` demands.
* **`pub` is excluded.**  `computeEnvFull` sets `pub := fun _ => 0`; `computeAIR.numPublic = 0` and
  no constraint of `Trans.computeAIRchained` reads a `publicVal` variable, so `Expr.rowScoped`
  rejects `publicVal` outright rather than carrying a hypothesis about `E.pub`.
* **Trace slot `93` is *determined*, not free.**  `computeEnvFull` decodes column `93` as
  `inp.z⁻¹` while `inp.z` is challenge `1`; the two are the same datum, so a projection cannot
  choose them independently.  `inpOf` takes `z` from the challenge (`E.chal 1`), which makes slot
  `93` determined, and the theorems therefore carry an explicit hypothesis relating the two.  The
  hypothesis is *not* an extra assumption in practice: `zZinvExpr = chl 1 * tc 93 - 1` is itself
  one of the 526 `.row` constraints, so `row_constraint_eval_agree_of_zZinv` derives it from that
  gate vanishing at `E`.
* **`Pub.state` is a parameter.**  `computeEnvFull` never reads `pub.state` (the opcode selectors
  come from `op`), so no projection can recover it and agreement holds for *every* choice.
  `pubOfState` therefore takes the state as an argument; `pubOf` is the `.s0` instance.
-/

namespace Nock.Reified

open ComputeTable

set_option maxRecDepth 100000

/-! ## 1. Row scoping: the variable discipline a row constraint respects

  `Expr.wellScoped` (`Nock/NockVMROM/TraceEncoding.lean:81`) already bounds `traceCur` and forbids
  `traceNext`, but it treats `challenge` and `publicVal` as unrestricted, so its congruence lemma
  `Expr.eval_eq_of_wellScoped` demands agreement on *all* challenge and public slots.  That is
  exactly what fails here: `computeEnvFull` zeroes `chal j` for `j ≥ 5` and zeroes `pub` entirely,
  while `E` is arbitrary.  `Expr.rowScoped` adds the missing two bounds. -/

/-- `true` iff the expression reads no `traceNext` and no `publicVal` variable, every `traceCur`
    index is `< nt`, and every `challenge` index is `< nc`. -/
def Expr.rowScoped (nt nc : ℕ) : Expr → Bool
  | .Var .traceCur i => decide (i < nt)
  | .Var .traceNext _ => false
  | .Var .challenge i => decide (i < nc)
  | .Var .publicVal _ => false
  | .Const _ => true
  | .Add a b => a.rowScoped nt nc && b.rowScoped nt nc
  | .Sub a b => a.rowScoped nt nc && b.rowScoped nt nc
  | .Mul a b => a.rowScoped nt nc && b.rowScoped nt nc
  | .Neg a => a.rowScoped nt nc
  | .Pow e _ => e.rowScoped nt nc

/-- **Evaluation congruence for `rowScoped` expressions.**  Two environments that agree on trace
    columns below `nt` and challenge columns below `nc` give the same value to any
    `rowScoped nt nc` expression — no constraint on `traceNext` or `pub`. -/
theorem Expr.eval_eq_of_rowScoped {K : Type*} [Field K] {nt nc : ℕ} :
    ∀ {e : Expr}, e.rowScoped nt nc = true → ∀ {env1 env2 : Env K},
      (∀ i, i < nt → env1.trace i = env2.trace i) →
      (∀ j, j < nc → env1.chal j = env2.chal j) →
      e.eval env1 = e.eval env2 := by
  intro e
  induction e with
  | Var kind idx =>
      intro he env1 env2 ht hc
      cases kind with
      | traceCur =>
          simp only [Expr.rowScoped, decide_eq_true_eq] at he
          simpa only [Expr.eval] using ht idx he
      | traceNext => simp [Expr.rowScoped] at he
      | challenge =>
          simp only [Expr.rowScoped, decide_eq_true_eq] at he
          simpa only [Expr.eval] using hc idx he
      | publicVal => simp [Expr.rowScoped] at he
  | Const c => intro _ _ _ _ _; rfl
  | Add a b iha ihb =>
      intro he env1 env2 ht hc
      simp only [Expr.rowScoped, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1 ht hc, ihb he.2 ht hc]
  | Sub a b iha ihb =>
      intro he env1 env2 ht hc
      simp only [Expr.rowScoped, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1 ht hc, ihb he.2 ht hc]
  | Mul a b iha ihb =>
      intro he env1 env2 ht hc
      simp only [Expr.rowScoped, Bool.and_eq_true] at he
      simp only [Expr.eval, iha he.1 ht hc, ihb he.2 ht hc]
  | Neg a iha =>
      intro he env1 env2 ht hc
      simp only [Expr.eval, iha he ht hc]
  | Pow a n iha =>
      intro he env1 env2 ht hc
      simp only [Expr.eval, iha he ht hc]

/-- **Every constraint of `computeAIR` is `rowScoped 94 5`** — 94 trace columns, 5 challenges, no
    next-row and no public reads.  Kernel reduction over the 526 reified constraints. -/
theorem computeAIR_rowScoped :
    computeAIR.constraints.all (fun c => c.expr.rowScoped 94 5) = true := by rfl

/-- **Every constraint of `computeAIR` is gated `.row`.** -/
theorem computeAIR_all_row :
    computeAIR.constraints.all (fun c => c.kind == .row) = true := by rfl

/-- A `.row` constraint of `Trans.computeAIRchained` is a constraint of `computeAIR`: the chained
    AIR only adds the `.transition` line-nonce hand-off. -/
theorem mem_computeAIR_of_row_mem_chained {c : Constraint}
    (hc : c ∈ Trans.computeAIRchained.constraints) (hkind : c.kind = .row) :
    c ∈ computeAIR.constraints := by
  have hc' : c ∈ computeAIR.constraints ++ [(⟨.transition, Trans.lnChainExpr⟩ : Constraint)] := by
    simpa [Trans.computeAIRchained] using hc
  rcases List.mem_append.mp hc' with h | h
  · exact h
  · rw [List.mem_singleton.mp h] at hkind
    exact absurd hkind (by decide)

/-! ## 2. The projections -/

variable {K : Type*} [Field K]

/-- The RAP inputs read off the challenge slots `0…4` (`(α, z, a, b, c)`, the paper). -/
def inpOf (E : Env K) : Inputs K where
  α := E.chal 0
  z := E.chal 1
  a := E.chal 2
  b := E.chal 3
  c := E.chal 4

/-- The one-hot opcode selector valuation read off trace columns `0…10`. -/
def opOf (E : Env K) : State → K := fun st => E.trace (opCol st)

/-- The fingerprint triple read off three consecutive trace columns based at `base`. -/
def fpOf (E : Env K) (base : ℕ) : FP K :=
  ⟨E.trace base, E.trace (base + 1), E.trace (base + 2)⟩

/-- The memory record read off eight consecutive trace columns based at `base`. -/
def mrOf (E : Env K) (base : ℕ) : MemRec K :=
  ⟨fpOf E base, fpOf E (base + 3), E.trace (base + 6), E.trace (base + 7)⟩

/-- The public label + witness read off trace columns `11…90`.  `Pub.state` is not recoverable
    (`computeEnvFull` never reads it), so it is supplied by the caller. -/
def pubOfState (E : Env K) (st : State) : Pub K where
  state := st
  s := fpOf E 11
  f := fpOf E 14
  e := fpOf E 17
  sf1_s := fpOf E 20
  sf1_f := fpOf E 23
  sf1_e := fpOf E 26
  sf2_s := fpOf E 29
  sf2_f := fpOf E 32
  sf2_e := fpOf E 35
  sf3_s := fpOf E 38
  sf3_f := fpOf E 41
  sf3_e := fpOf E 44
  ln_prev := E.trace 65
  ln := E.trace 66
  mr1 := mrOf E 67
  mr2 := mrOf E 75
  mr3 := mrOf E 83

/-- The `.s0` instance of `pubOfState`, for callers with no state to supply. -/
def pubOf (E : Env K) : Pub K := pubOfState E .s0

/-- The formula-decomposition columns read off trace columns `47…64`. -/
def decOf (E : Env K) : Dec K :=
  ⟨fpOf E 47, fpOf E 50, fpOf E 53, fpOf E 56, fpOf E 59, fpOf E 62⟩

/-- The auxiliary gate witnesses read off trace columns `91, 92`. -/
def exOf (E : Env K) : Extra K := ⟨E.trace 91, E.trace 92⟩

/-- The environment reconstituted from `E`'s own slots. -/
def reEnv (E : Env K) (st : State) : Env K :=
  computeEnvFull (inpOf E) (opOf E) (pubOfState E st) (decOf E) (exOf E)

/-! ## 3. Agreement -/

/-- **Trace agreement on every column the compute AIR can read.**  The hypothesis `hz` pins the
    one determined slot: column `93` is `computeEnvFull`'s honest `z⁻¹` witness and `z` is
    challenge `1`, so the projection cannot choose them independently. -/
theorem reEnv_trace_agree (E : Env K) (st : State) (hz : E.trace 93 = (E.chal 1)⁻¹) :
    ∀ i, i < 94 → (reEnv E st).trace i = E.trace i := by
  intro i hi
  simp only [reEnv]
  interval_cases i
  all_goals first | rfl | exact hz.symm

/-- **Challenge agreement on all five RAP input slots.** -/
theorem reEnv_chal_agree (E : Env K) (st : State) :
    ∀ j, j < 5 → (reEnv E st).chal j = E.chal j := by
  intro j hj
  simp only [reEnv]
  interval_cases j <;> rfl

/-- **The projections reproduce `E` on every slot the compute AIR can read** — the two agreement
    facts bundled.  `traceNext` and `pub` are deliberately excluded (see the module docstring). -/
theorem computeEnvFull_projections_agree (E : Env K) (st : State)
    (hz : E.trace 93 = (E.chal 1)⁻¹) :
    (∀ i, i < 94 → (computeEnvFull (inpOf E) (opOf E) (pubOfState E st) (decOf E)
        (exOf E)).trace i = E.trace i)
      ∧ (∀ j, j < 5 → (computeEnvFull (inpOf E) (opOf E) (pubOfState E st) (decOf E)
        (exOf E)).chal j = E.chal j) :=
  ⟨reEnv_trace_agree E st hz, reEnv_chal_agree E st⟩

/-! ## 4. The payoff: `.row` constraints cannot tell the two environments apart -/

/-- **Every `.row` constraint of `Trans.computeAIRchained` evaluates the same in `E` as in the
    reconstituted environment.**  `hz` is the determined-slot hypothesis of
    `reEnv_trace_agree`; `row_constraint_eval_agree_of_zZinv` discharges it from the AIR's own
    `z · zinv = 1` gate. -/
theorem row_constraint_eval_agree (E : Env K) (st : State)
    (hz : E.trace 93 = (E.chal 1)⁻¹)
    (c : Constraint) (hc : c ∈ Trans.computeAIRchained.constraints) (hkind : c.kind = .row) :
    c.expr.eval E
      = c.expr.eval (computeEnvFull (inpOf E) (opOf E) (pubOfState E st) (decOf E) (exOf E)) :=
  Expr.eval_eq_of_rowScoped
    ((List.all_eq_true.mp computeAIR_rowScoped) c (mem_computeAIR_of_row_mem_chained hc hkind))
    (fun i hi => (reEnv_trace_agree E st hz i hi).symm)
    (fun j hj => (reEnv_chal_agree E st j hj).symm)

/-- The determined-slot hypothesis is *derived*, not assumed, whenever the AIR's own `z·zinv = 1`
    row gate (`zZinvExpr`, one of `computeAIR`'s 526 constraints) vanishes at `E`. -/
theorem trace93_eq_inv_of_zZinv (E : Env K) (h : zZinvExpr.eval E = 0) :
    E.trace 93 = (E.chal 1)⁻¹ := by
  have h1 : E.chal 1 * E.trace 93 = 1 := by
    have := h
    simp only [zZinvExpr, Expr.eval, chl, tc, Int.cast_one, sub_eq_zero] at this
    exact this
  exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm] at h1; exact h1))

/-- **`row_constraint_eval_agree` with its hypothesis discharged from the AIR itself.**  If the
    `z·zinv = 1` witness gate vanishes at `E` — it is one of the 526 `.row` constraints, so any
    hypothesis that all of them vanish supplies it — then every `.row` constraint of
    `Trans.computeAIRchained` evaluates identically in `E` and in the reconstituted environment. -/
theorem row_constraint_eval_agree_of_zZinv (E : Env K) (st : State)
    (hz : zZinvExpr.eval E = 0)
    (c : Constraint) (hc : c ∈ Trans.computeAIRchained.constraints) (hkind : c.kind = .row) :
    c.expr.eval E
      = c.expr.eval (computeEnvFull (inpOf E) (opOf E) (pubOfState E st) (decOf E) (exOf E)) :=
  row_constraint_eval_agree E st (trace93_eq_inv_of_zZinv E hz) c hc hkind

/-- `zZinvExpr` is genuinely one of `computeAIR`'s constraints, gated `.row`. -/
theorem zZinv_row_mem_computeAIR :
    (⟨.row, zZinvExpr⟩ : Constraint) ∈ computeAIR.constraints := by
  simp [computeAIR]

/-- …and hence one of `Trans.computeAIRchained`'s. -/
theorem zZinv_row_mem_chained :
    (⟨.row, zZinvExpr⟩ : Constraint) ∈ Trans.computeAIRchained.constraints := by
  simp [Trans.computeAIRchained, computeAIR]

/-- **Row-vanishing transfers wholesale.**  If every `.row` constraint of
    `Trans.computeAIRchained` vanishes at `E`, then every one of them vanishes at the
    reconstituted environment too — no side hypothesis at all, since `zZinvExpr` is itself one of
    them. -/
theorem rows_vanish_transfer (E : Env K) (st : State)
    (h : ∀ c ∈ Trans.computeAIRchained.constraints, c.kind = .row → c.expr.eval E = 0) :
    ∀ c ∈ Trans.computeAIRchained.constraints, c.kind = .row →
      c.expr.eval (computeEnvFull (inpOf E) (opOf E) (pubOfState E st) (decOf E) (exOf E)) = 0 := by
  intro c hc hkind
  have hz : zZinvExpr.eval E = 0 := h _ zZinv_row_mem_chained rfl
  rw [← row_constraint_eval_agree_of_zZinv E st hz c hc hkind]
  exact h c hc hkind

end Nock.Reified

#print axioms Nock.Reified.Expr.eval_eq_of_rowScoped
#print axioms Nock.Reified.computeAIR_rowScoped
#print axioms Nock.Reified.mem_computeAIR_of_row_mem_chained
#print axioms Nock.Reified.computeEnvFull_projections_agree
#print axioms Nock.Reified.row_constraint_eval_agree
#print axioms Nock.Reified.trace93_eq_inv_of_zZinv
#print axioms Nock.Reified.row_constraint_eval_agree_of_zZinv
#print axioms Nock.Reified.rows_vanish_transfer
